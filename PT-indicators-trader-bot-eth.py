import os
import time
import csv
import logging
import numpy as np
import pandas as pd
import websockets
import http.client
from decimal import Decimal
from datetime import datetime, timedelta
from dotenv import load_dotenv
from typing import Dict, List, Optional, Tuple, Union, Any
from coinbase.rest import RESTClient
import requests
import asyncio
import json
import talib
import atexit
import re
import hmac
import hashlib
import base64
import aiohttp
import traceback
import pytz
import sys
import uuid
import threading
import psutil
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.asymmetric import ec

# Fix for Windows asyncio event loop issue
if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Load environment variables
load_dotenv()

# Debug environment variable loading
print("Checking environment variables...")
print(f"API Key loaded: {'Yes' if os.getenv('COINBASE_API_KEY') else 'No'}")
print(f"API Secret loaded: {'Yes' if os.getenv('COINBASE_API_SECRET') else 'No'}")
print(f"API Passphrase loaded: {'Yes' if os.getenv('COINBASE_API_PASSPHRASE') else 'No'}")

# Configure timezone
est = pytz.timezone('America/New_York')

class APICache:
    """Cache for API calls to reduce redundant requests"""
    def __init__(self, default_ttl=60):  # 60 seconds default TTL
        self.cache = {}
        self.default_ttl = default_ttl
        self.locks = {}
        
    async def get(self, key):
        """Get value from cache if still valid"""
        if key in self.cache:
            entry = self.cache[key]
            if time.time() < entry['expires']:
                return entry['data']
            # If expired but still present, return the data but mark for refresh
            elif time.time() < entry['expires'] + 300:  # 5-minute grace period
                return entry['data']  # Return stale data
        return None
    
    async def set(self, key, data, ttl=None):
        """Set value in cache with expiration"""
        if ttl is None:
            ttl = self.default_ttl
        self.cache[key] = {
            'data': data,
            'expires': time.time() + ttl
        }
        return data
    
    async def invalidate(self, key):
        """Invalidate a cache entry"""
        if key in self.cache:
            del self.cache[key]
    
    async def invalidate_all(self):
        """Invalidate all cache entries"""
        self.cache.clear()
    
    async def get_lock(self, key):
        """Get a lock for a specific key to prevent concurrent requests"""
        if key not in self.locks:
            self.locks[key] = asyncio.Lock()
        return self.locks[key]

class RiskManager:
    """Advanced risk management with dynamic stops based on volatility"""
    def __init__(self, bot_instance):
        self.bot = bot_instance
        self.logger = bot_instance.logger
        
        # Initial risk parameters
        self.max_position_size_pct = 0.05  # 5% of available balance
        self.max_risk_per_trade_pct = 0.01  # 1% account risk per trade
        self.atr_stop_multiplier = 2.0  # Stop loss distance in ATR
        self.fixed_stop_pct = 0.02  # Fallback fixed stop (2%)
        
        # Trailing stop parameters
        self.atr_trailing_activation = 1.0  # Activate at 1x ATR profit
        self.atr_trailing_distance = 1.5   # Trail at 1.5x ATR
        self.min_trailing_pct = 0.005      # Minimum 0.5% trailing distance
        
        # Take profit levels (R multiples)
        self.take_profit_r_multiples = [1.5, 2.5, 4.0]
        self.position_scale_out = [0.3, 0.3, 0.4]  # 30%, 30%, 40%
        
        # Market volatility adaptive parameters
        self.high_volatility_threshold = 50  # RSI threshold
        self.volatility_adjustment_factor = 0.7  # Reduce position size in high volatility
        
        # Position cap for correlation risk
        self.max_correlated_exposure = 0.15  # 15% max exposure to correlated assets
        
        # Current market state
        self.current_atr = None
        self.current_volatility = None  # RSI-based volatility measure
    
    def update_market_state(self, atr, rsi):
        """Update current market state metrics"""
        self.current_atr = atr
        
        # Use RSI to determine volatility state
        # RSI near extremes or rapidly changing indicates higher volatility
        if rsi is not None:
            rsi_distance_from_mid = abs(rsi - 50)
            self.current_volatility = rsi_distance_from_mid / 50  # 0 to 1 scale
        else:
            self.current_volatility = 0.5  # Default mid-volatility if RSI unavailable
    
    def calculate_position_size(self, available_balance, current_price, stop_price):
        """Calculate optimal position size based on risk parameters and market conditions"""
        # Base position size on risk per trade
        stop_distance = abs(current_price - stop_price)
        risk_amount = available_balance * self.max_risk_per_trade_pct
        
        risk_based_size = risk_amount / stop_distance
        
        # Apply position size limit as percentage of account
        max_size = available_balance * self.max_position_size_pct / current_price
        
        # Adjust for market volatility
        if self.current_volatility is not None and self.current_volatility > 0.7:  # High volatility
            volatility_adjusted_size = risk_based_size * self.volatility_adjustment_factor
            self.logger.info(f"High volatility detected. Reducing position size by {(1-self.volatility_adjustment_factor)*100:.0f}%")
        else:
            volatility_adjusted_size = risk_based_size
        
        # Take the most conservative size
        final_size = min(volatility_adjusted_size, max_size)
        
        self.logger.info(
            f"Position sizing: Risk-based size: {risk_based_size:.6f}, "
            f"Max size: {max_size:.6f}, "
            f"Volatility-adjusted: {volatility_adjusted_size:.6f}, "
            f"Final: {final_size:.6f}"
        )
        
        return final_size
    
    def calculate_stop_loss(self, side, entry_price):
        """Calculate ATR-based stop loss with fallback to fixed percentage"""
        if self.current_atr is not None and self.current_atr > 0:
            # ATR-based stop
            stop_distance = self.current_atr * self.atr_stop_multiplier
            
            # Use larger stop distance in high volatility
            if self.current_volatility is not None and self.current_volatility > 0.7:
                stop_distance *= (1 + self.current_volatility * 0.3)  # Up to 30% wider stops in high volatility
                self.logger.info(f"High volatility - widening stop loss by {self.current_volatility * 30:.1f}%")
        else:
            # Fixed percentage fallback
            stop_distance = entry_price * self.fixed_stop_pct
            
        if side == "long":
            stop_price = entry_price - stop_distance
        else:  # short
            stop_price = entry_price + stop_distance
            
        # Log the stop calculation
        self.logger.info(
            f"{side.upper()} position stop calculation: "
            f"Entry: {entry_price:.2f}, "
            f"ATR: {self.current_atr if self.current_atr else 'N/A'}, "
            f"Stop distance: {stop_distance:.2f}, "
            f"Stop price: {stop_price:.2f}"
        )
        
        return stop_price
    
    def calculate_take_profits(self, side, entry_price, stop_loss):
        """Calculate take profit levels based on R-multiples from stop distance"""
        stop_distance = abs(entry_price - stop_loss)
        take_profits = []
        
        for r_multiple in self.take_profit_r_multiples:
            if side == "long":
                tp_price = entry_price + (stop_distance * r_multiple)
            else:  # short
                tp_price = entry_price - (stop_distance * r_multiple)
            take_profits.append(tp_price)
            
        self.logger.info(
            f"Take profit levels calculated for {side.upper()}: "
            f"{[f'{tp:.2f}' for tp in take_profits]}"
        )
            
        return take_profits
    
    def should_activate_trailing_stop(self, position, current_price):
        """Determine if trailing stop should be activated based on ATR or price movement"""
        if position["trailing_stop_activated"]:
            return True
            
        entry_price = position["entry_price"]
        side = position["side"]
        
        # Calculate profit in price terms
        if side == "long":
            price_profit = current_price - entry_price
            profit_pct = price_profit / entry_price
        else:  # short
            price_profit = entry_price - current_price
            profit_pct = price_profit / entry_price
        
        # Check if profit exceeds threshold for trailing stop activation
        atr_profit_threshold = 0
        if self.current_atr:
            atr_profit_threshold = self.current_atr * self.atr_trailing_activation
            
        # Activate if either ATR threshold or percentage threshold is met
        should_activate = (
            (self.current_atr and price_profit >= atr_profit_threshold) or
            profit_pct >= self.bot.trailing_stop_activation
        )
        
        if should_activate:
            self.logger.info(
                f"Trailing stop activation for {side.upper()}: "
                f"Profit: {price_profit:.2f} ({profit_pct:.2%}), "
                f"ATR: {self.current_atr if self.current_atr else 'N/A'}, "
                f"ATR threshold: {atr_profit_threshold:.2f}"
            )
            
        return should_activate
    
    def calculate_trailing_stop_price(self, position, current_price):
        """Calculate dynamic trailing stop based on ATR and market volatility"""
        side = position["side"]
        
        # Use ATR for trailing distance if available, fallback to percentage
        if self.current_atr:
            # Adjust trailing distance based on volatility
            volatility_factor = 1.0
            if self.current_volatility is not None:
                # Wider trailing stops in high volatility
                volatility_factor = 1.0 + (self.current_volatility * 0.5)  # Up to 50% wider in high volatility
            
            trailing_distance = self.current_atr * self.atr_trailing_distance * volatility_factor
        else:
            trailing_distance = current_price * self.bot.trailing_stop_distance
        
        # Ensure minimum trailing distance
        min_trailing_distance = current_price * self.min_trailing_pct
        trailing_distance = max(trailing_distance, min_trailing_distance)
        
        # Calculate trailing stop price
        if side == "long":
            trailing_stop_price = current_price - trailing_distance
            
            # Ensure trailing stop only moves up for long positions
            if position.get("trailing_stop_price") and trailing_stop_price < position["trailing_stop_price"]:
                return position["trailing_stop_price"]
        else:  # short
            trailing_stop_price = current_price + trailing_distance
            
            # Ensure trailing stop only moves down for short positions
            if position.get("trailing_stop_price") and trailing_stop_price > position["trailing_stop_price"]:
                return position["trailing_stop_price"]
        
        self.logger.info(
            f"Trailing stop updated for {side.upper()}: "
            f"Price: {current_price:.2f}, "
            f"ATR: {self.current_atr if self.current_atr else 'N/A'}, "
            f"Trailing distance: {trailing_distance:.2f}, "
            f"Stop price: {trailing_stop_price:.2f}"
        )
        
        return trailing_stop_price
    
class TradingMetrics:        
    def __init__(self, metrics_file='trading_metrics.json'):
        """
        Initialize Trading Metrics tracking
        
        :param metrics_file: Path to store persistent metrics
        """
        self.metrics_file = metrics_file
        self.trades = []
        self.load_metrics()
    
    def load_metrics(self):
        """
        Load existing metrics from file
        """
        try:
            if os.path.exists(self.metrics_file):
                with open(self.metrics_file, 'r') as f:
                    saved_data = json.load(f)
                    self.trades = saved_data.get('trades', [])
        except Exception as e:
            print(f"Error loading metrics: {e}")
            self.trades = []
    
    def save_metrics(self):
        """
        Save metrics to persistent storage
        """
        try:
            data_to_save = {
                'trades': self.trades,
                'last_updated': datetime.now().isoformat()
            }
            with open(self.metrics_file, 'w') as f:
                json.dump(data_to_save, f, indent=4)
        except Exception as e:
            print(f"Error saving metrics: {e}")
    
    def record_trade(self, trade_data):
        """
        Record a new trade
        
        :param trade_data: Dictionary containing trade details
        """
        try:
            # Ensure required fields are present
            trade_entry = {
                'timestamp': datetime.now().isoformat(),
                'pnl_percent': trade_data.get('pnl', 0),
                'trade_type': trade_data.get('event_type', 'UNKNOWN'),
                'entry_price': trade_data.get('price', 0),
                'size': trade_data.get('size', 0)
            }
            
            self.trades.append(trade_entry)
            
            # Keep only last 1000 trades to prevent file growth
            self.trades = self.trades[-1000:]
            
            # Save updated metrics
            self.save_metrics()
        except Exception as e:
            print(f"Error recording trade: {e}")
    
    def get_summary(self):
        """
        Generate comprehensive trading performance summary
        
        :return: Dictionary of performance metrics
        """
        if not self.trades:
            return {
                'total_trades': 0,
                'win_rate': 0,
                'profit_factor': 1,
                'max_drawdown': 0,
                'avg_win': 0,
                'avg_loss': 0,
                'largest_win': 0,
                'largest_loss': 0,
                'current_streak': 0
            }
        
        # Convert trades to DataFrame for easier analysis
        df = pd.DataFrame(self.trades)
        df['pnl_percent'] = pd.to_numeric(df['pnl_percent'], errors='coerce')
        
        # Calculate metrics
        total_trades = len(df)
        wins = df[df['pnl_percent'] > 0]
        losses = df[df['pnl_percent'] < 0]
        
        # Win rate calculation
        win_rate = len(wins) / total_trades * 100 if total_trades > 0 else 0
        
        # Profit factor
        total_wins = wins['pnl_percent'].sum()
        total_losses = abs(losses['pnl_percent'].sum()) if len(losses) > 0 else 1
        profit_factor = total_wins / total_losses if total_losses > 0 else total_wins
        
        # Drawdown calculation
        cumulative_pnl = df['pnl_percent'].cumsum()
        max_drawdown = (cumulative_pnl.cummax() - cumulative_pnl).max()
        
        # Current streak calculation
        pnl_signs = np.sign(df['pnl_percent'])
        current_streak = self._calculate_current_streak(pnl_signs)
        
        return {
            'total_trades': total_trades,
            'win_rate': win_rate,
            'profit_factor': profit_factor,
            'max_drawdown': max_drawdown,
            'avg_win': wins['pnl_percent'].mean() if len(wins) > 0 else 0,
            'avg_loss': losses['pnl_percent'].mean() if len(losses) > 0 else 0,
            'largest_win': wins['pnl_percent'].max() if len(wins) > 0 else 0,
            'largest_loss': losses['pnl_percent'].min() if len(losses) > 0 else 0,
            'current_streak': current_streak
        }
    
    def _calculate_current_streak(self, pnl_signs):
        """
        Calculate current winning or losing streak
        
        :param pnl_signs: Array of trade signs (+1, -1, 0)
        :return: Streak count (positive for winning, negative for losing)
        """
        if len(pnl_signs) == 0:
            return 0
        
        # Get last streak
        streak = 0
        for sign in reversed(pnl_signs):
            if sign == 0:  # Skip zero trades
                continue
            if streak == 0:
                streak = sign
            elif sign == streak / abs(streak):
                streak += sign
            else:
                break
        
        return streak
    
    def get_weekly_performance(self, weeks=4):
        """
        Get weekly performance breakdown
        
        :param weeks: Number of weeks to analyze
        :return: Dictionary of weekly performance
        """
        if not self.trades:
            return {}
        
        # Convert trades to DataFrame
        df = pd.DataFrame(self.trades)
        df['timestamp'] = pd.to_datetime(df['timestamp'])
        df['week'] = df['timestamp'].dt.to_period('W')
        
        # Group by week and calculate total PNL
        weekly_pnl = df.groupby('week')['pnl_percent'].sum()
        
        # Get last 4 weeks (or fewer if not enough data)
        latest_weeks = weekly_pnl.sort_index().tail(weeks)
        
        # Convert to dictionary with week as string key
        return {str(week): pnl for week, pnl in latest_weeks.items()}
    
    def get_last_n_trades(self, n=5):
        """
        Get last N trades
        
        :param n: Number of recent trades to retrieve
        :return: List of recent trades
        """
        return self.trades[-n:]

class ExtendedTradeLogger:
    def __init__(self, log_directory='trade_logs'):
        """
        Initialize extended trade logger
        
        :param log_directory: Directory to store log files
        """
        self.log_directory = log_directory
        os.makedirs(log_directory, exist_ok=True)
        
        # Prepare logging files
        self.csv_log_path = os.path.join(log_directory, f'trades_{datetime.now().strftime("%Y%m%d_%H%M%S")}.csv')
        self.json_log_path = os.path.join(log_directory, f'trades_{datetime.now().strftime("%Y%m%d_%H%M%S")}.json')
        
        # Initialize log files with headers
        self._initialize_csv_log()
        self._initialize_json_log()
    
    def _initialize_csv_log(self):
        """
        Initialize CSV log file with headers
        """
        csv_columns = [
            'timestamp', 'event_type', 'price', 'size', 'pnl', 'stop_loss', 
            'take_profit', 'volatility', 'market_sentiment', 
            'cpu_usage', 'memory_usage', 'additional_context'
        ]
        
        with open(self.csv_log_path, 'w', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=csv_columns)
            writer.writeheader()
    
    def _initialize_json_log(self):
        """
        Initialize JSON log file with an empty list
        """
        with open(self.json_log_path, 'w') as jsonfile:
            json.dump([], jsonfile)
    
    def log_trade_event(self, event_type, data):
        """
        Log trade event to CSV and JSON
        
        :param event_type: Type of trade event
        :param data: Dictionary of trade event data
        """
        try:
            # Capture system resource usage
            system_metrics = self._get_system_metrics()
            
            # Prepare log entry
            log_entry = {
                'timestamp': datetime.now().isoformat(),
                'event_type': event_type,
                'price': data.get('price', 'N/A'),
                'size': data.get('size', 'N/A'),
                'pnl': data.get('pnl', 'N/A'),
                'stop_loss': data.get('stop_loss', 'N/A'),
                'take_profit': data.get('take_profit', 'N/A'),
                'volatility': data.get('volatility', 'N/A'),
                'market_sentiment': data.get('market_sentiment', 'N/A'),
                'cpu_usage': system_metrics['cpu_usage'],
                'memory_usage': system_metrics['memory_usage'],
                'additional_context': json.dumps(data)
            }
            
            # Log to CSV
            with open(self.csv_log_path, 'a', newline='') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=log_entry.keys())
                writer.writerow(log_entry)
            
            # Log to JSON
            with open(self.json_log_path, 'r+') as jsonfile:
                file_data = json.load(jsonfile)
                file_data.append(log_entry)
                jsonfile.seek(0)
                json.dump(file_data, jsonfile, indent=4)
        
        except Exception as e:
            print(f"Error logging trade event: {e}")
    
    def _get_system_metrics(self):
        """
        Capture current system resource usage
        
        :return: Dictionary of system metrics
        """
        try:
            return {
                'cpu_usage': psutil.cpu_percent(),
                'memory_usage': psutil.virtual_memory().percent
            }
        except Exception as e:
            print(f"Error capturing system metrics: {e}")
            return {
                'cpu_usage': 'N/A',
                'memory_usage': 'N/A'
            }
    
    def generate_performance_report(self):
        """
        Generate performance report using PerformanceAnalyzer
        
        :return: Performance report string
        """
        try:
            analyzer = PerformanceAnalyzer(self.csv_log_path)
            return analyzer.generate_performance_report()
        except Exception as e:
            print(f"Error generating performance report: {e}")
            return "Unable to generate performance report."

class PerformanceAnalyzer:
    def __init__(self, trading_data_file):
        """
        Initialize Performance Analyzer with trading log data
        
        :param trading_data_file: Path to the CSV file containing trading log data
        """
        try:
            self.df = pd.read_csv(trading_data_file)
            self.df['timestamp'] = pd.to_datetime(self.df['timestamp'])
        except Exception as e:
            print(f"Error loading trading data: {e}")
            self.df = pd.DataFrame()
    
    def calculate_performance_metrics(self):
        """
        Calculate comprehensive performance metrics
        
        :return: Dictionary of performance metrics
        """
        if self.df.empty:
            return {
                'total_trades': 0,
                'win_rate': 0,
                'total_pnl': 0,
                'max_drawdown': 0,
                'sharpe_ratio': 0,
                'trade_duration_analysis': {}
            }
        
        metrics = {
            'total_trades': len(self.df),
            'win_rate': self._calculate_win_rate(),
            'total_pnl': self._calculate_total_pnl(),
            'max_drawdown': self._calculate_max_drawdown(),
            'sharpe_ratio': self._calculate_sharpe_ratio(),
            'trade_duration_analysis': self._analyze_trade_durations()
        }
        return metrics
    
    def _calculate_win_rate(self):
        """
        Calculate percentage of profitable trades
        
        :return: Win rate percentage
        """
        # Assume 'pnl' column represents percentage profit/loss
        profitable_trades = self.df[self.df['pnl'] > 0]
        return len(profitable_trades) / len(self.df) * 100 if len(self.df) > 0 else 0
    
    def _calculate_total_pnl(self):
        """
        Calculate total profit and loss
        
        :return: Total PNL percentage
        """
        return self.df['pnl'].sum() if 'pnl' in self.df.columns else 0
    
    def _calculate_max_drawdown(self):
        """
        Calculate maximum portfolio drawdown
        
        :return: Maximum drawdown percentage
        """
        if 'pnl' not in self.df.columns:
            return 0
        
        cumulative_pnl = self.df['pnl'].cumsum()
        return (cumulative_pnl.cummax() - cumulative_pnl).max()
    
    def _calculate_sharpe_ratio(self, risk_free_rate=0.01):
        """
        Calculate Sharpe ratio of trading performance
        
        :param risk_free_rate: Annual risk-free rate
        :return: Sharpe ratio
        """
        if 'pnl' not in self.df.columns or len(self.df) < 2:
            return 0
        
        returns = self.df['pnl']
        excess_returns = returns - risk_free_rate
        
        # Handle potential division by zero
        return excess_returns.mean() / (excess_returns.std() or 1)
    
    def _analyze_trade_durations(self):
        """
        Analyze trade duration characteristics
        
        :return: Dictionary of trade duration metrics
        """
        # Check if required columns exist
        if not all(col in self.df.columns for col in ['entry_time', 'exit_time']):
            return {
                'avg_trade_duration': 0,
                'median_trade_duration': 0,
                'max_trade_duration': 0,
                'min_trade_duration': 0
            }
        
        # Convert times to datetime and calculate duration
        self.df['entry_time'] = pd.to_datetime(self.df['entry_time'])
        self.df['exit_time'] = pd.to_datetime(self.df['exit_time'])
        self.df['trade_duration'] = (self.df['exit_time'] - self.df['entry_time']).dt.total_seconds() / 3600  # hours
        
        return {
            'avg_trade_duration': self.df['trade_duration'].mean(),
            'median_trade_duration': self.df['trade_duration'].median(),
            'max_trade_duration': self.df['trade_duration'].max(),
            'min_trade_duration': self.df['trade_duration'].min()
        }
    
    def generate_performance_report(self):
        """
        Generate a comprehensive performance report
        
        :return: Formatted performance report string
        """
        metrics = self.calculate_performance_metrics()
        
        report = f"""
        === Trading Performance Report ===
        
        Total Trades: {metrics['total_trades']}
        Win Rate: {metrics['win_rate']:.2f}%
        Total P/L: {metrics['total_pnl']:.2f}%
        Max Drawdown: {metrics['max_drawdown']:.2f}%
        Sharpe Ratio: {metrics['sharpe_ratio']:.2f}
        
        Trade Duration Analysis:
        - Average Duration: {metrics['trade_duration_analysis'].get('avg_trade_duration', 0):.2f} hours
        - Median Duration: {metrics['trade_duration_analysis'].get('median_trade_duration', 0):.2f} hours
        - Longest Trade: {metrics['trade_duration_analysis'].get('max_trade_duration', 0):.2f} hours
        - Shortest Trade: {metrics['trade_duration_analysis'].get('min_trade_duration', 0):.2f} hours
        """
        
        return report

class DiscordLogNotifier:
    def __init__(self, webhook_url, log_directory='trade_logs'):
        """
        Initialize Discord Log Notifier
        
        :param webhook_url: Discord webhook URL for notifications
        :param log_directory: Directory to monitor for log files
        """
        self.webhook_url = webhook_url
        self.log_directory = log_directory
        
        # Ensure log directory exists
        os.makedirs(log_directory, exist_ok=True)
    
    async def send_discord_log_summary(self, log_file_path):
        """
        Generate and send a summary of the log file to Discord
        
        :param log_file_path: Path to the log CSV file
        """
        try:
            # Read the CSV file
            log_summary = self._analyze_log_file(log_file_path)
            
            # Prepare Discord message
            message = self._format_log_summary_message(log_summary)
            
            # Send to Discord
            await self._send_discord_notification(
                "📊 Trading Log Summary", 
                message, 
                0x1E90FF  # Blue color
            )
        
        except Exception as e:
            print(f"Error sending log summary to Discord: {e}")
    
    def _analyze_log_file(self, log_file_path):
        """
        Analyze the log file and extract key metrics
        
        :param log_file_path: Path to the log CSV file
        :return: Dictionary of log file summary
        """
        try:
            # Read the CSV file
            df = pd.read_csv(log_file_path)
            
            # Ensure the DataFrame is not empty
            if df.empty:
                return {
                    'total_trades': 0,
                    'profitable_trades': 0,
                    'total_pnl': 0,
                    'pnl_range': {'min': 0, 'max': 0},
                    'trade_types': {},
                    'last_trade_time': None
                }
            
            # Calculate metrics
            total_trades = len(df)
            profitable_trades = len(df[df['pnl'] > 0])
            total_pnl = df['pnl'].sum()
            
            # PNL range
            pnl_range = {
                'min': df['pnl'].min(),
                'max': df['pnl'].max()
            }
            
            # Trade type breakdown
            trade_types = df['event_type'].value_counts().to_dict()
            
            # Last trade time
            last_trade_time = df['timestamp'].max() if 'timestamp' in df.columns else None
            
            return {
                'total_trades': total_trades,
                'profitable_trades': profitable_trades,
                'total_pnl': total_pnl,
                'pnl_range': pnl_range,
                'trade_types': trade_types,
                'last_trade_time': last_trade_time
            }
        
        except Exception as e:
            print(f"Error analyzing log file: {e}")
            return {
                'total_trades': 0,
                'profitable_trades': 0,
                'total_pnl': 0,
                'pnl_range': {'min': 0, 'max': 0},
                'trade_types': {},
                'last_trade_time': None
            }
            
            
    def _format_log_summary_message(self, summary):
        """
        Format log summary into a readable Discord message
        
        :param summary: Dictionary of log summary
        :return: Formatted message string
        """
        # Handle empty or invalid summary
        if summary['total_trades'] == 0:
            return "No trading activity recorded in this log period."
        
        # Calculate win rate
        win_rate = (summary['profitable_trades'] / summary['total_trades']) * 100 if summary['total_trades'] > 0 else 0
        
        # Prepare trade type breakdown
        trade_types_str = "\n".join([
            f"• {trade_type}: {count}"
            for trade_type, count in summary['trade_types'].items()
        ])
        
        # Prepare message
        message = (
            f"**Trading Log Summary**\n\n"
            f"📊 Total Trades: {summary['total_trades']}\n"
            f"✅ Profitable Trades: {summary['profitable_trades']} ({win_rate:.2f}%)\n"
            f"💰 Total P/L: {summary['total_pnl']:.2f}%\n\n"
            f"📈 Best Trade: {summary['pnl_range']['max']:.2f}%\n"
            f"📉 Worst Trade: {summary['pnl_range']['min']:.2f}%\n\n"
            f"**Trade Type Breakdown:**\n"
            f"{trade_types_str}\n\n"
            f"🕒 Last Trade: {summary['last_trade_time'] or 'N/A'}"
        )
        
        return message
    
    async def _send_discord_notification(self, title, message, color=0xEE82EE ):
        """
        Send notification to Discord webhook
        
        :param title: Notification title
        :param message: Notification message
        :param color: Embed color
        """
        try:
            webhook_data = {
                "username": "Trading Bot Log Notifier",
                "embeds": [{
                    "title": title,
                    "description": message,
                    "color": color,
                    "timestamp": datetime.now().isoformat()
                }]
            }
            
            # Send with rate limiting and fallback mechanisms
            max_retries = 3
            retry_delay = 5  # seconds
            
            for attempt in range(max_retries):
                try:
                    connector = aiohttp.TCPConnector(ssl=False) if sys.platform == 'win32' else None
                    
                    async with aiohttp.ClientSession(connector=connector) as session:
                        async with session.post(self.webhook_url, json=webhook_data, timeout=15) as response:
                            if response.status == 204:  # Discord returns 204 No Content on success
                                return  # Success
                            elif response.status == 429:  # Rate limited
                                retry_data = await response.json()
                                retry_after = retry_data.get('retry_after', retry_delay)
                                print(f"Rate limited by Discord. Waiting {retry_after} seconds.")
                                await asyncio.sleep(float(retry_after))
                            else:
                                print(f"Discord webhook error: {response.status}")
                                await asyncio.sleep(retry_delay)
                except Exception as e:
                    print(f"Discord webhook connection error: {e}")
                    await asyncio.sleep(retry_delay)
        
        except Exception as e:
            print(f"Error sending Discord notification: {e}")
    
    async def monitor_and_notify(self, interval_hours=24):
        """
        Continuously monitor log directory and send summaries
        
        :param interval_hours: Hours between log summary notifications
        """
        while True:
            try:
                # Find the most recent log file
                log_files = [
                    os.path.join(self.log_directory, f) 
                    for f in os.listdir(self.log_directory) 
                    if f.endswith('.csv')
                ]
                
                if log_files:
                    # Get the most recent log file
                    latest_log = max(log_files, key=os.path.getctime)
                    
                    # Send log summary
                    await self.send_discord_log_summary(latest_log)
                
            except Exception as e:
                print(f"Error in log monitoring: {e}")
            
            # Wait for specified interval
            await asyncio.sleep(interval_hours * 3600)

# Utility function to enhance trading bot with extended logging
def enhance_trading_bot_logging(bot_instance):
    """
    Enhance trading bot with extended logging capabilities
    
    :param bot_instance: Instance of AdvancedTradingBot
    """
    # Create extended logger
    bot_instance.extended_logger = ExtendedTradeLogger()
    
    # Override existing logging method
    original_log_trade_event = bot_instance.log_trade_event
    def enhanced_log_trade_event(event_type, data):
        # Call original method
        original_log_trade_event(event_type, data)
        
        # Add extended logging
        bot_instance.extended_logger.log_trade_event(event_type, data)
    
    bot_instance.log_trade_event = enhanced_log_trade_event
    
    # Add performance report method
    def generate_performance_report():
        """Generate comprehensive performance report"""
        return bot_instance.extended_logger.generate_performance_report()
    
    bot_instance.generate_performance_report = generate_performance_report

class AdvancedTradingBot:
    def __init__(self, mode="sandbox", product_id: str = "ETH-USD"):
        """Initialize the trading bot with logging and other setup"""
        # Set initial attributes
        self.product_id = product_id
        self.current_order_id = 0
        self.is_running = False
        self.last_api_call = 0
        self.rate_limit_delay = 0.334
        self.trading_mode = mode
        
        # Initialize logging first
        self.logger = logging.getLogger("TradingBot")
        self.setup_logging()
        
        # Load configuration
        self._load_config()
        self._init_credentials()
        
        # Ensure RSI settings exist
        self.rsi_oversold = 30
        self.rsi_overbought = 70
        
        # Add risk management parameters
        self.max_daily_loss = 0.05  # 5% maximum daily loss
        self.trailing_stop_activation = 0.015  # 1.5% profit for trailing stop activation
        self.trailing_stop_distance = 0.01  
        
        # Initialize API caching
        self.api_cache = APICache()
        self.historical_cache_ttl = 300  # 5 minutes for historical data
        self.price_cache_ttl = 10        # 10 seconds for price data
        self.account_cache_ttl = 60      # 60 seconds for account data

        # Initialize last notification time
        self._last_notification_time = datetime.now() - timedelta(hours=1)
        self._last_logged_price = None

        # Add a flag for initial notification
        self._initial_notification_sent = False
        
        # Initialize open_positions dict and current price
        self.open_positions = {}
        self.current_price = 0
        
        # DNS Fallback configuration
        self.dns_fallbacks = [
            "api.exchange.coinbase.com",
            "api-public.sandbox.exchange.coinbase.com",
            "exchange.coinbase.com"
        ]
        
        try:
            # Initialize client (synchronously)
            self.initialize_client()
            
            # Initialize additional components
            self.metrics = TradingMetrics()
            self.risk_manager = RiskManager(self)
            
            # Add extended logging
            enhance_trading_bot_logging(self)
            
            self.logger.info("Bot initialization completed successfully")
            self.is_initialized = True
        except Exception as e:
            self.logger.error(f"Failed to initialize bot: {str(e)}")
            self.is_initialized = False
            raise
   
    def log_trade_event(self, event_type, data):
        """Log trade event to CSV and JSON"""
        try:
            # Prepare log entry
            log_entry = {
                'timestamp': datetime.now().isoformat(),
                'event_type': event_type,
                'price': data.get('price', 'N/A'),
                'size': data.get('size', 'N/A'),
                'pnl': data.get('pnl', 'N/A'),
                'stop_loss': data.get('stop_loss', 'N/A'),
                'take_profit': data.get('take_profit', 'N/A'),
                'reason': data.get('reason', '')
            }
            
            # Add indicator values if available
            if hasattr(self, 'current_indicators') and self.current_indicators is not None:
                log_entry.update({
                    'rsi': self.current_indicators.get('rsi', 'N/A'),
                    'macd': self.current_indicators.get('macd', 'N/A'),
                    'macd_signal': self.current_indicators.get('macd_signal', 'N/A'),
                    'ma_50': self.current_indicators.get('ma_50', 'N/A'),
                    'ma_200': self.current_indicators.get('ma_200', 'N/A'),
                    'atr': self.current_indicators.get('atr', 'N/A')
                })

            # Log to CSV
            csv_writer = csv.DictWriter(self.trade_csv, fieldnames=log_entry.keys())
            csv_writer.writerow(log_entry)
            self.trade_csv.flush()

            # Log to trade logger
            self.trade_logger.info(json.dumps(log_entry))

        except Exception as e:
            self.logger.error(f"Error logging trade event: {str(e)}")
            
    def _load_config(self):
        """Load configuration from environment variables with defaults"""
        # Trading parameters from environment
        self.paper_trading = os.getenv('PAPER_TRADING', 'false').lower() == 'true'
        
        # API endpoint configuration
        self.historical_url = "api.exchange.coinbase.com"
        self.market_data_url = "api.exchange.coinbase.com"
        self.ws_url = "wss://ws-feed.exchange.coinbase.com"
        
        # Trading URL can be sandbox or live based on environment
        if os.getenv('PAPER_TRADING', 'false').lower() == 'true':
            self.trading_url = "api-public.sandbox.exchange.coinbase.com"
        else:
            self.trading_url = "api.exchange.coinbase.com"

        print(f"Using trading endpoint: {self.trading_url}")
            
        # Set up cleanup lock
        self._cleanup_lock = threading.Lock()
        self._cleanup_performed = False
            
    def _init_credentials(self):
        """Initialize API credentials from environment variables"""
        # Initialize trading credentials
        self.trading_api_key = os.getenv('COINBASE_API_KEY')
        self.trading_api_secret = os.getenv('COINBASE_API_SECRET')
        self.trading_api_passphrase = os.getenv('COINBASE_API_PASSPHRASE')
        
        # Set WebSocket compatibility attributes
        self.api_key = self.trading_api_key
        self.api_secret = self.trading_api_secret
        self.api_passphrase = self.trading_api_passphrase
        
        # Historical data credentials (Live)
        self.historical_api_key = os.getenv('CB_HISTORICAL_API_KEY', self.trading_api_key)
        self.historical_api_secret = os.getenv('CB_HISTORICAL_API_SECRET', self.trading_api_secret)
        
        # Initialize Discord webhook
        self.discord_webhook_url = os.getenv('DISCORD_WEBHOOK_URL')
        if not self.discord_webhook_url:
            self.logger.warning("Discord notifications disabled - webhook URL not set")
        else:
            self.logger.info("Discord notifications enabled")
            
        # Validate required credentials
        if not all([self.trading_api_key, self.trading_api_secret, self.trading_api_passphrase]):
            self.logger.error("Missing required API credentials")
            raise ValueError("API credentials missing in .env file")
    
    def setup_logging(self):
        """Configure enhanced logging with error reporting"""
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler("trading_bot.log", mode='a', encoding='utf-8'),
                logging.StreamHandler(sys.stdout)
            ]
        )
        
        # Add error reporting mechanism
        def handle_exception(exc_type, exc_value, exc_traceback):
            if issubclass(exc_type, KeyboardInterrupt):
                sys.__excepthook__(exc_type, exc_value, exc_traceback)
                return
            
            logging.error("Uncaught exception", exc_info=(exc_type, exc_value, exc_traceback))
            
            # Optional: Send discord notification for critical errors
            if hasattr(self, 'send_discord_notification'):
                asyncio.create_task(
                    self.send_discord_notification(
                        "🚨 Critical Bot Error", 
                        f"An uncaught exception occurred: {exc_value}",
                        0xFF0000  # Red
                    )
                )

        sys.excepthook = handle_exception
            
    def setup_trade_logging(self):
        """Set up enhanced trade logging"""
        # Create a specific logger for trades
        self.trade_logger = logging.getLogger("TradeEvents")
        self.trade_logger.setLevel(logging.INFO)
        
        # Create handlers
        trade_file_handler = logging.FileHandler("trade_events.log")
        formatter = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
        trade_file_handler.setFormatter(formatter)
        
        # Clear existing handlers to prevent duplication
        if self.trade_logger.hasHandlers():
            self.trade_logger.handlers.clear()
        
        self.trade_logger.addHandler(trade_file_handler)
        
        # Create CSV file for structured trade data
        self.trade_csv = open("trade_history.csv", "a")
        
        # Write header if file is empty
        if os.path.getsize("trade_history.csv") == 0:
            header = "timestamp,event_type,price,size,pnl,stop_loss,take_profit,reason,"
            header += "rsi,macd,macd_signal,ma_50,ma_200,atr\n"
            self.trade_csv.write(header)
            self.trade_csv.flush()
        
        # Register cleanup for trade CSV
        atexit.register(self._close_trade_csv)
        
        self.logger.info("Trade logging initialized")

    def _close_trade_csv(self):
        """Close trade CSV file"""
        if hasattr(self, 'trade_csv') and self.trade_csv:
            try:
                self.trade_csv.close()
            except Exception as e:
                self.logger.error(f"Error closing trade CSV: {str(e)}")
                
    def initialize_client(self):
        """Initialize Coinbase client using REST authentication"""
        try:
            self.logger.info("Loading API credentials...")
            
            # Test connection
            self._test_api_connection()

            self.logger.info(f"Initialized Coinbase client for {self.product_id}")

        except Exception as e:
            error_msg = f"Failed to initialize Coinbase client: {str(e)}"
            self.logger.error(error_msg)
            raise
    
    async def _get_server_time_async(self) -> int:
        """Asynchronous server time fetch"""
        try:
            async with aiohttp.ClientSession() as session:
                url = f'https://{self.trading_url}/time'
                async with session.get(url, timeout=15) as response:
                    if response.status == 200:
                        data = await response.json()
                        return int(float(data.get('epoch', time.time())))
                    self.logger.error(f"Server time request failed: {response.status}")
                    return int(time.time())
        except Exception as e:
            self.logger.error(f"Error getting server time async: {str(e)}")
            return int(time.time())
    
    def _test_api_connection(self):
        """Test connection to API with proper message signing."""
        try:
            server_time = self._get_server_time()
            timestamp = str(server_time)

            request_path = "/time"  # Ensure correct API path format
            method = "GET"
            body = ""  # No body for GET requests

            # Generate the correct signature
            signature = self._generate_signature_trading(method, request_path, body)

            headers = {
                "CB-ACCESS-KEY": self.trading_api_key,
                "CB-ACCESS-TIMESTAMP": timestamp,
                "CB-ACCESS-PASSPHRASE": self.trading_api_passphrase,
                "CB-ACCESS-SIGN": signature,
                "Content-Type": "application/json",
                "User-Agent": "CoinbaseAdvancedTrader/1.0"
            }

            conn = http.client.HTTPSConnection(self.trading_url, timeout=15)
            conn.request(method, request_path, headers=headers)
            response = conn.getresponse()
            response_body = response.read().decode("utf-8")

            if response.status != 200:
                self.logger.error(f"Response: {response.status} {response.reason}")
                self.logger.error(f"Response body: {response_body}")
                raise ConnectionError(f"API test failed: {response.status} {response.reason} - {response_body}")

            conn.close()
            self.logger.info("API connection test successful")
            return True

        except Exception as e:
            self.logger.error(f"API connection test failed: {str(e)}")
            raise
        
    async def get_btc_market_data(self):
        """Fetch current ETH market data from Coinbase API"""
        try:
            async with aiohttp.ClientSession() as session:
                # Current price
                ticker_url = f"https://api.exchange.coinbase.com/products/{self.product_id}/ticker"
                async with session.get(ticker_url) as resp:
                    ticker_data = await resp.json()
                    current_price = float(ticker_data['price'])

                # 24h stats
                stats_url = f"https://api.exchange.coinbase.com/products/{self.product_id}/stats"
                async with session.get(stats_url) as resp:
                    stats_data = await resp.json()
                    high_24h = float(stats_data['high'])
                    low_24h = float(stats_data['low'])
                    percent_change_24h = round(((current_price - float(stats_data['open'])) / float(stats_data['open'])) * 100, 1)

                return {
                    'current_price': current_price,
                    'high_24h': high_24h,
                    'low_24h': low_24h,
                    'percent_change_24h': percent_change_24h
                }

        except Exception as e:
            self.logger.error(f"Error fetching {self.product_id} market data: {str(e)}")
            return {}
            
    def _generate_signature_trading(self, method: str, request_path: str, body: str = "") -> str:
        """Generate HMAC-SHA256 signature for Coinbase API authentication."""
        try:
            timestamp = str(self._get_server_time())

            # Ensure request_path starts with "/"
            if not request_path.startswith("/"):
                request_path = "/" + request_path

            message = timestamp + method.upper() + request_path + body
            key = base64.b64decode(self.trading_api_secret.strip())

            signature = hmac.new(key, message.encode("utf-8"), hashlib.sha256).digest()
            return base64.b64encode(signature).decode("utf-8")

        except Exception as e:
            self.logger.error(f"Error generating signature: {str(e)}")
            raise

    def get_product_stats(self, product_id="ETH-USD"):
        """Fetch 30-day and 24-hour stats for a given product with proper authentication."""
        try:
            request_path = f"/products/{product_id}/stats"
            method = "GET"
            body = ""

            timestamp = str(self._get_server_time())
            signature = self._generate_signature_trading(method, request_path, body)

            headers = {
                "CB-ACCESS-KEY": self.trading_api_key,
                "CB-ACCESS-TIMESTAMP": timestamp,
                "CB-ACCESS-PASSPHRASE": self.trading_api_passphrase,
                "CB-ACCESS-SIGN": signature,
                "Content-Type": "application/json",
                "User-Agent": "CoinbaseAdvancedTrader/1.0"
            }

            conn = http.client.HTTPSConnection(self.trading_url, timeout=15)
            conn.request(method, request_path, headers=headers)
            response = conn.getresponse()
            response_body = response.read().decode("utf-8")

            if response.status != 200:
                self.logger.error(f"Response: {response.status} {response.reason}")
                self.logger.error(f"Response body: {response_body}")
                raise ConnectionError(f"API request failed: {response.status} {response.reason} - {response_body}")

            conn.close()
            return json.loads(response_body)

        except Exception as e:
            self.logger.error(f"Failed to fetch product stats: {str(e)}")
            return None
       
    def _get_server_time(self) -> int:
        """Fetch Coinbase server time (for accurate request signing)."""
        try:
            conn = http.client.HTTPSConnection(self.trading_url, timeout=15)
            conn.request("GET", "/time")
            response = conn.getresponse()
            data = json.loads(response.read().decode())
            conn.close()
            return int(float(data.get("epoch", time.time())))
        except Exception as e:
            self.logger.error(f"Error getting server time: {str(e)}")
            return int(time.time())
               
    async def _process_websocket_message(self, data):
        """Process incoming WebSocket messages with improved error handling"""
        try:
            # Check if data is a dict and is a ticker message
            if isinstance(data, dict) and data.get('type') == 'ticker':
                price = float(data.get('price', 0))
                
                # Always use live production price
                if price > 0:
                    # Update current price
                    self.current_price = price
                    
                    # Check if price has changed more than 5%
                    if not hasattr(self, '_last_logged_price') or self._last_logged_price is None:
                        # First price log
                        self.logger.info(f"Current {self.product_id} price: ${price:.2f}")
                        self._last_logged_price = price
                    else:
                        # Calculate percentage change
                        percent_change = abs((price - self._last_logged_price) / self._last_logged_price * 100)
                        
                        # Log if price change is more than 5%
                        if percent_change > 5:
                            self.logger.info(f"Current {self.product_id} price: ${price:.2f} (Change: {percent_change:.2f}%)")
                            self._last_logged_price = price
                    
                    await self.update_trading_state(price, 0)
            elif isinstance(data, dict) and data.get('type') == 'heartbeat':
                # Just log at debug level to avoid flooding logs
                self.logger.debug("Received WebSocket heartbeat")
            elif isinstance(data, dict) and data.get('type') == 'error':
                self.logger.error(f"WebSocket error message: {data.get('message')}")
            elif isinstance(data, dict) and data.get('type') == 'subscriptions':
                self.logger.info(f"WebSocket subscriptions confirmed: {data.get('channels', [])}")
        except Exception as e:
            self.logger.error(f"Error processing WebSocket message: {str(e)}")
            
    async def update_trading_state(self, price: float, volume: float):
        """Update trading state with real-time data"""
        try:
            # Update current price
            self.current_price = price
            
            # Check open positions
            for position_id in list(self.open_positions.keys()):
                position = self.open_positions[position_id]
                
                # Calculate current P&L
                if position["side"] == "long":
                    pnl_pct = (price - position["entry_price"]) / position["entry_price"]
                else:
                    pnl_pct = (position["entry_price"] - price) / position["entry_price"]
                
                # Check stop loss and take profit levels
                await self.check_position_exits(position_id, price, pnl_pct)
                
        except Exception as e:
            self.logger.error(f"Error updating trading state: {str(e)}")
            
    async def setup_websocket_feed(self):
        """Initialize WebSocket connection for real-time data with better error handling"""
        reconnect_delay = 5  # Start with 5 seconds delay
        max_reconnect_delay = 60  # Maximum 1 minute delay
        
        while self.is_running:
            try:
                async with websockets.connect(
                    self.ws_url,  # This is now always the live feed 
                    ping_interval=30,
                    ping_timeout=15,
                    close_timeout=15
                ) as ws:
                    subscribe_message = {
                        "type": "subscribe",
                        "product_ids": [self.product_id],
                        "channels": ["ticker", "heartbeat"]
                    }
                    
                    await ws.send(json.dumps(subscribe_message))
                    self.logger.info(f"Successfully subscribed to {self.product_id} live feed")
                    
                    # Reset reconnect delay after successful connection
                    reconnect_delay = 5
                    
                    while self.is_running:
                        try:
                            message = await asyncio.wait_for(ws.recv(), timeout=30)
                            await self._process_websocket_message(json.loads(message))
                        except asyncio.TimeoutError:
                            self.logger.warning("WebSocket receive timeout, sending ping")
                            try:
                                pong = await ws.ping()
                                await asyncio.wait_for(pong, timeout=15)
                                self.logger.debug("Ping successful")
                            except:
                                self.logger.warning("Ping failed, reconnecting...")
                                break
                        except websockets.exceptions.ConnectionClosed as e:
                            self.logger.warning(f"WebSocket connection closed: {e}")
                            break
                        except Exception as e:
                            self.logger.error(f"Error processing message: {str(e)}")
                            self.logger.debug(traceback.format_exc())
            
            except websockets.exceptions.InvalidStatusCode as e:
                self.logger.error(f"WebSocket invalid status code: {e}")
            except OSError as e:
                self.logger.error(f"WebSocket network error: {e}")
            except Exception as e:
                self.logger.error(f"WebSocket connection error: {str(e)}")
                self.logger.debug(traceback.format_exc())
                    
            # Wait before reconnecting with exponential backoff
            self.logger.info(f"WebSocket reconnecting in {reconnect_delay} seconds...")
            await asyncio.sleep(reconnect_delay)
            reconnect_delay = min(reconnect_delay * 1.5, max_reconnect_delay)
        
    async def send_discord_notification(self, title: str, message: str, color: int = 0xEE82EE ):
        """Send notification to Discord webhook with better error handling and fallbacks"""
        if not self.discord_webhook_url:
            self.logger.warning("Discord webhook URL not set")
            return

        try:
            # Create a safe title for logging (remove emojis for Windows console)
            safe_title = ''.join(c for c in title if ord(c) < 127)
            
            # Prepare webhook data
            webhook_data = {
                "username": "Trading Bot",
                "embeds": [{
                    "title": title,
                    "description": message,
                    "color": color,
                    "timestamp": datetime.now().astimezone().isoformat(),
                    "footer": {"text": f"Trading Bot - {self.product_id}"}
                }]
            }

            # Log the message attempt
            self.logger.info(f"Sending Discord notification: {safe_title}")
            
            # Handle potential SSL issues on Windows
            connector = aiohttp.TCPConnector(ssl=False) if sys.platform == 'win32' else None
            
            async with aiohttp.ClientSession(connector=connector) as session:
                async with session.post(
                    self.discord_webhook_url, 
                    json=webhook_data,
                    timeout=15
                ) as response:
                    if response.status != 204:  # Discord returns 204 No Content on success
                        response_text = await response.text()
                        self.logger.error(f"Discord notification failed: {response.status}, Response: {response_text}")
                    else:
                        self.logger.info(f"Discord notification sent successfully: {safe_title}")
                        
        except asyncio.TimeoutError:
            self.logger.error("Discord notification timed out")
        except Exception as e:
            self.logger.error(f"Error sending Discord notification: {str(e)}")
            self.logger.debug(traceback.format_exc() if hasattr(self, 'logger') else str(e))
        
    async def check_position_exits(self, position_id: str, current_price: float, pnl_pct: float):
        """Check and handle position exits based on current price with improved trailing stops"""
        try:
            position = self.open_positions[position_id]
            
            # Check stop loss
            if position["side"] == "long" and current_price <= position["stop_loss"]:
                await self.close_position(position_id, "Stop loss triggered")
                return
            elif position["side"] == "short" and current_price >= position["stop_loss"]:
                await self.close_position(position_id, "Stop loss triggered")
                return
            
            # Check if trailing stop should be activated
            if not position["trailing_stop_activated"] and self.risk_manager.should_activate_trailing_stop(position, current_price):
                position["trailing_stop_activated"] = True
                position["trailing_stop_price"] = self.risk_manager.calculate_trailing_stop_price(position, current_price)
                
                self.logger.info(
                    f"{position['side'].upper()} position trailing stop activated at {position['trailing_stop_price']:.2f} "
                    f"(Price: {current_price:.2f}, P&L: {pnl_pct:.2%})"
                )
                
                await self.send_discord_notification(
                    "Trailing Stop Activated",
                    f"{position['side'].capitalize()} Position\nPrice: ${current_price:.2f}\n"
                    f"Trailing Stop: ${position['trailing_stop_price']:.2f}\nP&L: {pnl_pct*100:.2f}%",
                    0xEE82EE  if position['side'] == 'long' else 0xff0000
                )
            
            # Update trailing stop if already activated
            elif position["trailing_stop_activated"]:
                new_stop_price = self.risk_manager.calculate_trailing_stop_price(position, current_price)
                
                # Only update if stop price has moved in the favorable direction
                if ((position["side"] == "long" and new_stop_price > position["trailing_stop_price"]) or
                    (position["side"] == "short" and new_stop_price < position["trailing_stop_price"])):
                    
                    old_stop = position["trailing_stop_price"]
                    position["trailing_stop_price"] = new_stop_price
                    
                    # Update stop loss order if needed
                    await self.update_stop_loss_order(position_id, new_stop_price, position["remaining_size"])
                    
                    self.logger.info(
                        f"Updated trailing stop from {old_stop:.2f} to {new_stop_price:.2f} "
                        f"(Price: {current_price:.2f}, P&L: {pnl_pct:.2%})"
                    )
            
            # Check trailing stop if activated
            if position["trailing_stop_activated"]:
                if position["side"] == "long" and current_price <= position["trailing_stop_price"]:
                    await self.close_position(position_id, "Trailing stop triggered")
                    return
                elif position["side"] == "short" and current_price >= position["trailing_stop_price"]:
                    await self.close_position(position_id, "Trailing stop triggered")
                    return
                
            # Check take profit levels
            for i, (tp_price, scale_out) in enumerate(
                zip(position["take_profits"], self.risk_manager.position_scale_out)
            ):
                if position["side"] == "long" and current_price >= tp_price:
                    await self.take_partial_profit(position_id, i, scale_out)
                elif position["side"] == "short" and current_price <= tp_price:
                    await self.take_partial_profit(position_id, i, scale_out)
                    
        except Exception as e:
            self.logger.error(f"Error checking position exits: {str(e)}")
            
    def get_current_price(self, product_id="ETH-USD"):
        """Fetch the latest price for a given product."""
        try:
            request_path = f"/products/{product_id}/ticker"
            method = "GET"
            body = ""

            timestamp = str(self._get_server_time())
            signature = self._generate_signature_trading(method, request_path, body)

            headers = {
                "CB-ACCESS-KEY": self.trading_api_key,
                "CB-ACCESS-TIMESTAMP": timestamp,
                "CB-ACCESS-PASSPHRASE": self.trading_api_passphrase,
                "CB-ACCESS-SIGN": signature,
                "Content-Type": "application/json",
                "User-Agent": "CoinbaseAdvancedTrader/1.0"
            }

            api_url = "api.exchange.coinbase.com" if self.trading_mode == "live" else "api-public.sandbox.exchange.coinbase.com"
            conn = http.client.HTTPSConnection(api_url, timeout=15)

            conn.request(method, request_path, headers=headers)
            response = conn.getresponse()
            response_body = response.read().decode("utf-8")

            if response.status != 200:
                self.logger.error(f"Failed to get current price: {response.status} - {response_body}")
                return None

            conn.close()
            data = json.loads(response_body)
            return float(data["price"])

        except Exception as e:
            self.logger.error(f"Error fetching current price: {str(e)}")
            return None
        
    async def get_current_price(self) -> float:
        cache_key = f"price_{self.product_id}"
        
        try:
            # Fallback endpoints
            endpoints = [
                f'/products/{self.product_id}/ticker',
                f'/products/BTC-USD/ticker'  # Fallback to BTC/USD if specific product fails
            ]
            
            for endpoint in endpoints:
                try:
                    # Use a timeout and connection options for better reliability
                    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
                        url = f'https://api.exchange.coinbase.com{endpoint}'
                        async with session.get(url) as response:
                            if response.status == 200:
                                data = await response.json()
                                price = float(data.get('price', 0))
                                
                                if price > 0:
                                    self.logger.info(f"Successfully retrieved price from {endpoint}")
                                    # Cache successful price
                                    await self.api_cache.set(cache_key, price, self.price_cache_ttl)
                                    return price
                            else:
                                self.logger.warning(f"Price retrieval failed for {endpoint}: Status {response.status}")
                except aiohttp.ClientConnectorError:
                    self.logger.warning(f"Connection error with endpoint {endpoint}")
                except json.JSONDecodeError:
                    self.logger.warning(f"JSON decode error with endpoint {endpoint}")
                except Exception as endpoint_error:
                    self.logger.warning(f"Unexpected error with endpoint {endpoint}: {str(endpoint_error)}")
            
            # If all endpoints fail, return last known price or 0
            return self.current_price if hasattr(self, 'current_price') and self.current_price > 0 else 0
            
        except Exception as e:
            self.logger.error(f"Critical error getting current price: {str(e)}")
            return 0

    async def get_historical_data(self, granularity: int = 3600, limit: int = 300):
        """Fetch historical price data from the public Coinbase API without authentication."""
        cache_key = f"historical_{self.product_id}_{granularity}_{limit}"
        
        async with aiohttp.ClientSession() as session:
            url = f'https://api.exchange.coinbase.com/products/{self.product_id}/candles'
            params = {
                'granularity': granularity,
                'limit': limit
            }
            
            self.logger.info(f"Fetching historical data for {self.product_id}, granularity={granularity}, limit={limit}")
            
            async with session.get(url, params=params) as response:
                if response.status == 200:
                    data = await response.json()
                    if not data:
                        self.logger.warning("No historical data retrieved")
                        return pd.DataFrame()
                    
                    df = pd.DataFrame(data, columns=['time', 'low', 'high', 'open', 'close', 'volume'])
                    df['time'] = pd.to_datetime(df['time'], unit='s')
                    df = df.sort_values('time', ascending=False)
                    
                    self.logger.info(f"Retrieved {len(df)} historical candles.")
                    return df
                else:
                    error_text = await response.text()
                    self.logger.error(f"Failed to fetch historical data: {response.status} - {error_text}")
                    return pd.DataFrame()
        
        # Get lock to prevent multiple concurrent requests for same data
        async with await self.api_cache.get_lock(cache_key):
            # Check cache again in case another request updated it while waiting
            cached_data = await self.api_cache.get(cache_key)
            if cached_data is not None:
                return cached_data
                
            # Proceed with API call if not in cache
            try:
                # Always use public endpoint without authentication
                url = f'https://api.exchange.coinbase.com/api/v3/products/{self.product_id}/candles'
                
                # Parameters for historical data
                params = {
                    'granularity': granularity,  # 1 hour candles by default
                    'limit': limit  # Number of candles to retrieve
                }
                
                self.logger.info(f"Fetching historical data for {self.product_id}, granularity={granularity}, limit={limit}")
                
                async with aiohttp.ClientSession() as session:
                    async with session.get(url, params=params) as response:
                        if response.status == 200:
                            data = await response.json()
                            
                            # Additional validation
                            if not data:
                                self.logger.warning("No historical data retrieved")
                                return pd.DataFrame()
                            
                            # Convert to DataFrame with explicit column names
                            df = pd.DataFrame(data, columns=['time', 'low', 'high', 'open', 'close', 'volume'])
                            
                            # Validate data types and handle potential issues
                            numeric_cols = ['low', 'high', 'open', 'close', 'volume']
                            for col in numeric_cols:
                                df[col] = pd.to_numeric(df[col], errors='coerce')
                            
                            # Remove any rows with NaN values in critical columns
                            df = df.dropna(subset=['close'])
                            
                            # Convert timestamp
                            df['time'] = pd.to_datetime(df['time'], unit='s')
                            
                            # Sort by time in descending order (most recent first)
                            df = df.sort_values('time', ascending=False)
                            
                            # Log retrieved data details
                            self.logger.info(f"Retrieved {len(df)} historical candles, date range: {df['time'].min()} to {df['time'].max()}")
                            
                            # Store in cache
                            await self.api_cache.set(cache_key, df, self.historical_cache_ttl)
                            
                            return df
                        else:
                            error_text = await response.text()
                            self.logger.error(f"Failed to fetch historical data: {response.status} - {error_text}")
                            return pd.DataFrame()
            
            except Exception as e:
                self.logger.error(f"Critical error in historical data retrieval: {str(e)}")
                self.logger.error(traceback.format_exc())
                return pd.DataFrame()
                
    def calculate_indicators(self, df: pd.DataFrame) -> pd.DataFrame:
        """Calculate technical indicators with enhanced error handling and volume indicators"""
        if df.empty:
            self.logger.warning("Empty DataFrame passed to indicator calculation")
            return df
            
        # Make a copy to avoid modifying the original
        df_with_indicators = df.copy()
        
        # Data validation step
        df_with_indicators = self._validate_dataframe(df_with_indicators)
        if df_with_indicators.empty:
            self.logger.error("DataFrame validation failed")
            return df
        
        try:
            # Ensure close prices are valid and numeric
            close_prices = df_with_indicators['close'].astype(float)
            close_prices = close_prices.ffill().bfill()
            
            # Check if we have enough data points
            if len(close_prices) < 200:
                self.logger.warning(f"Insufficient data points for all indicators: {len(close_prices)}")
            
            # Convert to numpy array for TALib
            close_array = np.array(close_prices.values, dtype=float)
            
            # Prepare other arrays needed for indicators
            high_array = np.array(df_with_indicators['high'].astype(float).ffill().bfill().values, dtype=float)
            low_array = np.array(df_with_indicators['low'].astype(float).ffill().bfill().values, dtype=float)
            volume_array = np.array(df_with_indicators['volume'].astype(float).ffill().bfill().values, dtype=float)
            
            # Safely calculate volume indicators
            try:
                obv = talib.OBV(close_array, volume_array)
                valid_indices = ~np.isnan(obv)
                
                # Only add OBV where it's valid
                if np.any(valid_indices):
                    df_with_indicators.loc[close_prices.index[valid_indices], 'obv'] = obv[valid_indices]
                
                # Fallback OBV calculation if talib fails or no valid indices
                if 'obv' not in df_with_indicators.columns or df_with_indicators['obv'].isna().all():
                    self.logger.warning("Fallback OBV calculation")
                    df_with_indicators['obv'] = volume_array * np.sign(np.diff(np.concatenate(([close_array[0]], close_array))))
                    df_with_indicators['obv'] = df_with_indicators['obv'].cumsum()
                
                # OBV moving average
                obv_values = df_with_indicators['obv'].ffill().bfill().values
                obv_ma = talib.SMA(obv_values, timeperiod=20)
                valid_ma_indices = ~np.isnan(obv_ma)
                df_with_indicators.loc[df_with_indicators.index[valid_ma_indices], 'obv_ma'] = obv_ma[valid_ma_indices]
                
                # Fallback OBV MA if needed
                if 'obv_ma' not in df_with_indicators.columns or df_with_indicators['obv_ma'].isna().all():
                    df_with_indicators['obv_ma'] = df_with_indicators['obv'].rolling(window=20).mean()
            
            except Exception as e:
                self.logger.error(f"OBV calculation error: {str(e)}")
                # Complete fallback OBV calculation
                df_with_indicators['obv'] = volume_array * np.sign(np.diff(np.concatenate(([close_array[0]], close_array))))
                df_with_indicators['obv'] = df_with_indicators['obv'].cumsum()
                df_with_indicators['obv_ma'] = df_with_indicators['obv'].rolling(window=20).mean()
            
            # Continue with other indicator calculations...
            self._calculate_momentum_indicators(df_with_indicators, close_array)
            self._calculate_volatility_indicators(df_with_indicators, close_array, high_array, low_array)
            self._calculate_trend_indicators(df_with_indicators, close_array)
            
            # Log successful calculation
            self.logger.info("Technical indicators calculated successfully")
            
            return df_with_indicators
            
        except Exception as e:
            self.logger.error(f"Critical error in indicator calculation: {str(e)}")
            self.logger.error(traceback.format_exc())
            return df
            
    def _validate_dataframe(self, df: pd.DataFrame) -> pd.DataFrame:
        """Validate DataFrame for indicator calculations"""
        try:
            # Check required columns
            required_columns = ['time', 'open', 'high', 'low', 'close', 'volume']
            missing_columns = [col for col in required_columns if col not in df.columns]
            
            if missing_columns:
                self.logger.error(f"Missing required columns in DataFrame: {missing_columns}")
                return pd.DataFrame()
                
            # Check data types and convert if necessary
            for col in ['open', 'high', 'low', 'close', 'volume']:
                df[col] = pd.to_numeric(df[col], errors='coerce')
                
            # Check for NaN values in critical columns
            nan_counts = df[['open', 'high', 'low', 'close']].isna().sum()
            if nan_counts.sum() > 0:
                self.logger.warning(f"NaN values detected: {nan_counts}")
                
                # Fill NaN values using forward and backward fill
                df = df.fillna(method='ffill').fillna(method='bfill')
                
            # Ensure enough data points for calculations
            if len(df) < 50:
                self.logger.warning(f"Limited data points available: {len(df)}. Some indicators may be unreliable.")
                
            return df
            
        except Exception as e:
            self.logger.error(f"Error validating DataFrame: {str(e)}")
            return pd.DataFrame()
        
    def _sanitize_float(self, value, default=0.0):
        """Convert value to float, returning default if conversion fails"""
        try:
            return float(value) if value not in ['N/A', None, ''] else default
        except (ValueError, TypeError):
            return default
        
    def _default_account_summary(self):
        """Provide a consistent default account summary"""
        return {
            "total_value": 0.0,
            "available_balance": 0.0,
            "btc_balance": 0.0,
            "unrealized_pl": 0.0,
            "error": "Unable to retrieve account summary"
        }
            
    def _calculate_momentum_indicators(self, df: pd.DataFrame, close_array: np.ndarray):
        """Calculate momentum indicators such as RSI, MACD"""
        try:
            # RSI
            rsi = talib.RSI(close_array, timeperiod=14)
            df['rsi'] = rsi
            
            # MACD
            macd, macd_signal, macd_hist = talib.MACD(
                close_array,
                fastperiod=12,
                slowperiod=26,
                signalperiod=9
            )
            df['macd'] = macd
            df['macd_signal'] = macd_signal
            df['macd_hist'] = macd_hist
            
            # Stochastic
            slowk, slowd = talib.STOCH(
                high=np.array(df['high'].values),
                low=np.array(df['low'].values),
                close=close_array,
                fastk_period=14,
                slowk_period=3,
                slowk_matype=0,
                slowd_period=3,
                slowd_matype=0
            )
            df['stoch_k'] = slowk
            df['stoch_d'] = slowd
            
        except Exception as e:
            self.logger.error(f"Error calculating momentum indicators: {str(e)}")
            
    def _calculate_volatility_indicators(self, df: pd.DataFrame, close_array: np.ndarray, 
                                        high_array: np.ndarray, low_array: np.ndarray):
        """Calculate volatility indicators such as Bollinger Bands and ATR"""
        try:
            # Bollinger Bands
            upperband, middleband, lowerband = talib.BBANDS(
                close_array,
                timeperiod=20,
                nbdevup=2,
                nbdevdn=2,
                matype=0
            )
            df['bb_upper'] = upperband
            df['bb_middle'] = middleband
            df['bb_lower'] = lowerband
            
            # ATR - Average True Range
            atr = talib.ATR(
                high_array,
                low_array,
                close_array,
                timeperiod=14
            )
            df['atr'] = atr
            
        except Exception as e:
            self.logger.error(f"Error calculating volatility indicators: {str(e)}")
            
    def _calculate_trend_indicators(self, df: pd.DataFrame, close_array: np.ndarray):
        """Calculate trend indicators such as moving averages"""
        try:
            # Simple Moving Averages
            df['ma_50'] = talib.SMA(close_array, timeperiod=50)
            df['ma_200'] = talib.SMA(close_array, timeperiod=200)
            
            # Exponential Moving Averages
            df['ema_20'] = talib.EMA(close_array, timeperiod=20)
            
            # ADX - Trend Strength
            adx = talib.ADX(
                high=np.array(df['high'].values),
                low=np.array(df['low'].values),
                close=close_array,
                timeperiod=14
            )
            df['adx'] = adx
            
        except Exception as e:
            self.logger.error(f"Error calculating trend indicators: {str(e)}")
            
    def _validate_volume_data(self, df):
        """Validate volume data before indicator calculations"""
        required_columns = ['close', 'volume']
        if not all(col in df.columns for col in required_columns):
            self.logger.warning("Missing required columns for volume indicators")
            return False
        
        # Check for sufficient non-zero data
        if (df['volume'] == 0).all():
            self.logger.warning("All volume data is zero")
            return False
        
        return True
            
    def calculate_volume_indicators(self, df):
        """Calculate volume-based indicators"""
        try:
            if df.empty:
                self.logger.warning("Empty DataFrame for volume indicators calculation")
                return df
            
            # Make a copy to avoid modifying the original DataFrame
            df_with_volume = df.copy()
            
            # Ensure we have volume data
            if 'volume' not in df_with_volume.columns:
                self.logger.warning("Volume data not available for indicators")
                return df_with_volume
            
            # Convert volume to numeric and handle NaN values
            volume_data = df_with_volume['volume'].astype(float)
            volume_data = volume_data.replace([np.inf, -np.inf], np.nan).fillna(method='ffill').fillna(method='bfill')
            
            # Convert to numpy array for TALib
            volume_array = np.array(volume_data.values, dtype=float)
            close_array = np.array(df_with_volume['close'].astype(float).fillna(method='ffill').fillna(method='bfill').values, dtype=float)
            
            # Safely calculate OBV
            try:
                obv = talib.OBV(close_array, volume_array)
                valid_indices = ~np.isnan(obv)
                
                # Only add OBV where it's valid
                df_with_volume.loc[volume_data.index[valid_indices], 'obv'] = obv[valid_indices]
                
                # Fallback OBV calculation if talib fails
                if 'obv' not in df_with_volume.columns or df_with_volume['obv'].isna().all():
                    self.logger.warning("Fallback OBV calculation")
                    df_with_volume['obv'] = volume_data.cumsum()
                
                # Calculate OBV moving average
                obv_values = df_with_volume['obv'].fillna(method='ffill').fillna(method='bfill').values
                obv_ma = talib.SMA(obv_values, timeperiod=20)
                valid_ma_indices = ~np.isnan(obv_ma)
                df_with_volume.loc[df_with_volume.index[valid_ma_indices], 'obv_ma'] = obv_ma[valid_ma_indices]
            
            except Exception as e:
                self.logger.error(f"OBV calculation error: {str(e)}")
                # Fallback OBV calculation
                df_with_volume['obv'] = volume_data.cumsum()
                df_with_volume['obv_ma'] = df_with_volume['obv'].rolling(window=20).mean()
            
            return df_with_volume
            
        except Exception as e:
            self.logger.error(f"Critical error in volume indicators calculation: {str(e)}")
            self.logger.debug(traceback.format_exc())
            return df
            
    def _calculate_chaikin_money_flow(self, df: pd.DataFrame, periods=20) -> pd.Series:
        """Calculate Chaikin Money Flow indicator"""
        try:
            if not all(col in df.columns for col in ['close', 'low', 'high', 'volume']):
                return pd.Series(index=df.index)
                
            # Money Flow Multiplier
            mfm = ((df['close'] - df['low']) - (df['high'] - df['close'])) / (df['high'] - df['low'])
            mfm = mfm.replace([np.inf, -np.inf], 0)  # Handle division by zero
            
            # Money Flow Volume
            mfv = mfm * df['volume']
            
            # CMF
            cmf = mfv.rolling(window=periods).sum() / df['volume'].rolling(window=periods).sum()
            
            return cmf
            
        except Exception as e:
            self.logger.error(f"Error calculating Chaikin Money Flow: {str(e)}")
            return pd.Series(index=df.index)
            
    def apply_strategy_filter(self, df: pd.DataFrame) -> pd.DataFrame:
        """Apply strategy filtering logic based on technical indicators and volume analysis"""
        try:
            # Check for required columns
            required_cols = ['close', 'ma_50', 'ma_200', 'rsi', 'macd', 'macd_signal']
            if not all(col in df.columns for col in required_cols):
                self.logger.warning("Missing required columns for strategy filtering")
                df['Signal'] = 0
                return df

            # Initialize Signal column
            df['Signal'] = 0

            # Round indicators to nearest 0.1 for better filter stability
            df['rsi_rounded'] = df['rsi'].round(1)
            df['macd_rounded'] = df['macd'].round(1)
            df['macd_signal_rounded'] = df['macd_signal'].round(1)
            df['ma_50_rounded'] = df['ma_50'].round(1)
            df['ma_200_rounded'] = df['ma_200'].round(1)
            
            # Check if volume indicators are available
            volume_indicators_available = all(col in df.columns for col in ['obv', 'cmf', 'volume_rsi'])
            
            if volume_indicators_available:
                self.logger.info("Using volume indicators in strategy filter")
                # Round volume indicators
                df['volume_rsi_rounded'] = df['volume_rsi'].round(1) if 'volume_rsi' in df else np.nan
                df['cmf_rounded'] = df['cmf'].round(3) if 'cmf' in df else np.nan
                
                # Calculate OBV trend (rising/falling)
                if 'obv' in df and 'obv_ma' in df:
                    df['obv_trend'] = np.where(df['obv'] > df['obv_ma'], 1, -1)
                else:
                    df['obv_trend'] = np.nan
                    
                # Long Signal Conditions with Volume Confirmation
                long_conditions = (
                    (df['ma_50_rounded'] > df['ma_200_rounded']) &  # Golden Cross
                    (df['rsi_rounded'] < self.risk_manager.bot.rsi_oversold) &  # Oversold RSI
                    (df['macd_rounded'] > df['macd_signal_rounded']) &  # MACD bullish crossover
                    (
                        # Volume confirmation (need at least one of these conditions)
                        (df['volume_rsi_rounded'] < 30) |  # Low volume RSI
                        (df['obv_trend'] > 0) |  # Rising OBV
                        (df['cmf_rounded'] > 0)  # Positive Money Flow
                    )
                )

                # Short Signal Conditions with Volume Confirmation
                short_conditions = (
                    (df['ma_50_rounded'] < df['ma_200_rounded']) &  # Death Cross
                    (df['rsi_rounded'] > self.risk_manager.bot.rsi_overbought) &  # Overbought RSI
                    (df['macd_rounded'] < df['macd_signal_rounded']) &  # MACD bearish crossover
                    (
                        # Volume confirmation (need at least one of these conditions)
                        (df['volume_rsi_rounded'] > 70) |  # High volume RSI
                        (df['obv_trend'] < 0) |  # Falling OBV
                        (df['cmf_rounded'] < 0)  # Negative Money Flow
                    )
                )
            else:
                self.logger.info("Using price indicators only in strategy filter (volume indicators not available)")
                # Original conditions without volume (fallback)
                long_conditions = (
                    (df['ma_50_rounded'] > df['ma_200_rounded']) &  # Golden Cross
                    (df['rsi_rounded'] < self.risk_manager.bot.rsi_oversold) &  # Oversold RSI
                    (df['macd_rounded'] > df['macd_signal_rounded'])  # MACD bullish crossover
                )

                short_conditions = (
                    (df['ma_50_rounded'] < df['ma_200_rounded']) &  # Death Cross
                    (df['rsi_rounded'] > self.risk_manager.bot.rsi_overbought) &  # Overbought RSI
                    (df['macd_rounded'] < df['macd_signal_rounded'])  # MACD bearish crossover
                )

            # Assign Signals
            df.loc[long_conditions, 'Signal'] = 1
            df.loc[short_conditions, 'Signal'] = -1
            
            # Log signal counts
            long_count = np.sum(df['Signal'] == 1)
            short_count = np.sum(df['Signal'] == -1)
            self.logger.info(f"Strategy filter identified {long_count} long signals and {short_count} short signals")

            return df
        
        except Exception as e:
            self.logger.error(f"Error in strategy filter: {str(e)}")
            self.logger.debug(traceback.format_exc())
            # Create a Signal column with default value if it fails
            df['Signal'] = 0
            return df
                                            
    async def check_trading_conditions(self, df: pd.DataFrame) -> Tuple[bool, bool]:
        """Check if trading conditions are met with volume confirmation"""
        try:
            if df.empty or len(df) < 200:  # Need enough data for MA200
                return False, False

            current_price = df["close"].iloc[-1]
            current_rsi = df["rsi"].iloc[-1]
            current_macd = df["macd"].iloc[-1]
            current_signal = df["macd_signal"].iloc[-1]
            
            # Get volume indicators if available
            has_volume_indicators = all(indicator in df.columns for indicator in ['obv', 'cmf', 'volume_rsi'])
            
            if has_volume_indicators:
                current_obv = df["obv"].iloc[-1]
                current_cmf = df["cmf"].iloc[-1]
                current_volume_rsi = df["volume_rsi"].iloc[-1]
                
                if 'obv_ma' in df.columns:
                    current_obv_ma = df["obv_ma"].iloc[-1]
                    obv_trend_positive = current_obv > current_obv_ma
                else:
                    obv_trend_positive = True  # Default if OBV MA not available
                    
                # Log current trading conditions including volume
                self.logger.info(
                    f"Trading conditions - Price: {current_price:.2f}, RSI: {current_rsi:.2f}, "
                    f"MACD: {current_macd:.2f}, Signal: {current_signal:.2f}, "
                    f"CMF: {current_cmf:.4f}, Vol_RSI: {current_volume_rsi:.2f}, "
                    f"OBV trend: {'Positive' if obv_trend_positive else 'Negative'}"
                )
                
                # Enhanced buy conditions with volume confirmation
                buy_signal = (
                    df["Signal"].iloc[-1] == 1  # Pre-filter confirmation
                    and current_price > df["ma_200"].iloc[-1]  # Above MA200
                    and current_rsi < self.rsi_oversold  # Stronger oversold
                    and current_macd > current_signal  # MACD crossover
                    and current_price < df["bb_lower"].iloc[-1]  # Below lower BB
                    and (  # Volume confirmation (any one condition is sufficient)
                        current_volume_rsi < self.volume_rsi_low
                        or current_cmf > 0
                        or obv_trend_positive
                    )
                )

                # Enhanced sell conditions with volume confirmation
                sell_signal = (
                    df["Signal"].iloc[-1] == -1  # Pre-filter confirmation
                    and (current_price < df["ma_200"].iloc[-1]  # Below MA200
                        or current_rsi > self.rsi_overbought)  # Stronger overbought
                    and current_macd < current_signal  # MACD crossunder
                    and current_price > df["bb_upper"].iloc[-1]  # Above upper BB
                    and (  # Volume confirmation (any one condition is sufficient)
                        current_volume_rsi > self.volume_rsi_high
                        or current_cmf < 0
                        or not obv_trend_positive
                    )
                )
                
            else:
                # Original conditions without volume (fallback)
                self.logger.info(
                    f"Trading conditions (no volume) - Price: {current_price:.2f}, RSI: {current_rsi:.2f}, "
                    f"MACD: {current_macd:.2f}, Signal: {current_signal:.2f}"
                )
                
                buy_signal = (
                    df["Signal"].iloc[-1] == 1  # Pre-filter confirmation
                    and current_price > df["ma_200"].iloc[-1]  # Above MA200
                    and current_rsi < self.rsi_oversold  # Stronger oversold
                    and current_macd > current_signal  # MACD crossover
                    and current_price < df["bb_lower"].iloc[-1]  # Below lower BB
                )

                sell_signal = (
                    df["Signal"].iloc[-1] == -1  # Pre-filter confirmation 
                    and (current_price < df["ma_200"].iloc[-1]  # Below MA200
                        or current_rsi > self.rsi_overbought)  # Stronger overbought
                    and current_macd < current_signal  # MACD crossunder
                    and current_price > df["bb_upper"].iloc[-1]  # Above upper BB
                )

            # Log signal results
            if buy_signal:
                self.logger.info("BUY signal confirmed by trading conditions")
            elif sell_signal:
                self.logger.info("SELL signal confirmed by trading conditions")

            return buy_signal, sell_signal

        except Exception as e:
            self.logger.error(f"Error checking trading conditions: {str(e)}")
            self.logger.debug(traceback.format_exc())
            return False, False
            
    async def execute_strategy(self):
        """Execute trading strategy with enhanced error handling"""
        try:
            # Get historical data and calculate indicators
            df = await self.get_historical_data()
            if df is None or df.empty:
                self.logger.warning("No historical data available")
                return

            # Calculate indicators
            df = self.calculate_indicators(df)
            
            # Store indicators for logging trade context
            self.current_indicators = df.iloc[-1].copy() if not df.empty else None
            
            # Apply strategy filter
            df = self.apply_strategy_filter(df)

            # Get current market data
            try:
                # Get current price
                current_price = df["close"].iloc[-1]  # Default to latest historical price
                live_price = await self.get_current_price()
                if live_price > 0:
                    current_price = live_price
                    
                # Get key indicator values
                last_row = df.iloc[-1]
                current_rsi = last_row.get("rsi", 0)
                current_macd = last_row.get("macd", 0)
                current_macd_signal = last_row.get("macd_signal", 0)
                current_ma_50 = last_row.get("ma_50", 0)
                current_ma_200 = last_row.get("ma_200", 0)
                
                # Update risk manager state
                self.risk_manager.update_market_state(
                    last_row.get("atr", None),
                    current_rsi
                )
                
                # Log market conditions
                self.logger.info(
                    f"Current Market Conditions: Price: {current_price:.2f}, "
                    f"RSI: {current_rsi:.2f}, MACD: {current_macd:.2f}, "
                    f"Signal: {current_macd_signal:.2f}, "
                    f"SMA50: {current_ma_50:.2f}, SMA200: {current_ma_200:.2f}"
                )
            except Exception as e:
                self.logger.error(f"Error getting current market data: {str(e)}")
                return

            # Check trading conditions
            buy_signal, sell_signal = await self.check_trading_conditions(df)
            
            # Check for "near signal" conditions
            near_buy_signal = (
                not buy_signal and  # Not yet a full buy signal
                current_rsi < self.risk_manager.bot.rsi_oversold + 5 and  # RSI approaching oversold
                current_macd < current_macd_signal and  # MACD below signal
                current_macd > df["macd"].iloc[-2]  # But MACD rising
            )
            
            near_sell_signal = (
                not sell_signal and  # Not yet a full sell signal
                current_rsi > self.risk_manager.bot.rsi_overbought - 5 and  # RSI approaching overbought
                current_macd > current_macd_signal and  # MACD above signal
                current_macd < df["macd"].iloc[-2]  # But MACD falling
            )

            # Get account balance
            account_summary = await self._get_account_summary()
            
            # Extract available balance
            available_balance = 0
            try:
                if isinstance(account_summary, dict):
                    available_balance = float(account_summary.get("available_balance", 0))
                else:
                    self.logger.warning(f"Unexpected account summary format: {type(account_summary)}")
            except Exception as e:
                self.logger.error(f"Error parsing account balance: {str(e)}")
                available_balance = 0

            # Send alerts for near signals
            if near_buy_signal and available_balance > 0:
                self.logger.info("Near BUY signal detected, sending imminent trade alert")
                await self.send_trade_imminent_alert("buy", df, available_balance)
            elif near_sell_signal and available_balance > 0:
                self.logger.info("Near SELL signal detected, sending imminent trade alert")
                await self.send_trade_imminent_alert("sell", df, available_balance)

            # Execute trades based on signals
            if buy_signal and available_balance > 0:
                self.logger.info(f"Executing LONG trade with available balance: {available_balance}")
                await self.execute_trade("buy", df, available_balance)
            elif sell_signal and available_balance > 0:
                self.logger.info(f"Executing SHORT trade with available balance: {available_balance}")
                await self.execute_trade("sell", df, available_balance)
            else:
                self.logger.info("No trade signals or insufficient balance")

        except Exception as e:
            self.logger.error(f"Error in strategy execution: {str(e)}")
            self.logger.debug(traceback.format_exc())
            
    async def execute_trade(self, side: str, df: pd.DataFrame, available_balance: float):
        """Execute trade with comprehensive risk management"""
        try:
            # Get current price and market data
            last_row = df.iloc[-1]
            current_price = last_row["close"]
            current_atr = last_row.get("atr")
            current_rsi = last_row.get("rsi")
            
            # Ensure we have the most accurate price
            live_price = await self.get_current_price()
            if live_price > 0:
                current_price = live_price
            
            # Update risk manager with current market conditions
            self.risk_manager.update_market_state(current_atr, current_rsi)
            
            # Calculate stop loss price
            stop_loss_price = self.risk_manager.calculate_stop_loss(side, current_price)
            
            # Calculate position size based on risk parameters
            position_size = self.risk_manager.calculate_position_size(
                available_balance, current_price, stop_loss_price
            )

            # Ensure minimum position size
            if position_size <= 0.00001:  # Minimum size check
                self.logger.warning("Position size too small, aborting trade")
                return

            # Calculate take profit levels
            take_profits = self.risk_manager.calculate_take_profits(side, current_price, stop_loss_price)

            # Generate order ID
            order_id = str(uuid.uuid4())

            # Execute the trade
            if side == "buy":
                # Place main order
                order = await self.place_order(
                    side="buy",
                    size=str(position_size),
                    price=str(current_price)
                )

                if order:
                    self.open_positions[order_id] = {
                        "side": "long",
                        "entry_price": current_price,
                        "size": position_size,
                        "stop_loss": stop_loss_price,
                        "take_profits": take_profits,
                        "trailing_stop_activated": False,
                        "remaining_size": position_size,
                        "order_id": order['id'],
                        "entry_time": datetime.now(),
                        "atr": current_atr,  # Store ATR at entry for reference
                        "rsi": current_rsi    # Store RSI at entry for reference
                    }

                    # Place stop loss and take profit orders
                    await self.place_stop_loss_order(order_id, stop_loss_price, position_size)
                    for level, (tp_price, scale_out) in enumerate(zip(take_profits, self.risk_manager.position_scale_out)):
                        await self.place_take_profit_order(order_id, tp_price, position_size * scale_out, level)

                    # Calculate risk-reward ratio
                    risk = abs(current_price - stop_loss_price) / current_price
                    reward = abs(take_profits[0] - current_price) / current_price
                    risk_reward_ratio = reward / risk if risk > 0 else 0
                    
                    # Log trade event
                    self.log_trade_event(
                        "LONG_POSITION_OPEN",
                        {
                            "price": current_price,
                            "size": position_size,
                            "stop_loss": stop_loss_price,
                            "take_profit": take_profits[0],
                            "reason": "SIGNAL_TRIGGERED",
                            "atr": current_atr,
                            "rsi": current_rsi,
                            "r_multiple": risk_reward_ratio
                        }
                    )

                    # Send notification
                    await self.send_discord_notification(
                        "Long Position Opened",
                        f"Entry: ${current_price:.2f}\nSize: {position_size:.8f}\nStop Loss: ${stop_loss_price:.2f}\n"
                        f"Take Profit 1: ${take_profits[0]:.2f}\nR/R Ratio: {risk_reward_ratio:.2f}",
                        0xEE82EE 
                    )

            elif side == "sell":
                # Place main order
                order = await self.place_order(
                    side="sell",
                    size=str(position_size),
                    price=str(current_price)
                )

                if order:
                    self.open_positions[order_id] = {
                        "side": "short",
                        "entry_price": current_price,
                        "size": position_size,
                        "stop_loss": stop_loss_price,
                        "take_profits": take_profits,
                        "trailing_stop_activated": False,
                        "remaining_size": position_size,
                        "order_id": order['id'],
                        "entry_time": datetime.now(),
                        "atr": current_atr,
                        "rsi": current_rsi
                    }

                    # Place stop loss and take profit orders
                    await self.place_stop_loss_order(order_id, stop_loss_price, position_size)
                    for level, (tp_price, scale_out) in enumerate(zip(take_profits, self.risk_manager.position_scale_out)):
                        await self.place_take_profit_order(order_id, tp_price, position_size * scale_out, level)

                    # Calculate risk-reward ratio
                    risk = abs(stop_loss_price - current_price) / current_price
                    reward = abs(current_price - take_profits[0]) / current_price
                    risk_reward_ratio = reward / risk if risk > 0 else 0
                    
                    # Log trade event
                    self.log_trade_event(
                        "SHORT_POSITION_OPEN",
                        {
                            "price": current_price,
                            "size": position_size,
                            "stop_loss": stop_loss_price,
                            "take_profit": take_profits[0],
                            "reason": "SIGNAL_TRIGGERED",
                            "atr": current_atr,
                            "rsi": current_rsi,
                            "r_multiple": risk_reward_ratio
                        }
                    )
               # Send notification
                    await self.send_discord_notification(
                        "Short Position Opened",
                        f"Entry: ${current_price:.2f}\nSize: {position_size:.8f}\nStop Loss: ${stop_loss_price:.2f}\n"
                        f"Take Profit 1: ${take_profits[0]:.2f}\nR/R Ratio: {risk_reward_ratio:.2f}",
                        0xff0000
                    )

        except Exception as e:
            self.logger.error(f"Error executing trade: {str(e)}")
            self.logger.debug(traceback.format_exc())
            
    async def place_order(self, side: str, size: str, price: str, order_type: str = "limit"):
        """Place an order with the Coinbase API using the appropriate format"""
        try:
            # For sandbox, we use the legacy orders endpoint
            endpoint = '/orders'
            method = 'POST'
            
            # Generate a client order ID
            client_order_id = str(uuid.uuid4())
            
            # Use server time to ensure timestamp synchronization
            server_timestamp = await self._get_server_time_async()
            timestamp = str(server_timestamp)
            
            # Construct the order based on order type and format
            if order_type.lower() == "market":
                # Market order
                body = {
                    "side": side,
                    "product_id": self.product_id,
                    "type": "market",
                    "size": size
                }
            elif order_type.lower() == "stop":
                # Stop loss order (stop-limit for sandbox)
                body = {
                    "side": side,
                    "product_id": self.product_id,
                    "type": "stop",
                    "price": price,
                    "stop": "loss",
                    "stop_price": price,
                    "size": size
                }
            else:
                # Default to limit order
                body = {
                    "side": side,
                    "product_id": self.product_id,
                    "type": "limit",
                    "price": price,
                    "size": size,
                    "post_only": False
                }
            
            # Add client_order_id for tracking
            body["client_oid"] = client_order_id
            
            # Generate authentication headers
            body_str = json.dumps(body)
            
            headers = self._prepare_auth_headers(method, endpoint, body_str, timestamp)
            
            # Log the request details (excluding sensitive data)
            self.logger.info(f"Placing {order_type} {side} order for {size} {self.product_id} at price: {price}")
            
            # Send the request
            async with aiohttp.ClientSession() as session:
                url = f'https://{self.trading_url}{endpoint}'
                
                async with session.post(url, headers=headers, json=body, timeout=15) as response:
                    response_text = await response.text()
                    
                    # Log the response status for debugging
                    self.logger.debug(f"Order placement response status: {response.status}")
                    
                    if response.status != 200 and response.status != 201:
                        self.logger.error(f"Failed to place order: {response.status}, {response_text}")
                        return None
                    
                    # Parse the response
                    try:
                        data = json.loads(response_text)
                        
                        # Return order details in a standardized format
                        return {
                            "id": data.get("id", client_order_id),
                            "client_order_id": client_order_id,
                            "status": data.get("status", "open"),
                            "product_id": data.get("product_id", self.product_id),
                            "side": data.get("side", side),
                            "size": data.get("size", size),
                            "price": data.get("price", price),
                            "type": data.get("type", order_type)
                        }
                            
                    except json.JSONDecodeError as e:
                        self.logger.error(f"Failed to decode order response: {str(e)}")
                        return None
                    
        except Exception as e:
            self.logger.error(f"Error placing order: {str(e)}")
            self.logger.debug(traceback.format_exc())
            return None
            
    def _prepare_auth_headers(self, method: str, request_path: str, body: str = "", timestamp: str = None) -> dict:
        """Generate authentication headers for API requests."""
        if timestamp is None:
            timestamp = str(self._get_server_time())
        
        signature = self._generate_signature_trading(method, request_path, body)

        return {
            "CB-ACCESS-KEY": self.trading_api_key,
            "CB-ACCESS-TIMESTAMP": timestamp,
            "CB-ACCESS-PASSPHRASE": self.trading_api_passphrase,
            "CB-ACCESS-SIGN": signature,
            "Content-Type": "application/json"
        }

    async def cleanup_position(self, position_id: str):
        """Clean up a closed position"""
        try:
            position = self.open_positions[position_id]
            
            # Cancel any remaining orders
            orders_to_cancel = []
            if "stop_order_id" in position:
                orders_to_cancel.append(position["stop_order_id"])
            if "take_profit_orders" in position:
                orders_to_cancel.extend(position["take_profit_orders"])

            if orders_to_cancel:
                await self.cancel_orders(orders_to_cancel)

            # Remove position from open positions
            del self.open_positions[position_id]
            self.logger.info(f"Position {position_id} cleaned up")

        except Exception as e:
            self.logger.error(f"Error cleaning up position: {str(e)}")
            
    async def cancel_orders(self, order_ids: List[str]):
        """Cancel multiple orders with error handling"""
        try:
            for order_id in order_ids:
                await self.cancel_order(order_id)
            return True
        except Exception as e:
            self.logger.error(f"Error cancelling multiple orders: {str(e)}")
            return False
            
    async def cancel_order(self, order_id: str):
        """Cancel a specific order using sandbox-compatible endpoint"""
        try:
            # Sandbox uses legacy format without API version prefix
            endpoint = f'/orders/{order_id}'
            method = 'DELETE'
            
            # Get server time for timestamp
            timestamp = str(await self._get_server_time_async())
            
            # Create headers with authentication
            headers = self._prepare_auth_headers(method, endpoint, timestamp=timestamp)
            
            async with aiohttp.ClientSession() as session:
                url = f'https://{self.trading_url}{endpoint}'
                async with session.delete(url, headers=headers, timeout=15) as response:
                    if response.status != 200:
                        response_text = await response.text()
                        self.logger.error(f"Failed to cancel order: {response.status}, {response_text}")
                        return False
                    
                    self.logger.info(f"Successfully cancelled order: {order_id}")
                    return True
                    
        except Exception as e:
            self.logger.error(f"Error cancelling order: {str(e)}")
            self.logger.debug(traceback.format_exc())
            return False
            
    async def cancel_all_orders(self):
        """Cancel all pending orders"""
        try:
            # Correctly format the endpoint for sandbox
            endpoint = '/orders'  # Legacy sandbox endpoint
            method = 'DELETE'
            
            # Get server time for proper authentication
            timestamp = str(await self._get_server_time_async())
            
            # Create headers with authentication
            headers = self._prepare_auth_headers(method, endpoint, timestamp=timestamp)
            
            async with aiohttp.ClientSession() as session:
                url = f'https://{self.trading_url}{endpoint}'
                try:
                    async with session.delete(url, headers=headers, timeout=15) as response:
                        if response.status != 200:
                            error_text = await response.text()
                            self.logger.error(f"Failed to cancel all orders: {response.status}, {error_text}")
                            return False
                        
                        self.logger.info("Successfully cancelled all orders")
                        return True
                except aiohttp.ClientError as e:
                    self.logger.error(f"Connection error cancelling orders: {str(e)}")
                    return False
                except asyncio.TimeoutError:
                    self.logger.error("Request timed out when cancelling orders")
                    return False
                        
        except Exception as e:
            self.logger.error(f"Error cancelling all orders: {str(e)}")
            return False
    
    async def close_all_positions(self):
        """Close all open positions"""
        try:
            position_count = len(self.open_positions)
            if position_count == 0:
                self.logger.info("No positions to close")
                return
                
            self.logger.info(f"Closing {position_count} open positions")
            for position_id in list(self.open_positions.keys()):
                await self.close_position(position_id, "Emergency close - Bot shutdown")
                
            self.logger.info("All positions closed")
            
        except Exception as e:
            self.logger.error(f"Error closing all positions: {str(e)}")
            self.logger.debug(traceback.format_exc())
            
    async def send_position_update(self, periodic=False, initial=False, send_notification=True):
        """Send current position and account status with improved indicator processing"""
        try:
            # Import datetime at function level to ensure availability
            from datetime import datetime
            
            # Current time for notification tracking
            current_time = datetime.now()
            
            # If we're doing a periodic update, check if enough time has passed
            if periodic and hasattr(self, '_last_notification_time'):
                time_since_last = (current_time - self._last_notification_time).total_seconds()
                if time_since_last < 3600:  # Less than 1 hour since last notification
                    self.logger.debug("Skipping periodic update - less than 1 hour since last notification")
                    return
            
            # Get account summary with error handling
            account_summary = await self._get_account_summary()
            
            # Ensure account_summary is a dictionary
            if isinstance(account_summary, str):
                try:
                    account_summary = json.loads(account_summary)
                except json.JSONDecodeError:
                    account_summary = {
                        "summary_text": account_summary,
                        "available_balance": 0,
                        "total_value": 0,
                        "btc_balance": 0,
                        "unrealized_pl": 'N/A'
                    }
            
            # Fetch ETH market data with error handling
            btc_data = {}
            try:
                current_price = await self.get_current_price()
                if current_price > 0:
                    btc_data['current_price'] = current_price
                    # Try to get more comprehensive market data
                    try:
                        market_data = await self.get_btc_market_data()
                        if market_data and isinstance(market_data, dict):
                            # Update btc_data with any valid fields from market_data
                            for key in ['high_24h', 'low_24h', 'percent_change_24h']:
                                if key in market_data and market_data[key] is not None:
                                    btc_data[key] = market_data[key]
                        if 'percent_change_24h' in btc_data and isinstance(btc_data['percent_change_24h'], (int, float)):
                            btc_data['percent_change_24h'] = round(btc_data['percent_change_24h'], 1)
                    except Exception as e:
                        self.logger.warning(f"Error getting detailed market data: {str(e)}")
                    
                    # Ensure we have all required fields with defaults if not available
                    if 'high_24h' not in btc_data:
                        btc_data['high_24h'] = 'N/A'
                    if 'low_24h' not in btc_data:
                        btc_data['low_24h'] = 'N/A'
                    if 'percent_change_24h' not in btc_data:
                        btc_data['percent_change_24h'] = 'N/A'
                else:
                    # Defaults if we couldn't get a valid price
                    btc_data = {
                        'current_price': 'N/A',
                        'high_24h': 'N/A',
                        'low_24h': 'N/A',
                        'percent_change_24h': 'N/A'
                    }
            except Exception as e:
                self.logger.error(f"Error getting ETH data: {str(e)}")
                btc_data = {
                    'current_price': 'N/A',
                    'high_24h': 'N/A',
                    'low_24h': 'N/A',
                    'percent_change_24h': 'N/A'
                }

            # Get historical data for indicators
            df = await self.get_historical_data()
            indicators = {
                'rsi': 'N/A',
                'macd': 'N/A',
                'macd_signal': 'N/A',
                'sma_50': 'N/A',
                'sma_200': 'N/A'
            }
                
            if not df.empty:
                # Calculate indicators using our improved method
                df_with_indicators = self.calculate_indicators(df)
                
                # Get the last valid values for each indicator
                try:
                    # Extract RSI
                    if 'rsi' in df_with_indicators and df_with_indicators['rsi'].notna().any():
                        last_rsi = df_with_indicators['rsi'].dropna().iloc[-1]
                        indicators['rsi'] = f"{last_rsi:.2f}"
                        self.logger.info(f"Last RSI value for notification: {last_rsi:.2f}")
                        
                    # Extract MACD
                    if 'macd' in df_with_indicators and df_with_indicators['macd'].notna().any():
                        last_macd = df_with_indicators['macd'].dropna().iloc[-1]
                        indicators['macd'] = f"{last_macd:.2f}"
                        self.logger.info(f"Last MACD value for notification: {last_macd:.2f}")
                        
                    # Extract MACD Signal
                    if 'macd_signal' in df_with_indicators and df_with_indicators['macd_signal'].notna().any():
                        last_signal = df_with_indicators['macd_signal'].dropna().iloc[-1]
                        indicators['macd_signal'] = f"{last_signal:.2f}"
                        
                    # Extract SMA50
                    if 'ma_50' in df_with_indicators and df_with_indicators['ma_50'].notna().any():
                        last_sma50 = df_with_indicators['ma_50'].dropna().iloc[-1]
                        indicators['sma_50'] = f"{last_sma50:.2f}"
                        self.logger.info(f"Last SMA50 value for notification: {last_sma50:.2f}")
                        
                    # Extract SMA200
                    if 'ma_200' in df_with_indicators and df_with_indicators['ma_200'].notna().any():
                        last_sma200 = df_with_indicators['ma_200'].dropna().iloc[-1]
                        indicators['sma_200'] = f"{last_sma200:.2f}"
                        self.logger.info(f"Last SMA200 value for notification: {last_sma200:.2f}")                       
           
                    # Get volume vs average indicator
                    vol_vs_avg = 100  # Default value
                    vol_symbol = "➡️"  # Default symbol (neutral)
                    
                    # Add volume vs average indicator
                    if 'vol_vs_avg' in df and df['vol_vs_avg'].notna().any():
                        vol_vs_avg = df['vol_vs_avg'].dropna().iloc[-1]
                        indicators['vol_vs_avg'] = vol_vs_avg
                    
                    if not df.empty and 'vol_vs_avg' in df.columns and df['vol_vs_avg'].notna().any():
                        vol_vs_avg = df['vol_vs_avg'].dropna().iloc[-1]
                        
                        # Set appropriate symbol based on percentage
                        if vol_vs_avg >= 150:  # Very high volume (50%+ above average)
                            vol_symbol = "🔺"
                        elif vol_vs_avg >= 120:  # High volume (20-50% above average)
                            vol_symbol = "⬆️"
                        elif vol_vs_avg <= 50:  # Very low volume (50%+ below average)
                            vol_symbol = "🔻"
                        elif vol_vs_avg <= 80:  # Low volume (20-50% below average)
                            vol_symbol = "⬇️"
                        else:
                            vol_symbol = "➡️"  # Normal volume (within 20% of average)
                    
                except Exception as e:
                    self.logger.error(f"Error extracting indicator values for notification: {str(e)}")
            
            # Format ETH market performance for Discord
            # Convert price to formatted string if it's a number
            if isinstance(btc_data.get('current_price'), (int, float)):
                price_str = f"${btc_data['current_price']:,.2f}"
            else:
                price_str = f"${btc_data.get('current_price', 'N/A')}"
                
            discord_btc_message = (
                f"💵 **Current ETH Price:** ${float(btc_data.get('current_price', 0)):,.2f}\n"
                f"📉 **24h Change:** {btc_data.get('percent_change_24h', 'N/A')}%\n"
                f"🔺 **24h High:** ${float(btc_data.get('high_24h', 0)):,.2f}\n"
                f"🔻 **24h Low:** ${float(btc_data.get('low_24h', 0)):,.2f}\n"
            )

            # Get volume vs average indicator
            vol_vs_avg = indicators.get('vol_vs_avg', 100)  # Default value
            vol_symbol = "➡️"  # Default symbol (neutral)
                    
            # Set appropriate symbol based on percentage
            if vol_vs_avg >= 150:  # Very high volume (50%+ above average)
                vol_symbol = "🔺"
            elif vol_vs_avg >= 120:  # High volume (20-50% above average)
                vol_symbol = "⬆️"
            elif vol_vs_avg <= 50:  # Very low volume (50%+ below average)
                vol_symbol = "🔻"
            elif vol_vs_avg <= 80:  # Low volume (20-50% below average)
                vol_symbol = "⬇️"
            else:
                vol_symbol = "➡️"  # Normal volume (within 20% of average)

            # Format technical indicators for Discord with volume vs average added
            discord_indicators_message = (
                f"\n📊 **Technical Indicators:**\n"
                f"• RSI: {float(indicators.get('rsi', 0)):.2f}\n"
                f"• MACD: {float(indicators.get('macd', 0)):.2f}\n"
                f"• Signal: {float(indicators.get('macd_signal', 0)):,.2f}\n"
                f"• SMA(50): ${float(indicators.get('sma_50', 0)):,.2f}\n"
                f"• SMA(200): ${float(indicators.get('sma_200', 0)):,.2f}\n"
                f"• Vol: {vol_symbol} {vol_vs_avg:.0f}% of Avg\n"
            )

            # Format account summary for Discord
            eth_balance = float(account_summary.get('eth_balance', 0))
            eth_display = f"{eth_balance:.4f}" if eth_balance > 0 else "0 ETH"
            discord_portfolio_message = (
                f"\n💰 **Account Summary:**\n"
                f"• Total Value: ${format(float(account_summary.get('total_value', 0)), ',.2f')}\n"
                f"• Available Balance: ${format(float(account_summary.get('available_balance', 0)), ',.2f')}\n"
                f"• ETH Holdings: {eth_display}\n"
                f"• Unrealized P/L: {account_summary.get('unrealized_pl', 'N/A')}%\n"
            )
            
            # Combine messages for updates
            full_message = discord_btc_message + discord_indicators_message + discord_portfolio_message

            # HANDLE INITIAL NOTIFICATION
            if initial or (not hasattr(self, '_initial_notification_sent') or not self._initial_notification_sent):
                if send_notification:
                    await self.send_discord_notification(
                        "Trading Bot Started", 
                        full_message, 
                        0xEE82EE  # Purple border
                    )
                self._initial_notification_sent = True
                self.logger.info("Initial status notification sent")
                self._last_notification_time = current_time
                return

            # HANDLE PERIODIC UPDATE
            if periodic:
                self.logger.info("Sending periodic status update")
                await self.send_discord_notification(
                    "Hourly ETH Performance Update", 
                    full_message, 
                    0xEE82EE   # Purple color
                )
                self._last_notification_time = current_time
                return
            
            # HANDLE TRADE UPDATES (only if there are open positions)
            if self.open_positions:
                positions_msg = "**Open Positions:**\n"
                for pos_id, pos in self.open_positions.items():
                    # Get current price for position calculations
                    current_price_value = btc_data.get('current_price', 'N/A')
                    if current_price_value == 'N/A':
                        current_price_value = pos["entry_price"]  # Fallback to entry price
                    else:
                        try:
                            current_price_value = float(current_price_value)
                        except (TypeError, ValueError):
                            current_price_value = pos["entry_price"]
                    
                    # Calculate profit/loss
                    pnl = 0
                    try:
                        if pos["side"] == "long":
                            pnl = ((current_price_value - pos["entry_price"]) / pos["entry_price"]) * 100
                        else:
                            pnl = ((pos["entry_price"] - current_price_value) / pos["entry_price"]) * 100
                    except Exception as e:
                        self.logger.error(f"Error calculating P/L: {str(e)}")

                    positions_msg += (
                        f"• {pos['side'].upper()}: {pos['size']} {self.product_id}\n"
                        f"  Entry: ${pos['entry_price']:,.2f}\n"
                        f"  Current: ${current_price_value:,.2f}\n"
                        f"  P/L: {pnl:,.2f}%\n"
                    )
                    
                    # Add stop loss info if available
                    if "stop_loss" in pos:
                        positions_msg += f"  Stop Loss: ${pos['stop_loss']:,.2f}\n"
                    
                    # Add trailing stop info if activated
                    if pos.get("trailing_stop_activated", False):
                        positions_msg += f"  Trailing Stop: ${pos.get('trailing_stop_price', 'N/A'):,.2f}\n"

                trade_message = f"📈 **Trade Update** 📈\n\n{positions_msg}\n{discord_btc_message}"
                await self.send_discord_notification(
                    "Trade Status Update", 
                    trade_message, 
                    0xEE82EE   # Purple color
                )
                
            # Update last notification time
            self._last_notification_time = current_time

        except Exception as e:
            self.logger.error(f"Error sending position update: {str(e)}")
            self.logger.debug(traceback.format_exc())
                 
    async def get_market_data(self):
        """Get market data including 24h stats"""
        try:
            async with aiohttp.ClientSession() as session:
                # Current price
                ticker_url = f"https://api.exchange.coinbase.com/products/{self.product_id}/ticker"
                async with session.get(ticker_url) as resp:
                    if resp.status != 200:
                        self.logger.error(f"Failed to get ticker data: {resp.status}")
                        return None
                    
                    ticker_data = await resp.json()
                    current_price = float(ticker_data['price'])

                # 24h stats
                stats_url = f"https://api.exchange.coinbase.com/products/{self.product_id}/stats"
                async with session.get(stats_url) as resp:
                    if resp.status != 200:
                        self.logger.error(f"Failed to get stats data: {resp.status}")
                        return {
                            'current_price': current_price,
                            'high_24h': None,
                            'low_24h': None,
                            'percent_change_24h': None
                        }
                    
                    stats_data = await resp.json()
                    
                    # Calculate percent change
                    open_24h = float(stats_data.get('open', 0))
                    percent_change_24h = 0
                    if open_24h > 0:
                        percent_change_24h = ((current_price - open_24h) / open_24h) * 100

                    # Historical prices for indicators
                    candles_url = f"https://api.exchange.coinbase.com/products/{self.product_id}/candles?granularity=3600"
                    async with session.get(candles_url) as resp:
                        if resp.status == 200:
                            candles_data = await resp.json()
                            df = pd.DataFrame(candles_data, columns=['time', 'low', 'high', 'open', 'close', 'volume'])
                            df = df.sort_values('time')
                        else:
                            df = pd.DataFrame()

                    return {
                        'current_price': current_price,
                        'high_24h': float(stats_data.get('high', 0)),
                        'low_24h': float(stats_data.get('low', 0)),
                        'percent_change_24h': round(percent_change_24h, 1),
                        'historical_prices': df
                    }

        except Exception as e:
            self.logger.error(f"Error fetching ETH market data: {str(e)}")
            return {}
                    
    async def _get_account_summary(self) -> dict:
        """Get account summary with caching"""
        cache_key = "account_summary"
        
        # Check cache first
        cached_summary = await self.api_cache.get(cache_key)
        if cached_summary is not None:
            return cached_summary
        
        # Get lock for account summary requests
        async with await self.api_cache.get_lock(cache_key):
            # Check cache again
            cached_summary = await self.api_cache.get(cache_key)
            if cached_summary is not None:
                return cached_summary
                
            try:
                # Get server time for better synchronization
                server_time = await self._get_server_time_async()
                timestamp = str(server_time)
                
                # For sandbox environment, use the standard accounts endpoint without brokerage
                endpoint = '/accounts'  # Legacy endpoint for sandbox
                method = 'GET'
                body = ""
                
                headers = {
                    'CB-ACCESS-KEY': self.trading_api_key,
                    'CB-ACCESS-TIMESTAMP': timestamp,
                    'CB-ACCESS-PASSPHRASE': self.trading_api_passphrase,
                    'Content-Type': 'application/json',
                    'User-Agent': 'CoinbaseAdvancedTrader/1.0'
                }
                
                # Create signature according to Coinbase documentation
                headers['CB-ACCESS-SIGN'] = self._generate_signature_trading(method, endpoint, body)
                
                self.logger.info(f"Getting account summary from: {self.trading_url}")
                
                async with aiohttp.ClientSession() as session:
                    url = f'https://{self.trading_url}{endpoint}'
                    
                    async with session.get(url, headers=headers, timeout=15) as response:
                        response_text = await response.text()
                        
                        if response.status != 200:
                            self.logger.error(f"API request failed: {response.status}, {response_text}")
                            return {
                                "error": f"Error getting account summary: {response.status}",
                                "available_balance": 0,
                                "total_value": 0
                            }
                        
                        # Try to parse JSON response
                        try:
                            data = json.loads(response_text)
                            
                            # Process the response format based on type
                            if isinstance(data, list):
                                # Legacy sandbox API format - list of accounts
                                total_value = Decimal("0")
                                usd_balance = Decimal("0")
                                eth_balance = Decimal("0")
                                
                                for account in data:
                                    currency = account.get('currency')
                                    balance = Decimal(str(account.get('balance', '0')))
                                    available = Decimal(str(account.get('available', '0')))
                                    
                                    if currency == 'USD':
                                        usd_balance = available
                                        total_value += balance
                                    elif currency == 'ETH':
                                        eth_balance = balance
                                        # Calculate ETH value in USD
                                        eth_price = await self.get_current_price()
                                        if eth_price > 0:
                                            total_value += eth_balance * Decimal(str(eth_price))
                                
                                summary = {
                                    "total_value": float(total_value),
                                    "available_balance": float(usd_balance),
                                    "eth_balance": float(eth_balance),
                                    "unrealized_pl": 0
                                }
                                
                                # Cache the result
                                await self.api_cache.set(cache_key, summary, self.account_cache_ttl)
                                return summary
                            else:
                                # Unknown format, return default with error message
                                self.logger.error(f"Unexpected response format: {type(data)}")
                                return {
                                    "error": "Unexpected response format",
                                    "available_balance": 0,
                                    "total_value": 0
                                }
                                
                        except json.JSONDecodeError as json_err:
                            self.logger.error(f"Failed to decode account summary JSON: {json_err}")
                            return {
                                "error": f"JSON decode error: {str(json_err)}",
                                "available_balance": 0,
                                "total_value": 0
                            }
                        
            except Exception as e:
                error_msg = f"Error generating account summary: {str(e)}"
                self.logger.error(error_msg)
                self.logger.debug(traceback.format_exc())
                return {
                    "error": error_msg,
                    "available_balance": 0,
                    "total_value": 0
                }

    def _process_account_data(self, data):
        try:
            # If data is a string, try to parse it
            if isinstance(data, str):
                try:
                    data = json.loads(data)
                except json.JSONDecodeError:
                    self.logger.error(f"Cannot parse account data string: {data}")
                    return self._default_account_summary()
            
            # Ensure data is a list or dict
            if not isinstance(data, (list, dict)):
                self.logger.error(f"Unexpected account data type: {type(data)}")
                return self._default_account_summary()
            
            # Convert to list if it's a dict
            if isinstance(data, dict):
                data = [data]
            
            total_value = 0
            available_balance = 0
            coin_balance = 0
            coin_symbol = self.product_id.split('-')[0]
            
            for account in data:
                try:
                    currency = account.get('currency', '')
                    balance = self._sanitize_float(account.get('balance', 0))
                    available = self._sanitize_float(account.get('available', 0))
                    
                    if currency == 'USD':
                        available_balance = available
                        total_value += balance
                    elif currency == coin_symbol:
                        coin_balance = balance
                        # Calculate coin value in USD 
                        coin_price = self.current_price if hasattr(self, 'current_price') and self.current_price > 0 else 0
                        total_value += coin_balance * coin_price
                except Exception as account_error:
                    self.logger.warning(f"Error processing account: {account_error}")
            
            return {
                "total_value": total_value,
                "available_balance": available_balance,
                f"{coin_symbol.lower()}_balance": coin_balance,
                "unrealized_pl": 0  # You might want to calculate this differently
            }
        
        except Exception as e:
            self.logger.error(f"Error processing account data: {str(e)}")
            return self._default_account_summary()
                        
    async def monitor_positions(self):
        """Enhanced position monitoring with trailing stops and WebSocket integration"""
        self.logger.info("Starting position monitoring")
        
        while self.is_running:
            try:
                # Get current price once to use for all positions
                current_price = await self.get_current_price()
                if current_price <= 0:
                    await asyncio.sleep(10)  # Wait and try again if price is invalid
                    continue
                    
                # Log current monitoring stats periodically
                if len(self.open_positions) > 0:
                    self.logger.info(f"Monitoring {len(self.open_positions)} open positions at price ${current_price:.2f}")
                
                # Process each position
                for position_id, position in list(self.open_positions.items()):
                    # Skip if position is already being processed
                    if position.get("processing", False):
                        continue
                        
                    try:
                        # Mark position as being processed
                        position["processing"] = True
                        
                        # Calculate P&L
                        if position["side"] == "long":
                            profit_percentage = (current_price - position["entry_price"]) / position["entry_price"]
                        else:
                            profit_percentage = (position["entry_price"] - current_price) / position["entry_price"]
                        
                        # Update risk manager state with current conditions
                        self.risk_manager.update_market_state(position.get('atr'), position.get('rsi'))
                        
                        # Check if trailing stop should be activated
                        if not position["trailing_stop_activated"] and self.risk_manager.should_activate_trailing_stop(position, current_price):
                            position["trailing_stop_activated"] = True
                            position["trailing_stop_price"] = self.risk_manager.calculate_trailing_stop_price(position, current_price)
                            
                            self.logger.info(
                                f"{position['side'].upper()} position trailing stop activated at {position['trailing_stop_price']:.2f} "
                                f"(Price: {current_price:.2f}, P&L: {profit_percentage:.2%})"
                            )
                            
                            await self.send_discord_notification(
                                "Trailing Stop Activated",
                                f"{position['side'].capitalize()} Position\nPrice: ${current_price:.2f}\n"
                                f"Trailing Stop: ${position['trailing_stop_price']:.2f}\nP&L: {profit_percentage*100:.2f}%",
                                0xEE82EE  if position['side'] == 'long' else 0xff0000
                            )
                        
                        # Update trailing stop if already activated
                        elif position["trailing_stop_activated"]:
                            new_stop_price = self.risk_manager.calculate_trailing_stop_price(position, current_price)
                            
                            # Only update if stop price has moved in the favorable direction
                            if ((position["side"] == "long" and new_stop_price > position["trailing_stop_price"]) or
                                (position["side"] == "short" and new_stop_price < position["trailing_stop_price"])):
                                
                                old_stop = position["trailing_stop_price"]
                                position["trailing_stop_price"] = new_stop_price
                                
                                # Update stop loss order if needed
                                await self.update_stop_loss_order(position_id, new_stop_price, position["remaining_size"])
                                
                                self.logger.info(
                                    f"Updated trailing stop from {old_stop:.2f} to {new_stop_price:.2f} "
                                    f"(Price: {current_price:.2f}, P&L: {profit_percentage:.2%})"
                                )
                        
                        """Ensure this function returns a valid coroutine."""
                        if self.get_current_price() is None:
                            self.logger.error("Failed to fetch price. Retrying...")
                            return
                        await asyncio.sleep(10) 
                        
                        # Check stop conditions
                        # Long position stop
                        if position["side"] == "long" and (
                            current_price <= position["stop_loss"] or 
                            (position["trailing_stop_activated"] and current_price <= position["trailing_stop_price"])
                        ):
                            stop_type = "Regular stop" if current_price <= position["stop_loss"] else "Trailing stop"
                            await self.close_position(position_id, f"{stop_type} triggered")
                            continue  # Skip to next position
                            
                        # Short position stop
                        elif position["side"] == "short" and (
                            current_price >= position["stop_loss"] or 
                            (position["trailing_stop_activated"] and current_price >= position["trailing_stop_price"])
                        ):
                            stop_type = "Regular stop" if current_price >= position["stop_loss"] else "Trailing stop"
                            await self.close_position(position_id, f"{stop_type} triggered")
                            continue  # Skip to next position
                        
                        # Check take profit levels for scaling out
                        for i, (tp_price, scale_out) in enumerate(
                            zip(position["take_profits"], self.risk_manager.position_scale_out)
                        ):
                            # Skip already hit take profit levels
                            if position.get(f"tp_hit_{i}", False):
                                continue
                                
                            # Long position take profit
                            if position["side"] == "long" and current_price >= tp_price:
                                await self.take_partial_profit(position_id, i, scale_out)
                                position[f"tp_hit_{i}"] = True
                                
                            # Short position take profit
                            elif position["side"] == "short" and current_price <= tp_price:
                                await self.take_partial_profit(position_id, i, scale_out)
                                position[f"tp_hit_{i}"] = True
                    
                    finally:
                        # Mark position as no longer being processed
                        if position_id in self.open_positions:
                            self.open_positions[position_id]["processing"] = False

                # Calculate total daily P&L
                daily_pnl = 0
                for position in self.open_positions.values():
                    entry_price = position["entry_price"]
                    if position["side"] == "long":
                        position_pnl = (current_price - entry_price) / entry_price
                    else:
                        position_pnl = (entry_price - current_price) / entry_price
                    daily_pnl += position_pnl * position["size"]
                
                # Check daily P&L limit
                if abs(daily_pnl) >= self.risk_manager.bot.max_daily_loss:
                    self.logger.warning(f"Daily loss limit reached: {daily_pnl:.2%}")
                    await self.send_discord_notification(
                        "Daily Loss Limit Reached",
                        f"Current P&L: {daily_pnl:.2%}\nClosing all positions.",
                        0xff0000  # Red
                    )
                    await self.close_all_positions()
                
                # Wait before checking again
                await asyncio.sleep(10)  # Check every 10 seconds

            except Exception as e:
                self.logger.error(f"Error in position monitoring: {str(e)}")
                self.logger.debug(traceback.format_exc())
                await asyncio.sleep(10)
                
    async def log_and_notify(self, level: str, title: str, message: str, color: int = 0xEE82EE ):
        """Log a message and send a Discord notification with proper rate limiting"""
        # Log message using appropriate level
        if level == "info":
            self.logger.info(message)
        elif level == "warning":
            self.logger.warning(message)
        elif level == "error":
            self.logger.error(message)
        elif level == "critical":
            self.logger.critical(message)
        else:
            self.logger.info(message)
            
        # Check if we should send a Discord notification (avoid flooding)
        send_notification = True
        
        # Check if this is a critical or error message
        if level in ["critical", "error"]:
            # Always send these
            pass
        else:
            # For non-critical messages, implement rate limiting
            now = datetime.now()
            if hasattr(self, '_last_notification_times'):
                # Check if we've sent a similar notification recently
                for prev_time, prev_title in list(self._last_notification_times.items()):
                    if prev_title == title and (now - prev_time).total_seconds() < 300:  # 5 minutes
                        send_notification = False
                        break
                    
                    # Cleanup old entries (older than 1 hour)
                    if (now - prev_time).total_seconds() > 3600:
                        del self._last_notification_times[prev_time]
            else:
                self._last_notification_times = {}
            
            # Add this notification to the history if we're sending it
            if send_notification:
                self._last_notification_times[now] = title
            
        # Send notification if not rate limited
        if send_notification:
            await self.send_discord_notification(title, message, color)
            
    async def periodic_performance_updates(self):
        """Send performance updates periodically"""
        try:
            self.logger.info("Starting periodic performance updates")
            
            # Wait for initial delay before first report
            await asyncio.sleep(3600)  # 1 hour delay
            
            while self.is_running:
                # Get performance metrics
                summary = self.metrics.get_summary()
                
                # Only send if we have at least one trade
                if summary['total_trades'] > 0:
                    message = (
                        f"📊 **Performance Metrics**\n\n"
                        f"**Overall Statistics:**\n"
                        f"• Total Trades: {summary['total_trades']}\n"
                        f"• Win Rate: {summary['win_rate']:.2f}%\n"
                        f"• Profit Factor: {summary['profit_factor']:.2f}\n"
                        f"• Maximum Drawdown: {summary['max_drawdown']:.2f}%\n\n"
                        
                        f"**Trade Metrics:**\n"
                        f"• Average Win: {summary['avg_win']:.2f}%\n"
                        f"• Average Loss: {summary['avg_loss']:.2f}%\n"
                        f"• Largest Win: {summary['largest_win']:.2f}%\n"
                        f"• Largest Loss: {summary['largest_loss']:.2f}%\n"
                        f"• Current Streak: {abs(summary['current_streak'])} {'wins' if summary['current_streak'] > 0 else 'losses'}\n\n"
                    )
                    
                    # Add recent performance if available
                    weekly_performance = self.metrics.get_weekly_performance(4)
                    if weekly_performance:
                        message += f"**Weekly Performance:**\n"
                        for week, pnl in weekly_performance.items():
                            message += f"• {week}: {pnl:.2f}%\n"
                        message += "\n"
                    
                    # Add last few trades
                    last_trades = self.metrics.get_last_n_trades(5)
                    if last_trades:
                        message += f"**Recent Trades:**\n"
                        for trade in last_trades:
                            timestamp = trade.get('timestamp')
                            if isinstance(timestamp, str):
                                try:
                                    timestamp = datetime.fromisoformat(timestamp)
                                    date_str = timestamp.strftime("%Y-%m-%d %H:%M")
                                except:
                                    date_str = timestamp
                            else:
                                date_str = 'Unknown'
                                
                            pnl = trade.get('pnl_percent', 0)
                            message += f"• {date_str}: {pnl:.2f}% ({'win' if pnl > 0 else 'loss'})\n"
                    
                    # Send notification
                    await self.send_discord_notification(
                        "Trading Performance Metrics",
                        message,
                        0x1E90FF  # Blue
                    )
                
                # Wait for next update
                await asyncio.sleep(24 * 3600)  # 24 hours
                
        except asyncio.CancelledError:
            self.logger.info("Periodic performance updates task cancelled")
        except Exception as e:
            self.logger.error(f"Error in periodic performance updates: {str(e)}")
            self.logger.debug(traceback.format_exc())
            
    async def periodic_status_updates(self):
        """Send periodic status updates every hour with enhanced format matching initial notification"""
        try:
            self.logger.info("Starting periodic status updates")
            
            while self.is_running:
                # Wait for 1 hour between updates
                await asyncio.sleep(3600)  # 1 hour = 3600 seconds
                
                # Send detailed position update that mirrors initial notification format
                await self.send_position_update(periodic=True)
                    
        except asyncio.CancelledError:
            self.logger.info("Periodic status updates task cancelled")
        except Exception as e:
            self.logger.error(f"Error in periodic status updates: {str(e)}")
            self.logger.debug(traceback.format_exc())
            
    async def run_bot(self):
        """Run the trading bot with log monitoring and key processes."""

        try:
            # Ensure bot is initialized
            if not hasattr(self, 'is_initialized') or not self.is_initialized:
                raise RuntimeError("Bot not properly initialized")

            self.is_running = True
            self.logger.info(f"Starting trading bot for {self.product_id}")

            # Send startup notification
            await self.send_discord_notification(
                "🚀 Trading Bot Started", 
                f"Trading bot for {self.product_id} is now actively monitoring the market.", 
                0xFFFF00  # Yellow
            )

            # Perform initial position update
            await self.send_position_update(initial=True, send_notification=True)

            # Define main bot tasks
            tasks = [
                asyncio.create_task(self.monitor_positions()),
                asyncio.create_task(self.periodic_status_updates()),
                asyncio.create_task(self.setup_websocket_feed()),
                asyncio.create_task(self.execute_strategy()),  
                asyncio.create_task(self.periodic_performance_updates())
            ]

            # Register cleanup handler
            atexit.register(self.cleanup_handler)

            # Run tasks concurrently
            try:
                await asyncio.gather(*tasks, return_exceptions=True)
            except asyncio.CancelledError:
                self.logger.warning("Bot tasks were cancelled")
            except Exception as e:
                self.logger.error(f"Unexpected error in bot main loop: {str(e)}")
                self.logger.debug(traceback.format_exc())
            finally:
                try:
                    await self.cleanup()
                except Exception as cleanup_error:
                    self.logger.error(f"Error during final cleanup: {str(cleanup_error)}")

                self.logger.info("Bot main loop terminated")

        except Exception as e:
            self.logger.critical(f"Critical error starting bot: {str(e)}")
            await self.send_discord_notification(
                "🚨 Bot Startup Failed", 
                f"Critical error prevented bot from starting: {str(e)}", 
                0xFF0000  # Red
            )
            try:
                await self.cleanup()
            except Exception as cleanup_error:
                self.logger.error(f"Error during startup failure cleanup: {str(cleanup_error)}")
            raise
            
    async def cleanup(self):
        """Comprehensive cleanup procedure with thread-safe mechanism"""
        # Use a thread-safe check to prevent multiple simultaneous cleanups
        with self._cleanup_lock:
            # Check if cleanup has already been performed
            if self._cleanup_performed:
                return

            try:
                # Immediately set running flag to false to stop ongoing processes
                self.is_running = False
                
                self.logger.info("Starting comprehensive cleanup process...")
                
                # Close all positions if any are open
                if hasattr(self, 'open_positions') and self.open_positions:
                    self.logger.info(f"Closing {len(self.open_positions)} open positions...")
                    await self.close_all_positions()

                # Cancel all pending orders
                self.logger.info("Cancelling all pending orders...")
                await self.cancel_all_orders()

                # Clean up logging resources
                if hasattr(self, 'trade_csv'):
                    try:
                        self.trade_csv.close()
                        self.logger.info("Trade CSV file closed")
                    except Exception as e:
                        self.logger.error(f"Error closing trade CSV: {str(e)}")

                # Save trading metrics
                if hasattr(self, 'metrics'):
                    try:
                        self.metrics.save_metrics()
                        self.logger.info("Trading metrics saved")
                    except Exception as e:
                        self.logger.error(f"Error saving trading metrics: {str(e)}")

                # Send final shutdown notification
                try:
                    await self.send_discord_notification(
                        "🛑 Trading Bot Shutdown", 
                        "Trading bot has been shut down. All positions closed and resources released.\n"
                        "Bot will not restart until manually reactivated.",
                        0xFF0000  # Red color for shutdown
                    )
                except Exception as e:
                    self.logger.error(f"Error sending shutdown notification: {str(e)}")

                # Mark cleanup as performed
                self._cleanup_performed = True

                self.logger.info("Cleanup completed successfully")

            except Exception as e:
                self.logger.error(f"Error during cleanup: {str(e)}")
                self.logger.error(traceback.format_exc())
            finally:
                # Ensure cleanup is marked as performed even if an exception occurs
                self._cleanup_performed = True
                
    def cleanup_handler(self):
        """Synchronous cleanup handler for atexit"""
        try:
            # Create event loop for cleanup if necessary
            try:
                loop = asyncio.get_event_loop()
            except RuntimeError:
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
            
            if loop.is_closed():
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                
            # Run cleanup synchronously
            loop.run_until_complete(self.cleanup())
            
        except Exception as e:
            print(f"Error in cleanup handler: {str(e)}")
            traceback.print_exc()

async def async_main():
    """Async main function with enhanced error handling"""
    bot = None
    try:
        print("\n=== Starting Trading Bot ===")
        
        # Clear existing log handlers to avoid duplicate logs
        for handler in logging.root.handlers[:]:
            logging.root.removeHandler(handler)

        # Configure logging
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler("trading_bot.log"),
                logging.StreamHandler(sys.stdout),
            ],
        )
        logger = logging.getLogger("TradingBot")
        logger.info("Logging initialized successfully")
     
        # Load and validate environment variables
        if not os.path.exists('.env'):
            raise FileNotFoundError(".env file not found")
        load_dotenv()
        
        # Create bot instance
        logger.info("Creating bot instance...")
        bot = AdvancedTradingBot(product_id=os.getenv("TRADING_PRODUCT", "ETH-USD"))
        logger.info("Bot instance created successfully")

        # Get initial account summary
        logger.info("Getting initial account summary...")
        summary = await bot._get_account_summary()
        logger.info(f"Initial Account Summary: {summary}")
        
        # Start bot operations
        logger.info("Starting bot operations...")
        await bot.run_bot()

    except KeyboardInterrupt:
        logger.info("Bot stopped by user")
        if bot:
            try:
                await bot.cleanup()
            except Exception as cleanup_error:
                logger.error(f"Error during cleanup: {cleanup_error}")
    except Exception as e:
        logger.error(f"Critical error in main execution: {str(e)}")
        logger.error(traceback.format_exc())
        if bot:
            try:
                await bot.cleanup()
            except Exception as cleanup_error:
                logger.error(f"Error during critical cleanup: {cleanup_error}")
        raise
    finally:
        if bot and hasattr(bot, 'is_running') and bot.is_running:
            try:
                await bot.cleanup()
            except Exception as cleanup_error:
                logger.error(f"Final cleanup error: {cleanup_error}")
        
def main():
    """Main entry point with Windows event loop handling"""
    try:
        if sys.platform == "win32":
            asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
        asyncio.run(async_main())
    except KeyboardInterrupt:
        print("\nBot stopped by user")
    except Exception as e:
        print(f"\nFatal error: {str(e)}")
        traceback.print_exc()
    finally:
        sys.exit(0)

if __name__ == "__main__":
    main()
    