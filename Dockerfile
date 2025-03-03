# Use Python 3.10 base image
FROM python:3.10

# Set timezone environment variable
ENV TZ=America/New_York

# Install required packages
RUN apt-get update && apt-get install -y \
    tzdata \
    && ln -snf /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

# Install system dependencies required for building TA-Lib
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    build-essential \
    wget \
    tar \
    gcc \
    make \
    autoconf \
    libtool \
    python3-dev && \
    rm -rf /var/lib/apt/lists/*

# Download and install the latest TA-Lib 0.6.1 from GitHub
RUN wget https://github.com/TA-Lib/ta-lib/releases/download/v0.6.1/ta-lib-0.6.1-src.tar.gz && \
    tar -xzf ta-lib-0.6.1-src.tar.gz && \
    cd ta-lib-0.6.1 && \
    ./configure --prefix=/usr/local && \
    make && \
    make install && \
    cd .. && \
    rm -rf ta-lib-0.6.1 ta-lib-0.6.1-src.tar.gz

# Ensure TA-Lib is properly recognized
RUN ldconfig

# Explicitly set environment variables for TA-Lib
ENV TA_LIBRARY_PATH="/usr/local/lib"
ENV TA_INCLUDE_PATH="/usr/local/include"
ENV LD_LIBRARY_PATH="/usr/local/lib"
ENV LIBRARY_PATH="/usr/local/lib"
ENV CPATH="/usr/local/include"

# Upgrade pip and install necessary dependencies
RUN pip install --upgrade pip && \
    pip install numpy==1.23.5 Cython

# Install TA-Lib Python wrapper with correct version
RUN TA_LIBRARY_PATH=/usr/local/lib TA_INCLUDE_PATH=/usr/local/include pip install --no-cache-dir ta-lib==0.6.1

# Set working directory
WORKDIR /app

# Copy project requirements first to leverage Docker cache
COPY requirements.txt /app/

# Install project requirements
RUN pip install --no-cache-dir -r requirements.txt

# Copy the main Python file
COPY PT-indicators-trader-bot-eth.py /app/

# Explicitly copy .env (if COPY . ignores hidden files)
COPY .env /app/.env

# Ensure line endings are properly converted during container build
RUN sed -i 's/\r$//' /app/PT-indicators-trader-bot-eth.py

# Copy the rest of the application
COPY . /app

# Environment Variables
ENV PAPER_TRADING=true
ENV PORT=8080

# Install dependencies
RUN pip install --no-cache-dir -r requirements.txt

# List installed Python packages for debugging
RUN pip list

# Default command
CMD ["sh", "-c", "exec python PT-indicators-traderbot-eth.py 2>&1 | tee /app/trader_bot.log"]
