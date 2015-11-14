FROM debian:jessie
MAINTAINER Lukas Martinelli <me@lukasmartinelli.ch>

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    python python-pip \
    make clang-3.5 clang-format-3.5 \
 && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /usr/scr/app
WORKDIR /usr/src/app

COPY requirements.txt /usr/src/app/
RUN pip install -r requirements.txt

COPY . /usr/src/app

CMD ["python2", "server.py"]
EXPOSE 5000
