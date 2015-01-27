FROM debian:jessie
MAINTAINER Lukas Martinelli <me@lukasmartinelli.ch>

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    make \
    clang-3.5 \
    clang-format-3.5 \
 && rm -rf /var/lib/apt/lists/*
WORKDIR /root
