# docker buildx create --use --name insecure-builder --buildkitd-flags '--allow-insecure-entitlement security.insecure'
# docker buildx build -t archlinux:py2many --allow security.insecure -o type=docker \
#   --build-arg RUST=1 --build-arg CPP=1 --build-arg GOLANG=1 . -f docker/Dockerfile
#
# Edit the list of languages above based on what you're interested in
FROM archlinux:base-devel

MAINTAINER Arun Sharma <arun@sharma-home.net>

ARG RUST
ARG CPP
ARG GOLANG
ARG JULIA
ARG NIM
ARG KOTLIN
ARG DART
ARG VLANG
ARG SMT
ARG DLANG

RUN useradd --create-home --comment "Arch Build User" build
ENV HOME /home/build
ENV PATH "$PATH:/home/build/.local/bin:/home/build/.cargo/bin:/home/build/bin"
RUN usermod -aG wheel build
RUN echo '%wheel ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers

RUN pacman -Syu --noconfirm python python-pip unzip git

# C++
RUN test -z "$CPP" || pacman -Syu --noconfirm clang libc++

# Go
RUN test -z "$GOLANG" || pacman -Syu --noconfirm go

# Julia
RUN test -z "$JULIA" || pacman -Syu --noconfirm julia

# Nim
RUN test -z "$NIM" || pacman -Syu --noconfirm nim

# Kotlin
RUN test -z "$KOTLIN" || pacman -Syu --noconfirm kotlin

# Dart
RUN test -z "$DART" || pacman -Syu --noconfirm dart

# Dlang
RUN test -z "$DLANG" || pacman -Syu --noconfirm dlang

# Install yay
USER build
RUN cd $HOME && git clone https://aur.archlinux.org/yay-bin.git && cd yay-bin && makepkg -s
USER root
RUN cd $HOME/yay-bin && pacman -U --noconfirm *.zst && cd .. && rm -rf yay-bin

# Vlang:
RUN test -z "$VLANG" || (RUNNER_OS=Linux RELEASE=weekly.2021.29 \
    FILE=v_$(echo ${RUNNER_OS} | tr '[:upper:]' '[:lower:]').zip \
    && (cd /tmp && curl -sSLO https://github.com/vlang/v/releases/download/${RELEASE}/${FILE}) \
    && (cd /tmp && unzip ${FILE} && rm ${FILE}) \
    && ln -s /tmp/v/v /usr/bin)

# TODO: Add all formatters and other auxilliary setup from main.yml

USER build
RUN mkdir -p /home/build/bin
ADD scripts /scripts

# Per user package setup. Note that /root is inaccessible to user build
RUN python -m venv $HOME/.venv
RUN source  $HOME/.venv/bin/activate && pip3 install tox black isort flake8

# C++
RUN test -z "$CPP" || (source  $HOME/.venv/bin/activate && pip3 install conan && \
    /scripts/cpp-setup.sh)

# Rust
RUN test -z "$RUST" || (curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
   sh -s -- -y --default-toolchain nightly-2024-01-01)

# Go
RUN test -z "$GOLANG" || /scripts/go-setup.sh

# SMT
RUN test -z "$SMT" || yay -S --noconfirm cljstyle-bin

# DART/flutter
RUN test -z "$DART" || yay -S --noconfirm flutter-target-linux

# Julia
RUN test -z "$JULIA" || (julia -e 'using Pkg; Pkg.add("JuliaFormatter")' && \
    julia -e 'using Pkg; Pkg.add("SuperEnum")' && \
    (cd /home/build/bin && ln -s $(find ~/.julia -name format.jl)))

COPY docker/entrypoint.sh /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
