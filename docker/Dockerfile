# syntax=docker/dockerfile:1
#
# .github/workflows/main.yml builds and pushes this image before running tests.
#
# The image intentionally contains the language runtimes and test helpers that
# used to be assembled by GitHub Actions setup actions in main.yml.
FROM alpine:3.20

ARG FOCUS=
ARG V_VERSION=0.5.1
ARG RUST_TOOLCHAIN=nightly-2024-01-01
ARG DART_VERSION=3.4.4
ARG FLUTTER_VERSION=3.22.3
ARG GO_VERSION=1.26.0
ARG JULIA_VERSION=1.10.5
ARG KOTLIN_VERSION=2.0.21

ENV HOME=/root \
    PATH="/root/.venv/bin:/root/go/bin:/usr/local/go/bin:/root/.cargo/bin:/root/.pub-cache/bin:/opt/v:/opt/flutter/bin:/opt/dart-sdk/bin:/opt/julia/bin:/opt/kotlinc/bin:${PATH}" \
    CXX=clang++ \
    CXXFLAGS="-fuse-ld=lld" \
    CLANG_FORMAT_STYLE=Google \
    KOTLIN_HOME=/opt/kotlinc \
    PUB_CACHE=/root/.pub-cache \
    VFLAGS="-cc gcc -gc none"

RUN apk add --no-cache \
      astyle \
      bash \
      build-base \
      ca-certificates \
      catch2 \
      clang \
      clang-extra-tools \
      cmake \
      curl \
      dub \
      gc-dev \
      git \
      gcompat \
      libc++ \
      libc++-dev \
      libstdc++ \
      linux-headers \
      lld \
      ldc \
      make \
      nim \
      openjdk17-jdk \
      python3 \
      py3-pip \
      py3-virtualenv \
      sudo \
      tar \
      unzip \
      xz \
      z3 \
      z3-dev \
      zig \
      zip

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN ln -sf /usr/bin/ldmd2 /usr/local/bin/dmd

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    echo "Building py2many CI image for focus: ${FOCUS:-all}"

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install go; then \
      arch="$(apk --print-arch)" \
      && case "${arch}" in \
        x86_64) go_arch="amd64" ;; \
        aarch64) go_arch="arm64" ;; \
        *) echo "Unsupported Go release target: ${arch}" >&2; exit 1 ;; \
      esac \
      && curl -fsSL -o /tmp/go.tar.gz "https://go.dev/dl/go${GO_VERSION}.linux-${go_arch}.tar.gz" \
      && rm -rf /usr/local/go \
      && tar -C /usr/local -xzf /tmp/go.tar.gz \
      && rm /tmp/go.tar.gz \
      && go version; \
    fi

RUN python3 -m venv "${HOME}/.venv" \
    && source "${HOME}/.venv/bin/activate" \
    && pip install --upgrade pip \
    && pip install \
      black==24.10.0 \
      conan \
      cpplint \
      flake8 \
      isort \
      jgo \
      setuptools \
      tox

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install rust; then \
      curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --default-toolchain "${RUST_TOOLCHAIN}" --component clippy,rustfmt; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install vlang; then \
      curl -fsSL -o /tmp/v.zip "https://github.com/vlang/v/releases/download/${V_VERSION}/v_linux.zip" \
      && unzip -q /tmp/v.zip -d /opt \
      && rm /tmp/v.zip \
      && ln -sf /opt/v/v /usr/local/bin/v \
      && v version; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install julia; then \
      curl -fsSL -o /tmp/julia.tar.gz \
        "https://julialang-s3.julialang.org/bin/linux/x64/${JULIA_VERSION%.*}/julia-${JULIA_VERSION}-linux-x86_64.tar.gz" \
      && mkdir -p /opt/julia \
      && tar -xzf /tmp/julia.tar.gz -C /opt/julia --strip-components=1 \
      && rm /tmp/julia.tar.gz \
      && ln -sf /usr/lib/libgcc_s.so.1 /opt/julia/lib/julia/libgcc_s.so.1 \
      && julia --version; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install kotlin; then \
      curl -fsSL -o /tmp/kotlin.zip \
        "https://github.com/JetBrains/kotlin/releases/download/v${KOTLIN_VERSION}/kotlin-compiler-${KOTLIN_VERSION}.zip" \
      && unzip -q /tmp/kotlin.zip -d /opt \
      && rm /tmp/kotlin.zip \
      && kotlin -version; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install dart; then \
      curl -fsSL -o /tmp/dart.zip \
        "https://storage.googleapis.com/dart-archive/channels/stable/release/${DART_VERSION}/sdk/dartsdk-linux-x64-release.zip" \
      && unzip -q /tmp/dart.zip -d /opt \
      && rm /tmp/dart.zip; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install dart; then \
      curl -fsSL -o /tmp/flutter.tar.xz \
        "https://storage.googleapis.com/flutter_infra_release/releases/stable/linux/flutter_linux_${FLUTTER_VERSION}-stable.tar.xz" \
      && tar -xJf /tmp/flutter.tar.xz -C /opt \
      && rm /tmp/flutter.tar.xz \
      && git config --global --add safe.directory /opt/flutter \
      && flutter config --no-analytics \
      && flutter --version; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install mojo; then \
      curl -fsSL https://pixi.sh/install.sh | bash \
      && ln -sf "${HOME}/.pixi/bin/pixi" /usr/local/bin/pixi \
      && cd "${HOME}" \
      && pixi init life -c https://conda.modular.com/max-nightly/ -c conda-forge \
      && cd life \
      && pixi add modular \
      && pixi run mojo --version \
      && ln -sf "${HOME}/life/.pixi/envs/default/bin/mojo" /usr/local/bin/mojo; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install julia; then \
      julia -e 'using Pkg; Pkg.add("JuliaFormatter"); Pkg.add("SuperEnum")' \
      && JULIA_FORMATTER_ROOT="$(julia -e 'import JuliaFormatter;print(dirname(dirname(pathof(JuliaFormatter))));')" \
      && ln -sf "${JULIA_FORMATTER_ROOT}/bin/format.jl" /usr/local/bin/format.jl; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install dlang; then \
      mkdir -p /tmp/dlang-build \
      && cd /tmp/dlang-build \
      && dub init -n . \
      && dub add dfmt \
      && dub fetch dfmt --cache=local \
      && rm -rf /tmp/dlang-build; \
    fi

COPY scripts /scripts

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install cpp; then \
      source "${HOME}/.venv/bin/activate" \
      && mkdir -p /work/tests \
      && cd /work \
      && /scripts/cpp-setup.sh; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install dart; then \
      mkdir -p /work/tests \
      && cd /work \
      && /scripts/dart-setup.sh; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install go; then \
      mkdir -p /work/tests \
      && cd /work \
      && /scripts/go-setup.sh; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install zig; then \
      mkdir -p /work/tests \
      && cd /work \
      && /scripts/zig-setup.sh; \
    fi

RUN should_install() { case "${FOCUS}" in ""|all|omni|"${1}") return 0 ;; *) return 1 ;; esac; }; \
    if should_install vlang; then \
      v install div72.vexc; \
    fi

COPY docker/entrypoint.sh /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
