#!/usr/bin/env bash
set -euo pipefail

# Build dfmt once (version-pinned). `dub run dfmt` rebuilds/relinks on every
# call (https://github.com/dlang-community/dfmt/issues/407) and dub can't build
# a package safely from concurrent processes
# (https://github.com/dlang/dub/issues/1113), so the test suite (pytest-xdist)
# calls the prebuilt binary directly via PATH instead (see .mise.toml _.path
# and pyd/__init__.py). The dfmt version here must match the path in .mise.toml.
dub run --yes dfmt@0.15.2 -- --version

# Make `dfmt` resolvable on PATH so pyd/__init__.py calls the prebuilt binary
# directly. mise already handles this via .mise.toml _.path, so when dfmt is
# reachable we leave it alone. The Docker image doesn't add the dub cache to
# PATH, so there we symlink the binary into /usr/local/bin (cf. revive in
# go-setup.sh). Guarding on PATH (rather than detecting mise) keeps us off
# /usr/local whenever something has already put dfmt within reach.
if ! command -v dfmt >/dev/null 2>&1; then
  dfmt_bin="$(find "${DUB_HOME:-${HOME}/.dub}/packages" -type f -path '*/dfmt/bin/dfmt' 2>/dev/null | head -n1)"
  if [[ -n "${dfmt_bin}" && -d /usr/local/bin && ! -e /usr/local/bin/dfmt ]]; then
    if [[ -w /usr/local/bin ]]; then
      ln -fs "${dfmt_bin}" /usr/local/bin/dfmt
    else
      sudo ln -fs "${dfmt_bin}" /usr/local/bin/dfmt
    fi
  fi
else
  echo "dfmt already on PATH: $(command -v dfmt)"
fi
