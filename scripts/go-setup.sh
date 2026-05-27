#!/usr/bin/env bash

set -euo pipefail

mkdir -p tests/build
if [[ ! -f tests/build/go.mod ]]; then
  cd tests/build
  go mod init github.com/py2many/py2many/tests
  go get -u github.com/electrious/refutil
  go get -u github.com/hgfischer/go-iter
  go get -u github.com/google/go-cmp/cmp
  cd ..
fi

if ! command -v revive >/dev/null 2>&1; then
  go install github.com/mgechev/revive@latest
  if [[ -d /usr/local/bin && ! -f /usr/local/bin/revive && -f $HOME/go/bin/revive ]]; then
    if [[ -w /usr/local/bin ]]; then
      ln -fs "$HOME/go/bin/revive" /usr/local/bin/revive
    else
      sudo ln -fs "$HOME/go/bin/revive" /usr/local/bin/revive
    fi
  fi
fi
