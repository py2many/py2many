#!/bin/bash
set -e

source "/root/.venv/bin/activate"

workspace="${GITHUB_WORKSPACE:-$PWD}"
if [[ -d /work/tests/build && -d "${workspace}/tests" ]]; then
  mkdir -p "${workspace}/tests/build"
  cp -a /work/tests/build/. "${workspace}/tests/build/"

  # zig-runner.sh is invoked from tests/build and uses a cwd-relative
  # tests/build/common-zig-proj path.
  mkdir -p "${workspace}/tests/build/tests/build"
  cp -a /work/tests/build/. "${workspace}/tests/build/tests/build/"
fi

exec "$@"
