#!/usr/bin/env bash
set -e

julia -e 'using Pkg; Pkg.add("JuliaFormatter"); Pkg.add("SuperEnum")'

if julia -e 'using Pkg; exit(isdefined(Pkg, :Apps) ? 0 : 1)'; then
  julia -e 'using Pkg; Pkg.Apps.add("JuliaFormatter")'
else
  bin_dir="${JULIAUP_HOME:-${HOME}/.juliaup}/bin"
  mkdir -p "${bin_dir}"
  cat >"${bin_dir}/jlfmt" <<'EOF'
#!/usr/bin/env julia
using JuliaFormatter
JuliaFormatter.main(ARGS)
EOF
  chmod +x "${bin_dir}/jlfmt"
fi
