#!/usr/bin/env bash
set -e

julia -e 'using Pkg; Pkg.add("JuliaFormatter"); Pkg.add("SuperEnum")'

if julia -e 'using Pkg; exit(isdefined(Pkg, :Apps) ? 0 : 1)'; then
  julia -e 'using Pkg; Pkg.Apps.add("JuliaFormatter")'
else
  cat >/usr/local/bin/jlfmt <<'EOF'
#!/usr/bin/env julia
using JuliaFormatter
JuliaFormatter.main(ARGS)
EOF
  chmod +x /usr/local/bin/jlfmt
fi
