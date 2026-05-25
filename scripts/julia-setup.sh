#!/usr/bin/env bash

julia -e 'using Pkg; Pkg.add("JuliaFormatter"); Pkg.add("SuperEnum")'

julia -e 'using Pkg; Pkg.Apps.add("JuliaFormatter")'
