using tempfile: NamedTemporaryFile
using textwrap: wrap
abstract type AbstractFileOp end
mutable struct FileOp <: AbstractFileOp
    file_name::Any
    method::Any
    file::Any
end
function __enter__(self::AbstractFileOp)
    self.file = open(self.file_name, self.method)
    return self.file
end

function __exit__(
    self::AbstractFileOp,
    type_ = nothing,
    value = nothing,
    traceback = nothing,
)
    close(self.file)
end

function main()
    NamedTempFile::new() do temp_file
        file_path = name(temp_file)
        FileOp(file_path, "w") do file
            write_(file, "test")
        end
        open(file_path, "r") do f
            @assert(read(f) == "test")
        end
    end
end

main()
