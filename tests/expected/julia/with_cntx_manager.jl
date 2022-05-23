using tempfile: NamedTemporaryFile
using textwrap: wrap
abstract type AbstractFileOp end
mutable struct FileOp <: AbstractFileOp
    file_name
    method
    file
end
function __enter__(self::FileOp)
    self.file = open(self.file_name, self.method)
    return self.file
end

function __exit__(self::FileOp, type_ = nothing, value = nothing, traceback = nothing)
    close(self.file)
end

if abspath(PROGRAM_FILE) == @__FILE__
    NamedTempFile::new() do temp_file
        file_path = temp_file.name
        FileOp(file_path, "w") do file
            write(file, "test")
        end
        open(file_path, "r") do f
            @assert(read(f) == "test")
        end
    end
end
