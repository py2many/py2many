using PyCall
win32ui = pyimport("win32ui")

import string
function ParseArgs(str)::Vector
    ret = []
    pos = 0
    length = length(str)
    while pos < length
        try
            while str[pos+1] ∈ string.whitespace
                pos = pos + 1
            end
        catch exn
            if exn isa IndexError
                break
            end
        end
        if pos >= length
            has_break = true
            break
        end
        if str[pos+1] == "\""
            pos = pos + 1
            try
                endPos = index(str, "\"", pos) - 1
                nextPos = endPos + 2
            catch exn
                if exn isa ValueError
                    endPos = length
                    nextPos = endPos + 1
                end
            end
        else
            endPos = pos
            while endPos < length && !(str[endPos+1] ∈ string.whitespace)
                endPos = endPos + 1
            end
            nextPos = endPos + 1
        end
        push!(ret, strip(str[pos+1:endPos+1]))
        pos = nextPos
    end
    return ret
end

function FixArgFileName(fileName)
    #= Convert a filename on the commandline to something useful.
        Given an automatic filename on the commandline, turn it a python module name,
        with the path added to sys.path. =#
    path, fname = split(os.path, fileName)
    if length(path) == 0
        path = os.curdir
    end
    path = abspath(os.path, path)
    has_break = false
    for syspath in sys.path
        if abspath(os.path, syspath) === path
            has_break = true
            break
        end
    end
    if has_break != true
        append(sys.path, path)
    end
    return splitext(os.path, fname)[1]
end
