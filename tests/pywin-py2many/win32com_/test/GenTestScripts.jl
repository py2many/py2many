using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")

import win32com_
import win32com_.client.makepy
import win32com_.test

genList = [("msword8", "{00020905-0000-0000-C000-000000000046}", 1033, 8, 0)]
genDir = "Generated4Test"
function GetGenPath()
    return join
end

function GenerateFromRegistered(fname)
    genPath = GetGenPath()
    try
        stat(os, genPath)
    catch exn
        if exn isa os.error
            mkdir(os, genPath)
        end
    end
    close(readline(join))
    print("$(fname): generating -")
    f = readline(join)
    GenerateFromTypeLibSpec(win32com_.client.makepy, loadArgs, f, 1, 1)
    close(f)
    print("compiling -")
    fullModName = "win32com_.test.%s.%s" % (genDir, fname)
    exec("import " + fullModName)
    sys.modules[fname+1] = sys.modules[fullModName+1]
    println("done")
end

function GenerateAll()
    for args in genList
        try
            GenerateFromRegistered(args...)
        catch exn
            if exn isa KeyboardInterrupt
                println("** Interrupted ***")
                break
            end
            if exn isa pythoncom.com_error
                println("** Could not generate test code for $(args[1])")
            end
        end
    end
end

function CleanAll()
    println("Cleaning generated test scripts...")
    try
        1 / 0
    catch exn
        #= pass =#
    end
    genPath = GetGenPath()
    for args in genList
        try
            name = args[1] + ".py"
            std::fs::remove_file(join)
        catch exn
            let details = exn
                if details isa os.error
                    if type_(details) == type_(()) && details[1] != 2
                        println("Could not deleted generated$(name)$(details)")
                    end
                end
            end
        end
        try
            name = args[1] + ".pyc"
            std::fs::remove_file(join)
        catch exn
            let details = exn
                if details isa os.error
                    if type_(details) == type_(()) && details[1] != 2
                        println("Could not deleted generated$(name)$(details)")
                    end
                end
            end
        end
        try
            std::fs::remove_file(join)
        catch exn
            #= pass =#
        end
        try
            std::fs::remove_file(join)
        catch exn
            #= pass =#
        end
    end
    try
        rmdir(os, genPath)
    catch exn
        let details = exn
            if details isa os.error
                println("Could not delete test directory -$(details)")
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    GenerateAll()
    CleanAll()
end
