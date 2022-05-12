module localserver
using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")

sys.coinit_flags = 2

using win32com.server: factory
usage = "Invalid command line arguments\n\nThis program provides LocalServer COM support\nfor Python COM objects.\n\nIt is typically run automatically by COM, passing as arguments\nThe ProgID or CLSID of the Python Server(s) to be hosted\n"
function serve(clsids)
    infos = RegisterClassFactories(factory, clsids)
    EnableQuitMessage(pythoncom, GetCurrentThreadId(win32api))
    CoResumeClassObjects(pythoncom)
    PumpMessages(pythoncom)
    RevokeClassFactories(factory, infos)
    CoUninitialize(pythoncom)
end

function main_func()
    if length(append!([PROGRAM_FILE], ARGS)) == 1
        MessageBox(win32api, 0, usage, "Python COM Server")
        quit(1)
    end
    serve(append!([PROGRAM_FILE], ARGS)[2:end])
end

function main()
    main_func()
end

main()
end
