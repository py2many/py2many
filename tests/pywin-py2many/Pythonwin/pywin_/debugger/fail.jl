import win32com_.gen_py.debugger

function a()
    a = 1
    try
        b()
    catch exn
        post_mortem(win32com_.gen_py.debugger, exc_info(sys)[3])
        a = 1
        a = 2
        a = 3
        a = 4
        #= pass =#
    end
end

function b()
    b = 1
    set_trace(win32com_.gen_py.debugger)
    c()
    #= pass =#
end

function c()
    c = 1
    d()
end

function d()
    d = 1
    e(d)
    throw(ValueError("Hi"))
end

function e(arg)::Int64
    e = 1
    sleep(time, 1)
    return e
end

a()
