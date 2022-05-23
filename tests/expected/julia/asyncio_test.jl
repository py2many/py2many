
@async function nested()
    return 42
end
@async function async_main()
    @assert(wait(nested()) == 42)
    println("OK")
end
@async function echo_server()
    server = listen(2001)
    while true
        sock = wait(accept(server))
        @async function writer()
            while isopen(sock)
                data = wait(readline(sock))
                wait(write(sock, upper(data)))
            end
        end
        wait(writer())
    end
end
if abspath(PROGRAM_FILE) == @__FILE__
    run(asyncio, async_main())
    run(asyncio, echo_server())
end
