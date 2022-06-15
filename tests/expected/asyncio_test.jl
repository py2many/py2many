
@async function nested()
    return 42
end
@async function async_main()
    @assert(wait(nested()) == 42)
    println("OK")
end
if abspath(PROGRAM_FILE) == @__FILE__
    asyncio.run(async_main())
end
