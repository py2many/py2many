import datetime

function calendar_test()
    now = isoformat(datetime.datetime.utcnow())
    println(join([now], " "));
end

function main()
    calendar_test();
end

main()
