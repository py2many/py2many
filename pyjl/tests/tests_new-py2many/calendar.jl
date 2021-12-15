import Dates as dt
function calendar_test()
now = isoformat(dt.datetime.utcnow())
println(now);
end

function main()
calendar_test();
end

main()
