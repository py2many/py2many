import Dates
import Dates.DateTime
import JSON

# Microsecond and TimeZone not supported
function date_to_json(objDate::DateTime)
    return Dict(
        "__type__" => "datetime", 
        "year" => Dates.year(objDate), 
        "month" => Dates.month(objDate), 
        "day" => Dates.day(objDate), 
        "hour" =>  Dates.hour(objDate), 
        "minute" =>  Dates.minute(objDate), 
        "second" =>  Dates.second(objDate),
    )
end

function calendar_json_test()
    now = Dates.now()
    strDate = date_to_json(now)
    # strDate = Dates.format(now, "yyyy-mm-ddTHH:MM:SS")
    return strDate
end

function main()
    res = calendar_json_test()
    println(join([res], " "));
end

main()
