#!/usr/bin/env python3

import re
# Other Imports
import datetime as dt
import json as js


def typing_test():
    a: list[int] = [1, 2, 3]
    return a[1]


def calendar_test():
    return dt.datetime.utcnow().isoformat()


def date_to_json(objDate: dt.datetime) -> js:
    return {
        "__type__": "datetime",
        "year": objDate.year,
        "month": objDate.month,
        "day": objDate.day,
        "hour": objDate.hour,
        "minute": objDate.minute,
        "second": objDate.second,
        "microsecond": objDate.microsecond,
        "tz": (objDate.tzinfo.tzname(objDate), objDate.utcoffset().total_seconds()),
    }


def calendar_json_test() -> js:
    now = dt.datetime.now(dt.timezone.utc)  # Another way to import
    return js.dumps(now, default=date_to_json)


if __name__ == "__main__":
    b = typing_test()
    assert b == 2
    assert re.match(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}.\d{6}", calendar_test())

    res = calendar_json_test()
    print(res)
    # assert re.match(r'{\"__type__\": \"datetime\", \"year\": \d{4}, \"month\": \d{2}, \"day\": \d{2}|\d{1}, \"hour\": \d{2}, \"minute\": \d{2}, \"second\": \d{2}, \"microsecond\": \d{6}, \"tz\": [\"UTC\", 0.0]}', res)
    print("OK")
