
x::Int64 = None
y::Int64 = None
x > 2;
y < 10;
(x + repeat(y,2)) == 7;
check_sat();
get_value((x, y));
