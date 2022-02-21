
x::Int64 = None
y::Int64 = None
x > 2;
y < 10;
(x + 2 * y) == 7;
check_sat();
get_model((x, y));
