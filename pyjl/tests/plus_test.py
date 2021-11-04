# Runtime information
def plus_test(x, y):
    return x + y

# Last resort
# function plus_test(x, y)
    # return isa(x, String) && isa(y, String) ? x * y : x + y
# end

# Compile time information
def plus_test(x:str, y:str):
    return x + y

# function plus_test(x::String, y::String)::String
    # return (x * y)
# end

if __name__ == "__main__":
    x = "ss"
    y = "zz"
    res = plus_test(x, y)
    print(res)