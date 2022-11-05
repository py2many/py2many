
def test():
    # The definition of a depends on the for loop's range
    # Therefore, the propagated static type should not be
    # int, but Optional[int] (Union[int, None])
    # PyJL's fix_scope_bounds flag should propagate the type 
    # and generate the expected code
    for i in range(1):
        a = 2
    print(a*"aa")

test()