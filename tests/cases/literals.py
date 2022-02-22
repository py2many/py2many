def string_literals():
    l1 = "literals\a" # bell
    l2 = "literals\b" # backspace
    l3 = "literals\f" # Formfeed
    l4 = "literals\n" # Linefeed
    l5 = "literals\r" # Carriage return
    l6 = "literals\v" # Vertical tab
    l7 = "literals\t" # Horizontal tab
    l8 = "\u002B"
    assert l8 == "+"
    l9 = "\U0000002B"
    assert l9 == "+"

    # multi-line String
    m = '''literal
           literal'''
    # single quote
    s = 'literal'
 
    # double quotes
    t = "literal"

# Supporting type comments to convert literals (PyJL)
def integer_literals():
    # Byte Literals
    l1 = 0b10110 # type: BLiteral
    assert l1 == 22
    
    # Octal Literal
    l2 = 0o333 # type: OLiteral
    assert l2 == 219

    # Decimal Literal
    l3 = 50
    assert l3 == 50 # should be trivial
    
    # Hexadecimal Literal
    l4 = 0x14c # type: HLiteral
    assert l4 == 332

def floating_point_literals():
    l1 = 25.99999
    l2 = 26.11111
    l3 = .001
    l4 = 10.
    l5 = 1e10
    l6 = 3.14e-10
    l7 = 3.14_15_93

    assert l3 == 0.001
    assert l4 == 10
    assert l5 == 10000000000
    assert l6 == 0.000000000314
    assert l7 == 3.141593

def imaginary():    
    l1 = 5j

def boolean_literals():
    l1 = (1 == True)
    l2 = (1 == False)
    l3 = True + l1
    l4 = False + l2
    assert l1 == 1
    assert l2 == 0
    assert l3 == 2
    assert l4 == 0

if __name__ == "__main__":
    string_literals()
    integer_literals()
    floating_point_literals()
    imaginary()
    boolean_literals()