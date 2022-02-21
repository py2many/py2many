from decimal import *

if __name__ == "__main__":
    getcontext().prec = 17
    d1 = 4.84143144246472090e+00
    d2 = -1.16032004402742839e+00
    d3 = -1.03622044471123109e-01
    print(Decimal(4.84143144246472090e+00))
    print(d1 == Decimal(4.84143144246472090e+00))