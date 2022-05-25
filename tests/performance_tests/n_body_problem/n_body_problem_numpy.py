# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# originally by Kevin Carson
# modified by Tupteq, Fredrik Johansson, and Daniel Nanz
# modified by Maciej Fijalkowski
# 2to3

from time import perf_counter
import numpy as np

def combinations(l):
    result = []
    for x in range(len(l) - 1):
        ls = l[x+1:]
        for y in ls:
            result.append([l[x],y])
            # np.append(result, [l[x],y], axis=0)

    return np.array(result, dtype=np.float64)

PI = 3.14159265358979323
SOLAR_MASS = 4 * PI * PI
DAYS_PER_YEAR = 365.24

SYSTEM = np.array([
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, SOLAR_MASS], # sun
            [4.84143144246472090e+00, # jupiter
            -1.16032004402742839e+00,
            -1.03622044471123109e-01,
            1.66007664274403694e-03 * DAYS_PER_YEAR,
            7.69901118419740425e-03 * DAYS_PER_YEAR,
            -6.90460016972063023e-05 * DAYS_PER_YEAR,
            9.54791938424326609e-04 * SOLAR_MASS],
            [8.34336671824457987e+00, # saturn
            4.12479856412430479e+00,
            -4.03523417114321381e-01,
            -2.76742510726862411e-03 * DAYS_PER_YEAR,
            4.99852801234917238e-03 * DAYS_PER_YEAR,
            2.30417297573763929e-05 * DAYS_PER_YEAR,
            2.85885980666130812e-04 * SOLAR_MASS],
            [1.28943695621391310e+01, # uranus
            -1.51111514016986312e+01,
            -2.23307578892655734e-01,
            2.96460137564761618e-03 * DAYS_PER_YEAR,
            2.37847173959480950e-03 * DAYS_PER_YEAR,
            -2.96589568540237556e-05 * DAYS_PER_YEAR,
            4.36624404335156298e-05 * SOLAR_MASS],
            [1.53796971148509165e+01, # neptune
            -2.59193146099879641e+01,
            1.79258772950371181e-01,
            2.68067772490389322e-03 * DAYS_PER_YEAR,
            1.62824170038242295e-03 * DAYS_PER_YEAR,
            -9.51592254519715870e-05 * DAYS_PER_YEAR,
            5.15138902046611451e-05 * SOLAR_MASS]
        ], dtype=np.float64)


PAIRS = combinations(SYSTEM)


def advance(dt, n, bodies=SYSTEM, pairs=PAIRS):
    for i in range(n):
        for j in range(len(pairs)):
            ((x1, y1, z1, v11, v12, v13, m1),
             (x2, y2, z2, v21, v22, v23, m2)) = pairs[j]
            dx = x1 - x2
            dy = y1 - y2
            dz = z1 - z2
            mag = dt * ((dx * dx + dy * dy + dz * dz) ** (-1.5))
            b1m = m1 * mag
            b2m = m2 * mag
            pairs[j, 0, 3] -= dx * b2m
            pairs[j, 0, 4] -= dy * b2m
            pairs[j, 0, 5] -= dz * b2m
            pairs[j, 1, 3] += dx * b1m
            pairs[j, 1, 4] += dy * b1m
            pairs[j, 1, 5] += dz * b1m
        for (r1, r2, r3, vx, vy, vz, m) in bodies:
            r1 += dt * vx
            r2 += dt * vy
            r3 += dt * vz


def report_energy(bodies=SYSTEM, pairs=PAIRS, e=0.0):
    for ((x1, y1, z1, v11, v12, v13, m1),
         (x2, y2, z2, v21, v22, v23, m2)) in pairs:
        dx = x1 - x2
        dy = y1 - y2
        dz = z1 - z2
        e -= (m1 * m2) / ((dx * dx + dy * dy + dz * dz) ** 0.5)
    for (r1, r2, r3, vx, vy, vz, m) in bodies:
        e += m * (vx * vx + vy * vy + vz * vz) / 2.
    print("%.9f" % e)

def offset_momentum(ref, bodies=SYSTEM, px=0.0, py=0.0, pz=0.0):
    for (r1, r2, r3, vx, vy, vz, m) in bodies:
        px -= vx * m
        py -= vy * m
        pz -= vz * m
    m = ref[-1]
    ref[3] = px / m
    ref[4] = py / m
    ref[5] = pz / m

def main(n):
    offset_momentum(SYSTEM[0])
    report_energy()
    advance(0.01, n)
    report_energy()

if __name__ == '__main__':
    # main(int(sys.argv[1]))
    start = perf_counter()
    main(500000)
    end = perf_counter()
    print(end - start)
