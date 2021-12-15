using BenchmarkTools

function combinations(l)::Array
    result = []
    for x in (1:(length(l) - 1) - 1)
        ls = l[(x + 1):end]
        for y in ls
            push!(result, (l[x], y));
        end
    end
    return result
end

PI = 3.141592653589793
SOLAR_MASS = 4*PI*PI
DAYS_PER_YEAR = 365.24
BODIES = [
    # Sun
    ([0.0, 0.0, 0.0], [0.0, 0.0, 0.0], SOLAR_MASS)
    # Jupiter
    ([4.841431442464721, -1.1603200440274284, -0.10362204447112311], 
        [0.001660076642744037*DAYS_PER_YEAR, 0.007699011184197404*DAYS_PER_YEAR, -6.90460016972063e-05*DAYS_PER_YEAR],
        0.0009547919384243266*SOLAR_MASS)
    # Saturn
    ([8.34336671824458, 4.124798564124305, -0.4035234171143214],
        [-0.002767425107268624*DAYS_PER_YEAR, 0.004998528012349172*DAYS_PER_YEAR, 2.3041729757376393e-05*DAYS_PER_YEAR], 
        0.0002858859806661308*SOLAR_MASS)
    # Uranus
    ([12.894369562139131, -15.111151401698631, -0.22330757889265573],
        [0.002964601375647616*DAYS_PER_YEAR, 0.0023784717395948095*DAYS_PER_YEAR, -2.9658956854023756e-05*DAYS_PER_YEAR], 
        4.366244043351563e-05*SOLAR_MASS)
    # Neptune
    ([15.379697114850917, -25.919314609987964, 0.17925877295037118], 
        [0.0026806777249038932*DAYS_PER_YEAR, 0.001628241700382423*DAYS_PER_YEAR, -9.515922545197159e-05*DAYS_PER_YEAR], 
        5.1513890204661145e-05*SOLAR_MASS)
]
PAIRS = combinations(BODIES)

function advance(dt, n, bodies = BODIES, pairs = PAIRS)
    for i in (1:n)
        for ((a1,v1,m1),(a2,v2,m2)) in pairs
            # (([x1, y1, z1], v1, m1), ([x2, y2, z2], v2, m2))
            # Converted
            x1,x2 = a1[1], a2[1]
            y1,y2 = a1[2], a2[2]
            z1,z2 = a1[3], a2[3]

            dx = (x1 - x2)
            dy = (y1 - y2)
            dz = (z1 - z2)
            mag = dt*((dx*dx + dy*dy) + dz*dz)^-1.5
            b1m = m1*mag
            b2m = m2*mag

            v1[1] -= dx*b2m
            v1[2] -= dy*b2m
            v1[3] -= dz*b2m
            v2[1] += dx*b1m
            v2[2] += dy*b1m
            v2[3] += dz*b1m
        end
        for (r, v, m) in bodies
            # (r, [vx, vy, vz], m)
            # Converted
            vx = v[1]
            vy = v[2]
            vz = v[3]

            r[1] += dt*vx
            r[2] += dt*vy
            r[3] += dt*vz
        end
    end
end

function report_energy(bodies = BODIES, pairs = PAIRS, e = 0.0)
    for ((a1,v1,m1),(a2,v2,m2)) in pairs
        # (((x1, y1, z1), v1, m1), ((x2, y2, z2), v2, m2))
        # Converted
        x1,x2 = a1[1], a2[1]
        y1,y2 = a1[2], a2[2]
        z1,z2 = a1[3], a2[3]

        dx = (x1 - x2)
        dy = (y1 - y2)
        dz = (z1 - z2)
        e -= (m1*m2/((dx*dx + dy*dy) + dz*dz)^0.5)
    end
    for (r, v, m) in bodies
        # (r, [vx, vy, vz], m)
        # Converted
        vx = v[1]
        vy = v[2]
        vz = v[3]

        e += (m*((vx*vx + vy*vy) + vz*vz)/2.0)
    end
    println(e);
end

function offset_momentum(ref, bodies = BODIES, px = 0.0, py = 0.0, pz = 0.0)
    for (r,v,m) in bodies
        # (r, [vx, vy, vz], m)
        # Converted
        vx = v[1]
        vy = v[2]
        vz = v[3]

        px -= vx*m
        py -= vy*m
        pz -= vz*m
    end
    r, v, m = ref
    v[1] = (px/m)
    v[2] = (py/m)
    v[3] = (pz/m)
end

function main_func(n)
    offset_momentum(BODIES[1]);
    report_energy();
    advance(0.01, n);
    report_energy();
end

function main()
    # 50000000
    # -0.169075164
    # -0.169078071
    test_num::Int64 = 500000
    @time main_func(Int64(test_num))
end


main()
