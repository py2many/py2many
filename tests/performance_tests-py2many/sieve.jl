function sieve(n)::Int64
    primes = repeat([true], (n + 1))
    counter = 0
    for i in (2:n-1)
        if primes[i+1]
            counter = counter + 1
            for j in (i*i:i:n-1)
                primes[j+1] = false
            end
        end
    end
    return counter
end

function main()
    @assert(sieve(10000000) == 664579)
end

main()
