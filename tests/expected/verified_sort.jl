



struct BankAccount
    balance::Int64
end

function deposit(self::BankAccount, amount::Int64)::BankAccount
    self.balance += amount
    return self
end

function safe_sqrt(n::Int64)::Int64
    i::Int64 = 0
    while i*i <= n
        i += 1
    end
    return i - 1
end

function sqrt_of_9()::Bool
    return safe_sqrt(9) == 3
end

function merge(left::Array{Int64}, right::Array{Int64})::Array{Int64}
    result::Array{Int64} = []
    i::Int64 = 0
    j::Int64 = 0
    while i < length(left)&&j < length(right)
        if left[i+1] <= right[j+1]
            push!(result, left[i+1])
            i += 1
        else

            push!(result, right[j+1])
            j += 1
        end
    end
    while i < length(left)
        push!(result, left[i+1])
        i += 1
    end
    while j < length(right)
        push!(result, right[j+1])
        j += 1
    end
    return result
end

function take(xs::Array{Int64}, n::Int64)::Array{Int64}
    out::Array{Int64} = []
    i::Int64 = 0
    while i < n
        push!(out, xs[i+1])
        i += 1
    end
    return out
end

function drop(xs::Array{Int64}, n::Int64)::Array{Int64}
    out::Array{Int64} = []
    i::Int64 = n
    while i < length(xs)
        push!(out, xs[i+1])
        i += 1
    end
    return out
end

function sort_u64(arr::Array{Int64})::Array{Int64}
    if length(arr) <= 1
        return arr
    end
    mid::Int64 = length(arr) / 2
    left::Array{Int64} = sort_u64(take(arr, mid))
    right::Array{Int64} = sort_u64(drop(arr, mid))
    return merge(left, right)
end

function concrete_example()::Bool
    return sort_u64([3, 1, 4, 1, 5, 9, 2, 6]) == [1, 1, 2, 3, 4, 5, 6, 9]
end

function main()
    acct = BankAccount(10)
    println(join([acct.balance], " "))
end

main()
