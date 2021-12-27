using bisect: bisect
using contextlib: closing, contextmanager
using itertools: accumulate, chain, islice, zip_longest
using multiprocessing: Lock, RawValue, Process

using re: sub

write = buffer(stdout).write
function acquired_lock()
lock = Lock()
acquire(lock);
return lock
end

function started_process(target, args)
process = Process(target, args)
start(process);
return process
end

function lock_pair(pre_lock, post_lock, locks)
channel_lock_pair = Channel(1)
pre, post = locks ? (locks) : ((pre_lock, post_lock))
if pre
acquire(pre);
end

if post
release(post);
end
close((channel_lock_pair))
return channel_lock_pair
end

function write_lines(sequence, n, width, lines_per_block = 10000, newline = b'\n', table)
i = 0
blocks = ((n - width) / width) / lines_per_block
if blocks
for _ in (0:blocks - 1)
output = bytearray()
for i in (i:width:i + width*lines_per_block - 1)
output += sequence[(i + 1):i + width + 1] + newline
end
if table
write(translate(output, table));
else

write(output);


end
end
end
output = bytearray()
if i < (n - width)
for i in (i:width:n - width - 1)
output += sequence[(i + 1):i + width + 1] + newline
end
end
output += sequence[(i + 1):n + 1] + newline
if table
write(translate(output, table));
else

write(output);


end
flush(stdout.buffer);
end

function cumulative_probabilities(alphabet, factor = 1.0)
probabilities = tuple(accumulate((p*factor for (_, p) in alphabet)))
table = maketrans(bytearray, bytes(chain((0:length(alphabet) - 1), [255])), bytes(chain((ord(c) for (c, _) in alphabet), [10])))
return (probabilities, table)
end

function copy_from_sequence(header, sequence, n, width, locks)
sequence = bytearray(sequence, "utf8")
while length(sequence) < n
sequence = append!(sequence, sequence);
end
if true
__tmp1 = lock_pair()
write(header);
write_lines(sequence, n, width);
end
end

function lcg(seed, im, ia, ic)
channel_lcg = Channel(1)
local_seed = seed.value
try
while true
local_seed = (local_seed*ia + ic) % im
put!(channel_lcg, local_seed);
end
finally
seed.value = local_seed
end
close((channel_lcg))
return channel_lcg
end

function lookup(probabilities, values)
channel_lookup = Channel(1)
for value in values
put!(channel_lookup, bisect(probabilities, value));
end
close((channel_lookup))
return channel_lookup
end

function lcg_lookup_slow(probabilities, seed, im, ia, ic)
channel_lcg_lookup_slow = Channel(1)
if true
prng = closing(lcg(seed, im, ia, ic))
for value_lcg_lookup_slow in lookup(probabilities, prng)
put!(channel_lcg_lookup_slow, value_lcg_lookup_slow)
end;
end
close((channel_lcg_lookup_slow))
return channel_lcg_lookup_slow
end

function lcg_lookup_fast(probabilities, seed, im, ia, ic)
channel_lcg_lookup_fast = Channel(1)
local_seed = seed.value
try
while true
local_seed = (local_seed*ia + ic) % im
put!(channel_lcg_lookup_fast, bisect(probabilities, local_seed));
end
finally
seed.value = local_seed
end
close((channel_lcg_lookup_fast))
return channel_lcg_lookup_fast
end

function lookup_and_write(header, probabilities, table, values, start, stop, width, locks)
if isinstance(values, bytearray)
output = values
elseif

output = bytearray()


else

output[(begin + 1):stop - start] = lookup(probabilities, values)


end
if true
__tmp2 = lock_pair()
if start == 0
write(header);
end
write_lines(output, length(output), width);
end
end

function random_selection(header, alphabet, n, width, seed, locks)
im = 139968.0
ia = 3877.0
ic = 29573.0
probabilities, table = cumulative_probabilities(alphabet, im)
if !(locks)
if true
prng = closing(lcg_lookup_fast(probabilities, seed, im, ia, ic))
output = bytearray(islice(prng, n))
end
lookup_and_write(header, probabilities, table, output, 0, n, width);
elseif

pre_seed, post_seed, pre_write, post_write = locks


elseif

m = n > (width*15) ? (cpu_count()*3) : (1)


elseif

partitions = [(n / width*m)*width*i for i in (1:m - 1)]


elseif

processes = []


elseif

pre = pre_write


elseif

if true
__tmp3 = lock_pair()
if true
prng = closing(lcg(seed, im, ia, ic))
for (start, stop) in zip([0] + partitions, partitions + [n])
values = collect(islice(prng, stop - start))
post = stop < n ? (acquired_lock()) : (post_write)
push!(processes, started_process(lookup_and_write, (header, probabilities, table, values, start, stop, width, (pre, post))));
pre = post
end
end
end


else

for p in processes
join(p);
end


end
end

function fasta(n)
alu = sub("\s+", "", "\nGGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGA\nTCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACT\nAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAG\nGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCG\nCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA\n")
iub = collect(zip_longest("acgtBDHKMNRSVWY", (0.27, 0.12, 0.12, 0.27), 0.02))
homosapiens = collect(zip("acgt", (0.302954942668, 0.1979883004921, 0.1975473066391, 0.3015094502008)))
seed = RawValue("f", 42)
width = 60
tasks = [(copy_from_sequence, [b">ONE Homo sapiens alu
", alu, n*2, width]), (random_selection, [b">TWO IUB ambiguity codes
", iub, n*3, width, seed]), (random_selection, [b">THREE Homo sapiens frequency
", homosapiens, n*5, width, seed])]
if cpu_count() < 2
for (func, args) in tasks
func(starred!(args)/*unsupported*/);
end
elseif

written_1 = acquired_lock()


elseif

seeded_2 = acquired_lock()


elseif

written_2 = acquired_lock()


elseif

locks_sets = [(nothing, written_1), (nothing, seeded_2, written_1, written_2), (seeded_2, nothing, written_2, nothing)]


elseif

processes = [started_process(target, args + [locks_sets[i]]) for (i, (target, args)) in tasks.iter().enumerate()]


else

for p in processes
join(p);
end


end
end

function main()
fasta(Int64(argv[2]));
end

main()
