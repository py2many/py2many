# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# regex-dna program contributed by Dominique Wahli
# 2to3
# mp by Ahmad Syukri
# modified by Justin Peel
# converted from regex-dna program
# Modified to be single threaded

from sys import stdin
from re import sub, findall

def var_find(f):
    return len(findall(f, seq))

def main():
    # Set seq as global, as pool was removed
    global seq
    seq = stdin.read()

    ilen = len(seq)

    seq = sub('>.*\n|\n', '', seq)
    clen = len(seq)

    variants = (
          'agggtaaa|tttaccct',
          '[cgt]gggtaaa|tttaccc[acg]',
          'a[act]ggtaaa|tttacc[agt]t',
          'ag[act]gtaaa|tttac[agt]ct',
          'agg[act]taaa|ttta[agt]cct',
          'aggg[acg]aaa|ttt[cgt]ccct',
          'agggt[cgt]aa|tt[acg]accct',
          'agggta[cgt]a|t[acg]taccct',
          'agggtaa[cgt]|[acg]ttaccct')
    for f in zip(variants, map(var_find, variants)):
        print(f[0], f[1])

    subst = {
          'tHa[Nt]' : '<4>', 'aND|caN|Ha[DS]|WaS' : '<3>', 'a[NSt]|BY' : '<2>',
          '<[^>]*>' : '|', '\\|[^|][^|]*\\|' : '-'}
    for f, r in subst.items():
        seq = sub(f, r, seq)

    print()
    print(ilen)
    print(clen)
    print(len(seq))

if __name__=="__main__":
    main()