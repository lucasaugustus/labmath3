#! /usr/bin/env python3

from sys import argv
from time import time
from labmath3 import *
n = int(argv[1])

def sqfrcount1(n): return sum(mu*(n//(d*d)) for (d,mu) in enumerate(mobiussieve(isqrt(n)+1),start=1))   # O(n^0.5)T, O(n^0.25)S

def TabulateMobiusBlock(a,b):   # https://arxiv.org/pdf/1107.4890, algorithm 6
    # In the reference's pseudocode, the arrays m and mu are indexed over the interval (a,b].
    # We will index them from 0 to b-a, inclusive, so that mu[k] == mobius(a+k).
    mu = [1] * (b-a+1)
    m  = [1] * (b-a+1)
    for p in primegen(isqrt(b)+1):
        for k in range((-a) % p*p, b-a+1, p*p): mu[k]  =  0
        for k in range((-a) %  p , b-a+1,  p ): mu[k] *= -1; m[k] *=  p
    for k in range(b-a+1):
        if m[k] < a+k: mu[k] *= -1
    return mu

starttime = time()
print("Algorithm 1: ", end='', flush=True)
answer_1 = sqfrcount1(n)
print(answer_1, time() - starttime)

def MxBlockUpdate(a,b,i,k): # https://arxiv.org/pdf/1107.4890, algorithm 3
    global Mx,n,I,M,al,B,L,l
    assert 0 <= a < b
    assert 1 <= i < I
    xi = isqrt(n//i)    # as per section 3, line (3)
    da = xi // k
    while True:
        db = xi // (k+1)
        try: Mx[i] -= (da - db) * M[k-al]
        except IndexError:
            print(M, len(M))
            print(k, al, k-al)
            print(B, L, l, D)
            raise
        k = xi // db
        da = db
        if k > b: break
    return k

# Line 1:
I = int((n**0.2) * (log(log(n))**0.8) * 1.0) # TODO: the "1.0" part is a tunable parameter.
D = isqrt(n//I)

s1_brute = sum(mu * (n//(d*d)) for (d,mu) in enumerate(mobiussieve(D+1), start=1))
print("s1 brute:", s1_brute)

B = isqrt(D)
L = -(D // -B)  # ceil(D/B)
# Lines 2,3,4:
ilist = [set() for l in range(L+1)]
# Lines 5,6,7,8,9:
Mx = [1] * I
mink = [1] * I
ilist[0] = set(range(I))
# Line 10:
s1 = 0
# My addition:
lastM = 0
# Line 11:
for l in range(L):
    al = B * l              # as per the first paragraph of section 4.3
    alp1 = min(al + B, D)   # as per the first paragraph of section 4.3
    # Line 12:
    mu = TabulateMobiusBlock(al, alp1)
    # Lines 13,14,15:
    for k in range(al+1, alp1+1): s1 += mu[k-al] * (n // (k*k))
    # Line 16:
    M = [0] * (alp1 - al + 1)
    M[0] = lastM
    for k in range(1, alp1+1):
        M[k] = M[k-1] + mu[k]
    # At this point, M[k] == mertens(al + k) for all 0 <= k <= alp1.
    # My addition:
    lastM = M[-1]
    # Line 17:
    for i in ilist[l]:
        # Line 18:
        mink[i] = MxBlockUpdate(al, alp1, i, mink[i])
        # Line 19:
        lprime = mink[i] // B
        # My addition:
        xi = isqrt(n//i)    # as per section 3, line (3)
        # Line 20:
        if lprime <= L and mink[i] < xi:
            # Line 21:
            ilist[lprime].add(i)
        # Line 22: end if
    # Line 23: end for
    # Line 24:
    ilist[l] = set()
# Line 25: end for

print("s1 fancy:", s1)
assert s1 == s1_brute

# My addition:
Mx.append(lastM)    # records M(D) as Mx[I]

# Line 26:
for i in range(I-1, 0, -1):
    # Line 27:
    d = 2
    while d*d*i < I:
        # Line 28:
        Mx[i] -= Mx[d*d*i]
        # Line 27:
        d += 1
    # Line 29: end while
# Line 30: end for

s2_brute = sum(mu * (n//(d*d)) for (d,mu) in enumerate(mobiussieve(isqrt(n)+1), start=1) if d > D)
print("s2 brute:", s2_brute)

# Line 31:
s2 = sum(Mx[i] for i in range(1, I)) - (I-1) * Mx[I]
print("s2 fancy:", s2)

answer_4 = s1 + s2
print("Algorithm 4:", answer_4, time() - starttime)

assert s2 == s2_brute
assert answer_1 == answer_4




# https://github.com/jakubpawlewicz/sqrfree/blob/debug/sol5.cpp




