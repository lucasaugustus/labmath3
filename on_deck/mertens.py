#! /usr/bin/env python3

from labmath3 import *

def mobiusblock(a, b, primes):
    """
    [mu(n) for n in range(a, b)].
    primes is assumed to include all primes <= sqrt(b).
    """
    mobs = [1] * (b-a)
    for p in primes:
        for n in range((-a) %   p  , b - a,  p ): mobs[n] *= -p
        for n in range((-a) % (p*p), b - a, p*p): mobs[n]  =  0
        # TODO: Do we need to check here whether p*p > b?
    for n in range(b - a):
        m = mobs[n]
        if m == 0: continue
        if -a-n < m < a+n:
            if m > 0: mobs[n] = -1
            if m < 0: mobs[n] =  1
        else:
            if m > 0: mobs[n] =  1
            if m < 0: mobs[n] = -1
    return mobs

def mertensblock(a, b, Ma, primes):
    """
    [Mertens[n] for n in range(a,b)].
    Ma == Mertens(a).
    primes is assumed to include all primes <= sqrt(b).
    """
    M = mobiusblock(a, b, primes)
    # At this point, M[k] == mobius(a+k).
    M[0] = Ma
    for n in range(a+1, b): M[n] += M[n-1]
    # We now have M[k] == Mertens(k).
    return M

def mertens_unsegmented(x):
    # This is the unsegmented version of the Deleglise-Rivat algorithm.
    # On my system, under PyPy3, this computes mertens(10**14) == -875575 in 5 minutes exactly,
    # but uses 38.7 GB of memory along the way.  Segmentation should cut that down by a factor of 100,000 or so.
    if x < 8: return (0, 1, 0, -1, -1, -2, -1, -2)[x]
    u = introot(x, 3)
    mobs = [0] + list(mobiussieve(x//u + 2))
    merts = mobs[:]
    for i in range(1, len(merts)): merts[i] = merts[i-1] + merts[i]
    S1 = 0
    for m in range(1, u+1):
        if mobs[m] == 0: continue
        innersum = 0
        for n in range(-(u//-m), isqrt(x//m)+1):    # -(u//-m) == ceil(u/m)
            innersum += merts[x//(m*n)]
        S1 += mobs[m] * innersum
    S2 = 0
    for k in range(1, isqrt(x)+1):
        innersum = 0
        for m in range(1, min(u, x//(k*k))+1):
            # l is the number of integers n in the interval (sqrt(y), y] such that y // n == k.
            # These are the n such that k <= x/(mn) < k+1, or equivalently, x / ((k+1)*m) < n <= x / (m*k).
            lo1 = isqrt(x//m) + 1
            hi1 = x // m
            lo2 = x // (m * (k+1)) + 1
            hi2 = x // (m * k)
            lo = max(lo1, lo2)
            hi = min(hi1, hi2)
            l = hi - lo + 1
            if l < 0: l = 0
            innersum += mobs[m] * l
        S2 += merts[k] * innersum
    return (merts[u] - S1 - S2, merts[u], S1, S2)

def mertens_segmented(x):
    if x < 21: return (0, 1, 0, -1, -1, -2, -1, -2, -2, -2, -1, -2, -2, -3, -2, -1, -1, -2, -2, -3, -3)[x]
    u = introot(x, 3)   # TODO: for best results, use u == x^(1/3) * log(log(x))^(2/3) * constant.
    primes16 = list(primegen(isqrt(u)+1))
    mobs13 = mobiusblock(0, u+1, primes16)
    merts13 = [0] * (u+1)
    for n in range(u+1): merts13[n] = merts13[n-1] + mobs13[n]
    
    #primes13 = list(primegen(isqrt(x//u) + 1))
    #bigmertens = mertensblock(0, x//u+1, 0, primes13)
    #S1_dumb = sum(mobs13[m] * sum(bigmertens[x//m//n] for n in range((u//m)+1, isqrt(x//m)+1)) for m in range(1, u+1))
    #print("S1 dumb:", S1_dumb)
    #S2_dumb = sum(mobs13[m] * sum(bigmertens[x//m//n] for n in range(isqrt(x//m)+1, (x//m)+1)) for m in range(1, u+1))
    #print("S2 dumb:", S2_dumb)
    
    S1 = 0                                                                                                                # TODO
    for m in range(u, 0, -1):
        
    
    
    """
    m == 1:
    u < n <= sqrt(x)
    x^(1/3) --- x^(1/2)
    M(x/(1*n)): M(x^(2/3)) ... M(x^(1/2))
    
    m == u:
    1 < n <= sqrt(x/u)
    1 --- x^(1/3)
    M(x/(m*n)): M(x^(2/3)) ... M(x^(1/3))
    """
    
    S2 = 0
    M = 0
    for (k,mu) in enumerate(mobiussieve(isqrt(x)+1), start=1):
        M += mu
        innersum = 0
        for m in range(1, min(u, x//(k*k))+1):
            # l is the number of integers n in the interval (sqrt(y), y] such that y // n == k.
            # These are the n such that k <= x/(mn) < k+1, or equivalently, x / ((k+1)*m) < n <= x / (m*k).
            lo1 = isqrt(x//m) + 1
            hi1 = x // m
            lo2 = x // (m * (k+1)) + 1
            hi2 = x // (m * k)
            lo = max(lo1, lo2)
            hi = min(hi1, hi2)
            l = hi - lo + 1
            if l < 0: l = 0
            innersum += mobs13[m] * l
        S2 += M * innersum
    
    print("S2 nice:", S2)
    
    return merts13[u] - S1 - S2

from sys import argv
#print(mertens_unsegmented(int(argv[1])))
print(mertens_segmented(int(argv[1])))






