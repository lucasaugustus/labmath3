#! /usr/bin/env python3

from labmath3 import *

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
    [Mertens(n) for n in range(a,b)].
    Ma == Mertens(a).
    primes is assumed to include all primes <= sqrt(b).
    """
    M = mobiusblock(a, b, primes)
    # At this point, M[k] == mobius(a+k).
    M[0] = Ma
    for n in range(1, b-a): M[n] += M[n-1]
    # We now have M[k] == Mertens(k).
    return M

def mertens_segmented(x):
    if x < 21: return (0, 1, 0, -1, -1, -2, -1, -2, -2, -2, -1, -2, -2, -3, -2, -1, -1, -2, -2, -3, -3)[x]
    u = introot(int(x * log(log(x))**2 * 1.0), 3)                     # TODO: experiment with various values for the multiplier.
    primes16 = list(primegen(isqrt(u)+1))
    mobs_u = mobiusblock(0, u+1, primes16)
    merts_u = [0] * (u+1)
    for n in range(u+1): merts_u[n] = merts_u[n-1] + mobs_u[n]
    
    primes13 = list(primegen(isqrt(x//u) + 1))
    
    # Here beginneth the S1 phase.
    
    S1 = 0
    # We will sieve the Mertens function in blocks of size u.
    lo = isqrt(x//u)
    hi = lo + u
    lastM = merts_u[lo]
    
    # We need to sieve Mertens up to the maximum value of x/mn that gets passed into it.
    # This means that we need to find the minimum value of mn in the sum.
    # For any m, the minimum value of n is (u//m) + 1.
    min_mn = min(m * ((u//m)+1) for m in range(1, u+1))
    max_xmn = x // min_mn
    
    # m must be strictly greater than this, and this bound does not vary with the sieving iteration.
    global_min_m = max(0, u**2//x)   # This bound becomes nontrivial when c > sqrt(x) / log(log(x))^2.
    
    isqrtxm = {m:isqrt(x//m) for m in range(1, u+1)}
    
    while lo <= max_xmn:
        merts_lo = mertensblock(lo, hi+1, lastM, primes13)
        
        # TODO: This implementation proceeds by, within each sieving block, iterating over m in an outer loop and then
        # iterating over n in an inner one.  Would it be better to iterate over n in the outer loop and m in the inner?
        """
        Now we need to find all pairs (m,n) with 1 <= m <= u and u/m < n <= sqrt(x/m) such that x/mn is in [lo, hi),
        and for each such term, add mu(m) * Mertens(x/mn) to S1.
        
        The inequalities that characterize the valid (m,n) pairs are:
        
        1.  u/m < n
        2.  n <= sqrt(x/m)
        3.  lo <= x/mn
        4.  x/mn < hi
        5.  1 <= m
        6.  m <= u
        
        What is the range of m such that there exists an n in u/m < n <= sqrt(x/m) such that lo <= x/mn < hi?
        
        For a given m, n is constrained by:
        
        1.  u/m < n
        2.  n^2 <= x / m
        3.  n <= x / (m*lo)
        4.  x / (m*hi) < n
        
        Additionally, m is constrained by
        
        5.  1 <= m
        6.  m <= u
        
        We therefore have three lower bounds (1,4) on n and three upper bounds (2,3).
        
        (1) & (2) imply      u^2 < x m      u^2 / x < m
        (1) & (3) imply   u * lo < x        This does not constrain m, but its failure is a signal that the S1 phase is done.
        (4) & (2) imply        x < m hi^2   x / hi^2 < m
        (4) & (3) imply       lo < hi       This is always true.
        
        (1) & (2) is trivially true for small c, but may fail for larger c.  This manifests as the "global_min_m" variable.
        (4) & (2) provides a local minimum value for m; "local" means that it is specific to this sieving block.
        
        For a given m, the range of admissible n-values is bounded by (2) and (4):
        
        x / (m*hi) < n   and   n^2 <= x / m
        
        If we are to have our outer loop be m and the inner loop be n, then we will be calculating many square roots.
        However, the range of admissible m-values for the whole S1 phase is 1 <= m <= u.
        We can therefore store a cache of isqrt(x//m) values for all m for only a constant factor penalty in the memory usage.
        In the S2 phase, we will need to calculate these again, so there are further benefits to be had in doing so.
        """
        
        local_min_m = x // hi**2
        min_m = max(local_min_m, global_min_m) + 1
        
        for m in range(min_m, u+1):
            min_n = max(1, x//(m*hi) + 1, (u//m) + 1)   # n >= this
            max_n = min(isqrtxm[m], x//(m*lo))          # n <= this
            for n in range(min_n, max_n+1):
                xmn = x // (m*n)
                if lo <= xmn < hi:
                    S1 += mobs_u[m] * merts_lo[xmn-lo]
        
        lo, hi = hi, hi + u
        lastM = merts_lo[u]
    
    # Here endeth the S1 phase.
    # Here beginneth the S2 phase.
    
    S2 = 0
    M = 0
    for (k,mu) in enumerate(mobiussieve(isqrt(x)+1), start=1):
        M += mu
        innersum = 0
        for m in range(1, min(u, x//(k*k))+1):
            # l is the number of integers n in the interval (sqrt(y), y] such that y // n == k.
            # These are the n such that k <= x/(mn) < k+1, or equivalently, x / ((k+1)*m) < n <= x / (m*k).
            lo1 = isqrtxm[m] + 1
            hi1 = x // m
            lo2 = x // (m * (k+1)) + 1
            hi2 = x // (m * k)
            lo = max(lo1, lo2)
            hi = min(hi1, hi2)
            l = hi - lo + 1
            if l < 0: l = 0
            innersum += mobs_u[m] * l
        S2 += M * innersum
    
    # Here endeth the S2 phase.
    
    return merts_u[u] - S1 - S2

from sys import argv
print(mertens_segmented(int(argv[1])))
