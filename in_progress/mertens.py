#! /usr/bin/env python3

from labmath3 import *

def mertens(x):
    """
    Computes the Mertens function (the partial sums of the Mobius function) using the Deleglise-Rivat algorithm.
    The time- and space-complexities are within logarithmic factors of O(x^(2/3)) and O(x^(1/3)), respectively.
    See https://projecteuclid.org/euclid.em/1047565447 for further explanation.
    
    Input: x -- an integer.
    
    Output: an integer.
    
    Examples:
    
    >>> list(map(mertens, range(22)))
    [0, 1, 0, -1, -1, -2, -1, -2, -2, -2, -1, -2, -2, -3, -2, -1, -1, -2, -2, -3, -3, -2]
    
    >>> mertens(10**10)
    -33722
    
    >>> mertens(2**32)
    1814
    """
    if x < 22: return (0, 1, 0, -1, -1, -2, -1, -2, -2, -2, -1, -2, -2, -3, -2, -1, -1, -2, -2, -3, -3, -2)[x]
    u = int((x * log(log(x))**2)**(1/3))
    primes = list(primegen(isqrt(x//u) + 1))
    mobs_u = [0] + list(mobiussieve(u+1))
    merts_u = [0] * (u+1)
    for n in range(u+1): merts_u[n] = merts_u[n-1] + mobs_u[n]
    
    # Here beginneth the S1 phase.
    
    S1 = 0
    # We will sieve the Mertens function in blocks of size u.
    lo = isqrt(x//u)
    hi = lo + u
    M_lo = merts_u[lo]
    merts_u = merts_u[u]
    
    # We need to sieve Mertens up to the maximum value of x/mn that gets passed into it.
    # This means that we need to find the minimum value of mn in the sum.
    # For any m, the minimum value of n is (u//m) + 1.
    min_mn = min(m * ((u//m)+1) for m in range(1, u+1))
    max_xmn = x // min_mn
    
    # m must be strictly greater than this, and this bound does not vary with the sieving iteration.
    global_min_m = max(0, u**2//x)   # This bound becomes nontrivial when c > sqrt(x) / log(log(x))^2.
    
    isqrtxm = [0]
    isqrtxm.extend([isqrt(x//m) for m in range(1, u+1)])
    
    while lo <= max_xmn:
        # First, we sieve a block of Mobius values in the array merts_lo, and then convert it to a block of Mertens values.
        merts_lo = [1] * (hi-lo+1)
        for p in primes:
            for n in range((-lo) %   p  , hi - lo + 1,  p ): merts_lo[n] *= -p
            for n in range((-lo) % (p*p), hi - lo + 1, p*p): merts_lo[n]  =  0
        for n in range(hi - lo + 1):
            m = merts_lo[n]
            if m == 0: continue
            if -lo-n < m < lo+n:
                if m > 0: merts_lo[n] = -1
                if m < 0: merts_lo[n] =  1
            else:
                if m > 0: merts_lo[n] =  1
                if m < 0: merts_lo[n] = -1
        # At this point, merts_lo[k] == mobius(lo+k).
        merts_lo[0] = M_lo
        for n in range(1, hi+1-lo): merts_lo[n] += merts_lo[n-1]
        # We now have merts_lo[k] == Mertens(lo+k).
        
        # TODO: This implementation proceeds by, within each sieving block, iterating over m in an outer loop and then
        # iterating over n in an inner one.  Would it be better to iterate over n in the outer loop and m in the inner?
        """
        Now we need to find all pairs (m,n) with 1 <= m <= u and u/m < n <= sqrt(x/m) such that x/mn is in [lo, hi),
        and for each such term, add mu(m) * Mertens(x/mn) to S1.
        
        The inequalities that characterize the valid (m,n) pairs are:
        
            1: u/m < n    2: n <= sqrt(x/m)    3: lo <= x/mn    4: x/mn < hi    5: 1 <= m    6: m <= u
        
        For a given m, we therefore have two lower bounds (1,4) on n and two upper bounds (2,3).
        
        (1) & (2) imply      u^2 < x m      u^2 / x < m
        (1) & (3) imply   u * lo < x        This does not constrain anything; its failure is a signal that the S1 phase is done.
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
            subtotal = 0
            for n in range(min_n, max_n+1):
                xmn = x // (m*n)
                if lo <= xmn < hi:
                    subtotal += merts_lo[xmn-lo]
            S1 += mobs_u[m] * subtotal
        
        lo, hi = hi, hi + u
        M_lo = merts_lo[u]
    
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
    
    return merts_u - S1 - S2

def test_mertens():
    M = 0
    for (n,m) in enumerate(mobiussieve(2**14), start=1):
        M += m
        MM = mertens(n)
        assert M == MM, (n, M, MM)
    A084237 = [1, -1, 1, 2, -23, -48, 212, 1037, 1928, -222, -33722, -87856]
    for n in range(len(A084237)):
        M = mertens(10**n)
        assert M == A084237[n], (n, M, A084237[n])
    A084236 = [1, 0, -1, -2, -1, -4, -1, -2, -1, -4, -4, 7, -19, 22, -32, 26, 14, -20, 24, -125, 257, -362,\
               228, -10, 211, -1042, 329, 330, -1703, 6222, -10374, 9569, 1814, -10339, -3421, 8435, 38176]
    for n in range(len(A084236)):
        M = mertens(2**n)
        assert M == A084236[n], (n, M, A084236[n])

#test_mertens()
from sys import argv; print(mertens(int(argv[1])))
