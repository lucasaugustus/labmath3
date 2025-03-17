#! /usr/bin/env python3

from sys import argv
from time import time
from math import log10
from labmath3 import *
from mertens import mertens

def totientsum0(x): return sum(totientsieve(x+1))

def totientsum1(n):
    """
    This algorithm is derived by using the Dirichlet hyperbola method on phi = Id * mu.
    The time complexity is O(n^(3/4))-ish: This is due to our use of the Deleglise-Rivat algorithm for computing the
    Mertens function; its O(n^(2/3)) time-complexity makes the optimal choice of parameter a O(n^(3/4)).
    The overall space complexity is O(n^(3/8))-ish, due to the segmented Mobius sieve in stage X.
    Space usage from the Mertens calls is O(n^(1/3))-ish.
    
    Using the Helfgott-Thompson algorithm for the Mertens calls would bring the time complexity down to O(n^(5/7)),
    and the space complexity would be brought down to O(n^(5/14)) == O(n^(0.3571428...)).
    The space complexity from the Mertens calls would then be O(n^0.3).
    """
    if n < 3: return 0 if n < 0 else (0, 1, 2)[n]
    a = introot(n**3, 4)
    b = n // a
    Z = mertens(a) * (b * (b+1) // 2)
    Y = sum(y * mertens(n//y) for y in range(1, b+1))
    X = sum(mu * ((n//x) * ((n//x)+1) // 2) for (x, mu) in enumerate(mobiussieve(a+1), start=1))
    return X + Y - Z

def totientsum2(n):
    """
    phi = Id * mu, so totientsum(n) == sum(Id(x) * mu(y)), where the sum ranges over all (x,y) such x and y are integers
    and 1 <= x and 1 <= y and xy <= n:
    totientsum(n) == sum(sum(Id(x) * mu(y) for y in range(1, n//x+1)) for x in range(1, n+1)).
    Therefore totientsum(n) == sum(d * mertens(n//d) for d in range(1, n+1)).
    We split the sum into two segments:
    sum(d * mertens(n//d) for d in range(1, a+1)) + sum(d * mertens(n//d) for d in range(a+1, n+1)).
    For the first segment, no argument of mertens will be used more than once, and these arguments will be on the large side.
    We compute this sum directly as formulated, and use mertens().
    For the second segment, many d-values will produce the same n//d-value.  We will compute mertens(n//d) once for each such
    n//d-value, and then find all d-values that yield that n//d-value.  Their collective contribution can be easily computed.
    Furthermore, these n//d-values will go right down to 1, so we will compute these by sieving.
    
    The time complexity is O(n^(3/4))-ish.
    The space complexity of the high-Mertens-argument phase is O(n^(1/3))-ish.
    The space complexity of the  low-Mertens-argument phase is O(n^(3/8))-ish.
    """
    if n < 10: return 0 if n < 0 else (0, 1, 2, 4, 6, 10, 12, 18, 22, 28)[n]
    
    #split = isqrt(n)    # TODO: Optimize.
    split = introot(n,4)
    
    answer = 0
    for d in range(1, split+1):
        Mnd = mertens(n//d)
        answer += d * Mnd
    
    # If there are any further d-values such that n//d == n//split, then find them and amalgamate them.
    d = split + 1
    while n // d == n // split:
        answer += d * Mnd
        d += 1
        print(d)
    
    # We now know that n//d and below have not had their Mertens contributions accounted for yet.
    dmin = d
    #"""
    ndmax = n // dmin
    M = 0
    for (nd,mu) in enumerate(mobiussieve(ndmax+1), start=1):
        M += mu
        #assert M == mertens(nd)
        # Let y = nd.
        # Now we must find all d such that n//d = y.
        # They are those d such that y <= n/d < y+1
        #                        1 / y >= d/n > 1 / (y + 1)
        #                        n / y >= d   > n / (y + 1)
        # At the high end, we need integers <= n / y.        In terms of floor division, this becomes <= n // y.
        # At the low  end, we need integers >  n / (y + 1).  In terms of floor division, this becomes >  n // (y + 1).
        t = n // nd
        b = n // (nd + 1)
        # So we need to add to answer d * M for all b < d <= t.
        answer += M * ((t * (t+1) - b * (b+1)) // 2)
    
    return answer

def totientsum3(N, bcache=[], rcache={}):
    if N < 10: return 0 if N < 0 else (0, 1, 2, 4, 6, 10, 12, 18, 22, 28)[N]
    if N in rcache: return rcache[N]
    if len(bcache) == 0:
        k = introot(int(N/log(log(N)))**2, 3)
        bcache = [0] * (k+1)
        T = 0
        for (x,t) in enumerate(totientsieve(k+1), start=1):
            T += t
            bcache[x] = T
    if N <= len(bcache): return bcache[N]
    answer = N * (N+1) // 2
    for k in range(1, isqrt(N)+1):
        if k != 1:      answer -= totientsum3(N//k, bcache=bcache, rcache=rcache)
        if k != N // k: answer -= ((N//k) - (N//(k+1))) * bcache[k]
    rcache[N] = answer
    return answer

def totientsum4(n):
    z = time()
    HI = introot(n**2, 3)
    totsums = [0] * HI
    T = 0
    for (x,t) in enumerate(totientsieve(HI), start=1):
        T += t
        totsums[x] = T
    print(time() - z)
    big = [0] * (n // HI + 2)
    for i in range(n // HI + 1, 0, -1):
        mx = n // i
        big[i] = mx * (mx + 1) // 2
        fac = 2
        while fac <= mx:
            quo = mx // fac
            nex = mx // quo + 1
            big[i] -= (nex - fac) * (totsums[quo] if quo < HI else big[i * fac])
            fac = nex
    
    return big[1]







def totientsum5(x):
    
    z = time()
    
    # Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    # and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    xr = isqrt(x)
    L = 2 * xr
    if xr == x // xr: L -= 1
    M = [0] * L
    # M is a "floor-indexed array".  It stores values of the Mertens function.
    # In the first half, M[n] == Mertens(n + 1).  In the second half, M[-(x//n)] == Mertens(n).
    # getting: M[v]
    # 0 if v <= 0 else (M[v-1] if v <= xr else M[-(x//v)])
    # setting: M[v] = z
    # M[(v-1) if v <= xr else -(x//v)] = z
    y = introot(int(x * 1.0)**2, 3)                                                      # TODO: The 1.0 is a tunable parameter.
    #print(y)
    # We will compute the Mertens function by sieving up to y.
    # We do not need to sieve all the way up to y; we only need to sieve up to the last M-key <= y.
    # We can therefore save a tiny amount of time by reducing y to this point.
    #y = max((x//n) for n in range(xr - (xr == x//xr), 0, -1) if x//n <= y)
    #for n in range(1, xr - (xr == x//xr) + 1):
    #    if x // n <= y: break
    #y = x // n
    # TODO: Figure out a better way of computing that reduced y-value.
    #print(y)
    #print(time() - z)
    mobs = [0] * (xr+1)
    mert = 0
    # We need to fill M with a bunch of Mertens values.
    # First, we sieve the Mobius function up to y.
    # Along the way, we compute the corresponding Mertens values and store those that go in M.
    
    Mkeygen = ((x//n) for n in range(xr - (xr == x//xr), 0, -1))
    nextMkey = next(Mkeygen)    # This goes all the way up to x; we do not need to worry about running out in this loop.
    for (k, mu) in enumerate(mobiussieve(y+1), start=1):
        mert += mu
        
        if k <= xr:
            mobs[k] = mu
            M[k-1] = mert
        
        elif k == nextMkey:
            M[-(x//k)] = mert
            nextMkey = next(Mkeygen)
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to xr stored in mobs, and some Mertens values up to y
    # stored in M, we compute the rest of the needed Mertens values up to x with the formula
    # M(v) == 1 - v - sum(mu(n) * (v//n) + M(v//n)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= n <= sqrt(v).
    for v in ((x//n) for n in range(xr-1, 0, -1)):
        if v <= y: continue
        Mv = 1 - v
        vr = isqrt(v)
        for i in range(2, vr+1):
            vi = v // i
            Mv -= mobs[i] * vi
            # We need to extract Mertens(vi) from M, and then subtract it from Mv.  The general formula for this is
            #     Mv -= 0 if vi <= 0 else (M[vi-1] if vi <= xr else M[-(x//vi)])
            # In this case, however, we have vi = v//i, and i <= sqrt(v), so v//i != 0.  We can therefore use
            #     Mv -= M[vi-1] if vi <= xr else M[-(x//vi)]
            Mv -= M[vi-1] if vi <= xr else M[-(x//vi)]
        # Now we need to extract Mertens(sqrt(v)) from M, multiply it by vr, and add it to Mv.  The general formula for this is
        #     Mv += (0 if vr <= 0 else (M[vr-1] if vr <= xr else M[-(x//vr)])) * vr
        # But vr can never be 0, so we can therefore use
        #     Mv += (M[vr-1] if vr <= xr else M[-(x//vr)]) * vr
        # Furthermore, v <= x, so vr <= xr, so we can use
        #     Mv += M[vr-1] * vr
        Mv += M[vr-1] * vr
        # We now have Mv = Mertens(v).  We need to store it in M.  The general formula for this is
        #     M[(v-1) if v <= xr else -(x//v)] = Mv
        # In this case, we have v > y, and y > xr, so we can use
        #     M[-(x//v)] = Mv
        M[-(x//v)] = Mv
    
    print("%f" % (time() - z))
    z = time()
    
    # Now we can compute the totient sum.  We use the formula
    # totientsum(n) == 1/2 * sum(mu(k) * (n//k) * (1 + n//k)), where 1 <= k <= n.
    # We exploit the fact that n//k takes many repeated values when sqrt(n) <= k <= n.
    result = 0
    for n in range(1, xr+1):
        v = x // n
        result += mobs[n] * (v * (v+1) // 2)
        # We need to extract Mertens(v)), multiply it by n, and add it to the result.  The general formula for this is
        #     result += n * (0 if v <= 0 else (M[v-1] if v <= xr else M[-(x//v)]))
        # In this case, v > xr, so we can use
        #     result += n * M[-(x//v)]
        result += n * M[-(x//v)]
    
    print("%f" % (time() - z))
    
    return result - (xr * (xr+1) // 2) * M[xr-1]








def totientsum6(x):
    
    z = time()
    
    # Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    # and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    xr = isqrt(x)
    M     = [0] * (   xr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (x//xr + 1)  # Mover[x//n] will store Mertens(n) for large n.
    y = introot(int(x * 1.0)**2, 3)                                        # TODO: The 1.0 is a tunable parameter.
    #print(y)
    mobs = [0] * (xr+1)
    mert = 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to y.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    n = xr - (xr == x//xr)
    nextMkey = x // n
    for (k, mu) in enumerate(mobiussieve(y+1), start=1):
        mert += mu
        
        if k <= xr:
            mobs[k] = mu
            M[k] = mert
        
        elif k == nextMkey:
            Mover[x//k] = mert
            n -= 1
            nextMkey = x // n
    
    Mover[x//xr] = M[xr]
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to xr stored in mobs, and some Mertens values up to y
    # stored in M and Mover, we compute the rest of the needed Mertens values up to x with the formula
    # M(v) == 1 - v - sum(mu(n) * (v//n) + M(v//n)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= n <= sqrt(v).
    
    for v in ((x//n) for n in range(xr-1, 0, -1)):
        if v <= y: continue
        Mv = 1 - v
        vr = isqrt(v)
        for i in range(2, vr+1):
            vi = v // i
            Mv -= mobs[i] * vi
            Mv -= M[vi] if vi <= xr else Mover[x//vi]
        Mv += M[vr] * vr
        # Mv is now Mertens(v).
        Mover[x//v] = Mv
    
    print("%f" % (time() - z))
    z = time()
    
    # Now we can compute the totient sum.  We use the formula
    # totientsum(n) == 1/2 * sum(mu(k) * (n//k) * (1 + n//k)), where 1 <= k <= n.
    # We exploit the fact that n//k takes many repeated values when sqrt(n) <= k <= n.
    
    result = -M[xr] * (xr * (xr+1) // 2)
    for n in range(1, xr+1):
        v = x // n
        result += mobs[n] * (v * (v+1) // 2)
        result += n * Mover[x//v]
    
    print("%f" % (time() - z))
    
    return result







def totientsum7(x):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    The time  complexity is TBD; allegedly, it is O(n^(2/3))-ish.
    The space compelxity is O(n^(1/2))-ish, dominated by the arrays that store Mobius and Mertens values.
    """         # TODO: What is the time complexity?  Can the space complexity be brought down?
    
    z = time()
    
    xr = isqrt(x)
    M     = [0] * (   xr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (x//xr + 1)  # Mover[x//n] will store Mertens(n) for large n.
    y = introot(int(x * 1.0)**2, 3)                 # TODO: The 1.0 is a tunable parameter.  Also, consider logarithmic factors.
    #print(y)
    mobs = [0] * (xr+1)
    mert = 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to y.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # We also need to store the Mobius values up to xr.
    
    n = xr - (xr == x//xr)
    nextMkey = x // n
    for (k, mu) in enumerate(mobiussieve(y+1), start=1):
        mert += mu
        
        if k <= xr:
            mobs[k] = mu
            M[k] = mert
        
        elif k == nextMkey:
            Mover[x//k] = mert
            n -= 1
            nextMkey = x // n
            # We can early-exit this loop once we have reached the greatest x//n-value <= y.
            if nextMkey > y: break
    
    Mover[x//xr] = M[xr]
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to xr stored in mobs, and some Mertens values up to y
    # stored in M and Mover, we compute the rest of the needed Mertens values up to x with the formula
    # M(v) == 1 - v - sum(mu(n) * (v//n) + M(v//n)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= n <= sqrt(v).
    
    for v in ((x//n) for n in range(xr-1, 0, -1)):
        if v <= y: continue                     # TODO: Compute the first n that gets past this point, and start the loop there.
        vr = isqrt(v)
        Mv = 1 - v + M[vr] * vr
        for i in range(2, vr+1):
            vi = v // i
            Mv -= mobs[i] * vi
            Mv -= M[vi] if vi <= xr else Mover[x//vi]
        # Mv is now Mertens(v).
        Mover[x//v] = Mv
    
    print("%f" % (time() - z))
    z = time()
    
    # Now we can compute the totient sum.  We use the formula
    # totientsum(n) == 1/2 * sum(mu(k) * (n//k) * (1 + n//k)),
    # where the sum runs over 1 <= k <= n.
    # We exploit the fact that n//k takes many repeated values when sqrt(n) <= k <= n.
    
    result = -M[xr] * (xr * (xr+1) // 2)
    for n in range(1, xr+1):
        v = x // n
        result += mobs[n] * (v * (v+1) // 2)                                                                        # (*)
        result += n * Mover[x//v]
    
    print("%f" % (time() - z))
    
    return result
    
    """
    Line (*) can be integrated into the Mobius-sieving stage.
    This would let us delete mobs when the Mover-completing stage is done.
    We would still have O(x^(1/2)) storage thanks to M, Mover, and keeping mobs until stage 2 finishes.
    """




def totientsum8(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.
    We select a parameter a, sieve the Mobius function up to a, accumulate it into the needed Mertens values,
    and store the Mertens values.  We also store the Mobius values up to Nr.  We then use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    to compute the remaining Mertens values.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2))-ish, dominated by the arrays that store Mobius and Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    print("N   :", N)
    Nr = isqrt(N)
    print("Nr  :", Nr)
    print("N/Nr:", N//Nr)
    a = introot(N**2, 3)
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    print("a   :", a)
    M     = [0] * (   Nr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (N//Nr + 1)  # Mover[N//n] will store Mertens(n) for large n.
    mobs  = [0] * (   Nr + 1)
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # We also need to store the Mobius values up to Nr.
    
    s = Nr - (Nr == N//Nr)
    Mkey1 = nextMkey = N // s
    print("1mk :", nextMkey)
    mert = 0
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            mobs[k] = mu
            M[k] = mert
            X += mobs[k] * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == N // (a+1)
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    # Furthermore, Mertens(Nr) needs to be recorded in both M and Mover,
    # and the term Nr * Mover[Nr] from Y is sometimes not caught in phase 1.
    
    Mover[N//Nr] = M[Nr]
    if N // Nr != Mkey1: Y += Nr * Mover[Nr]
    Z = M[Nr] * (Nr * (Nr + 1) // 2)
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to Nr stored in mobs, and some Mertens values up to a
    # stored in M and Mover, we compute the rest of the needed Mertens values up to N with the formula
    # M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = isqrt(v)
        Mv = 1 - v + M[vr] * vr
        for k in range(2, vr+1):
            vk = v // k
            Mv -= mobs[k] * vk
            Mv -= M[vk] if vk <= Nr else Mover[k*t] # Mover[N//vk]
        # Mv is now Mertens(v).
        Mover[t] = Mv
        Y += t * Mv
    
    """
    For each (k,t) pair, with 1 <= t <= phase2start and 2 <= k <= isqrt(N//t),
    phase 2 subtracts mobs[k] * (N//t//k) from Mover[t].
    The maximum k happens at the minimum t.
    The minimum t is 1, so the maximum k is isqrt(N).
    For each k, the range of t-values that touch it is
    
    k <= isqrt(N//t)
    k < sqrt(N//t)
    k < sqrt(N/t)
    k^2 < N/t
    t < N/k^2
    t <= N // k^2
    """
    
    print("%f" % (time() - z))
    
    return X + Y - Z









def totientsum9(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.
    We select a parameter a, sieve the Mobius function up to a, accumulate it into the needed Mertens values,
    and store the Mertens values.  We also store the Mobius values up to Nr.  We then use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    to compute the remaining Mertens values.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    print("N   :", N)
    print("l10 :", log10(N))
    Nr = isqrt(N)
    print("Nr  :", Nr)
    print("N/Nr:", N//Nr)
    print("N23 :", introot(N**2, 3))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    print("a   :", a)
    M     = [0] * (   Nr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (N//Nr + 1)  # Mover[N//n] will store Mertens(n) for large n.
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # We also need to store the Mobius values up to Nr.
    
    s = Nr - (Nr == N//Nr)
    Mkey1 = nextMkey = N // s
    print("1mk :", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    mobsieve = mobiussieve(a+1)
    # We unroll the first iteration of the phase 1 loop,
    # so that the bit of phase 2 that happens in phase 1 does not have to have an "if k > 1" guarding it:
    mu = next(mobsieve)
    mert = 1
    M[1] = mert
    X += N * (N+1) // 2
    for (k, mu) in enumerate(mobsieve, start=2):
        mert += mu
        v = N // k
        
        if k <= Nr:
            for t in range(1, min(v//k, Na1) + 1):
                # We do some of phase 2's work here so that we do not have to store the Mobius values.
                Mover[t] -= mu * (v//t)
            M[k] = mert
            X += mu * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == N // (a+1)
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    # Furthermore, Mertens(Nr) needs to be recorded in both M and Mover,
    # and the term Nr * Mover[Nr] from Y is sometimes not caught in phase 1.
    
    Mover[N//Nr] = M[Nr]
    if N // Nr != Mkey1: Y += Nr * Mover[Nr]
    Z = M[Nr] * (Nr * (Nr + 1) // 2)
    
    print("%f" % (time() - z))
    z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = isqrt(v)
        Mv = 1 - v + M[vr] * vr
        for k in range(2, vr+1):
            vk = v // k
            #Mv -= mobs[k] * vk     # This bit is handled in phase 1.
            Mv -= M[vk] if vk <= Nr else Mover[k*t] # Mover[N//vk]
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    print("%f" % (time() - z))
    
    return X + Y - Z











def totientsum10(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.
    We select a parameter a, sieve the Mobius function up to a, accumulate it into the needed Mertens values,
    and store the Mertens values.  We also store the Mobius values up to Nr.  We then use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    to compute the remaining Mertens values.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    print("           N:", N)
    print("    log10(N):", log10(N))
    Nr = isqrt(N)
    print("    isqrt(N):", Nr)
    print(" N//isqrt(N):", N//Nr)
    print("int(N^(2/3)):", introot(N**2, 3))
    print(" log(log(N)):", log(log(N)))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    print("           a:", a)
    M     = [0] * (   Nr + 1)  # For small n, Mertens(n) will be stored as M    [   n].
    Mover = [0] * (N//Nr + 1)  # For large n. Mertens(n) will be stored as Mover[N//n].
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    s = Nr - (Nr == N//Nr)
    Mkey1 = nextMkey = N // s
    print(" Mover start:", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    mobsieve = mobiussieve(a+1)
    # We unroll the first iteration of the phase 1 loop,
    # so that the bit of phase 2 that happens in phase 1 does not have to have an "if k > 1" guarding it:
    mu = next(mobsieve)
    mert = 1
    M[1] = mert
    X += N * (N+1) // 2
    for (k, mu) in enumerate(mobsieve, start=2):
        mert += mu
        v = N // k
        
        if k <= Nr:
            
            # This next line is a phase-2 bit, but doing it here lets us avoid storing an array of Mobius values.
            for t in range(1, min(v//k, Na1) + 1): Mover[t] -= mu * (v//t)
            
            # This next line is a phase-2 bit, but doing it here lets us avoid storing Mertens(n) for n <= sqrt(N).
            for t in range(N//(k+1)**2 + 1, min(Na1, N//k**2) + 1): Mover[t] += 1 - (N//t) + mert * k
                
            M[k] = mert
            X += mu * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == Na1
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    # Furthermore, Mertens(Nr) needs to be recorded in both M and Mover,
    # and the term Nr * Mover[Nr] from Y is sometimes not caught in phase 1.
    
    Mover[N//Nr] = M[Nr]
    if N // Nr != Mkey1: Y += Nr * Mover[Nr]
    Z = M[Nr] * (Nr * (Nr + 1) // 2)
    
    print("%f" % (time() - z))
    z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = isqrt(v)
        Mv = 0#1 - v + M[vr] * vr   # This bit is handled in phase 1.
        for k in range(2, vr+1):
            vk = v // k
            #Mv -= mobs[k] * vk     # This bit is handled in phase 1.
            Mv -= M[vk] if vk <= Nr else Mover[k*t] # Mover[N//vk]
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    print("%f" % (time() - z))
    
    return X + Y - Z









def totientsum11(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.  Note that we need only O(sqrt(n)) of those:
    we need Mertens(k) and Mertens(N/k) for 1 <= k <= Nr.  To compute the low-argument values, we sieve the Mobius function
    and accumulate the results into an array M.  For the high-argument values, we use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    
    For Mertens(k) where Nr <= k < a, for some suitable parameter a, it is more efficient to continue the sieve than to use
    the formula.
    
    Using the formula as-is calls for storing the Mobius values in their own array, which uses O(sqrt(N)) space.
    This can be avoided by computing mu(n) == M(n) - M(n-1), but we instead move the relevant terms into phase 1.
    
    We can also get away with not storing the low-argument Mertens values by moving their terms into phase 1 as well.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    print("           N:", N)
    print("    log10(N):", log10(N))
    Nr = isqrt(N)
    print("    isqrt(N):", Nr)
    print(" N//isqrt(N):", N//Nr)
    print("int(N^(2/3)):", introot(N**2, 3))
    print(" log(log(N)):", log(log(N)))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    print("           a:", a)
    M     = [0] * (   Nr + 1)  # For small n, Mertens(n) will be stored as M    [   n].
    Mover = [0] * (N//Nr + 1)  # For large n. Mertens(n) will be stored as Mover[N//n].
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    s = Nr - (Nr == N//Nr)
    Mkey1 = nextMkey = N // s
    print(" Mover start:", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            
            M[k] = mert
            X += mu * (v * (v+1) // 2)
            
            # The rest of this if-true-block morally belongs in phase 2,
            # but doing it here lets us avoid storing an array of Mobius values.
            
            if k > 1:
                for t in range(1, min(v//k, Na1) + 1):
                    Mover[t] -= mu * (v//t)
            
            for t in range(N//(k+1)**2 + 1, min(Na1, N//k**2) + 1):
                Mover[t] += 1 - (N//t) + mert * k
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == Na1
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    # Furthermore, Mertens(Nr) needs to be recorded in both M and Mover,
    # and the term Nr * Mover[Nr] from Y is sometimes not caught in phase 1.
    
    Mover[N//Nr] = M[Nr]
    if N // Nr != Mkey1: Y += Nr * Mover[Nr]
    Z = M[Nr] * (Nr * (Nr + 1) // 2)
    
    print("%f" % (time() - z))
    z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = isqrt(v)
        Mv = 0
        
        #Mv += 1 - v + M[vr] * vr   # This bit is handled in phase 1.
        
        #for k in range(2, vr+1):   # This bit is handled in phase 1.
        #    vk = v // k
        #    Mv -= mobs[k] * vk
        
        for l in range(2, vr+1):
            k = v // l
            if k > Nr: Mv -= Mover[l*t]     # Mover[N//k]
            else: Mv -= M[k]                # TODO: Put this line in phase 1.
        
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    print("%f" % (time() - z))
    
    return X + Y - Z









def totientsum12(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.  Note that we need only O(sqrt(n)) of those:
    we need Mertens(k) and Mertens(N/k) for 1 <= k <= Nr.  To compute the low-argument values, we sieve the Mobius function
    and accumulate the results into an array M.  For the high-argument values, we use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    
    For Mertens(k) where Nr <= k < a, for some suitable parameter a, it is more efficient to continue the sieve than to use
    the formula.
    
    Using the formula as-is calls for storing the Mobius values in their own array, which uses O(sqrt(N)) space.
    This can be avoided by computing mu(n) == M(n) - M(n-1), but we instead move the relevant terms into phase 1.
    
    We can also get away with not storing the low-argument Mertens values by moving their terms into phase 1 as well.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    print("           N:", N)
    print("    log10(N):", log10(N))
    Nr = isqrt(N)
    print("    isqrt(N):", Nr)
    print(" N//isqrt(N):", N//Nr)
    print("int(N^(2/3)):", introot(N**2, 3))
    print(" log(log(N)):", log(log(N)))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    print("           a:", a)
    Mover = [0] * (N//Nr + 1)  # For large n. Mertens(n) will be stored as Mover[N//n].
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    s = Nr - (Nr == N//Nr)
    Mkey1 = nextMkey = N // s
    print(" Mover start:", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    
    sqrtN = [0] + [isqrt(N//t) for t in range(1, Na1+1)]
    
    MertensBlock = []
    MertensBlockStart = 1
    MertensBlockSize = Na1  # TODO: Optimize.
    
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            
            #M[k] = mert
            X += mu * (v * (v+1) // 2)
            
            # The rest of this if-true-block morally belongs in phase 2,
            # but doing it here lets us avoid storing an array of Mobius values.
            
            if k > 1:
                for t in range(1, min(v//k, Na1) + 1):
                    Mover[t] -= mu * (v//t)
            
            for t in range(N//(k+1)**2 + 1, min(Na1, N//k**2) + 1):
                Mover[t] += 1 - (N//t) + mert * k
            
            # This is the "sum(M(v//k), 2 <= k <= sqrt(v))" part of the formula for M(v).
            # For each 1 <= k <= Nr, we need to find all pairs (t,l) such that
            # 1 <= t <= Na1    and    2 <= l <= isqrt(N//t)    and    k == N // (t*l).
            # Doing this one k at a time takes O(N^(1/3)) time per k, which makes the whole algorithm O(N^(5/6))-ish.
            # To avoid breaking the clock, we accumulate a block of consecutive Mertens values and process them all at once.
            # To avoid breaking the target memory usage of O(N^(1/3))-ish, we use blocks of that size.
            # TODO: Rewrite this bit to do less (re)allocation of MertensBlock.
            MertensBlock.append(mert)
            if len(MertensBlock) >= MertensBlockSize or k == Nr:
                if k == Nr:
                    Mover[N//Nr] = mert
                    Z = mert * (Nr * (Nr + 1) // 2)
                
                for t in range(1, Na1 + 1):
                    A = MertensBlockStart
                    B = MertensBlockStart + len(MertensBlock)
                    lmin = max(1, N // (B*t))
                    #lmax = min(isqrt(N//t), N // (A*t))
                    lmax = min(sqrtN[t], N // (A*t))
                    for l in range(lmin+1, lmax+1):
                        k = N // (t*l)
                        if A <= k < B:
                            Mover[t] -= MertensBlock[k - MertensBlockStart]
                MertensBlockStart += len(MertensBlock)
                MertensBlock = []
                
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == Na1
    
    # The X- and Z-formulas are now fully evaluated.
    
    # The term Nr * Mover[Nr] from Y is sometimes not caught in phase 1.
    if N // Nr != Mkey1: Y += Nr * Mover[Nr]
    
    print("%f" % (time() - z))
    z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = sqrtN[t] #isqrt(v)
        Mv = 0
        
        #Mv += 1 - v + M[vr] * vr   # This bit is handled in phase 1.
        
        #for k in range(2, vr+1):   # This bit is handled in phase 1.
        #    vk = v // k
        #    Mv -= mobs[k] * vk
        
        for l in range(2, vr+1):
            k = v // l
            if k > Nr: Mv -= Mover[l*t]     # Mover[N//k]   # TODO: Put this bit in phase 1.
            #else: Mv -= M[k]                # This bit is handled in phase 1.
        
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    print("%f" % (time() - z))
    
    return X + Y - Z









def totientsum13(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.
    
    Mertens(n) gets computed for n in three intervals: 1 <= n <= Nr, Nr < n < a, and a <= n <= N.
    We call these the low-argument, medium-argument, and high-argument intervals, respectively.
    
    Note that we need only O(sqrt(n)) Mertens values: we need Mertens(i) and Mertens(N/i) for 1 <= i <= Nr.
    
    To compute the low-argument values, we sieve the Mobius function and accumulate the results into an array M.
    To compute the medium-argument values, we continue the sieve, but only store those Mertens values whose arguments are of
    the form N/i for some integer i.
    For the high-argument values, we use the formula
        M(j) == 1 - j + isqrt(j) * M(sqrt(j)) - sum(mu(i) * (j//i) + M(j//i), 2 <= i <= sqrt(j))
    The medium- and high-argument Mertens values get stored in an array Mover, in which Mertens(n) is stored as Mover[N//n].
    
    The basic way to proceed is to  initialize at the start three arrays: one for Mobius values (which are only needed up to
    argument Nr), one for low-argument Mertens values, and one for medium- and high-argument Mertens values.  Each array stores
    about sqrt(N) integers.  Once all the Mertens values are computed, we can then evaluate the X-, Y-, and Z-formulas.
    
    The first modification to this procedure is to evaluate X while we sieve: we initialize X = 0 at the start of the procedure,
    and then as soon as mu(x) is computed, we add mu(x) * binomial(N//x + 1, 2) to X until all terms of the formula are done.
    
    The second modification is to evaluate Z once the sieve reaches index Nr.
    
    At this point, we still need to store the Mobius values for use in evaluating Y: for each j, the formula for Mertens(j)
    requires mu(i) for all 2 <= i <= sqrt(j).  This can be handled during the low-argument sieving phase by, once the sieve has
    produced mu(i), subtracting mu(i) * ((N//i)//t) from Mover[t] for each high-argument t.
    
    At this point, we no longer need to store the array of Mobius values.  We still have both of the arrays of Mertens values.
    
    We can also get away with not storing the low-argument Mertens values by handling them during the low-argument sieving phase
    as well: as soon as a low-argument Mertens value is computed by the sieve, we apply it to all high-argument Mertens values
    that require it.  For the "1 - j + isqrt(j) * M(sqrt(j))" part, this is trivial.  The "sum(M(j//i))" part requires some
    additional care; doing it naively breaks the clock by slowing the algorithm down to O(N^(5/6)), but assembling a batch of
    O(N^(1/3)) contiguous Mertens values and then processing them all at once fixes this.
    
    We have now brought the memory requirements for the low-argument phase down to O(N^(1/3)).  It remains to reduce the memory
    requirements for the medium- and high-argument phases.
    
     applying them to the high-argument Mertens values
    that require them, as soon as they are computed.  
     moving their terms into phase 1 as well.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    if verbose: print("           N:", N)
    if verbose: print("      log(N):", log(N))
    if verbose: print("     log2(N):", log2(N))
    if verbose: print("    log10(N):", log10(N))
    Nr = isqrt(N)
    if verbose: print("    isqrt(N):", Nr)
    if verbose: print(" N//isqrt(N):", N//Nr)
    if verbose: print("int(N^(2/3)):", introot(N**2, 3))
    if verbose: print(" log(log(N)):", log(log(N)))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    if verbose: print("           a:", a)
    Mover = [0] * (N//Nr + 1)  # For large n. Mertens(n) will be stored as Mover[N//n].
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    s = Nr - (Nr == N//Nr)
    Mkey1 = nextMkey = N // s
    if verbose: print(" Mover start:", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    
    sqrtN = [0] + [isqrt(N//t) for t in range(1, Na1+1)]
    
    MertensBlock = []
    MertensBlockStart = 1
    MertensBlockSize = Na1  # TODO: Optimize.
    
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            
            #M[k] = mert
            X += mu * (v * (v+1) // 2)
            
            # This bit morally belongs in phase 2, but doing it here lets us avoid storing an array of Mobius values.
            if k > 1:
                for t in range(1, min(v//k, Na1) + 1):
                    Mover[t] -= mu * (v//t)
            
            # This bit also morally belongs in phase 2, but doing it here
            # helps us avoid storing the array of low-argument Mertens values.
            for t in range(N//(k+1)**2 + 1, min(Na1, N//k**2) + 1):
                Mover[t] += 1 - (N//t) + mert * k
            
            # This bit also morally belongs in phase 2, but doing it here
            # does the rest of the work to avoid storing the array of low-argument Mertens values.
            # This is the "sum(M(j//i), 2 <= i <= sqrt(j))" part of the formula for M(j), for j//i <= Nr.
            # For each 1 <= k <= Nr, we need to find all pairs (t,l) such that
            # 1 <= t <= Na1    and    2 <= l <= isqrt(N//t)    and    k == N // (t*l).
            # Doing this one k at a time takes O(N^(1/3)) time per k, which makes the whole algorithm O(N^(5/6))-ish.
            # To avoid breaking the clock, we accumulate a block of consecutive Mertens values and process them all at once.
            # To avoid breaking the target memory usage of O(N^(1/3))-ish, we use blocks of that size.
            # TODO: Rewrite this bit to do less (re)allocation of MertensBlock.
            MertensBlock.append(mert)
            if len(MertensBlock) >= MertensBlockSize or k == Nr:
                if k == Nr:
                    Mover[N//Nr] = mert
                    Z = mert * (Nr * (Nr + 1) // 2)
                
                for t in range(1, Na1 + 1):
                    A = MertensBlockStart
                    B = MertensBlockStart + len(MertensBlock)
                    lmin = max(1, N // (B*t))
                    #lmax = min(isqrt(N//t), N // (A*t))
                    lmax = min(sqrtN[t], N // (A*t))
                    for l in range(lmin+1, lmax+1):
                        Ntl = N // (t*l)
                        if A <= Ntl < B:
                            Mover[t] -= MertensBlock[Ntl - MertensBlockStart]
                MertensBlockStart += len(MertensBlock)
                MertensBlock = []
                
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == Na1
    
    # The X- and Z-formulas are now fully evaluated.
    
    # The term Nr * Mover[Nr] from Y is sometimes not caught in phase 1.
    if N // Nr != Mkey1: Y += Nr * Mover[Nr]
    
    if verbose:
        print("%f" % (time() - z))
        z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(j) == 1 - j + isqrt(j) * M(sqrt(j)) - sum(mu(i) * (j//i) + M(j//i), 2 <= i <= sqrt(j)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = sqrtN[t] # isqrt(v)
        Mv = 0
        
        #Mv += 1 - v + M[vr] * vr   # This bit is handled in phase 1.
        
        #for k in range(2, vr+1):   # This bit is handled in phase 1.
        #    vk = v // k
        #    Mv -= mobs[k] * vk
        
        for l in range(2, vr+1):
            k = v // l                      # N // (t * l)
            if k > Nr: Mv -= Mover[l*t]     # Mover[N//k]; Mertens(k)   # TODO: Put this bit in phase 1.
            """
            Mv -= Mertens(N//(l*t))
            Mover[t] -= Mertens(N//(l*t))
            k == N // (t * l)
            t * l == N // k
            t == N // (k * l)
            """
            #else: Mv -= M[k]               # This bit is handled in phase 1.
        
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    if verbose:
        print("%f" % (time() - z))
    
    return X + Y - Z









def totientsum14(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.
    
    Mertens(n) gets computed for n in three intervals: 1 <= n <= Nr, Nr < n < a, and a <= n <= N.
    We call these the low-argument, medium-argument, and high-argument intervals, respectively.
    
    Note that we need only O(sqrt(n)) Mertens values: we need Mertens(i) and Mertens(N/i) for 1 <= i <= Nr.
    
    To compute the low-argument values, we sieve the Mobius function and accumulate the results into an array M.
    To compute the medium-argument values, we continue the sieve, but only store those Mertens values whose arguments are of
    the form N/i for some integer i.
    For the high-argument values, we use the formula
        M(j) == 1 - j + isqrt(j) * M(sqrt(j)) - sum(mu(i) * (j//i) + M(j//i), 2 <= i <= sqrt(j))
    The medium- and high-argument Mertens values get stored in an array Mover, in which Mertens(n) is stored as Mover[N//n].
    
    The basic way to proceed is to  initialize at the start three arrays: one for Mobius values (which are only needed up to
    argument Nr), one for low-argument Mertens values, and one for medium- and high-argument Mertens values.  Each array stores
    about sqrt(N) integers.  Once all the Mertens values are computed, we can then evaluate the X-, Y-, and Z-formulas.
    
    The first modification to this procedure is to evaluate X while we sieve: we initialize X = 0 at the start of the procedure,
    and then as soon as mu(x) is computed, we add mu(x) * binomial(N//x + 1, 2) to X until all terms of the formula are done.
    
    The second modification is to evaluate Z once the sieve reaches index Nr.
    
    At this point, we still need to store the Mobius values for use in evaluating Y: for each j, the formula for Mertens(j)
    requires mu(i) for all 2 <= i <= sqrt(j).  This can be handled during the low-argument sieving phase by, once the sieve has
    produced mu(i), subtracting mu(i) * ((N//i)//t) from Mover[t] for each high-argument t.
    
    At this point, we no longer need to store the array of Mobius values.  We still have both of the arrays of Mertens values.
    
    We can also get away with not storing the low-argument Mertens values by handling them during the low-argument sieving phase
    as well: as soon as a low-argument Mertens value is computed by the sieve, we apply it to all high-argument Mertens values
    that require it.  For the "1 - j + isqrt(j) * M(sqrt(j))" part, this is trivial.  The "sum(M(j//i))" part requires some
    additional care; doing it naively breaks the clock by slowing the algorithm down to O(N^(5/6)), but assembling a batch of
    O(N^(1/3)) contiguous Mertens values and then processing them all at once fixes this.
    
    We have now brought the memory requirements for the low-argument phase down to O(N^(1/3)).  It remains to reduce the memory
    requirements for the medium- and high-argument phases.
    
     applying them to the high-argument Mertens values
    that require them, as soon as they are computed.  
     moving their terms into phase 1 as well.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    if verbose: print("           N:", N)
    if verbose: print("      log(N):", log(N))
    if verbose: print("     log2(N):", log2(N))
    if verbose: print("    log10(N):", log10(N))
    Nr = isqrt(N)
    if verbose: print("    isqrt(N):", Nr)
    if verbose: print(" N//isqrt(N):", N//Nr)
    if verbose: print("int(N^(2/3)):", introot(N**2, 3))
    if verbose: print(" log(log(N)):", log(log(N)))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    if verbose: print("           a:", a)
    Mover = [0] * (N//Nr + 1)  # For large n. Mertens(n) will be stored as Mover[N//n].
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    s = Nr
    Mkey1 = nextMkey = N // s
    if verbose: print(" Mover start:", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    
    sqrtN = [0] + [isqrt(N//t) for t in range(1, Na1+1)]
    
    MertensBlock = []
    MertensBlockStart = 1
    MertensBlockSize = Na1  # TODO: Optimize.
    
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            
            X += mu * (v * (v+1) // 2)
            
            # This bit morally belongs in phase 2, but doing it here lets us avoid storing an array of Mobius values.
            if k > 1:
                for t in range(1, min(v//k, Na1) + 1):
                    Mover[t] -= mu * (v//t)
            
            # This bit also morally belongs in phase 2, but doing it here
            # helps us avoid storing the array of low-argument Mertens values.
            for t in range(N//(k+1)**2 + 1, min(Na1, N//k**2) + 1):
                Mover[t] += 1 - (N//t) + mert * k
            
            # This bit also morally belongs in phase 2, but doing it here
            # does the rest of the work to avoid storing the array of low-argument Mertens values.
            # This is the "sum(M(j//i), 2 <= i <= sqrt(j))" part of the formula for M(j), for j//i <= Nr.
            # For each 1 <= k <= Nr, we need to find all pairs (t,l) such that
            # 1 <= t <= Na1    and    2 <= l <= isqrt(N//t)    and    k == N // (t*l).
            # Doing this one k at a time takes O(N^(1/3)) time per k, which makes the whole algorithm O(N^(5/6))-ish.
            # To avoid breaking the clock, we accumulate a block of consecutive Mertens values and process them all at once.
            # To avoid breaking the target memory usage of O(N^(1/3))-ish, we use blocks of that size.
            # TODO: Rewrite this bit to do less (re)allocation of MertensBlock.
            MertensBlock.append(mert)
            if len(MertensBlock) >= MertensBlockSize or k == Nr:
                if k == Nr:
                    Mover[N//Nr] = mert
                    Z = mert * (Nr * (Nr + 1) // 2)
                
                for t in range(1, Na1 + 1):
                    A = MertensBlockStart
                    B = MertensBlockStart + len(MertensBlock)
                    lmin = max(1, N // (B*t))
                    #lmax = min(isqrt(N//t), N // (A*t))
                    lmax = min(sqrtN[t], N // (A*t))
                    for l in range(lmin+1, lmax+1):
                        Ntl = N // (t*l)
                        if A <= Ntl < B:
                            Mover[t] -= MertensBlock[Ntl - MertensBlockStart]
                MertensBlockStart += len(MertensBlock)
                MertensBlock = []
                
        
        if k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == Na1
    
    # The X- and Z-formulas are now fully evaluated.
    
    if verbose:
        print("%f" % (time() - z))
        z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(j) == 1 - j + isqrt(j) * M(sqrt(j)) - sum(mu(i) * (j//i) + M(j//i), 2 <= i <= sqrt(j)).
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = sqrtN[t] # isqrt(v)
        Mv = 0
        
        #Mv += 1 - v + M[vr] * vr   # This bit is handled in phase 1.
        
        #for k in range(2, vr+1):   # This bit is handled in phase 1.
        #    vk = v // k
        #    Mv -= mobs[k] * vk
        
        for l in range(2, vr+1):
            k = v // l                      # N // (t * l)
            if k > Nr: Mv -= Mover[l*t]     # Mover[N//k]; Mertens(k)   # TODO: Put this bit in phase 1.
            #else: Mv -= M[k]               # This bit is handled in phase 1.
        
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    if verbose:
        print("%f" % (time() - z))
    
    if DEBUG:
        print(Mover)
        print([0] + [mertens(N//k) for k in range(1, N//Nr+1)])
    
    return X + Y - Z









def totientsum15(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    By using the Dirichlet hyperbola method on phi = Id * mu, we obtain
        totientsum(N) == X + Y - Z,
    where
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= Nr)
        Y == sum(y * Mertens(N//y), 1 <= y <= Nr)
        Z == Mertens(Nr) * binomial(Nr + 1, 2)
        Nr == isqrt(N)
    This calls for an efficient way to compute all those Mertens values.
    
    Mertens(n) gets computed for n in three intervals: 1 <= n <= Nr, Nr < n < a, and a <= n <= N.
    We call these the low-argument, medium-argument, and high-argument intervals, respectively.
    
    Note that we need only O(sqrt(n)) Mertens values: we need Mertens(i) and Mertens(N/i) for 1 <= i <= Nr.
    
    To compute the low-argument values, we sieve the Mobius function and accumulate the results into an array M.
    To compute the medium-argument values, we continue the sieve, but only store those Mertens values whose arguments are of
    the form N/i for some integer i.
    For the high-argument values, we use the formula
        M(j) == 1 - j + isqrt(j) * M(sqrt(j)) - sum(mu(i) * (j//i) + M(j//i), 2 <= i <= sqrt(j))
    The medium- and high-argument Mertens values get stored in an array Mover, in which Mertens(n) is stored as Mover[N//n].
    
    The basic way to proceed is to  initialize at the start three arrays: one for Mobius values (which are only needed up to
    argument Nr), one for low-argument Mertens values, and one for medium- and high-argument Mertens values.  Each array stores
    about sqrt(N) integers.  Once all the Mertens values are computed, we can then evaluate the X-, Y-, and Z-formulas.
    
    The first modification to this procedure is to evaluate X while we sieve: we initialize X = 0 at the start of the procedure,
    and then as soon as mu(x) is computed, we add mu(x) * binomial(N//x + 1, 2) to X until all terms of the formula are done.
    
    The second modification is to evaluate Z once the sieve reaches index Nr.
    
    At this point, we still need to store the Mobius values for use in evaluating Y: for each j, the formula for Mertens(j)
    requires mu(i) for all 2 <= i <= sqrt(j).  This can be handled during the low-argument sieving phase by, once the sieve has
    produced mu(i), subtracting mu(i) * ((N//i)//t) from Mover[t] for each high-argument t.
    
    At this point, we no longer need to store the array of Mobius values.  We still have both of the arrays of Mertens values.
    
    We can also get away with not storing the low-argument Mertens values by handling them during the low-argument sieving phase
    as well: as soon as a low-argument Mertens value is computed by the sieve, we apply it to all high-argument Mertens values
    that require it.  For the "1 - j + isqrt(j) * M(sqrt(j))" part, this is trivial.  The "sum(M(j//i))" part requires some
    additional care; doing it naively breaks the clock by slowing the algorithm down to O(N^(5/6)), but assembling a batch of
    O(N^(1/3)) contiguous Mertens values and then processing them all at once fixes this.
    
    We have now brought the memory requirements for the low-argument phase down to O(N^(1/3)).  It remains to reduce the memory
    requirements for the medium- and high-argument phases.
    
     applying them to the high-argument Mertens values
    that require them, as soon as they are computed.  
     moving their terms into phase 1 as well.
    
    THe optimal choice for a turns out to be about (N / log(log(n))) ^ (2/3).
    
    The time  complexity is O(N^(2/3) * log(log(N))^(1/3)).
    The space compelxity is O(N^(1/2)), dominated by the arrays that store Mertens values.
    """                                             # TODO: Can the space complexity be brought down without breaking the clock?
    
    z = time()
    
    if verbose: print("           N:", N)
    if verbose: print("      log(N):", log(N))
    if verbose: print("     log2(N):", log2(N))
    if verbose: print("    log10(N):", log10(N))
    Nr = isqrt(N)
    if verbose: print("    isqrt(N):", Nr)
    if verbose: print(" N//isqrt(N):", N//Nr)
    if verbose: print("int(N^(2/3)):", introot(N**2, 3))
    if verbose: print(" log(log(N)):", log(log(N)))
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    if verbose: print("           a:", a)
    Mover = [0] * (N//Nr + 1)  # For large n. Mertens(n) will be stored as Mover[N//n].
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    
    s = Nr
    Mkey1 = nextMkey = N // s
    if verbose: print(" Mover start:", nextMkey)
    mert = 0
    Na1 = N // (a+1)
    
    sqrtN = [0] + [isqrt(N//t) for t in range(1, Na1+1)]
    
    MertensBlock = []
    MertensBlockStart = 1
    MertensBlockSize = Na1  # TODO: Optimize.
    
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            
            X += mu * (v * (v+1) // 2)
            
            # This bit morally belongs in phase 2, but doing it here lets us avoid storing an array of Mobius values.
            if k > 1:
                for t in range(1, min(v//k, Na1) + 1):
                    Mover[t] -= mu * (v//t)
            
            # This bit also morally belongs in phase 2, but doing it here
            # helps us avoid storing the array of low-argument Mertens values.
            for t in range(N//(k+1)**2 + 1, min(Na1, N//k**2) + 1):
                Mover[t] += 1 - (N//t) + mert * k
            
            # This bit also morally belongs in phase 2, but doing it here
            # does the rest of the work to avoid storing the array of low-argument Mertens values.
            # This is the "sum(M(j//i), 2 <= i <= sqrt(j))" part of the formula for M(j), for j//i <= Nr.
            # For each 1 <= k <= Nr, we need to find all pairs (t,l) such that
            # 1 <= t <= Na1    and    2 <= l <= isqrt(N//t)    and    k == N // (t*l).
            # Doing this one k at a time takes O(N^(1/3)) time per k, which makes the whole algorithm O(N^(5/6))-ish.
            # To avoid breaking the clock, we accumulate a block of consecutive Mertens values and process them all at once.
            # To avoid breaking the target memory usage of O(N^(1/3))-ish, we use blocks of that size.
            # TODO: Rewrite this bit to do less (re)allocation of MertensBlock.
            MertensBlock.append(mert)
            if len(MertensBlock) >= MertensBlockSize or k == Nr:
                if k == Nr:
                    Mover[N//Nr] = mert
                    Z = mert * (Nr * (Nr + 1) // 2)
                
                for t in range(1, Na1 + 1):
                    A = MertensBlockStart
                    B = MertensBlockStart + len(MertensBlock)
                    lmin = max(1, N // (B*t))
                    #lmax = min(isqrt(N//t), N // (A*t))
                    lmax = min(sqrtN[t], N // (A*t))
                    for l in range(lmin+1, lmax+1):
                        Ntl = N // (t*l)
                        if A <= Ntl < B:
                            Mover[t] -= MertensBlock[Ntl - MertensBlockStart]
                MertensBlockStart += len(MertensBlock)
                MertensBlock = []
                
        
        if k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            
            
            
            
            """
            We need to find all pairs (l,t) of integers such that
            
            (1):    k == N // (l*t)         (and therefore Mover[l*t] == Mertens(k) == mert)
            (2):    1 <= t <= phase2start
            (3):    v == N // t
            (4):    vr == isqrt(v)
            (5):    2 <= l <= vr
            (6):    l*t > phase2start
            (7):    v//l > Nr
            
            For each pair, we subtract Mover[l*t] from Mover[t].
            
            (1):    k <= N / (l*t) < k + 1
            N / (t*(k+1)) < l <= N / (t*k)
            N / (k+1) < l*t <= N/k
            """
            
            for t in range(1, Na1+1):   # TODO: This loop breaks the clock.
                for l in range(N // (t*(k+1)) + 1, N // (t*k) + 1):
                    v = N // t
                    vr = sqrtN[t]   # isqrt(v)
                    if 2 <= l <= vr:
                        if Na1 < l*t:
                            if Nr < v // l:
                                Mover[t] -= Mover[l*t]
                                assert Mover[l*t] == mert
            
            
            
            
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once we have reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == Na1
    
    # The X- and Z-formulas are now fully evaluated.
    
    if verbose:
        print("%f" % (time() - z))
        z = time()
    
    # We now compute the rest of the needed Mertens values up to N with the formula
    # M(j) == 1 - j + isqrt(j) * M(sqrt(j)) - sum(mu(i) * (j//i) + M(j//i), 2 <= i <= sqrt(j)).
    
    """
    for t in range(phase2start, 0, -1): # TODO: Put this loop in phase 1.
        v = N // t
        vr = sqrtN[t] # isqrt(v)
        Mv = 0
        
        for l in range(2, vr+1):
            if l*t > phase2start:
                if v//l > Nr:
                    Mv -= Mover[l*t]
        
        Mover[t] += Mv
    #"""
    
    if verbose:
        print("%f" % (time() - z))
        z = time()
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = sqrtN[t] # isqrt(v)
        Mv = 0
        
        for l in range(2, vr+1):
            if l*t <= phase2start:
                if v//l > Nr:
                    Mv -= Mover[l*t]
        
        Mover[t] += Mv
        # Mover[t] is now Mertens(v).
        Y += t * Mover[t]
    
    if verbose:
        print("%f" % (time() - z))
    
    if DEBUG:
        print(Mover)
        print([0] + [mertens(N//k) for k in range(1, N//Nr+1)])
    
    return X + Y - Z
























methods = (#totientsum, \
           #totientsum0, \
           #totientsum1, \
           #totientsum2, \
           #totientsum3, \
           #totientsum4, \
           #totientsum5, \
           #totientsum6, \
           #totientsum7, \
           #totientsum8, \
           #totientsum9, \
           #totientsum10, \
           #totientsum11, \
           #totientsum12, \
           totientsum13, \
           totientsum14, \
           totientsum15, \
          )

if "testlow" in argv:
    DEBUG = False
    verbose = False
    real_s = 0
    for n in range(1, int(argv[2])):
        t = totient(n)
        real_s += t
        if t < 5: continue
        test_s = methods[-1](n)
        print('\b'*42, n, real_s, test_s, end='', flush=True)
        assert real_s == test_s
    print()
    exit()

verbose = True

if "DEBUG" in argv:
    args = [x for x in argv if x != "DEBUG"]
    DEBUG = True
    
else:
    args = argv
    DEBUG = False

numbers = (2**30, 2**33, 2**34, 2**33 * 3, 10**10)#, 10**11)
randos = [randrange(10**8, 10**10) for _ in range(5)]

for n in chain(randos, numbers) if len(args) == 1 else [int(args[1])]:
    print()
    print()
    print()
    print()
    print("N ==", n)
    print()
    print()
    answers = []
    for m in methods:
        print(m.__name__)
        print()
        z = time()
        A = m(n)
        z = time() - z
        print("\t", A)
        print("%f" % z)
        answers.append(A)
        print()
        print()

    for a in answers: print(a)
    assert len(set(answers)) == 1

