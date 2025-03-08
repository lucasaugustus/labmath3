#! /usr/bin/env python3

from sys import argv
from labmath3 import *
from mertens import mertens
from time import process_time, time

def totientsum0(x): return sum(totientsieve(x+1))

def totientsum1(n):
    # This is derived by using the Dirichlet hyperbola method on phi = Id * mu.
    # The time complexity is O(n^(3/4))-ish.
    # The overall space complexity is O(n^(3/8))-ish, due to the segmented Mobius sieve in stage X.
    # Space usage from the Mertens calls is O(n^(1/3))-ish.
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
    
    #print(process_time())
    
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
    
    #print(process_time())
    
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
        print(process_time())
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




def totientsum7a(x):
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
    X, Y, Z = 0, 0, 0
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to y.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # We also need to store the Mobius values up to xr.
    
    n = xr - (xr == x//xr)
    nextMkey = x // n
    for (k, mu) in enumerate(mobiussieve(y+1), start=1):
        mert += mu
        v = x // k
        
        if k <= xr:
            mobs[k] = mu
            M[k] = mert
            X += mobs[k] * (v * (v+1) // 2)                                                                        # (*)
        
        elif k == nextMkey:
            Mover[v] = mert
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
    
    Z = M[xr] * (xr * (xr+1) // 2)
    for n in range(1, xr+1):
        v = x // n
        Y += n * Mover[n]
    
    print("%f" % (time() - z))
    
    return X + Y - Z
    
    """
    Line (*) can be integrated into the Mobius-sieving stage.
    This would let us delete mobs when the Mover-completing stage is done.
    We would still have O(x^(1/2)) storage thanks to M, Mover, and keeping mobs until stage 2 finishes.
    """




def totientsum8(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    The overall method is to use the Dirichlet hyperbola method on phi = Id * mu.  This yields the formula
        totientsum(N) == X + Y - Z,
    where
        a is a selectable parameter
        b == N // a
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= a)
        Y == sum(y * Mertens(N//y), 1 <= y <= b)
        Z == Mertens(a) * binomial(b, 2)
    This requires using an efficient way to calculate all of those Mertens values.
    We sieve the Mobius function directly up to a, compute the Mertens function along the way, and store the results.
    We then use the formula
        M(v) == 1 - v - sum(mu(k) * (v//k) + M(v//k)) + isqrt(v) * M(sqrt(v)),
    where the sum runs over 2 <= k <= sqrt(v), to compute the remaining Mertens values.
    
    The time  complexity is TBD; allegedly, it is O(N^(2/3))-ish.
    The space compelxity is O(N^(1/2))-ish, dominated by the arrays that store Mobius and Mertens values.
    """                                          # TODO: What is the time complexity?  Can the space complexity be brought down?
    
    z = time()
    
    Nr = isqrt(N)
    a = introot(N**2, 3)                                                                                       # TODO: Optimize.
    X, Y, Z = 0, 0, 0
    #print(a)
    M     = [0] * (   Nr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (N//Nr + 1)  # Mover[N//n] will store Mertens(n) for large n.
    mobs  = [0] * (   Nr + 1)
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.  Those <= Nr get stored.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # As we go, we accumulate terms from the X- and Y-formulas.
    
    t = Nr - (Nr == N//Nr)
    nextMkey = N // t
    mert = 0
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            mobs[k] = mu
            M[k] = mert
            X += mu * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            t -= 1
            nextMkey = N // t
            # We can early-exit this loop once k has reached the greatest N//t-value <= a.
            if nextMkey > a:
                phase2start = t
                break
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    
    Z = M[Nr] * (Nr * (Nr+1) // 2)
    Mover[N//Nr] = M[Nr]
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to Nr stored in mobs, and some Mertens values up to a
    # stored in M and Mover, we compute the rest of the needed Mertens values with the formula
    # M(v) == 1 - v - sum(mu(k) * (v//k) + M(v//k)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= k <= sqrt(v).
    # As we go, we accumulate the remaining terms from the Y-formula.
    
    for k in range(phase2start, 0, -1):
        v = N // k
        vr = isqrt(v)
        Mv = 1 - v + M[vr] * vr
        for i in range(2, vr+1):
            vi = v // i
            Mv -= mobs[i] * vi
            Mv -= M[vi] if vi <= Nr else Mover[i*k] # Mover[N//vi]
        # Mv is now Mertens(v).
        Mover[k] = Mv
    
    print("%f" % (time() - z))
    
    for n in range(1, Nr+1):
        v = N // n
        Y += n * Mover[n]
    
    return X + Y - Z









def totientsum9(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    The overall method is to use the Dirichlet hyperbola method on phi = Id * mu.  This yields the formula
        totientsum(N) == X + Y - Z,
    where
        a is a selectable parameter
        b == N // a
        X == sum(mu(x) * binomial(N//x, 2), 1 <= x <= a)
        Y == sum(y * Mertens(N//y), 1 <= y <= b)
        Z == Mertens(a) * binomial(b, 2)
    This requires using an efficient way to calculate all of those Mertens values.
    We sieve the Mobius function directly up to a, compute the Mertens function along the way, and store the results.
    We then use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    to compute the remaining Mertens values.
    
    The time  complexity is O(N^(2/3) * log(log(N))^(-2/3)).
    The space compelxity is O(N^(1/2))-ish, dominated by the arrays that store Mobius and Mertens values.
    """    # TODO: Make the space-complexity statement more precise.  Also, can that be brought down without breaking the clock?
    
    z = time()
    
    Nr = isqrt(N)
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    #print(a)
    X, Y, Z = 0, 0, 0
    M     = [0] * (   Nr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (N//Nr + 1)  # Mover[N//n] will store Mertens(n) for large n.
    mobs  = [0] * (   Nr + 1)
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.  Those <= Nr get stored.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # As we go, we accumulate terms from the X- and Y-formulas.
    
    t = Nr - (Nr == N//Nr)
    nextMkey = N // t
    mert = 0
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            mobs[k] = mu
            M[k] = mert
            X += mu * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            #Y += v * mert
            t -= 1
            nextMkey = N // t
            # We can early-exit this loop once k has reached the greatest N//t-value <= a.
            if nextMkey > a:
                phase2start = t
                break
    
    # phase2start is the greatest integer t such that a < N // t.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == N // (a+1)
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    
    Z = M[Nr] * (Nr * (Nr+1) // 2)
    Mover[N//Nr] = M[Nr]
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to Nr stored in mobs, and some Mertens values up to a
    # stored in M and Mover, we compute the rest of the needed Mertens values with the formula
    # M(v) == 1 - v - sum(mu(k) * (v//k) + M(v//k)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= k <= sqrt(v).
    # As we go, we accumulate the remaining terms from the Y-formula.
    
    for k in range(phase2start, 0, -1):
        v = N // k
        vr = isqrt(v)
        Mv = 1 - v + M[vr] * vr
        for i in range(2, vr+1):
            vi = v // i
            Mv -= mobs[i] * vi
            Mv -= M[vi] if vi <= Nr else Mover[i*k] # Mover[N//vi]
        # Mv is now Mertens(v).
        Mover[k] = Mv
        #Y += k * Mv
    
    """
    For each (i,k) pair, with 1 <= k <= phase2start and 2 <= i <= isqrt(N//k),
    phase 2 subtracts mobs[i] * (N//k//i) from Mover[k].
    """
    
    for n in range(1, Nr+1):
        v = N // n
        Y += n * Mover[n]
    
    print("%f" % (time() - z))
    
    return X + Y - Z






def totientsum10(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    The overall method is to use the Dirichlet hyperbola method on phi = Id * mu.  This yields the formula
        totientsum(N) == X + Y - Z,
    where
        a is a selectable parameter
        b == N // a
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= a)
        Y == sum(y * Mertens(N//y), 1 <= y <= b)
        Z == Mertens(isqrt(N)) * binomial(isqrt(N) + 1, 2)
    This requires using an efficient way to calculate all of those Mertens values.
    We sieve the Mobius function directly up to a, compute the Mertens function along the way, and store the results.
    We then use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    to compute the remaining Mertens values.
    
    The time  complexity is O(N^(2/3) * log(log(N))^(-2/3)).
    The space compelxity is O(N^(1/2))-ish, dominated by the arrays that store Mobius and Mertens values.
    """    # TODO: Make the space-complexity statement more precise.  Also, can that be brought down without breaking the clock?
    
    z = time()
    
    Nr = isqrt(N)
    a = introot(N**2, 3)
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    #print(a)
    X, Y, Z = 0, 0, 0
    M     = [0] * (   Nr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (N//Nr + 1)  # Mover[N//n] will store Mertens(n) for large n.
    mobs  = [0] * (   Nr + 1)
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.  Those <= Nr get stored.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # As we go, we accumulate terms from the X- and Y-formulas.
    
    t = Nr - (Nr == N//Nr)
    nextMkey = N // t
    mert = 0
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            mobs[k] = mu
            M[k] = mert
            X += mu * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            #Y += v * mert      # TODO: We should be able to contribute to Y here.  Why does that not work?
            t -= 1
            nextMkey = N // t
            # We can early-exit this loop once k has reached the greatest N//t-value <= a.
            if nextMkey > a:
                phase2start = t
                break
    
    # phase2start is the greatest integer t such that a < N // t.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == N // (a+1)
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    
    Z = M[Nr] * (Nr * (Nr+1) // 2)
    Mover[N//Nr] = M[Nr]
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to Nr stored in mobs, and some Mertens values up to a
    # stored in M and Mover, we compute the rest of the needed Mertens values with the formula
    # M(v) == 1 - v - sum(mu(k) * (v//k) + M(v//k)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= k <= sqrt(v).
    # As we go, we accumulate the remaining terms from the Y-formula.
    
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
        #Y += t * Mv            # TODO: We should be able to contribute to Y here.  Why does that not work?
    
    for n in range(1, Nr+1):    # TODO: We should be able to integrate this into phases 1 and 2.  Why does that not work?
        Y += n * Mover[n]
    
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









def totientsum11(N):
    """
    Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html
    and https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim.
    
    The overall method is to use the Dirichlet hyperbola method on phi = Id * mu.  This yields the formula
        totientsum(N) == X + Y - Z,
    where
        a is a selectable parameter
        b == N // a
        X == sum(mu(x) * binomial(N//x + 1, 2), 1 <= x <= a)
        Y == sum(y * Mertens(N//y), 1 <= y <= b)
        Z == Mertens(isqrt(N)) * binomial(isqrt(N) + 1, 2)
    This requires using an efficient way to calculate all of those Mertens values.
    We sieve the Mobius function directly up to a, compute the Mertens function along the way, and store the results.
    We then use the formula
        M(v) == 1 - v + isqrt(v) * M(sqrt(v)) - sum(mu(k) * (v//k) + M(v//k), 2 <= k <= sqrt(v))
    to compute the remaining Mertens values.
    
    The time  complexity is O(N^(2/3) * log(log(N))^(-2/3)).
    The space compelxity is O(N^(1/2))-ish, dominated by the arrays that store Mobius and Mertens values.
    """    # TODO: Make the space-complexity statement more precise.  Also, can that be brought down without breaking the clock?
    
    z = time()
    
    Nr = isqrt(N)
    a = introot(N**2, 3)
    a = introot(int((N / log(log(N)))**2), 3)                                                                  # TODO: Optimize.
    #print(a)
    X, Y, Z = 0, 0, 0
    M     = [0] * (   Nr + 1)  # M[n]        will store Mertens(n) for small n.
    Mover = [0] * (N//Nr + 1)  # Mover[N//n] will store Mertens(n) for large n.
    mobs  = [0] * (   Nr + 1)
    
    # We need to fill M and Mover with a bunch of Mertens values.
    # First, we sieve the Mobius function up to a.  Those <= Nr get stored.
    # Along the way, we compute the corresponding Mertens values and store those that go in M and Mover.
    # As we go, we accumulate terms from the X- and Y-formulas.
    
    s = Nr - (Nr == N//Nr)
    nextMkey = N // s
    mert = 0
    for (k, mu) in enumerate(mobiussieve(a+1), start=1):
        mert += mu
        v = N // k
        
        if k <= Nr:
            mobs[k] = mu
            M[k] = mert
            X += mu * (v * (v+1) // 2)
        
        elif k == nextMkey:
            Mover[v] = mert
            Y += v * mert
            s -= 1
            nextMkey = N // s
            # We can early-exit this loop once k has reached the greatest N//s-value <= a.
            if nextMkey > a:
                phase2start = s
                break
    
    # phase2start is the greatest integer s such that a < N // s.
    assert N // (phase2start + 1) <= a < N // phase2start
    assert phase2start == N // (a+1)
    
    # The X-formula is now fully evaluated, and we have the data needed to evaluate Z as well.
    
    Mover[N//Nr] = M[Nr]
    Y += Nr * Mover[Nr]
    Z = M[Nr] * (Nr * (Nr+1) // 2)
    
    print("%f" % (time() - z))
    z = time()
    
    # Now that we have Mobius values up to Nr stored in mobs, and some Mertens values up to a
    # stored in M and Mover, we compute the rest of the needed Mertens values with the formula
    # M(v) == 1 - v - sum(mu(k) * (v//k) + M(v//k)) + isqrt(v) * M(sqrt(v)),
    # where the sum runs over 2 <= k <= sqrt(v).
    # As we go, we accumulate the remaining terms from the Y-formula.
    
    for t in range(phase2start, 0, -1):
        v = N // t
        vr = isqrt(v)
        Mv = 1 - v + M[vr] * vr
        for k in range(2, vr+1):
            vk = v // k
            Mv -= mobs[k] * vk
            Mv -= M[vk] if vk <= Nr else Mover[k*t] # Mover[N//vk]
        # Mv is now Mertens(v).
        Mover[t] += Mv
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




methods = (totientsum, \
           #totientsum0, \
           #totientsum1, \
           #totientsum2, \
           #totientsum3, \
           #totientsum4, \
           #totientsum5, \
           #totientsum6, \
           #totientsum7, \
           #totientsum7a, \
           #totientsum8, \
           #totientsum9, \
           #totientsum10, \
           totientsum11, \
          )
answers = []
n = int(argv[1])
for m in methods:
    z = time()
    A = m(n)
    z = time() - z
    print("\t", A)
    print("%f" % z)
    answers.append(A)
    print()

for a in answers: print(a)
assert len(set(answers)) == 1
