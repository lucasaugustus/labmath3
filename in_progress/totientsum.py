#! /usr/bin/env python3

from sys import argv
from labmath3 import *
from time import process_time, time

from mertens import mertens

def totientsum_brute(x): return sum(totient(n) for n in range(1, x+1))

def totientsum0(x):
    """
    Computes sum(totient(n) for n in range(1, x+1)), allegedly efficiently.
    Using the Dirichlet hyperbola method, we find that this equals
    sum(a * M(x//a) + mobius(a) * binomial(x//a + 1, 2) for a in range(1, isqrt(x)+1)) - M(isqrt(x)) * binomial(isqrt(x) + 1, 2)
    where M is the Mertens function.
    """
    xr = isqrt(x)
    term1 = sum(a * mertens(x//a) + mu * comb(x//a + 1, 2) for (a, mu) in enumerate(mobiussieve(xr+1), start=1))
    term2 = comb(xr + 1, 2) * mertens(xr)
    return term1 - term2

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

#for x in chain(range(10), (100, 1000, 10000)):
#    print(totientsum_brute(x), totientsum(x), totientsum0(x), totientsum1(x), totientsum2(x), totientsum3(x))


#import cProfile; cProfile.run("print(totientsum0(10**9))", sort="tottime")



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








class FIArray(object):  # https://github.com/gbroxey/blog/blob/main/code/utils/fiarrays.nim
    
    def __init__(self, x):
        self.x = x
        self.isqrt = isqrt(x)
        self.L = 2 * self.isqrt
        if self.isqrt == self.x // self.isqrt: self.L -= 1
        self.arr = [0] * self.L
    
    def __getitem__(self, v):
        if v <= 0: return 0
        if v <= self.isqrt: return self.arr[v-1]
        return self.arr[-(self.x//v)]
    
    def __setitem__(self, v, z):
        if v <= self.isqrt: self.arr[v-1] = z
        else: self.arr[-(self.x // v)] = z
    
    def indexOf(self, v):
        if v <= self.isqrt: return v - 1
        return self.L - (self.x // v)
    
    def keysInc(self):
        for v in range(1, self.isqrt+1): yield v
        if self.isqrt != self.x // self.isqrt: yield self.x // self.isqrt
        for n in range(self.isqrt - 1, 0, -1): yield self.x // n
    
    def keysDec(self):
        for n in range(1, self.isqrt): yield self.x // n
        if self.isqrt != self.x // self.isqrt: yield self.x // self.isqrt
        for v in range(self.isqrt, 0, -1): yield v



def mertensFast1(x):
    M = FIArray(x)
    y = introot(int(x * 1.0)**2, 3)
    x12 = isqrt(x)
    mobs = [0] * (x12+1)
    mert = 0
    Mkeygen = M.keysInc()
    nextMkey = next(Mkeygen)    # This goes all the way up to x; we do not need to worry about running out.
    for (k, mu) in enumerate(mobiussieve(y+1), start=1):
        mert += mu
        if k <= x12: mobs[k] = mu
        if k == nextMkey:
            M[k] = mert
            nextMkey = next(Mkeygen)
    for v in M.keysInc():
        if v <= y: continue
        muV = 1
        vsqrt = isqrt(v)
        for i in range(1, vsqrt+1):
            muV -= mobs[i] * (v // i)
            muV -= M[v // i]
        muV += M[vsqrt] * vsqrt
        M[v] = muV
    return M

def sumN(x): return x * (x + 1) // 2

def totientsum_1(x):
    # Derived from https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html.
    M = mertensFast1(x)
    xsqrt = M.isqrt
    result = 0
    for n in range(1, xsqrt+1):
        result += (M[n] - M[n-1]) * sumN(x // n)
        result += n * M[x // n]
    result -= sumN(xsqrt) * M[xsqrt]
    return result

def totientsum_2(x):
    Phi = FIArray(x)
    y = introot(int(x * 1.0)**2, 3)
    smallPhi = [0] * (y+1)
    T = 0
    for (x,t) in enumerate(totientsieve(y+1), start=1):
        T += t
        smallPhi[x] = T
    for v in Phi.keysInc():
        if v <= y:
            Phi[v] = smallPhi[v]
            continue
        phiV = sumN(v)
        vsqrt = isqrt(v)
        for i in range(1, vsqrt+1):
            phiV -= (smallPhi[i] - smallPhi[i-1]) * (v // i)
            phiV -= Phi[v // i]
        phiV += Phi[vsqrt] * vsqrt
        Phi[v] = phiV
    return phiV

#z = time()
#print(totientsum(int(argv[1])))
#print(time() - z)

z = time()
print(totientsum_1(int(argv[1])))
print(time() - z)

#print(totientsum(int(argv[1])))

#z = time()
#print(totientsum_2(int(argv[1])))
#print(time() - z)

#z = time()
#print(totientsum3(int(argv[1])))
#print(time() - z)

#z = time()
#print(totientsum4(int(argv[1])))
#print(time() - z)


"""
201   120   012
3.397 3.364 3.433
2.288 2.523 2.464
4.163 4.104 4.286

"""



exit()
starttime = time()
print(totientsum3(int(argv[1])))
print(time() - starttime)
print()
starttime = time()
print(totientsum4(int(argv[1])))
print(time() - starttime)













