#! /usr/bin/env python3

# Formatting note: this file uses lines of up to 128 characters and employs 4-space chunks for indentations.
# Docstring lines are limited to 80 characters except for the occasional example output.

from multiprocessing import Process, Queue as mpQueue
from itertools import chain, count, groupby, islice, tee, cycle, takewhile, compress, product, zip_longest
from fractions import Fraction
from random import randrange, random
from math import pi, log, log2, ceil, sqrt, factorial, comb, prod, gcd, lcm, isqrt; inf = float('inf')
from heapq import merge

try: from gmpy2 import mpz; mpzv, inttypes = 2, (int, type(mpz(1)))
except ImportError: mpz, mpzv, inttypes = int, 0, (int,)

__version__ = labmathversion = "3.0.0"

def primegen(limit=inf):
    """
    Generates primes strictly less than limit almost-lazily by a segmented
    sieve of Eratosthenes.  Memory usage depends on the sequence of prime
    gaps; on Cramer's conjecture, it is O(sqrt(p) * log(p)^2), where p is
    the most-recently-yielded prime.
    
    Input: limit -- a number (default = inf)
    
    Output: sequence of integers
    
    Examples:
    
    >>> list(islice(primegen(), 19))
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
    
    >>> list(primegen(71))
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
    """
    # We do not sieve 2, so we ought to be able to get sigificant savings by halving the length of the sieve.
    # But the tiny extra computation involved in that seems to exceed the savings.
    yield from takewhile(lambda x: x < limit, (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47))
    pl, pg = [3,5,7], primegen()
    for p in pl: next(pg)
    while True:
        lo = pl[-1]**2
        if lo >= limit: break
        pl.append(next(pg))
        hi = min(pl[-1]**2, limit)
        sieve = bytearray([True]) * (hi - lo)
        for p in pl: sieve[(-lo)%p::p] = bytearray([False]) * ((hi-1)//p - (lo-1)//p)
        yield from compress(range(lo,hi,2), sieve[::2])

def rpn(instr):
    """
    Evaluates a string in reverse Polish notation.
    
    The available binary operators are +, -, *, /, //, %, and **, which all
    indicate the same operations here as they indicate in Python3 source
    code.  The available unary operators are ! and #, which denote the
    factorial and primorial, respectively.  For terminal syntax
    compatibility reasons, the RPN expression may be enclosed in quotes, and
    four aliases are allowed: x for *, xx for **, f for !, and p for #.
    
    Input: instr -- a string
    
    Output: A list of numbers
    
    Examples:
    
    >>> rpn("38 ! 1 +")
    [523022617466601111760007224100074291200000001]
    
    >>> rpn("1729 42 %")
    [7]
    
    >>> rpn("2 3 xx 5 6 7 +")
    [8, 5, 13]
    """
    stack = []
    for token in instr.split():
        if set(token).issubset("1234567890"): stack.append(int(token))
        elif len(token) > 1 and token[0] == '-' and set(token[1:]).issubset("1234567890"): stack.append(int(token))
        elif token in ('+', '-', '*', '/', '//', '%', '**', 'x', 'xx'):   # binary operators
            b = stack.pop()
            a = stack.pop()
            if   token == '+' : res = a  + b
            elif token == '-' : res = a  - b
            elif token == '*' : res = a  * b
            elif token == 'x' : res = a  * b
            elif token == '/' : res = a  / b
            elif token == '//': res = a // b
            elif token == '%' : res = a  % b
            elif token == '**': res = a ** b
            elif token == 'xx': res = a ** b
            stack.append(res)
        elif token in ('!', 'f', '#', 'p'):                             # unary operators
            a = stack.pop()
            if   token == '!' : res = prod(range(1, a+1))
            elif token == 'f' : res = prod(range(1, a+1))
            elif token == '#' : res = prod(primegen(a+1))
            elif token == 'p' : res = prod(primegen(a+1))
            stack.append(res)
        else: raise Exception
    return stack

def listprod(l):
    """
    Computes the product of the elements of a list.
    
    This function is superior to the built-in math.prod in situations where
    the product is very large.  The reason is that algorithm used by
    math.prod(l) amounts to
        reduce(lambda x,y:x*y, l)
    which is quadratically slow when the elements of l are similarly-sized.
    The algorithm implemented here splits the list into halves, recursively
    applies itself to each half, and then returns the product of the
    results.  This is asymptotically faster for cases where the products get
    large; however, it takes a long list to make this faster than math.prod.
    
    Input: l -- list of numbers
    
    Output: A number
    
    Examples:
    
    >>> listprod(range(1, 8))
    5040
    
    >>> listprod([])
    1
    """
    if len(l) == 0: return 1
    while len(l) > 1:
        q = [l[2*t] * l[2*t+1] for t in range(len(l) // 2)]
        if len(l) % 2 == 1: q.append(l[-1])
        l = q
    return l[0]

def polyval(f, x, m=None):
    """
    Evalutates a polynomial at a particular point, optionally modulo m.
    
    Input:
        f -- List.  These are the polynomial's coefficients in order of
             increasing degree; that is, f[k] is the coefficient of the term
             of degree k.
        x -- Integer.  The polynomial is evaluated at this point.
        m -- Integer or None (default).  If not None, we evaluate modulo m.
    
    Output: An integer.
    
    Examples:
    
    >>> polyval([1,2,3], 2)
    17
    
    >>> polyval([1,2,3], 2, 3)
    2
    """
    out = 0
    if m is None:
        for a in reversed(f): out = a + out * x
    else:
        for a in reversed(f): out = (a + out * x) % m
    return out

def powerset(l):    # TODO: make this handle sets as well.
    """
    Generates the powerset of a list, tuple, or string.  Output is a
    sequence of lists.
    
    Do not expect the output to be in any particular order.
    
    Input: l -- indexable iterable
    
    Output: Sequence of lists
    
    Examples:
    
    >>> sorted(powerset([]))
    [[]]
    
    >>> sorted(powerset([1]))
    [[], [1]]
    
    >>> sorted(powerset([1, 2]))
    [[], [1], [1, 2], [2]]
    
    >>> sorted(powerset([1, 2, 3]))
    [[], [1], [1, 2], [1, 2, 3], [1, 3], [2], [2, 3], [3]]
    """
    n = len(l)
    for mask in range(2**n): yield [l[i-1] for i in range(1, n+1) if mask & (1 << (i-1))]

def _primepi_S1(x, y, b, c, square_free, primes, mob):   # TODO: Make this non-recursive.
    """
    This is a helper function for primepi.
    """
    S1 = 0
    b += 1
    while b < len(primes):
        next_ = square_free * primes[b]
        if next_ > y: break
        S1 += mob * primephi(x//next_, c, primes)
        S1 += _primepi_S1(x, y, b, c, next_, primes, -mob)
        b += 1
    return S1

def primephi(x, a, primes):
    """
    Legendre's partial sieve function: the number of positive integers <= x
    with no prime factor <= the ath prime.
    
    Input:
        x, a -- integers
        primes -- list of length >= a such that primes[n] is the nth prime.
                  The value of primes[0] is irrelevant.
    
    Output: an integer.
    
    Examples:
    
    >>> primes20 = [0, 2, 3, 5, 7, 11, 13, 17, 19]
    
    >>> primephi(123456789, 0, primes20)
    123456789
    
    >>> primephi(123456789, 1, primes20)
    61728395
    
    >>> primephi(123456789, 2, primes20)
    41152263
    
    >>> primephi(123456789, 3, primes20)
    32921810
    
    >>> primephi(123456789, 4, primes20)
    28218694
    
    >>> primephi(123456789, 5, primes20)
    25653358
    """
    if a == 0: return x
    if a == 1: return (x + 1) // 2
    if a == 2: return 2 * (x // 6) + (0,1,1,1,1,2)[x%6]
    if a == 3: return 8 * (x // 30) + (0,1,1,1,1,1,1,2,2,2,2,3,3,4,4,4,4,5,5,6,6,6,6,7,7,7,7,7,7,8)[x%30]
    pa = primes[a]
    if x < pa: return 1
    answer = primephi(x, a-1, primes) - primephi(x//pa, a-1, primes)
    return answer

def primepi(x, alpha=2.5):
    """
    Number of primes <= x, computed with the Lagarias-Miller-Odlyzko method.
    The P2 phase was written by me; the S1 and S2 phases are translated from
    Kim Walisch's primecount package.  The time- and space-complexities are
    within logarithmic factors of O(x^(2/3)) and O(x^(1/3)), respectively.
    
    Input:
        x -- an integer.
        alpha -- a tuning parameter that determines how much work gets done
                 in each phase of the algorithm.  This has consequences for
                 execution time, but as long as 1 <= alpha < x^(1/6), the
                 return value will be correct.  Default == 2.5.
     
    Output: An integer.
    
    Examples:
    
    >>> primepi(97)
    25
    
    >> primepi(100)
    25
    
    >>> primepi(542)
    100
    
    >>> primepi(10**6)
    78498
    
    >>> primepi(10**6, alpha=1)
    78498
    
    >>> primepi(10**6, alpha=5)
    78498
    
    >>> primepi(10**6, alpha=9.9)
    78498
    
    >>> primepi(2**27)
    7603553
    """
    if x < 29: return 0 if x < 0 else (0,0,1,2,2,3,3,4,4,4,4,5,5,6,6,6,6,7,7,8,8,8,8,9,9,9,9,9,9)[x]
    
    # Here beginneth the P2 section of the LMO algorithm.
    # I wrote it myself from scratch in accordance with the LMO paper.
    
    x13 = introot(x, 3)
    x12 = isqrt(x)
    x23 = introot(x*x, 3)
    
    y = int(x13 * alpha)
    if y >= x12: y = x12 - 1
    
    sieve = bytearray([True]) * (y+1)
    sieve[0] = sieve[1] = False
    for p in range(isqrt(y)+1):
        if not sieve[p]: continue
        for n in range(p*2, y+1, p):
            sieve[n] = False
    pi_y = sum(sieve)
    primes = [0] * pi_y
    k = 0
    for n in range(y+1):
        if sieve[n]:
            primes[k] = n
            k += 1
    del sieve
    
    # At this point, primes is a list in increasing order of all primes <= y.
    
    P2 = 0
    j = 2
    pilist = [0] * y
    pin = pi_y       # A running total of primes.
    while (j-1)*y + 1 <= x23:
        # Sieve the interval [(j-1)*y + 1 , j*y]
        lo = (j-1) * y + 1
        hi = min(j*y, x23)
        sl = hi - lo + 1                        # "sl" stands for "sieve length".
        sieve = bytearray([True]) * sl
        # sieve[0] corresponds to lo.
        # sieve[sl] corresponds to hi.
        for p in primes:
            start = (-lo) % p
            if lo + start == p: start += p      # This line ensures that only proper multiples of p get sieved out.
            for n in range(start, sl, p):
                sieve[n] = False
        for n in range(sl):
            pin += sieve[n]
            pilist[n] = pin
        # If sl == y, then at this point, we have pilist == [pi(k) for k in range((j-1)*y+1, j*y+1)],
        # so that pilist[l] == pi((j-1)*y+1 + l), or pi(k) == pilist[k - (j-1)*y - 1].
        # Also, pin == pilist[-1] == pi(j*y).
        # If sl < y, then the obvious modifications can be made to the above statements to make them true.
        if lo <= x12 <= hi: pi_12 = pilist[x12 - lo]
        Ij_lo = max(x // (  j  *y + 1),  y ) + 1
        Ij_hi = min(x // ((j-1)*y + 1), x12)
        sl = Ij_hi - Ij_lo + 1
        sieve = bytearray([True]) * sl
        for p in primes:
            if p**2 > Ij_hi: break
            start = (-Ij_lo) % p
            if Ij_lo + start == p: start += p   # This line ensures that only proper multiples of p get sieved out.
            for n in range(start, sl, p):
                sieve[n] = False
        P2 += sum(pilist[x // (Ij_lo + n) - (j-1)*y - 1] for n in range(sl) if sieve[n])
        j += 1
    del pilist, sieve
    
    P2 += (pi_y * (pi_y-1) - pi_12 * (pi_12-1)) // 2
    
    # Here endeth the P2 section of the LMO algorithm.
    # Now we precompute the least-prime-factor and Mobius functions.
    
    lpf = [0] * (y + 1)
    mu  = [1] * (y + 1)
    for p in reversed(primes):  # The reversal is important for lpf; for mu, it is irrelevant.
        for n in range(p, y+1, p):
            lpf[n] = p
            mu[n] *= -1
        for n in range(p*p, y+1, p*p): mu[n] = 0
    
    primes = [0] + primes       # We need the list to be 1-based for the rest of the function.
    
    # Here beginneth the S1 section of the LMO algorithm, translated from
    # https://github.com/kimwalisch/primecount/blob/master/src/S1.cpp.
    
    c = 8 if y >= 20 else (0,0,1,2,2,3,3,4,4,4,4,5,5,6,6,6,6,7,7,8)[y]
    
    S1 = primephi(x, c, primes)
    for b in range(c+1, len(primes)):
        S1 -= primephi(x//primes[b], c, primes)
        S1 += _primepi_S1(x, y, b, c, primes[b], primes, 1)
    
    # Here endeth the S1 section of the LMO algorithm.
    # Here beginneth the S2 section of the LMO algorithm, translated from
    # https://github.com/kimwalisch/primecount/blob/master/src/lmo/pi_lmo4.cpp.
    
    limit = x // y
    lr = isqrt(limit)
    segment_size = lr if (lr & (lr - 1) == 0) else (1 << lr.bit_length())   # the least power of 2 >= lr
    S2 = 0
    next_ = primes[:]
    phi = [0] * len(primes)
    
    for low in range(1, limit, segment_size):
        high = min(low + segment_size, limit)
        sieve = bytearray([1]) * segment_size
        # The current segment of the sieve is [low, high).
        
        for b in range(1, c+1):
            k = next_[b]
            prime = primes[b]
            while k < high:
                sieve[k - low] = 0
                k += prime
            next_[b] = k
        
        # Initialize the Fenwick tree
        treesize = len(sieve) // 2
        tree = [0] * treesize
        for i in range(0, treesize):
            tree[i] = sieve[i*2]
            k = ((i + 1) & (~i)) >> 1   # (i+1) & (~i) is the number that, when ored into i, would set i's lowest unset bit.
            j = i
            while k != 0:
                tree[i] += tree[j - 1]
                j &= j - 1      # clears the lowest set bit
                k >>= 1
        
        for b in range(c+1, pi_y):
            prime = primes[b]
            min_m = max(x // (prime * high), y // prime)
            max_m = min(x // (prime * low ), y         )
            
            if prime >= max_m: break
            
            for m in range(max_m, min_m, -1):
                if mu[m] != 0 and prime < lpf[m]:
                    n = prime * m
                    
                    # phi_xn = phi[b] + tree.count
                    pos = (x//n - low) >> 1
                    phi_xn = phi[b] + tree[pos]
                    pos += 1
                    while True:
                        pos &= pos - 1      # clears the lowest set bit
                        if pos == 0: break
                        phi_xn += tree[pos - 1]
                    
                    S2 -= mu[m] * phi_xn
            
            # phi[b] += tree.count
            pos = (high - 1 - low) >> 1
            phi[b] += tree[pos]
            pos += 1
            while True:
                pos &= pos - 1      # clears the lowest set bit
                if pos == 0: break
                phi[b] += tree[pos - 1]
            
            # cross_off
            m = next_[b]
            while m < high:
                if sieve[m - low]:
                    pos = m - low
                    sieve[pos] = 0
                    pos >>= 1
                    while True:
                        tree[pos] -= 1
                        pos |= pos + 1      # sets the lowest unset bit
                        if pos >= treesize: break
                m += prime * 2
            next_[b] = m
    
    # Here endeth the S2 section of the LMO algorithm.
    
    return pi_y - 1 - P2 + S1 + S2

def primesum(n):    # TODO: What are the time- and space-complexities?
    """
    Sum of primes <= n.  This code is originally from Lucy_Hedgehog's post
    at https://projecteuler.net/thread=10;page=5.
    
    Input: n -- integer
    
    Output: An integer
    
    Examples:
    
    >>> [primesum(n) for n in (100, 1729, 10**6)]
    [1060, 213538, 37550402023]
    """
    if n < 2: return 0
    r = isqrt(n)
    V = [n//i for i in range(1,r+1)]
    V += list(range(V[-1]-1,0,-1))
    S = {i:i*(i+1)//2-1 for i in V}
    for p in range(2,r+1):
        if S[p] > S[p-1]:  # p is prime
            sp = S[p-1]  # sum of primes smaller than p
            p2 = p*p
            for v in V:
                if v < p2: break
                S[v] -= p*(S[v//p] - sp)
    return S[n]

def altseriesaccel(a, n):
    """
    Convergence acceleration for alternating series.  This is Algorithm 1
    from the article "Convergence Acceleration of Alternating Series" by
    Cohen, Villegas, and Zagier, with a minor tweak so that the d-value is
    not computed via floating point.  The article is available at
    https://people.mpim-bonn.mpg.de/zagier/files/exp-math-9/fulltext.pdf.
    
    Input:
        a -- an iterable.  The series to be summed is
             a[0] - a[1] + a[2] - a[3] + a[4] - a[5] ...
        n -- the number of terms to use.  A few dozen is usually sufficient.
    
    Output: a floating-point number.
    
    Examples:
    
    The Riemann zeta function is
        1/1^x + 1/2^x + 1/3^x + 1/4^x + ...
    This is slowly-convergent, but it is not alternating, so this algorithm
    does not seem to apply.  However, it is closely related to the Dirichlet
    eta function:
        1/1^x - 1/2^x + 1/3^x - 1/4^x + ...
    which *is* alternating.  This is still slowly convergent, but feeding it
    into this algorithm is profitable:
    
    >>> eta = lambda x: altseriesaccel((1/j**x for j in count(1)), 24)
    >>> zeta = lambda x: eta(x) / (1-2**(1-x))
    >>> zeta(2)
    1.6449340668482264
    >>> pi**2 / 6
    1.6449340668482264
    
    The sum of the harmonic series, modified to have alternating signs, is
    the natural logarithm of 2.  It converges quite slowly, but because its
    signs alternate, this algorithm can be used to great effect:
    >>> altseriesaccel((1/j for j in count(1)), 24)
    0.6931471805599452
    >>> log(2)
    0.6931471805599453
    
    The Leibniz formula for pi/4 is the alternating reciprocal sum of the
    odd numbers: 1/1 - 1/3 + 1/5 - 1/7 + ...  It converges quite slowly, but
    because its signs alternate, this algorithm can be used to great effect:
    >>> altseriesaccel((1/j for j in count(1,2)), 24) * 4
    3.1415926535897936
    >>> pi
    3.141592653589793
    """
    Vl, Vh = 2, 6
    for bit in bin(n)[2:]: Vl, Vh = (Vh * Vl - 6, Vh * Vh - 2) if bit == '1' else (Vl * Vl - 2, Vh * Vl - 6)
    d = Vl // 2
    #d = (3 + sqrt(8))**n
    #d = (d + 1/d) / 2
    b, c, s = -1, -d, 0
    for k in range(n):
        c = b - c
        s = s + c * next(a)
        b = (k + n) * (k - n) * b / ((k + 0.5) * (k + 1))
    return s / d

def riemannzeta(z, k=24):   # TODO: Where is this accurate?
    """
    The Riemann zeta function, computed by using a convergence-acceleration
    technique (implemented as altseriesaccel) on the Dirichlet eta function.
    
    Input:
        z -- point to evaluate at
        k -- number of terms to use.  Default == 24.
    
    Output:
        A floating-point real number (if n is real) or a floating-point
        complex number (if n is complex).
        The pole at n == 1 manifests as a ZeroDivisionError.
    
    Examples:
    
    >>> try: riemannzeta(1)
    ... except ZeroDivisionError: print("Do not pass 1 to this function.")
    Do not pass 1 to this function.
    
    >>> try: riemannzeta(1.0)
    ... except ZeroDivisionError: print("Do not pass 1.0 to this function.")
    Do not pass 1.0 to this function.
    
    >>> riemannzeta(2)
    1.6449340668482264
    
    The use of the Dirichlet eta function as an intermediary allows us to
    investigate the critical strip:
    >>> riemannzeta(complex(0.5, 14.134725))
    (1.7672547844177162e-08-1.1100463048215172e-07j)
    """
    return altseriesaccel((1/j**z for j in count(1)), k+1) / (1-2**(1-z))

def zetam1(n, k=24):
    """
    Computes the Riemann zeta function minus 1 by applying a convergence-
    acceleration technique (implemented as altseriesaccel) to the Dirichlet
    eta function.  This should converge for any complex n with positive real
    part unless 1 == 2**(n-1), and accuracy may be low near such points.
    
    When computing zeta(z) - 1 when the real part of z is large, floating-
    point numbers cannot be expected to have enough precision to distinguish
    zeta(z) from 1.0, so the formula
        riemannzeta(z) - 1
    will evaluate to 0.0.  This function returns accurate answers even in
    such cases.
    
    Input:
        n -- point to evaluate at
        k -- number of terms to use.  Default == 24.  Since we are using
             altseriesaccel, this is almost certainly sufficient.
    
    Output:
        A floating-point real number (if n is real) or a floating-point
        complex number (if n is complex).
        The pole at n == 1 manifests as a ZeroDivisionError.
    
    Examples:
    
    >>> riemannzeta(100) - 1        # A misleading result!
    0.0
    
    >>> zetam1(100)                 # Rather more accurate!
    7.888609052210118e-31
    """
    return (altseriesaccel((-1/j**n for j in count(2)), k+1) + 2**(1-n)) / (1-2**(1-n))

def riemannR(x, n=None, zc={}):
    """
    Uses the Gram series to compute Riemann's R function, which is a very
    good approximation to primepi.
    
    Input:
        x -- Integer. The function is evaluated at this point.
        n -- Integer.  Number of terms to use.  Default == None; in this
             case, we set n = (11 * ln(x) + 153) / 6.  This was chosen by
             experiment to get a relateive error of < 10^-14 w.r.t. to the
             true values for x in [10**2, 10**3, ..., 10**15].
             An OverflowError may occur if n is sufficiently large.
        zc -- Dict.  Default = {}.  Keys are integers; values are the
              Riemann zeta function at those integers.  Erroneous values are
              neither detected nor corrected.  Unprovided values are
              computed as needed.
    
    Output: a floating-point real number.
    
    Examples:
    
    >>> riemannR(10**2)
    25.661633266924188
    
    >>> riemannR(10**3)
    168.3594462811672
    
    >>> riemannR(10**4)
    1226.9312183434338
    
    >>> riemannR(10**5)
    9587.431738841964
    """
    if n is None: n = int((11 * log(x) + 153) // 6)
    lnx = log(x)
    total, lnxp, kfac = 0, 1, 1
    for k in range(1, n+1):
        lnxp *= lnx
        kfac *= k
        rz = zc.get(k+1, None)
        if rz is None: rz = zc[k+1] = riemannzeta(k+1)
        t = lnxp / (k * kfac * rz)
        tt = total + t
        if total - tt == 0: break   # This should protect from OverflowErrors.
        total = tt
    return 1 + total

def nthprimeapprox(n):
    """
    Produces an integer that should be rather close to the nth prime number
    by using binary splitting on Riemann's R function.
    
    Input: n -- an integer
    
    Output: an integer
    
    Examples:
    
    >>> nthprimeapprox(10**1)
    29
    
    >>> nthprimeapprox(10**2)
    502
    
    >>> nthprimeapprox(10**3)
    7830
    
    >>> nthprimeapprox(10**4)
    104767
    
    >>> nthprimeapprox(10**5)
    1299733
    """
    if n <= 2000:
        if n < 26: return None if n < 1 else (0,2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)[n]
        ln_n = log(n)
        lnln_n = log(ln_n)
        return int(n * (ln_n + lnln_n - 1 + ( (lnln_n - 2) / ln_n )))
    ln_n = log(n)
    lnln_n = log(ln_n)
    hi = ln_n + lnln_n
    lo = hi - 1
    x = lo + ( (lnln_n - 2) / ln_n )
    lo, x, hi = int(lo * n), int(x * n), int(hi * n)
    assert lo < x < hi
    zc = {}
    lo_g, x_g, hi_g = riemannR(lo, zc=zc), riemannR(x, zc=zc), riemannR(hi, zc=zc)
    while lo != hi - 1:
        x = (lo + hi) // 2
        x_g = riemannR(x, zc=zc)
        if   x_g < n: lo = x
        elif x_g > n: hi = x
        else: return x
    return lo

def nthprime(n):
    """
    Returns the nth prime (counting 2 as #1)
    
    Input: n -- an integer
    
    Output: An integer
    
    Examples:
    
    >>> list(map(nthprime, (0, 1, 2, 3, 4, 25, 2**20)))
    [None, 2, 3, 5, 7, 97, 16290047]
    """
    if n < 1: return None
    elif n <= 25:
        ps = primegen()
        for _ in range(n-1): next(ps)
        return next(ps)
    x = prevprime(nthprimeapprox(n))
    c = primepi(x)
    # x is prime and approximates the nth prime number.
    # c is the number of primes <= x.
    while c > n:                    # TODO we can do better than this
        x = prevprime(x)
        c -= 1
    while c < n:                    # TODO we can do better than this
        x = nextprime(x)
        c += 1
    return x

def xgcd(a, b):     # TODO: this is ugly.  Clean it up.
    """
    Extended Euclidean algorithm: returns a tuple (g,x,y) where
    g == gcd(a, b) and g == a*x + b*y.  Many such tuples for each (a,b);
    we make no guarantees about which tuple will be returned.
    
    Input: a, b -- integers
    
    Output: Tuple of three integers
    
    Examples:
    
    >>> xgcd(42, 57)
    (3, -4, 3)
    
    >>> xgcd(1729, 98)
    (7, -3, 53)
    
    >>> xgcd(67, 71)
    (1, -18, 17)
    
    >>> xgcd(-20, 55)
    (5, -3, -1)
    """
    if a == 0 and b == 0: return (0, 0, 1)
    if a == 0: return (abs(b), 0, b//abs(b))
    if b == 0: return (abs(a), a//abs(a), 0)
    x_sign = 1; y_sign = 1
    if a < 0: a = -a; x_sign = -1
    if b < 0: b = -b; y_sign = -1
    x, y, r, s = 1, 0, 0, 1
    while b != 0:
        q = a//b
        a, b, r, s, x, y = b, a%b, x-q*r, y-q*s, r, s
    return (a, x*x_sign, y*y_sign)

def crt(rems, mods):
    """
    The Chinese remainder theorem: returns the unique integer in
    range(prod(mods)) that reduces to x % y for (x,y) in zip(rems,mods).
    All elements of mods must be pairwise coprime.
    
    Input: rems, mods -- iterables of the same finite length,
                         containing integers
    
    Output: an integer in range(prod(mods))
    
    Examples:
    
    >>> crt((1, 2), (3, 4))
    10
    
    >>> crt((4, 5), (10, 3))
    14
    
    >>> crt((-1, -1), (100, 101))
    10099
    
    >>> crt((1,2,3), (5,6,7))
    206
    """
    if len(mods) == 1: return rems[0]
    N = prod(mods)
    return sum(r * (N//m) * pow(N//m, -1, m) for (r, m) in zip(rems, mods) if m != 1) % N

def introot(n, r=2):    # TODO Newton iteration?
    """
    Returns the rth root of n, rounded to the nearest integer in the
    direction of zero.  Returns None if r is even and n is negative.
    
    Input:
        n -- an integer
        r -- a natural number or None
    
    Output: An integer
    
    Examples:
    
    >>> [introot(-729, 3), introot(-728, 3)]
    [-9, -8]
    
    >>> [introot(1023, 2), introot(1024, 2)]
    [31, 32]
    """
    if n < 0: return None if r%2 == 0 else -introot(-n, r)
    if n < 2: return n
    if r == 1: return n
    if r == 2: return isqrt(n)
    if r % 2 == 0: return introot(isqrt(n), r//2)
    lower = upper = 1 << (n.bit_length() // r)
    while lower ** r >  n: lower >>= 2
    while upper ** r <= n: upper <<= 2
    while lower != upper - 1:
        mid = (lower + upper) // 2
        m = mid**r
        if   m == n: return  mid
        elif m <  n: lower = mid
        elif m >  n: upper = mid
    return lower

def ispower(n, r=0):
    """
    Checks whether n is a perfect power.
    
    If r == 0:
        If n is a perfect power, then we return a tuple containing largest
        integer (in terms of magnitude) that, when squared/cubed/etc, yields
        n as the first entry; the relevant power is the second component.
        If n is not a perfect power, then we return None.
    
    If r > 0:
        We check whether n is a perfect rth power; we return its rth root if
        it is and None if it is not.
    
    Input:
        n -- an integer
        r -- an integer
    
    Output: An integer, a 2-tuple of integers, or None
    
    Examples:
    
    >>> [ispower(n) for n in [64, 25, -729, 1729]]
    [(8, 2), (5, 2), (-9, 3), None]
    
    >>> [ispower(64, r) for r in range(7)]
    [(8, 2), 64, 8, 4, None, None, 2]
    """
    #if r == 0: return any(ispower(n, r) for r in primegen(n.bit_length()+1))
    #return n == introot(n, r) ** r
    if r == 0:
        if n in (0, 1, -1): return (n, 1)
        for r in primegen(n.bit_length()+1):
            x = ispower(n, r)
            if x: return (x, r)
        return None
    # TODO tricks for special cases
    if (r == 2) and (n & 2): return None
    if (r == 3) and (n & 7) in (2,4,6): return None
    x = introot(n, r)
    return None if x is None else (x if x**r == n else None)

def ilog(x, b):                                 # TODO: investigate optimization starting from x.bin_length() * 2 // b
    """
    Greatest integer l such that b**l <= x.
    
    Input: x, b -- integers
    
    Output: An integer
    
    Examples:
    
    >>> ilog(263789, 10)
    5
    
    >>> ilog(1023, 2)
    9
    """
    l = 0
    while x >= b:
        x //= b
        l += 1
    return l
    # TODO possible optimization route: x.bit_length() == ilog(x, 2) + 1; we can therefore use x.bit_length() * 2 // b as a
    #      1st approximation to ilog(x, b), then compute pow(b, x.bit_length() * 2 // b), then compare that to x and adjust.

def semiprimegen():                                                 # TODO: implement an upper bound as in primegen.
    """
    Generates the semiprimes, by filtering the primes out of the output of
    pspgen.
    
    Input: none.
    
    Output: infinite sequence of integers
    
    Examples:
    
    >>> list(islice(semiprimegen(), 18))
    [4, 6, 9, 10, 14, 15, 21, 22, 25, 26, 33, 34, 35, 38, 39, 46, 49, 51]
    """
    pg, pspg = primegen(), pspgen()
    p, psp = next(pg), next(pspg)
    while True:
        if p == psp: p, psp = next(pg), next(pspg)
        else: yield psp; psp = next(pspg)

def pspgen():                                                       # TODO: implement an upper bound as in primegen.
    """
    Generates the primes and semiprimes, using a segmented sieve based on
    the sieve of Eratosthenes and the fact that these are precisely the
    numbers not divisible by any smaller semiprimes.
    
    Input: none
    
    Output: infinite sequence of integers
    
    Examples:
    
    >>> list(islice(pspgen(), 19))
    [2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 25, 26]
    """
    yield from (2,3,4,5,6,7,9,10,11,13,14,15,17,19,21,22,23,25,26,29,31,33,34,35,37,38,39,41,43,46,47,49,51)
    low = 52
    length = 7**3 - 52 # == 293
    end = low + length # == 343
    maxsp = introot(end**2, 3) + 1 # == 50
    spg = semiprimegen()
    spl = [next(spg) for _ in range(16)] # == [4,6,9,10,14,15,21,22,25,26,33,34,35,38,39,46,49]
    nextsp = next(spg)
    while True:
        sieve = bytearray([True]) * length
        for sp in spl:
            n = (-low) % sp
            while n < length:
                sieve[n] = False
                n += sp
            #sieve[n::sp] = bytearray([False]) * ((length-n-1)//sp + 1)
        for n in range(length):
            if sieve[n]: yield n + low
        low += length
        length = len(spl)
        end = low + length
        maxsp = introot(end**2, 3) + 1
        while nextsp < maxsp:
            spl.append(nextsp)
            nextsp = next(spg)

def almostprimegen(k):                                              # TODO: implement an upper bound as in primegen.
    """
    Generates the k-almost-primes, which are the numbers that have precisely
    k prime factors, counted with multiplicity.  This is done by filtering
    nearlyprimegen(k-1) out of the output of nearlyprimegen(k).
    
    Input: k -- an integer
    
    Output: infinite sequence of integers
    
    Examples:
    
    >>> list(islice(almostprimegen(3), 18))
    [8, 12, 18, 20, 27, 28, 30, 42, 44, 45, 50, 52, 63, 66, 68, 70, 75, 76]
    
    >>> list(islice(almostprimegen(4), 16))
    [16, 24, 36, 40, 54, 56, 60, 81, 84, 88, 90, 100, 104, 126, 132, 135]
    """
    # A number is called a k-almost-prime if it has exactly k prime factors, counted with multiplicity.
    # We proceed by generating the k-nearly-primes and (k-1)-nearly-primes, and filtering the (k-1)-nps out of the k-nps.
    if k == 1:
        yield from primegen()
        return
    km1_npgen, k_npgen = nearlyprimegen(k-1), nearlyprimegen(k)
    km1_np, k_np = next(km1_npgen), next(k_npgen)
    while True:
        if km1_np == k_np: km1_np, k_np = next(km1_npgen), next(k_npgen)
        else: yield k_np; k_np = next(k_npgen)

def nearlyprimegen(k):                                              # TODO: implement an upper bound as in primegen.
    """
    Generates the numbers (other than 1) that have k or fewer prime factors,
    counted with multipicity.  This is done via a segmented sieve based on
    the sieve of Eratosthenes and the fact that these are precisely the
    numbers not divisible by any smaller k-almost-primes.
    
    Input: k -- an integer
    
    Output: infinite sequence of integers
    
    Examples:
    
    >>> list(islice(nearlyprimegen(3), 35))
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39, 41]
    """
    # This generates the numbers that have 1, 2, 3, ..., or k prime factors, counted with multiplicity.
    if k == 1:
        yield from primegen()
        return
    if k == 2:
        yield from pspgen()
        return
    assert k >= 3
    # The first number that is not a k-nearly-prime is 2**(k+1).
    yield from range(2, 2**(k+1))
    # All numbers strictly between 2**(k+1) and 9 * 2**(k-2) have Omega < k.
    # 9 * 2**(k-2) is the first number > 2**(k+1) (and third overall) with Omega == k.
    yield from range(2**(k+1) + 1, 9 * 2**(k-2) + 1)
    # The k-nearly-primes are precisely the numbers that are not divisible by any smaller k-almost-primes.
    kapgen = almostprimegen(k)
    low = 9 * 2**(k-2) + 1      # This variable holds the number that is at the bottom end of the sieving interval.
    # To sieve out to x, we need to store the k-almost-primes up to x**(k/(k+1)).
    # Equivalently, if we have the k-almost-primes up to x, then we can sieve out to x**((k+1)/k).
    end = introot(low**(k+1), k)
    length = end - low
    maxkap = 2**(k+1) + 1 #introot(end**k, k+1) + 1
    kaplist = []
    while True:
        nextkap = next(kapgen)
        if nextkap < maxkap: kaplist.append(nextkap)
        else: break
    while True:
        sieve = bytearray([True]) * length
        for kap in kaplist:
            n = (-low) % kap
            while n < length:
                sieve[n] = False
                n += kap
            #sieve[n::kap] = bytearray([False]) * ((length-n-1)//kap + 1)
        for n in range(length):
            if sieve[n]: yield n + low
        low += length
        length = len(kaplist)
        end = low + length
        maxkap = introot(end**k, k+1) + 1
        while nextkap < maxkap:
            kaplist.append(nextkap)
            nextkap = next(kapgen)

def fibogen():
    """
    Generates the Fibonacci numbers, starting with 0 and 1.
    
    Input: none
    
    Output: Sequence of integers
    
    Examples:
    
    >>> list(islice(fibogen(), 17))
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]
    """
    a, b = 0, 1
    while True: yield a; a, b = b, a+b

def fibo(n, f={0:0, 1:1, 2:1}):         # TODO iterative version
    """
    Efficiently extracts the nth Fibonacci number, indexed so that
    fibo(0) == 0 and fibo(1) == fibo(2) == 1.  Computes O(log(n)) earlier
    Fibonaccis along the way.  This is, in the big-O sense, just about as
    fast as possible.
    
    Input:
        n -- non-negative integer
        f -- dict of Fibonacci numbers.  Used for memoization purposes.
    
    Output: An integer
    
    Examples:
    
    >>> fibo(346)
    912511873855702065852730553217787283194150290277873860991322859307033303
    
    >>> x = fibo(100000)
    >>> x // 10**20879
    25974069347221724166
    >>> x % 10**20
    49895374653428746875
    """
    if n in f: return f[n]
    if n % 2: f[n] = fibo(n//2 + 1 , f) ** 2  +  fibo(n//2     , f) ** 2
    else:     f[n] = fibo(n//2 + 1 , f) ** 2  -  fibo(n//2 - 1 , f) ** 2
    return f[n]

def fibomod(n, m, f={0:0, 1:1, 2:1}):   # TODO iterative version.  What is up with the caching weirdness?
    """
    Efficiently extracts the nth Fibonacci number, indexed so that
    fibo(0) == 0 and fibo(1) == fibo(2) == 1, mod m.  Computes O(log(n))
    earlier Fibonaccis along the way.  This is, in the big-O sense, just
    about as fast as possible.
    
    Input:
        n -- non-negative integer
        m -- positive integer
        f -- dict of Fibonacci numbers.  Used for memoization.
    
    Output: An integer
    
    Examples:
    >>> fibomod(512, 73)
    8
    
    >>> fibomod(100000, 10**20)
    49895374653428746875
    """
    if m == 1: return 0
    if n in f: return f[n]
    if n % 2: f[n] = ( fibomod(n//2 + 1, m, f) ** 2  +  fibomod(n//2    , m, f) ** 2 ) % m
    else:     f[n] = ( fibomod(n//2 + 1, m, f) ** 2  -  fibomod(n//2 - 1, m, f) ** 2 ) % m
    return f[n]

def lucaschain(n, x0, x1, op1, op2):
    """
    Algorithm 3.6.7 from Crandall & Pomerance 2005 (page 147): evaluation of
    a binary Lucas chain.  To quote their description:
    
    For a sequence x0, x1, ... with a rule for computing x_2j from x_j and a
    rule for computing x_(2j+1) from x_j and x_(j+1), this algorithm
    computes (x_n, x_(n+1)) for a given positive integer n.  We have n in
    binary as (n0, n1, ..., n_(b-1)) with n0 being the low-order bit.  We
    write the rules as follows: x_2j = op1(x_j) and
    x_(2j+1) = op2(x_j, x_(j+1)).  At each step in the for loop we have
    u = x_j, v = x_(j+1) for some nonnegative integer j.
    
    Input:
        n -- positive integer
        x0, x1 -- numbers
        op1, op2 -- functions.  op1 takes one argument; op2 takes two.
    
    Output: 2-tuple of numbers
    
    Examples:
    
    >>> m, A, n = 10000, 5, 307
    
    To compute terms m and m + 1 of the Lucas sequence V(A,1) modulo n, we
    can write
    
    >>> lucaschain(m, 2, A, lambda x:(x*x-2)%n, lambda x,y:(x*y-A)%n)
    (154, 132)
    """
    u, v = x0, x1
    for j in bin(n)[2:]:
        if j == '1': u, v = op2(u, v), op1(v)
        else:        u, v = op1(u), op2(u, v)
    return u, v

def lucasgen(P, Q):
    """
    Generates the Lucas U- and V-sequences with parameters (P, Q).
    
    Input: P, Q -- integers
    
    Output: sequence of 2-tuples of integers.  The first element is a term
            of the U-sequence; the second element is of the V-sequence.
    
    Examples:
    
    >>> list(islice(lucasgen(1, -1), 8))         # Fibonacci & Lucas numbers
    [(0, 2), (1, 1), (1, 3), (2, 4), (3, 7), (5, 11), (8, 18), (13, 29)]
    
    >>> list(islice(lucasgen(3,  2), 7))         # (2**n - 1) & (2**n + 1)
    [(0, 2), (1, 3), (3, 5), (7, 9), (15, 17), (31, 33), (63, 65)]
    """
    u0, u1, v0, v1 = 0, 1, 2, P
    while True:
        yield (u0, v0)
        u0, u1, v0, v1 = u1, P*u1 - Q*u0, v1, P*v1 - Q*v0

def lucas(k, P, Q):    # coded after http://www.scirp.org/journal/PaperDownload.aspx?paperID=3368
    """
    Efficiently computes the kth terms in the Lucas U- and V-sequences
    U(P,Q) and V(P,Q).  More explicitly, if
        U_0, U_1, V_0, V_1 = 0, 1, 2, P
    and we have the recursions
        U_n = P * U_(n-1) - Q * U_(n-2)
        V_n = P * V_(n-1) - Q * V_(n-2),
    then we compute U_k and V_k in O(ln(k)) arithmetic operations.
    
    If P**2 != 4*Q, then these sequences grow exponentially, so the number
    of bit operations is anywhere from O(k**2) to O(k * ln(k)**2),
    depending on how multiplication is handled.
    
    Input: k, P, Q -- integers (k >= 0).
    
    Output: 2-tuple of integers
    
    Examples:
    
    >>> [lucas(k, 1, -1)[0] for k in range(18)]         # Fibonacci numbers
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
    
    >>> [lucas(k, 1, -1)[1] for k in range(17)]         # Lucas numbers
    [2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, 521, 843, 1364, 2207]
    """
    D = P * P - 4 * Q
    if D == 0:  # critical polynomial has repeated root: there exists S such that P = 2*S and Q = S**2
        if k == 0: return (0, 2)    # avoid returning floats
        S = P // 2
        ss = S ** (k-1)
        return (k * ss, 2 * S * ss)
    Vl, Vh, Ql, Qh = 2, P, 1, 1
    for kj in bin(k)[2:]:
        Ql *= Qh
        if kj == '1': Qh, Vl, Vh = Ql * Q, Vh * Vl - P * Ql, Vh * Vh - 2 * Ql * Q
        else:         Qh, Vh, Vl = Ql    , Vh * Vl - P * Ql, Vl * Vl - 2 * Ql
    return ((2 * Vh - P * Vl) // D, Vl)

def binlinrecgen(P, Q, a, b):
    """
    The general binary linear recursion.  This is exactly like lucasgen,
    except we only compute one sequence, and we supply the seeds.
    
    Basically, it is the same thing as linrecgen([P, -Q], [a, b]).
    
    Input:
        P, Q -- the sequence parameters
        a, b -- the zeroth and first terms, respectively
    
    Output: sequence of numbers
    
    Examples:
    
    >>> list(islice(binlinrecgen(1, -1, 0, 1), 18))   # Fibonacci
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
    
    >>> list(islice(binlinrecgen(1, -1, 2, 1), 17))   # Lucas
    [2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, 521, 843, 1364, 2207]
    
    >>> list(islice(binlinrecgen(3,  2, 0, 1), 15))   # Binary repunits
    [0, 1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383]
    """
    while True: yield a; a, b = b, P*b - Q*a

def binlinrec(k, P, Q, a, b):  # general binary linear recursion: x2 == P * x1 - Q * x0.  k == 0 --> x == a; x == 1 --> x == b.
    """
    The general binary linear recursion.  Exactly like lucas, except we only
    compute one sequence, and we supply the seeds.
    
    Basically, it is the same thing as linrec(k, [P, -Q], [a, b]).
    
    Input:
        k -- integer.  Index of the term to extract.
        P, Q -- the sequence parameters
        a, b -- the zeroth and first terms, respectively
    
    Output: sequence of numbers
    
    Examples:
    
    >>> [binlinrec(k, 1, -1, 0, 1) for k in range(18)]   # Fibonacci
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
    
    >>> [binlinrec(k, 1, -1, 2, 1) for k in range(17)]   # Lucas
    [2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, 521, 843, 1364, 2207]
    
    >>> [binlinrec(k, 3,  2, 0, 1) for k in range(15)]   # Binary repunits
    [0, 1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383]
    """
    u, v = lucas(k, P, Q)
    return a * (v - P * u) // 2 + u * b
    # In that numerator, v - P * u is always even:
    # if P is even, then v is always even; if P is odd, then u and v always have the same parity.

def linrecgen(a, b, m=None):
    """
    The general homogeneous linear recursion: yields the sequence defined by
        x_(n+1) == a_k * x_n + a_(k-1) * x_(n-1) + ... + a_0 * x_(n-k),
    where the initial values are [x_0, x_1, ..., x_k] == b.  The terms of
    this sequence grow exponentially, so computing a distant term
    incrementally by plucking it out of this generator takes O(n**2) bit
    operations.  Extraction of distant terms should therefore be done via
    linrec; using Schoenhage-Strassen multiplication, it takes
    O(n * ln(n)**2 * ln(ln(n))) bit operations.
    
    Input:
        a -- List or tuple of numbers.  The coefficients of the recursion.
        b -- List of numbers.  The initial values of the recursion.
        m -- Integer.  If present, we compute the sequence modulo m.
    
    Output: sequence of numbers
    
    Examples:
    
    >>> list(islice(linrecgen([1, 1], [0, 1]), 18))  # Fibonacci
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
    
    >>> list(islice(linrecgen([1, 1], [2, 1]), 17))  # Lucas
    [2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, 521, 843, 1364, 2207]
    
    >>> list(islice(linrecgen([1, 1, 0], [3, 0, 2]), 19))  # Perrin
    [3, 0, 2, 3, 2, 5, 5, 7, 10, 12, 17, 22, 29, 39, 51, 68, 90, 119, 158]
    
    >>> list(islice(linrecgen([1, 1], [0, 1], 5), 20))  # Fibonacci
    [0, 1, 1, 2, 3, 0, 3, 3, 1, 4, 0, 4, 4, 3, 2, 0, 2, 2, 4, 1]
    
    >>> list(islice(linrecgen([1, 1], [2, 1], 5), 20))  # Lucas
    [2, 1, 3, 4, 2, 1, 3, 4, 2, 1, 3, 4, 2, 1, 3, 4, 2, 1, 3, 4]
    
    >>> list(islice(linrecgen([1, 1, 0], [3, 0, 2], 5), 20))  # Perrin
    [3, 0, 2, 3, 2, 0, 0, 2, 0, 2, 2, 2, 4, 4, 1, 3, 0, 4, 3, 4]
    """
    n = len(a)
    assert n == len(b)
    if m is not None: a, b = [x%m for x in a], [x%m for x in b]
    while True:
        yield b[0]
        x = sum(a[x]*b[x] for x in range(n))
        b.append(x if m is None else (x % m))
        del b[0]

def linrec(n, a, b, m=None):                    # TODO: See https://projecteuler.net/thread=258#29618.
    """
    The general homogeneous linear recursion mod m.  We use matrix methods
    to efficiently compute the nth term of the recursion
    x_(n+1) == ( a_k * x_n + a_(k-1) * x_(n-1) + ... + a_0 * x_(n-k) ) % m,
    where the initial values are [x_0, x_1, ..., x_k] == b.  The terms of
    this sequence grow exponentially, so computing a distant term
    incrementally by plucking it out of the sequence produced by
    linrecgen(a, b) takes O(n**2) bit operations while this method, using
    Schoenhage-Strassen multiplication, takes O(n * ln(n)**2) operations.
    
    Input:
        n -- Integer.  Index of the term to extract.
        a -- List of numbers.  The coefficients of the recursion.
        b -- List of numbers.  The initial values of the recursion.
        m -- Integer.  If present, we compute everything modulo m.
    
    Output: a number
    
    Examples:
    
    >>> [linrec(k, [1, 1], [0, 1]) for k in range(18)]  # Fibonacci
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
    
    >>> [linrec(k, [1, 1], [2, 1]) for k in range(17)]  # Lucas
    [2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, 521, 843, 1364, 2207]
    
    >>> [linrec(k, [1, 1, 0], [3, 0, 2]) for k in range(19)]  # Perrin
    [3, 0, 2, 3, 2, 5, 5, 7, 10, 12, 17, 22, 29, 39, 51, 68, 90, 119, 158]
    
    >>> linrec(400, [1, 0, 1], [0, 0, 1])
    719696709185072238228862568935651761390476159269863132285895106694
    
    >>> [linrec(k, [1, 1], [0, 1], 10) for k in range(20)]  # Fibonacci
    [0, 1, 1, 2, 3, 5, 8, 3, 1, 4, 5, 9, 4, 3, 7, 0, 7, 7, 4, 1]
    
    >>> [linrec(k, [1, 1], [2, 1], 10) for k in range(20)]  # Lucas
    [2, 1, 3, 4, 7, 1, 8, 9, 7, 6, 3, 9, 2, 1, 3, 4, 7, 1, 8, 9]
    
    >>> [linrec(k, [1, 1, 0], [3, 0, 2], 10) for k in range(20)]  # Perrin
    [3, 0, 2, 3, 2, 5, 5, 7, 0, 2, 7, 2, 9, 9, 1, 8, 0, 9, 8, 9]
    
    >>> linrec(400, [1, 0, 1], [0, 0, 1], 10**10)
    5895106694
    """
    d = len(a)
    assert d == len(b)
    if n < d: return b[n]
    A = [[0]*d for k in range(d-1)]
    A.append(a[:] if m is None else [x % m for x in a])
    for k in range(d-1): A[k][k+1] = 1
    # The transition matrix A is now constructed.  We proceed to raise it to the power n - d + 1 via exponentiation by squaring.
    # We use a left-to-right ladder, since this enables an optimization for when we compute A * z: we can exploit the structure
    # of A by appending to z the new bottom row and then deleting z's first row.  This uses d**2 ops rather than matmul's d**3.
    # The squaring steps still use the full matrix multiplication, however.
    z = [row[:] for row in A]
    for k in bin(n - d + 1)[3:]:    # skip the highest bit
        if m is None: z = [[sum(x * z[i][col] for (i,x) in enumerate(row))     for col in range(d)] for row in z]     # z *= z
        else:         z = [[sum(x * z[i][col] for (i,x) in enumerate(row)) % m for col in range(d)] for row in z]     # z *= z
        if k == '1': #z = matmul(A, z)
            if m is None: z.append([sum(A[-1][x] * z[x][y] for x in range(d))     for y in range(d)])
            else:         z.append([sum(A[-1][x] * z[x][y] for x in range(d)) % m for y in range(d)])
            del z[0]
    # z is now A ** (n - d + 1)
    ans = sum(x*y for (x,y) in zip(z[-1], b))  # pluck off the last element of A * b --- i.e., the dot product of A[-1] with b.
    return ans if m is None else (ans % m)

def legendre(a, p):
    """
    The Legendre symbol (a|p): 1 if a is a quadratic residue mod p, -1 if it
    is not, and 0 if a % p == 0.  If p is not an odd prime, then the return
    value is meaningless.
    
    Input:
        a -- an integer
        p -- a prime
    
    Output: -1, 0, or 1
    
    Examples:
    
    >>> [legendre(a, 11) for a in [-10, -7, -4, -2, -1, 0, 1, 2, 4, 7, 10]]
    [1, 1, -1, 1, -1, 0, 1, -1, 1, -1, -1]
    
    >>> [legendre(a, 17) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [-1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1]
    
    >>> [legendre(a, 101) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [-1, 1, 1, -1, 1, 0, 1, -1, 1, 1, -1]
    """
    return ((pow(a, (p-1) >> 1, p) + 1) % p) - 1

def jacobi(a, n):
    """
    The Jacobi symbol (a|n).  If n is not a positive odd integer, then the
    return value is meaningless.
    
    Input:
        a -- any integer
        n -- positive odd integer
    
    Output: -1, 0, or 1
    
    Examples:
    
    >>> [jacobi(a, 15) for a in [-10, -7, -4, -2, -1, 0, 1, 2, 4, 7, 10]]
    [0, 1, -1, -1, -1, 0, 1, 1, 1, -1, 0]
    
    >>> [jacobi(a, 13) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [1, 1, 1, -1, 1, 0, 1, -1, 1, 1, 1]
    
    >>> [jacobi(a, 11) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [1, -1, -1, 1, -1, 0, 1, -1, 1, 1, -1]
    """
    if (a == 0) or (a == 1): return a
    a, t = a%n, 1
    while a != 0:
        while not a & 1:
            a //= 2
            if n & 7 in (3, 5): t *= -1
        a, n = n, a
        if (a & 3 == 3) and (n & 3) == 3: t *= -1
        a %= n
    return t if n == 1 else 0

def kronecker(a, n):
    """
    The Kronecker symbol (a|n).  Note that this is the generalization of the
    Jacobi symbol, /not/ the Dirac-delta analogue.
    
    Input: a, n -- integers
    
    Output: -1, 0, or 1
    
    Examples:
    
    >>> [kronecker(a, 15) for a in [-10, -7, -4, -2, -1, 0, 1, 2, 4, 7, 10]]
    [0, 1, -1, -1, -1, 0, 1, 1, 1, -1, 0]
    
    >>> [kronecker(a, 14) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [0, -1, 0, 0, -1, 0, 1, 0, 0, 1, 0]
    
    >>> [kronecker(a, 11) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [1, -1, -1, 1, -1, 0, 1, -1, 1, 1, -1]
    
    >>> [kronecker(a, -11) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [-1, 1, 1, -1, 1, 0, 1, -1, 1, 1, -1]
    
    >>> [kronecker(a, 32) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]]
    [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]
    """
    if n == -1: return -1 if a < 0 else 1
    if n ==  0: return 1 if abs(a) == 1 else 0
    if n ==  1: return 1
    if n ==  2: return 0 if a%2 == 0 else (1 if a%8 in [1, 7] else -1)
    if n  <  0: return kronecker(a, -1) * kronecker(a, -n)
    f = (n & (-n)).bit_length() - 1     # number of trailing zeros of n in binary
    n >>= f                             # the odd part of n
    return kronecker(a, 2)**f * jacobi(a, n)

def sprp(n, b):
    """
    The Strong Probable Primality Test, also known as a single round
    of the Miller-Rabin test.
    
    Input:
        n -- Integer.  Number to be checked.
        b -- Integer.  The base of the test.  We assume that n != b.
    
    Output: True or False.  If True, then the number is probably prime; if
            False, then it is definitely composite.  Note that if n == b,
            then we return False regardless of n's actual primality.
    
    Examples:
    
    >>> sprp(factorial(38) - 1, 2)
    True
    
    >>> sprp(factorial(38) + 1, 2)
    False
    """
    s = ((n - 1) & (1 - n)).bit_length() - 1    # number of trailing zeros of n-1 in binary
    t = (n - 1) >> s                            # the odd part of n-1
    #assert 1 + 2**s * t == n
    x = pow(b, t, n)
    if x == 1 or x == n - 1: return True
    for j in range(1, s):
        x = pow(x, 2, n)
        if x == 1: return False
        elif x == n - 1: return True
    return False

def mrab(n, basis):
    """
    The Miller-Rabin probable primality test.
    
    Input:
        n -- Integer.  Number to be checked.
        basis -- Iterable of integers.  Bases to be used for the test.  We
                 assume that n is not in basis.
    
    Output: True or False.  If True, then the number is probably prime; if
            False, then it is definitely composite.  Note that if n is in
            basis, then we will return False regardless of n's actual
            primality.
    
    Examples:
    
    >>> mrab(factorial(38) - 1, (2,3))
    True
    
    >>> mrab(factorial(38) + 1, (2,3))
    False
    """
    return all(sprp(n, b) for b in basis)

def miller(n):
    """
    Miller's primality test.  If the extended Riemann hypothesis (the one
    about Dirichlet L-functions) is true, then this test is deterministic.
    
    Input: n -- number to check
    
    Output: True if n is (conditionally) prime; False otherwise.
    
    Examples:
    
    >>> [miller(n) for n in [2, 3, 5, 7, 101, 127, 1009, factorial(38) - 1]]
    [True, True, True, True, True, True, True, True]
    
    >>> [miller(n) for n in [28, 36, 72, 98, 105, factorial(38) + 1]]
    [False, False, False, False, False, False]
    """
    return n == 2 if n % 2 == 0 or n < 3 else mrab(n, range(2, min(n-1, int(2 * log(n)**2))))

def lprp(n, a, b):
    """
    The Lucas Probable Primality Test as described in Crandall & Pomerance
    2005 (Algorithm 3.6.9, pg 148).
    
    Input: n, a, b -- integers
    
    Output: True or False
    
    Examples:
    
    >>> [n for n in range(11, 80) if lprp(n, 1, -1)]
    [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
    
    >>> [lprp(n, 1, -1) for n in (factorial(38)+1, factorial(38)-1)]
    [False, True]
    
    >>> pseudoprimes = (17*19, 13*29, 31*61, 43*89, 37*113, 53*109, 7*23*41)
    
    >>> [lprp(n, 1, -1) for n in pseudoprimes]
    [True, True, True, True, True, True, True]
    """
    D = a*a - 4*b
    if ispower(D, 2) or (b == 1 and abs(a) == 1): raise Exception("bad parameters: lprp(%d, %d, %d)" % (n, a, b))
    g = gcd(n, 2*a*b*D)
    if g > 1:
        if g < n: return False
        # So n divides 2 * a * b * (a**2 - 4 * b).
        if n == 2: return True
        raise Exception("bad parameters: lprp(%d, %d, %d)" % (n, a, b))                     # TODO further analysis of this case
    # Uncommenting the next line would produce an exactly equivalent test, but there is a large speedup to be had by doing it
    # via the trick in CranPom Alg 3.6.9, pg 148/161.  Note that this trick avoids actually calculating U_(2m) (which is what
    # the Lucas test examines).  There is another significant speedup to be had by integrating the next two lines' lucaschain
    # stuff.
    #m = n - jacobi(D, n); u, v = lucasmod(m, a, b, n); return u == 0
    #A, m = (a**2 * modinv(b, n) - 2) % n, (n - jacobi(D, n)) // 2   # Note that n - (D|n) is even.
    #Vm, Vm1 = lucaschain(m, 2, A, lambda x: (x*x - 2) % n, lambda x,y: (x*y - A) % n)
    A = (a**2 * pow(b, -1, n) - 2) % n  # No ValueErrors here thanks to the "if g > 1" bit above.
    u, v = 2, A
    for j in bin((n - jacobi(D, n)) // 2)[2:]:
        if j == '1': u, v = (u*v - A) % n, (v*v - 2) % n
        else:        u, v = (u*u - 2) % n, (u*v - A) % n
    # Note that u == V_m(A, 1) and v == V_(m+1)(A, 1) modulo n.
    return (A * u - 2 * v) % n == 0 # == (pow(b, (n-1)/2, n) * Vm - 2) % n    <-- uncomment that to get the quad frob test

def lucasmod(k, P, Q, m):    # coded after http://www.scirp.org/journal/PaperDownload.aspx?paperID=3368     TODO gcd(D,m)!=1?
    # Efficiently computes the kth terms of Lucas U- and V-sequences modulo m with parameters (P, Q).
    # Currently just a helper function for slprp and xslprp.
    # Will be upgraded to full status when the case gcd(D,m)!=1 is handled properly.
    Vl, Vh, Ql, Qh = 2 % m, P % m, 1, 1
    for kj in bin(k)[2:]:
        Ql = (Ql * Qh) % m
        if kj == '1': Qh, Vl, Vh = (Ql * Q) % m, (Vh * Vl - P * Ql) % m, (Vh * Vh - 2 * Ql * Q) % m
        else:         Qh, Vh, Vl =  Ql         , (Vh * Vl - P * Ql) % m, (Vl * Vl - 2 * Ql    ) % m
    return (   ( (2*Vh-P*Vl) * pow(P*P-4*Q,-1,m) ) % m   ,   Vl   )     # TODO: ValueError gcd(P*P-4*Q, m) != 1.

def slprp(n, a, b):
    """
    The Strong Lucas Probable Primality Test.  Its false positives are a
    strict subset of those for lprp with the same parameters.
    
    Input: n, a, b -- integers
    
    Output: True or False
    
    Examples:
    
    >>> [n for n in range(11, 80) if slprp(n, 1, -1)]
    [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
    
    >>> [slprp(n, 1, -1) for n in (factorial(38)+1, factorial(38)-1)]
    [False, True]
    
    >>> pseudoprimes = (17*19, 13*29, 31*61, 43*89, 37*113, 53*109, 7*23*41)
    
    >>> [slprp(n, 1, -1) for n in pseudoprimes]
    [False, False, False, False, True, True, False]
    """
    D = a*a - 4*b
    if ispower(D, 2) or (b == 1 and abs(a) == 1): raise Exception("bad parameters: slprp(%d, %d, %d)" % (n, a, b))
    g = gcd(n, 2*a*b*D)
    if g > 1:
        if g < n: return False
        # So n divides 2 * a * b * (a**2 - 4 * b).
        if n == 2: return True
        raise Exception("bad parameters: slprp(%d, %d, %d)" % (n, a, b))                    # TODO further analysis of this case
    x = (n - jacobi(D, n))
    s = (x & (-x)).bit_length() - 1     # number of trailing zeros of x in binary
    t = x >> s                          # the odd part of x
    u, v = lucasmod(t, a, b, n)
    if u == 0 or v == 0: return True
    q = pow(b, t, n)
    for _ in range(1, s):
        v = (v*v - 2*q) % n
        if v == 0: return True
        q = (q*q) % n
    return False

def xslprp(n, a):
    """
    The Extra Strong Lucas Probable Primality Test.  Its false positives are
    a strict subset of those for slprp (and therefore lprp) with the
    parameters (a, 1).
    
    Input: n, a -- integers
    
    Output: True or False
    
    Examples:
    
    >>> [n for n in range(31, 100) if xslprp(n, 3)]
    [31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    
    >>> [xslprp(n, 3) for n in (factorial(38)+1, factorial(38)-1)]
    [False, True]
    
    >>> pseudoprimes = (17*19, 13*29, 31*61, 43*89, 37*113, 53*109, 7*23*41)
    
    >>> [xslprp(n, 3) for n in pseudoprimes]
    [False, False, False, False, True, True, False]
    """
    D = a*a - 4
    if ispower(D, 2) or (abs(a) == 1): raise Exception("bad parameters: xslprp(%d, %d)" % (n, a))
    g = gcd(n, 2*a*D)
    if g > 1:
        if g < n: return False
        # So n divides 2 * (a-2) * a * (a+2).
        if n == 2: return True
        raise Exception("bad parameters: xslprp(%d, %d)" % (n, a))                     # TODO further analysis of this case
    x = (n - jacobi(D, n))
    s = (x & (-x)).bit_length() - 1     # number of trailing zeros of x in binary
    u, v = lucasmod(x>>s, a, 1, n)      # x>>s is the odd part of x
    if (u == 0 and (v == 2 or v == n - 2)) or v == 0: return True
    for _ in range(1, s):
        v = (v*v - 2) % n
        if v == 0: return True
    return False

def bpsw(n):
    """
    The Baillie-Pomerance-Selfridge-Wagstaff probable primality test.
    Infinitely many false positives are conjectured to exist, but none are
    known, and the test is known to be deteriministic below 2**64.
    
    Input: n -- integer
    
    Output: True or False
    
    Examples:
    
    >>> [n for n in range(90) if bpsw(1000*n+1)]
    [3, 4, 7, 9, 13, 16, 19, 21, 24, 28, 51, 54, 55, 61, 69, 70, 76, 81, 88]
    
    >>> [bpsw(factorial(38)+1), bpsw(factorial(38)-1)]
    [False, True]
    """
    if n % 2 == 0 or n < 3: return n == 2
    if not sprp(n, 2): return False
    for D in count(5, 4):
        j = jacobi(D, n)
        if j == 0: return D == n
        if j == -1: break
        D = -2 - D
        j = jacobi(D, n)
        if j == 0: return -D == n
        if j == -1: break
        if D == -11 and ispower(n,2): return False
    return slprp(n, 1, (1 - D) // 4)

def qfprp(n, a, b): # As described in CranPom Alg 3.6.9, pg 148/161
    """
    The Quadratic Frobenius Probable Primality Test as described in Crandall
    & Pomerance 2005 (Alg 3.6.9, pg 148).
    
    Input: n, a, b -- integers
    
    Output: True or False
    
    Examples:
    
    >>> [n for n in range(11, 80) if qfprp(n, 1, -1)]
    [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
    
    >>> [qfprp(n, 1, -1) for n in (factorial(38)+1, factorial(38)-1)]
    [False, True]
    
    >>> fp = (9, 65, 105, 3*7*13, 13*37, 7*73, 3*11*17, 3*3*5*13, 7*11*13)
    >>> [qfprp(n, 4, 8) for n in fp]                       # False positives
    [True, True, True, True, True, True, True, True, True]
    
    >>> fp = (23*67, 151*3301, 661*1321, 23*199*353, 1153*3457, 919*4591)
    >>> [qfprp(n, 7, 5) for n in fp]                       # False positives
    [True, True, True, True, True, True]
    """
    D = a**2 - 4*b
    if ispower(D, 2) or (b == 1 and abs(a) == 1): raise Exception("bad parameters: qfprp(%d, %d, %d)" % (n, a, b))
    if gcd(n, 2*a*b*D) != 1: return False
    A = (a**2 * pow(b, -1, n) - 2) % n  # No ValueErrors here, thanks to the previous line.
    u, v = 2, A
    for j in bin((n - jacobi(D, n)) // 2)[2:]:
        if j == '1': u, v = (u*v - A) % n, (v*v - 2) % n
        else:        u, v = (u*u - 2) % n, (u*v - A) % n
    return (A * u - 2 * v) % n == 0 == (pow(b, (n-1)//2, n) * u - 2) % n

def polyaddmodp(a, b, p):
    """
    Adds two polynomials and reduces their coefficients mod p.
    
    Polynomials are written as lists of integers with the constant terms
    first.  If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If one of the input
    polynomials is None, then we return None.
    
    Input:
        a, b -- polynomials
        p -- integer
    
    Output: A polynomial.
    
    Examples:
    
    >>> polyaddmodp([1,2,3], [4,5,6], 7)
    [5, 0, 2]
    
    >>> polyaddmodp([1,2,3], [6,5,4], 7)
    []
    """
    if a is None or b is None: return None
    c = [(x+y) % p for (x,y) in zip_longest(a, b, fillvalue=0)]
    while len(c) > 0 and c[-1] == 0: del c[-1]
    return c

def polysubmodp(a, b, p):
    """
    Subtracts the polynomial b from a and reduces their coefficients mod p.
    
    Polynomials are written as lists of integers with the constant terms
    first.  If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If one of the input
    polynomials is None, then we return None.
    
    Input:
        a, b -- polynomials
        p -- integer
    
    Output: A polynomial.
    
    Examples:
    
    >>> polysubmodp([1,2,3], [4,5,6], 7)
    [4, 4, 4]
    
    >>> polysubmodp([1,2,3], [6,5,10], 7)
    [2, 4]
    """
    if a is None or b is None: return None
    c = [(x-y) % p for (x,y) in zip_longest(a, b, fillvalue=0)]
    while len(c) > 0 and c[-1] == 0: del c[-1]
    return c

def polymulmodp(a, b, p):
    """
    Multiplies the polynomials a and b and reduces their coefficients mod p.
    
    Polynomials are written as lists of integers with the constant terms
    first.  If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If one of the input
    polynomials is None, then we return None.
    
    Input:
        a, b -- polynomials
        p -- integer
    
    Output: A polynomial.
    
    Examples:
    
    >>> polymulmodp([1,2,3], [4,5,6], 7)
    [4, 6, 0, 6, 4]
    
    >>> polymulmodp([2,2], [3,3,3], 6)
    []
    """
    if a is None or b is None: return None
    c = [0]*(len(a)+len(b)-1)
    for (k,x) in enumerate(a):
        for (l,y) in enumerate(b):
            c[k+l] += x*y
    for (k,x) in enumerate(c): c[k] = x % p
    while len(c) > 0 and c[-1] == 0: del c[-1]
    return c

def polydivmodmodp(a, b, p):    # TODO: Convert the recursion to iteration.  Also, optimize.
    """
    Divides the polynomial a by the polynomial b and returns the quotient
    and remainder.  The coefficients are interpreted mod p.
    
    Polynomials are written as lists of integers with the constant terms
    first.  If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If an input polynomial is
    None, or if b == [], then we return (None, None).  The result is not
    guaranteed to exist; in such cases, we return (None, None).
    
    Input:
        a, b -- polynomials
        p -- integer
    
    Output: a tuple of two polynomials (quotient, remainder)
    
    Examples:
    
    >>> polydivmodmodp([1,4,6,4,1], [1,2,1], 7)
    ([1, 2, 1], [])
    
    >>> polydivmodmodp([4,5,6,4,1], [1,2,1], 7)
    ([1, 2, 1], [3, 1])
    
    >>> polydivmodmodp([4,5,6,4,1], [1,2,2], 8)
    (None, None)
    """
    if a is None or b is None or b == []: return (None, None)
    ndeg, ddeg = len(a)-1, len(b)-1
    if ndeg < ddeg: return ([], a[:])
    num, den = a[:], b[:]
    div = gcd(b[-1], p)
    if div != 1: return (None, None)
    c = pow(b[-1], -1, p)  # No ValueErrors here thanks to the previous line.
    term = [0]*(ndeg-ddeg) + [(num[-1]*c) % p]
    newnum = polysubmodp(num, polymulmodp(den, term, p), p)
    quo, rem = polydivmodmodp(newnum, den, p)
    quo = polyaddmodp(term, quo, p)
    while len(quo) > 0 and quo[-1] == 0: del quo[-1]
    while len(rem) > 0 and rem[-1] == 0: del rem[-1]
    #assert polysubmodp(polyaddmodp(polymulmodp(quo, b, p), rem, p), a, p) == [], (a, b, p, quo, rem)
    return (quo, rem)

def gcmd(f, g, p):   # CranPom 2.2.1
    """
    Computes the greatest common monic divisor of the polynomials f and g.
    The coefficients are interpreted mod p.
    
    Polynomials are written as lists of integers with the constant terms
    first.  If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If one of the input
    polynomials is None, then we return (None, None).  The result is not
    guaranteed to exist; in such cases, we return (None, None).
    
    Polynomials are written as lists of integers with the constant terms
    first. If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If an input polynomials is
    None, or if both input polynomials are [], then we return None.  The
    result is not guaranteed to exist; in such cases, we return None.
    
    Input:
        f, g -- polynomials
        p -- integer
    
    Output: A polynomial.
    
    Examples:
    
    >>> gcmd([1,4,6,4,1], [2,3,1], 7)
    [1, 1]
    
    >>> gcmd([1,6,4,3,7], [1,5,2,4], 8) is None
    True
    """
    if (f is None) or (g is None) or f == [] == g: return None
    df, dg = len(f)-1, len(g)-1
    if dg > df: u, v = g[:], f[:]
    else:       u, v = f[:], g[:]
    while v != []:
        r = polydivmodmodp(u, v, p)[1]
        if r is None: return None
        u, v = v[:], r
    div = gcd(u[-1], p)
    if div != 1: return None
    c = pow(u[-1], -1, p)   # No ValueErrors here thanks to the previous line.
    return [(x*c)%p for x in u]

def polypowmodpmodpoly(a, e, p, f): # a**e mod p mod f
    """
    Computes the remainder when the polynomial a is raised to the eth power
    and reduced modulo f.  The coefficients are interpreted mod p.
    
    Polynomials are written as lists of integers with the constant terms
    first.  If the high-degree coefficients are zero, then those terms will
    be deleted from the answer so that the highest-degree term is nonzero.
    We assume that the inputs also satisfy this property.  The zero
    polynomial is represented by the empty list.  If an input polynomials is
    None, or if f == [], then we return None.  The answer is not guaranteed
    to exist.  In such cases, we return None.
    
    Input:
        a, f -- polynomials
        e, p -- integers
    
    Output: A polynomial.
    
    Examples:
    
    >>> polypowmodpmodpoly([1,1], 101, 7, [1,2,3,4,5])
    [1, 6, 0, 2]
    
    >>> polypowmodpmodpoly([1,1], 101, 15, [1,2,3,4,5]) is None
    True
    """
    if a is None or f is None or f == []: return None
    ans, a = [1], polydivmodmodp(a, f, p)[1]
    for k in bin(e)[2:]:
        ans = polydivmodmodp(polymulmodp(ans, ans, p), f, p)[1]
        if k == '1': ans = polydivmodmodp(polymulmodp(ans, a, p), f, p)[1]
    return ans

def frobenius_prp(n, poly, strong=False):
    """
    Grantham's general Frobenius probable primality test, both strong and
    weak versions, as described in doi.org/10.1090/S0025-5718-00-01197-2.
    
    Input:
        n -- integer.  The number to be tested.
        poly -- the polynomial to test n against, represented as the list
                of its coefficients in order of increasing degree.  The
                leading coefficient must be 1.  For example, to test against
                the polynomial x^3 + 2x^2 + 3x + 4, use [4, 3, 2, 1].
        strong -- True or False.  If True, then we do the strong test.
    
    Output: True or False.
    
    Examples:
    
    >>> pseuds = [911*2731,1087*3259,1619*6473,1031*10301,2003*6007,883*25579]
    
    >>> [frobenius_prp(n, [-1, 1, 0, 1], strong=False) for n in pseuds]
    [False, False, True, True, False, False]
    
    >>> [frobenius_prp(n, [-1, 1, 0, 1], strong=True) for n in pseuds]
    [False, False, True, False, False, False]
    
    >>> [frobenius_prp(n, [-1, 1, 1, 1], strong=False) for n in pseuds]
    [True, True, False, False, True, True]
    
    >>> [frobenius_prp(n, [-1, 1, 1, 1], strong=True) for n in pseuds]
    [True, True, False, False, True, False]
    
    >>> frobenius_prp(factorial(38)-1, [-1, 1, 0, 1])
    True
    
    >>> frobenius_prp(factorial(38)+1, [-1, 1, 0, 1])
    False
    """
    # Input is a monic polynomial.
    # Let f(x) in Z[x] be a monic polynomial of degree d with discriminant D.  An odd integer > 1 is said to pass the Frobenius
    # PRP test wrt f(x) if gcd(n, f(0)*D) == 1 and it is declared to be a PRP by the following algorithm.  (Such an integer will
    # be called a Frobenius PRP wrt f(x).)  All computations are done in (Z/nZ)[x].
    if n % 2 == 0: return n == 2
    f = [k % n for k in poly]
    g = gcd(n, f[0])
    d = len(f) - 1
    if 1 < g < n: return False
    assert g == 1, (n, poly, D) # If this fails, then the number being checked divides the constant term.
    D = discriminant(f)
    g = gcd(n, D)
    if 1 < g < n: return False
    assert g == 1, (n, poly, D) # If this fails, then the number being checked divides the discriminant.
    # Factorization step: Let f_0(x) = f(x) mod n.  For 1 <= i <= d, let F_i(x) = gcmd(x^(n^i)-x, f_(i-1)(x)) and
    # f_i(x) = f_(i-1)(x)/F_i(x).  If any of the gcmds fails to exist, declare n to be composite and stop.
    # If f_d(x) != 1, declare n to be composite.
    flist = [f[:]]
    Flist = [None]
    for i in range(1, d+1):
        powpoly = polysubmodp(polypowmodpmodpoly([0,1], n**i, n, flist[i-1]), [0,1], n)
        if powpoly is None: return False
        F = gcmd(powpoly, flist[i-1], n)
        if F is None: return False
        Flist.append(F)
        quo, rem = polydivmodmodp(flist[i-1], F, n)
        assert rem == []
        flist.append(quo)
    if flist[-1] != [1]: return False
    # Frobenius step: For 2 <= i <= d, compute F_i(x^n) mod F_i(x).  If it is nonzero for some i, declare n to be composite.
    for i in range(2, d+1):
        Fix = Flist[i]
        Fixn = []
        for (j,k) in enumerate(Fix): Fixn = polyaddmodp(Fixn, polymulmodp(polypowmodpmodpoly([0,1], j*n, n, Fix), [k], n), n)
        Fixn = polydivmodmodp(Fixn, Fix, n)[1]
        if Fixn != []: return False
    # Jacobi step: Let S = $\sum_{2|i} deg(F_i(x))/i$.  If (-1)^S != jacobi(D, n), declare n to be composite.
    # If n is not yet declared composite, then it is a Frobenius PRP.
    S = 0
    for (i,Fi) in enumerate(Flist):
        if i % 2 == 1 or i == 0: continue
        Fid = len(Fi) - 1
        assert Fid % i == 0
        S += Fid//i
    if (-1)**S != jacobi(D, n): return False
    # If we get to this point, then n is a Frobenius PRP.
    if not strong: return True
    # Square root step: For each 1 <= i <= d, let n^i-1 = 2^r * s with s odd.  Let F_(i,0)(x) = gcmd(F_i(x),x^s-1) and let
    # F_(i,j) = gcmd(F_i(x), x^(2^(j-1)*s)+1).  Then if F_i(x) != $\prod_{j=0}^r F_{i,j}(x)$, if for some j the degree of
    # F_(i,j)(x) is not a multiple of i, or if one of the gcmds fails to exist, declare n to be composite and terminate.
    for i in range(1, d+1):
        s = n**i - 1
        r = (s & (-s)).bit_length() - 1     # number of trailing zeros of s in binary
        s >>= r                             # the odd part of s
        # Note that the source article (under the heading "Square Root Step") says that r should be odd.  This seems rather
        # weird, and is in fact wrong, as shown by experiment and the fact that Theorem 5.1 immediately above indicates that
        # it is s that should be odd.
        assert n**i - 1 == 2**r * s
        Fi = Flist[i]
        Filist = [gcmd(Fi, polysubmodp(polypowmodpmodpoly([0,1], s, n, Fi), [1], n), n)]
        for j in range(1, r+1): Filist.append(gcmd(Fi, polyaddmodp(polypowmodpmodpoly([0,1], s<<(j-1), n, Fi), [1], n), n))
        if any(Fij is None for Fij in Filist): return False                 # ... if one of the gcmds fails to exist
        if any((len(Fij)-1) % i != 0 for Fij in Filist): return False       # ... if for some j, deg(Fij) is not a multiple of i
        Filistprod = [1]
        for Fij in Filist: Filistprod = polymulmodp(Filistprod, Fij, n)
        if Fi != Filistprod: return False                                   # ... if F_i(x) != $\prod_{j=0}^r F_{i,j}(x)$
    # If we get to this point, then n is a strong Frobenius PRP.
    return True

def isprime(n, tb=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59)): # TODO optimize the basis, possibly by varying it with n
    """
    This a variant of the BPSW primality test: we use the strong Lucas PRP
    test and preface the computation with trial division for speed.  No
    composites are known to pass the test, though it is suspected that
    infinitely many will do so.  It is known that there are no such errors
    below 2^64.  This function is mainly a streamlined version of bpsw().
    
    This is this library's default primality test.
    
    Input:
        n -- integer.  Number to be examined.
        tb -- iterable of primes.  Basis for trial division.
    
    Output: True if probably prime; False if definitely composite.
    
    Examples:
    
    >>> [n for n in range(90) if isprime(1000*n+1)]
    [3, 4, 7, 9, 13, 16, 19, 21, 24, 28, 51, 54, 55, 61, 69, 70, 76, 81, 88]
    
    >>> [isprime(factorial(38)+1), isprime(factorial(38)-1)]
    [False, True]
    """
    # 1.  Do some trial division with tb as the basis.
    if n % 2 == 0 or n < 3: return n == 2
    for p in tb:
        if n % p == 0: return n == p
    
    # 2.  If sprp(n,2) fails, return False.  If it succeeds, continue.
    s = ((n - 1) & (1 - n)).bit_length() - 1    # number of trailing zeros of n-1 in binary
    t = (n - 1) >> s                            # the odd part of n-1
    #assert 1 + 2**s * t == n
    x = pow(2, t, n)
    if x != 1 and x != n - 1:
        for j in range(1, s):
            x = pow(x, 2, n)
            if x == 1: return False
            elif x == n - 1: break
        else: return False
    
    # 3.  Select parameters for slprp.
    for D in count(5, 4):
        j = jacobi(D, n)
        if j == 0: return D == n
        if j == -1: break
        D = -2 - D
        j = jacobi(D, n)
        if j == 0: return -D == n
        if j == -1: break
        if D == -13 and ispower(n,2): return False      # If n is square, then this loop amounts to very slow trial division.
    
    # Now run slprp(n, 1, (1 - D) // 4) and return the result.
    b = (1 - D) // 4
    if 1 < gcd(n, b) < n: return False
    s = ((n+1) & (-n-1)).bit_length() - 1       # the number of trailing zeros of n+1 in binary
    t = (n+1) >> s                              # the odd part of n+1
    v, w, q, Q = 2, 1, 1, 1
    for k in bin(t)[2:]:
        q = (q*Q) % n
        if k == '1': Q, v, w = (q*b) % n, (w*v - q) % n, (w*w - 2*q*b) % n
        else:        Q, w, v =  q       , (w*v - q) % n, (v*v - 2*q  ) % n
    # assert ( (2*w-v) * modinv(D,n) ) % n, v == lucasmod(t, 1, b, n)
    # If gcd(D,n) were 0, then we would have returned during stage 3, so the pow in the next line will not raise a ValueError.
    if v == 0 or ( (2*w-v) * pow(D,-1,n) ) % n == 0: return True
    q = pow(b, t, n)
    for _ in range(1, s):
        v = (v*v - 2*q) % n
        if v == 0: return True
        q = (q*q) % n
    return False

def isprimepower(n):
    """
    If n is of the form p**e for some prime number p and positive integer e,
    then we return (p,e).  Otherwise, we return None.
    
    Input: An integer.
    
    Output: None or a 2-tuple of integers.
    
    Examples:
    
    >>> [isprimepower(n) for n in range(6, 11)]
    [None, (7, 1), (2, 3), (3, 2), None]
    """
    if n <= 1 or not isinstance(n, inttypes): return None
    x = ispower(n)
    if x is None: return (n,1) if isprime(n) else None
    assert isinstance(x, tuple)
    assert len(x) == 2
    ipp = isprimepower(x[0])
    return None if ipp is None else (ipp[0], x[1]*ipp[1])

def nextprime(n, primetest=isprime):           # TODO: we can do better than this.
    """
    Computes the smallest prime strictly greater than n.
    
    Input:
        n -- an integer
        primetest -- boolean function.  Default == isprime.
    
    Output: An integer
    
    Examples:
    
    >>> [nextprime(n) for n in (0,1,2,3,4,5,6,7,540,1425172824437699411)]
    [2, 2, 3, 5, 5, 7, 7, 11, 541, 1425172824437700887]
    
    >>> nextprime(factorial(38)+1)
    523022617466601111760007224100074291200000043
    """
    if n < 2: return 2
    if n == 2: return 3
    n = (n + 1) | 1    # first odd larger than n
    m = n % 6
    if   m == 5:
        if primetest(n  ): return n
        n += 2
    elif m == 3:
        if primetest(n+2): return n+2
        n += 4
    for m in count(n, 6):
        if primetest(m  ): return m
        if primetest(m+4): return m+4

def prevprime(n, primetest=isprime):           # TODO: we can do better than this.
    """
    Computes the largest prime strictly less than n,
    or None if no such prime exists.
    
    Input:
        n -- an integer or None
        primetest -- boolean function.  Default == isprime.
    
    Output: An integer or None
    
    Examples:
    
    >>> [prevprime(n) for n in [0, 1, 2, 3, 4, 5, 6, 7, 540]]
    [None, None, None, 2, 3, 3, 5, 5, 523]
    
    >>> prevprime(factorial(38))
    523022617466601111760007224100074291199999999
    """
    if n <= 13: return [0,0,0,2,3,3,5,5,7,7,7,7,11,11][n] if n > 2 else None
    N = n
    if n % 2 == 0: n -= 1
    else: n -= 2
    # n is now the largest odd < the input.
    m = n % 6
    if m == 5:
        if primetest(n): return n
        n -= 4
    elif m == 3: n -= 2
    for m in count(n-6, -6):
        if primetest(m+6): return m+6
        if primetest(m+4): return m+4

def randprime(digits, base=10):
    """
    Returns a random prime with the specified number of digits when rendered
    in the specified base.  The primes are selected uniformly among all
    primes of the indicated size.
    
    Input:
        digits -- a positive integer
        base -- base in which the output is to have
                the specified number of digits
        primetest -- Function.  Default == isprime.
    
    Output: A prime integer that, when rendered in the specified base,
            has the specified number of digits.
    
    Examples:
    
    >>> x = randprime(20)
    
    >>> len(str(x))
    20
    
    >>> isprime(x)
    True
    """
    if (digits,base) == (1,2): return None
    n, lo = 0, base**(digits-1)
    hi = lo * base
    while not isprime(n): n = randrange(lo, hi)
    return n

def randomfactored(n, method="kalai"):
    """
    Efficiently generates a factored integer in the range [1,n] or (n/2,n],
    selected at random with a uniform probability distribution.
    
    Both Bach's and Kalai's algorithms are implemented.  If Bach's algorithm
    is selected, then the integer is in the interval (n/2, n].  This
    algorithm uses O(log(n)) primality tests.  If Kalai's algorithm is
    selected, then the integer is in the interval [1,n], and O(log(n)^2)
    primality tests are used.
    
    Input:
        n -- integer
        method -- "bach" or "kalai" (default).
    
    Output: 2-tuple.  The first element is the generated integer, and the
            second is its factorization in factorint format.
    """
    assert n > 0 and isinstance(n, inttypes)
    if method == "kalai":
        while True:
            r, ps, x = 1, [], n
            while r <= n:
                x = randrange(1, x+1)
                if x == 1:
                    if randrange(1, n+1) > r: break
                    fac = {}
                    for p in ps: fac[p] = fac.get(p, 0) + 1
                    return (r, fac)
                if isprime(x): r *= x; ps.append(x)
    if method == "bach":
        if n <= 10**6:
            x = randrange(n//2 + 1, n + 1)
            return (x, factorint(x))
        while True:
            while True:
                j = 2**randrange(1, n.bit_length())
                q = j + randrange(j)
                if q > n: continue
                pe = isprimepower(q)
                if pe is None: continue
                hi = n // q
                if random() * log(n, pe[0]) * n < (hi - (hi//2)) * j: break
            x, fac = randomfactored(n // q, method="bach")
            x *= q
            p, e = pe
            fac[p] = fac.get(p,0) + e
            if random() < log(n/2, x): return (x,fac)

def sqrtmod_prime(a, p):
    """
    Solves x**2 == a (mod p) for x.  We assume that p is a prime and a is a
    quadratic residue modulo p.  If either of these assumptions is false,
    the return value is meaningless.
    
    We do not make any guarantees about which square root will be returned.
    
    The Cipolla-Lehmer section is my own.  The rest appears to be derived
    from https://codegolf.stackexchange.com/a/9088.
    
    Input:
        a -- natural number
        p -- prime number
    
    Output: whole number less than p
    
    Examples:
    
    >>> sqrtmod_prime(4, 5)
    3
    
    >>> sqrtmod_prime(13, 23)
    6
    
    >>> sqrtmod_prime(997, 7304723089)
    761044645
    """
    a %= p
    if p%4 == 3: return pow(a, (p+1) >> 2, p)
    elif p%8 == 5:
        v = pow(a << 1, (p-5) >> 3, p)
        return (a*v*(((a*v*v<<1)%p)-1))%p
    elif p%8 == 1:
        # CranPom ex 2.31, pg 112 / 126.  Pretty sure this amounts to Cipolla-Lehmer.
        if a == 0: return 0     # Necessary to avoid an infinite loop in the legendre section
        h = 2
        while legendre(h*h - 4*a, p) != -1: h += 1
        #return ( lucasmod((p+1)//2, h, a, p)[1] * modinv(2, p) ) % p
        k, v, w, q, Q = (p+1)//2, 2, h % p, 1, 1
        for kj in bin(k)[2:]:
            q = (q*Q) % p
            if kj == '1': Q, v, w = (q*a) % p, (w*v - h*q) % p, (w*w - 2*q*a) % p
            else:         Q, w, v =  q       , (w*v - h*q) % p, (v*v - 2*q  ) % p
        return (v*k) % p
    else: return a # p == 2

def cbrtmod_prime(a, p):
    """
    Returns, in a sorted list, all cube roots of a mod p.
    
    There are a bunch of easily-computed special formulae for various cases
    with p != 1 (mod 9); we do those first, and then if p == 1 (mod 9) then
    we use Algorithm 4.2 in "Taking Cube Roots in Zm" by Padro and Saez,
    Applied Mathematics Letters 15 (2002) 703-708,
    https://doi.org/10.1016/S0893-9659(02)00031-9, which is essentially
    a variation on the Tonelli-Shanks algorithm for modular square roots.
    
    Input: a, p -- Integers.  We assume that p is prime.
    
    Output: List of integers.
    
    Examples:
    
    >>> [cbrtmod_prime(a,11) for a in range(11)]
    [[0], [1], [7], [9], [5], [3], [8], [6], [2], [4], [10]]
    
    >>> [cbrtmod_prime(a,19) for a in range(11)]
    [[0], [1, 7, 11], [], [], [], [], [], [4, 6, 9], [2, 3, 14], [], []]
    """
    a %= p
    if a == 0 or p == 2 or p == 3: return [a % p]
    if p % 3 == 2: return [pow(a, (2*p-1)//3, p)]
    assert a != 0 and p % 3 == 1
    crs = pow(a, (p-1)//3, p)   # Cubic residue symbol.  There will be roots iff it is 1.
    if crs != 1: return []
    # There will be three roots.  Find one, and then compute the others by using a nontrivial root of unity.
    if p%9 != 1:    # There are simple formulae for the p == 4 and p == 7 mod 9 cases and for a nontrivial cube roots of unity.
        # We already handled the p == 2 case, so the pow in the next line will not throw a ValueError.
        x, c = pow(a, (2*p+1)//9, p) if p%9 == 4 else pow(a, (p+2)//9, p), ( (-1 + sqrtmod_prime(-3, p)) * pow(2, -1, p) ) % p
        return sorted((x, (x*c)%p, (x*c*c)%p))
    e, q = 2, (p-1)//9
    while q % 3 == 0: q //= 3; e += 1
    # 1: Find h in Zp at random such that [h/p] != 1 mod p.
    for h in count(2):
        if pow(h, (p-1)//3, p) != 1: break
    # 2: Initialize.
    y = g = pow(h, q, p)
    r, s, x = e, pow(g, 3**(e-1), p), pow(a, (((-q)%3)*q-2)//3, p)
    b, x = ( pow(a*x, 2, p) * x ) % p, (a*x) % p
    # 3
    while b % p != 1:
        for m in count():
            if pow(b, 3**m, p) == 1: break
        #if m == r: return [] # Our special cases above prevent this from happening.
        # 4: Reduce exponent.
        if s == pow(b, 3**(m-1), p): t, s = pow(y, 2, p), pow(s, 2, p)
        else:                        t = y
        t = pow(t, 3**(r-m-1), p)
        y = pow(t, 3, p)
        r, x, b = m, (x * t) % p, (b * y) % p
        # Goto 3.
    return sorted((x, (x*s) % p, (x*s*s) % p))

def pollardrho_brent(n):
    """
    Factors integers using Brent's variation of Pollard's rho algorithm.  If
    n is prime, then we immediately return n; if not, we keep chugging until
    a nontrivial factor is found.  This function calls the randomizer; two
    successive calls may therefore return two different results.
    
    Input: n -- number to factor
    
    Output: A factor of n.
    
    Examples:
    >>> n = factorial(20)+1
    >>> f = pollardrho_brent(n)
    >>> f in (20639383, 117876683047)
    True
    """
    if isprime(n): return n
    g = n
    while g == n:
        y, c, m, g, r, q = randrange(1, n), randrange(1, n), randrange(1, n), 1, 1, 1
        while g==1:
            x, k = y, 0
            for i in range(r): y = (y**2 + c) % n
            while k < r and g == 1:
                ys = y
                for i in range(min(m, r-k)):
                    y = (y**2 + c) % n
                    q = q * abs(x-y) % n
                g, k = gcd(q, n), k+m
            r *= 2
        if g==n:
            while True:
                ys = (ys**2+c)%n
                g = gcd(x-ys, n)
                if g > 1: break
    return g

def pollard_pm1(n, B1=100, B2=1000):       # TODO: What are the best default bounds and way to increment them?
    """
    Integer factoring function.  Uses Pollard's p-1 algorithm.  Note that
    this is only efficient if the number to be factored has a prime factor p
    such that p-1's largest prime factor is "small".  In this
    implementation, that tends to mean less than 10,000,000 or so.
    
    Input:
        n -- number to factor
        B1 -- Natural number.  Bound for phase 1.  Default == 100.
        B2 -- Natural number > B1.  Bound for phase 2.  Default == 1000.
    
    Output: A factor of n.
    
    Examples:
    
    >>> pollard_pm1((factorial(28) - 1) // 239)
    1224040923709997
    """
    if isprime(n): return n
    m = ispower(n)
    if m: return m[0]
    while True:
        pg = primegen()
        q = 2           # TODO: what about other initial values of q?
        p = next(pg)
        while p <= B1: q, p = pow(q, p**ilog(B1, p), n), next(pg)
        g = gcd(q-1, n)
        if 1 < g < n: return g
        while p <= B2: q, p = pow(q, p, n), next(pg)
        g = gcd(q-1, n)
        if 1 < g < n: return g
        # These bounds failed.  Increase and try again.
        B1 *= 10
        B2 *= 10

def _mlucas(v, a, n):
    # Helper for williams_pp1().  Multiplies along a Lucas sequence mod n.
    v1, v2 = v, (v**2 - 2) % n
    for bit in bin(a)[3:]: v1, v2 = ((v1**2 - 2) % n, (v1*v2 - v) % n) if bit == "0" else ((v1*v2 - v) % n, (v2**2 - 2) % n)
    return v1
def williams_pp1(n):      # TODO: experiment with different values of v0, and implement the two-phase version
    """
    Integer factoring function.  Uses Williams' p+1 algorithm, single-stage
    variant.  Note that this is only efficient when the number to be
    factored has a prime factor p such that p+1's largest prime factor is
    "small".
    
    Input: n -- integer to factor
    
    Output: Integer.  A nontrivial factor of n.
    
    Example:
    
    >>> williams_pp1(315951348188966255352482641444979927)
    12403590655726899403
    """
    if isprime(n): return n
    m = ispower(n)
    if m: return m[0]
    for v in count(3):
        for p in primegen():
            e = ilog(isqrt(n), p)
            if e == 0: break
            for _ in range(e): v = _mlucas(v, p, n)
            g = gcd(v - 2, n)
            if 1 < g < n: return g
            if g == n: break

def _ecadd(p1, p2, p0, n):
    # Helper for ecm().  Adds two points on a Montgomery curve mod n.
    x1,z1 = p1; x2,z2 = p2; x0,z0 = p0
    t1, t2 = (x1-z1)*(x2+z2), (x1+z1)*(x2-z2)
    return (z0*pow(t1+t2,2,n) % n, x0*pow(t1-t2,2,n) % n)
def _ecdub(p, A, n):
    # Helper for ecm().  Doubles a point on a Montgomery curve mod n.
    x, z = p; An, Ad = A
    t1, t2 = pow(x+z,2,n), pow(x-z,2,n)
    t = t1 - t2
    return (t1*t2*4*Ad % n, (4*Ad*t2 + t*An)*t % n)
def _ecmul(m, p, A, n):
    # Helper for ecm().  Multiplies a point on a Montgomery curve mod n.
    if m == 0: return (0, 0)
    elif m == 1: return p
    else:
        q = _ecdub(p, A, n)
        if m == 2: return q
        b = 1
        while b < m: b *= 2
        b //= 4
        r = p
        while b:
            if m&b: q, r = _ecdub(q, A, n), _ecadd(q, r, p, n)
            else:   q, r = _ecadd(r, q, p, n), _ecdub(r, A, n)
            b //= 2
        return r
def secm(n, B1, B2, seed):
    """
    Seeded ECM.  Helper function for ecm().  Returns a possibly-trivial
    divisor of n given two bounds and a seed.  Uses the two-phase algorithm
    on Montgomery curves.  See https://wp.me/prTJ7-zI and
    https://wp.me/prTJ7-A7 for more details.  Most of the code for this
    function's "helpers" were copied from the first of those links.
    
    Input:
        n -- Integer to factor
        B1 -- Integer.  Number of iterations for the first phase.
        B2 -- Integer.  Number of iterations for the second phase.
        seed -- Integer.  Selects the specific curve we will be working on.
    
    Output: Integer.  A possibly-trivial factor of n.
    
    Examples:
    
    >>> secm(factorial(24)-1, 100, 1000, 22)
    991459181683
    """
    u, v = (seed**2 - 5) % n, 4*seed % n
    p = pow(u, 3, n)
    Q, C = (pow(v-u,3,n)*(3*u+v) % n, 4*p*v % n), (p, pow(v,3,n))
    pg = primegen()
    p = next(pg)
    while p <= B1: Q, p = _ecmul(p**ilog(B1, p), Q, C, n), next(pg)
    g = gcd(Q[1], n)
    if 1 < g < n: return g
    while p <= B2:
        # There is a trick that can speed up the second stage.  Instead of multiplying each prime by Q, we iterate over i from
        # B1 + 1 to B2, adding 2Q at each step; when i is prime, the current Q can be accumulated into the running solution.
        # Again, we defer the calculation of the GCD until the end of the iteration.    TODO: Implement and compare performance.
        Q = _ecmul(p, Q, C, n)
        g *= Q[1]
        g %= n
        p = next(pg)
    return gcd(g, n)
def ecmparams(n):   # TODO: Better parameters.
    counter = 0
    for i in count():
        for _ in range(2*i+1):
            yield (2**i, 10 * 2**i, randrange(6,n), counter)
            counter += 1
        for j in range(i+1):
            yield (2**j, 10 * 2**j, randrange(6,n), counter)
            counter += 1
def ecm(n, paramseq=ecmparams, nprocs=1):
    """
    "Modern" integer factoring via elliptic curves.  Uses Montgomery curves,
    the two-phase algorithm, and (optionally) multiple processes.  The hard
    work is done by secm(); this function just does the managerial work of
    pulling a sequence of parameters out of a generator and feeding them
    into secm().
    
    Input:
        n -- number to factor
        paramseq -- sequence of parameters to feed into secm().  It must be
                    an infinite generator of 4-tuples (a,b,c,d), where a is
                    the number of iterations for the first phase, b is the
                    number of iterations for the second phase, c is a seed
                    to select the curve to work on, and d is an auxiliary
                    used to count the parameters generated so far.  We need
                    a < b and 6 <= c < n.
        nprocs -- number of processes to use.  Default == 1.  Setting this >
                  1 is discouraged on "small" inputs because managing
                  multiple processes incurs significant overhead.
    
    Output:
        A factor of n.
        Note that if the parameter sequence calls the randomizer (which is
        currently the default behavior), then two identical calls may return
        two different results.
    
    Examples:
    
    >>> n = factorial(24) - 1
    >>> f = ecm(n)
    >>> f in (625793187653, 991459181683)
    True
    """
    g = n % 6
    if g % 2 == 0: return 2
    if g % 3 == 0: return 3
    if isprime(n): return n
    m = ispower(n)
    if m: return m[0]
    if nprocs == 1:
        for (B1,B2,seed,i) in paramseq(n):
            f = secm(n, B1, B2, seed)
            if 1 < f < n: return f
        return None
    assert nprocs != 1
    def factory(params, output): output.put(secm(*params))
    ps, facs, procs = paramseq(n), mpQueue(), []
    procs = [Process(target=factory, args=((n,)+next(ps)[:3], facs)) for _ in range(nprocs)]
    for p in procs: p.start()
    while True:
        g = facs.get()
        if 1 < g < n:
            for p in procs: p.terminate()
            return g
        for p in range(nprocs):                                                      # TODO: Try doing this with a process pool.
            if not procs[p].is_alive():
                del procs[p]
                break
        procs.append(Process(target=factory, args=((n,)+next(ps)[:3], facs)))
        procs[-1].start()

def siqs(n):
    """
    Uses the Self-Initializing Quadratic Sieve to extract a factor of n.  We
    use the randomizer, so the output may change from call to call.  This
    is derived from https://github.com/skollmann/PyFactorise.
    
    Input: n -- number to factor
    
    Output:
        If n is prime, we return n.
        If n is composte, we return a nontrivial factor of n.
    
    Examples:
    
    >>> siqs(factorial(24) - 1) in (625793187653, 991459181683)
    True
    """
    
    if (not isinstance(n, inttypes)) or n < 0: raise ValueError("Number must be a positive integer.")
    
    if n < 2**64: return pollardrho_brent(n)
    
    if isprime(n): return n
    
    perfect_power = ispower(n)
    if perfect_power: return perfect_power[0]
    
    # Choose parameters nf (sieve of factor base) and m (for sieving in [-m,m]).
    # Using similar parameters as msieve-1.52
    dig = len(str(n))
    if   dig <= 34: nf, m = 200, 65536
    elif dig <= 36: nf, m = 300, 65536
    elif dig <= 38: nf, m = 400, 65536
    elif dig <= 40: nf, m = 500, 65536
    elif dig <= 42: nf, m = 600, 65536
    elif dig <= 44: nf, m = 700, 65536
    elif dig <= 48: nf, m = 1000, 65536
    elif dig <= 52: nf, m = 1200, 65536
    elif dig <= 56: nf, m = 2000, 65536 * 3
    elif dig <= 60: nf, m = 4000, 65536 * 3
    elif dig <= 66: nf, m = 6000, 65536 * 3
    elif dig <= 74: nf, m = 10000, 65536 * 3
    elif dig <= 80: nf, m = 30000, 65536 * 3
    elif dig <= 88: nf, m = 50000, 65536 * 3
    elif dig <= 94: nf, m = 60000, 65536 * 9
    else:           nf, m = 100000, 65536 * 9
    
    class FactorBasePrime:
        """A factor base prime for the SIQS"""
        def __init__(self, p, tmem, lp):
            self.p, self.soln1, self.soln2, self.tmem, self.lp, self.ainv = p, None, None, tmem, lp, None
    
    # Compute and return nf factor base primes suitable for a SIQS on n.
    factor_base = []
    for p in primegen():
        if pow(n, (p-1) >> 1, p) == 1:          # if n is a quadratic residue mod p
            t = sqrtmod_prime(n, p)
            lp = round(log2(p))                 # This gets rounded for the sake of speed.
            factor_base.append(FactorBasePrime(p, t, lp))
            if len(factor_base) >= nf: break
    
    npolys, i_poly, prev_cnt, relcount, smooth_relations, required_relations_ratio = 0, 0, 0, 0, [], 1.05
    
    p_min_i, p_max_i = None, None
    for (i,fb) in enumerate(factor_base):
        if p_min_i is None and fb.p >= 400:                                            # 400 is a tunable parameter.
            p_min_i = i
        if p_max_i is None and fb.p > 4000:                                           # 4000 is a tunable parameter.
            p_max_i = i - 1
            break
    
    # The following may happen if the factor base is small, make sure that we have enough primes.
    if p_max_i is None: p_max_i = len(factor_base) - 1
    if p_min_i is None or p_max_i - p_min_i < 20: p_min_i = min(p_min_i, 5)    # TODO This line is problematic for some small n.
    
    target = sqrt(2 * float(n)) / m
    target1 = target / sqrt((factor_base[p_min_i].p + factor_base[p_max_i].p) / 2)
    
    while True:
        
        required_relations = round(nf * required_relations_ratio)
        enough_relations = False
        while not enough_relations:
            
            # BEGIN POLYNOMIAL SELECTION
            if i_poly == 0: # Compute the first of a set of polynomials
                # find q such that the product of factor_base[q_i] is about sqrt(2n)/m; try a few sets to find a good one
                best_q, best_a, best_ratio = None, None, None
                for _ in range(30):
                    a, q = 1, []
                    
                    while a < target1:
                        p_i = 0
                        while p_i == 0 or p_i in q: p_i = randrange(p_min_i, p_max_i+1)
                        a *= factor_base[p_i].p
                        q.append(p_i)
                    
                    ratio = a / target
                    
                    # ratio too small seems to be not good
                    if (best_ratio is None or (ratio >= 0.9 and ratio < best_ratio) or best_ratio < 0.9 and ratio > best_ratio):
                        best_q, best_a, best_ratio = q, a, ratio
                a, q = best_a, best_q
                
                s, B = len(q), []
                for l in range(s):
                    fb_l = factor_base[q[l]]
                    q_l = fb_l.p
                    assert a % q_l == 0
                    # a is a squarefree product of primes in the factor base.  Dividing out q_l guarantees that the result is
                    # coprime to q_l, so the pow in the next line will not raise a ValueError.
                    gamma = (fb_l.tmem * pow(a // q_l, -1, q_l)) % q_l
                    if gamma > q_l // 2: gamma = q_l - gamma
                    B.append(a // q_l * gamma)
                
                b = sum(B) % a
                b_orig = b
                if (2 * b > a): b = a - b
                
                assert 0 < b and 2 * b <= a and (b * b - n) % a == 0
                
                g1, g2, g3, ga, gb = b * b - n, 2 * a * b, a * a, a, b_orig
                ha, hb = a, b
                for fb in factor_base:
                    if a % fb.p != 0:
                        fb.ainv = pow(a, -1, fb.p)  # No ValueErrors here: a is guaranteed nonzero mod fb.p by the if-statement.
                        fb.soln1 = (fb.ainv * (fb.tmem - b)) % fb.p
                        fb.soln2 = (fb.ainv * (-fb.tmem - b)) % fb.p
            
            else: # Compute the (i+1)-th polynomial, given that g is the i-th polynomial.
                #v = lowest_set_bit(i) + 1
                #z = -1 if ceil(i / (2 ** v)) % 2 == 1 else 1
                z = -1 if ceil(i_poly / (1 + (i_poly ^ (i_poly-1)))) % 2 == 1 else 1
                #b = (g.b + 2 * z * B[v - 1]) % g.a
                b = (gb + 2 * z * B[(i_poly & (-i_poly)).bit_length() - 1]) % ga
                a = ga
                b_orig = b
                if (2 * b > a): b = a - b
                assert (b * b - n) % a == 0
                
                g1, g2, g3, ga, gb = b * b - n, 2 * a * b, a * a, a, b_orig
                ha, hb = a, b
                for fb in factor_base:
                    if a % fb.p != 0:
                        fb.soln1 = (fb.ainv * ( fb.tmem - b)) % fb.p
                        fb.soln2 = (fb.ainv * (-fb.tmem - b)) % fb.p
            
            i_poly += 1
            npolys += 1
            if i_poly >= 2 ** (len(B) - 1): i_poly = 0
            # END POLYNOMIAL SELECTION
            
            # BEGIN SIEVING.  Most of our time is spent between here and the "END SIEVING" comment.
            sieve_array = [0] * (2 * m + 1)
            for fb in factor_base:
                if fb.soln1 is None: continue
                p, lp = fb.p, fb.lp
                a_start_1 = fb.soln1 - ((m + fb.soln1) // p) * p
                if p > 20:
                    for a in range(a_start_1 + m, 2 * m + 1, p): sieve_array[a] += lp
                    a_start_2 = fb.soln2 - ((m + fb.soln2) // p) * p
                    for a in range(a_start_2 + m, 2 * m + 1, p): sieve_array[a] += lp
            # Perform the trial division step of the SIQS.
            limit = round(log2(m * sqrt(float(n)))) - 25                # 25 is a tunable parameter.  The rounding is for speed.
            for (i,sa) in enumerate(sieve_array):
                if sa >= limit:
                    x = i - m
                    gx = (g3 * x + g2) * x + g1
                    # Determine whether gx can be fully factorized into primes from the factor base.
                    # If so, store the indices of the factors from the factor base as divisors_idx. If not, set that to None.
                    a, divisors_idx = gx, []
                    for (fbi,fb) in enumerate(factor_base):
                        if a % fb.p == 0:
                            exp = 0
                            while a % fb.p == 0:
                                a //= fb.p
                                exp += 1
                            divisors_idx.append((fbi, exp))
                        if a == 1:
                            u = ha * x + hb
                            v = gx
                            assert (u * u) % n == v % n
                            smooth_relations.append((u, v, divisors_idx))
                            break
                    relcount = len(smooth_relations)
                    if relcount >= required_relations:
                        enough_relations = True
                        break
            # END SIEVING.  Most of our time is spent between here and the "BEGIN SIEVING" comment.
        
        M = [0] * nf
        mask = 1
        for sr in smooth_relations:
            for (j,exp) in sr[2]:
                if exp % 2: M[j] += mask
            mask <<= 1
        
        # Perform the linear algebra step of the SIQS: do fast Gaussian elimination to determine pairs of perfect squares mod n.
        # Use the optimisations described in [Çetin K. Koç and Sarath N. Arachchige. "A Fast Algorithm for Gaussian Elimination
        # over GF(2) and its Implementation on the GAPP." Journal of Parallel and Distributed Computing 13.1 (1991): 118-122].
        row_is_marked = bytearray([False]) * relcount
        pivots = [-1] * nf
        for j in range(nf):
            M_j = M[j]
            i = (M_j & (-M_j)).bit_length() - 1         #i = -1 if M[j] == 0 else lowest_set_bit(M[j])
            # i is now the row of the first nonzero entry in column j, or -1 if no such row exists.
            if i > -1:
                pivots[j] = i
                row_is_marked[i] = True
                for k in range(nf):
                    if (M[k] >> i) & 1 and k != j:  # test M[i][k] == 1
                        M[k] ^= M_j         # add column j to column k mod 2
        for i in range(relcount):
            if not row_is_marked[i]:
                square_indices = [i]
                for j in range(nf):
                    if (M[j] >> i) & 1:  # test M[i][j] == 1
                        square_indices.append(pivots[j])
                # Given the solution encoded by square_indices, try to find a factor of n, and return it.
                # Given on of the solutions returned by siqs_solve_matrix and the corresponding smooth relations,
                # calculate the pair (sqrt1, sqrt2) such that sqrt1^2 = sqrt2^2 (mod n).
                sqrt1, sqrt2 = 1, 1
                for idx in square_indices:
                    sqrt1 *= smooth_relations[idx][0]
                    sqrt2 *= smooth_relations[idx][1]
                sqrt2 = isqrt(sqrt2)
                assert (sqrt1 * sqrt1) % n == (sqrt2 * sqrt2) % n
                factor = gcd(sqrt1 - sqrt2, n)
                if 1 != factor != n: return factor
        
        required_relations_ratio += 0.05

def multifactor(n, methods):
    """
    Integer factoring function.  Uses several methods in parallel.  Waits
    for a function to return, kills the rest, and reports.  Note that two
    successive calls may return different results depending on which method
    finishes first and whether any methods call the randomizer.
    
    Input:
        n -- number to factor
        methods -- list of functions to run.
    
    Output: A factor of n.
    
    Examples:
    
    >>> methods = [pollardrho_brent, pollard_pm1, williams_pp1, ecm, siqs]
    >>> n = factorial(24) - 1
    >>> f = multifactor(n, methods)
    >>> sorted([f, n//f])
    [625793187653, 991459181683]
    """
    # Note that the multiprocing incurs relatively significant overhead.  Only call this if n is proving difficult to factor.
    def factory(method, n, output): output.put(method(n))
    factors = mpQueue()
    procs = [Process(target=factory, args=(m, n, factors)) for m in methods]
    for p in procs: p.start()
    f = factors.get() # .get() waits for something to be .put() into the queue before returning that value.
    for p in procs: p.terminate()
    return f

def primefac(n, trial=1000, rho=42000, primetest=isprime, methods=(pollardrho_brent,), trialextra=[]):
    """
    Generates the prime factors of the input.  Factors that appear x times
    are yielded x times.
    
    Do not expect the output to be in any particular order.
    
    This algorithm has three phases:
    1.  Trial division.
    2.  Pollard's rho algorithm.
    3.  Handling difficult cofactors.
    A future version of this software may add further phases, such as
    Fermat's method or the elliptic curve method.
    
    Input:
        n -- the number to be factored
        trial -- integer.  Trial division is performed with all primes
                 strictly less than this.  Default == 1000.  Regardless of
                 what number is passed to this parameter, trial division is
                 also performed w.r.t. 2, 3, and whichever numbers are
                 listed in trialextra.
        rho -- integer.  This is the number of rounds of Pollard's rho
               algorithm that we use before declaring a cofactor difficult.
               By default, this is 42,000.  Floating-point inf is also an
               acceptable value.
        primetest -- Use this function to test primality.  Default: isprime.
        methods -- Tuple of methods to use on difficult cofactors.  If the
                   tuple has more than 1 element, then we use all elements
                   in parallel by calling multifactor.  Calling multifactor
                   has a high overhead, so when the tuple has a single
                   element, we call that function directly.  The default is
                   (pollardrho_brent,).  Each function f in methods must
                   accept a single number n as its argument.  If n is prime,
                   then f(n) must return n. If n is composite, then f(n)
                   must return a nontrivial factor of n.  Giving up is not
                   allowed.
        trialextra -- List of numbers to include in the trial-division
                      stage.  The intent is that this argument will be used
                      for primes that are known to be likely factors of n,
                      but which are too large for trial division of all
                      primes up to them to be practical.
    
    Output: Prime factors of n
    
    Examples:
    
    >>> list(primefac(1729))
    [7, 13, 19]
    
    >>> list(sorted(primefac(factorial(24) - 1)))
    [625793187653, 991459181683]
    
    This next example finishes quickly thanks to the trialextra argument:
    >>> list(sorted(primefac(factorial(38) + 1, trialextra=[14029308060317546154181])))
    [14029308060317546154181, 37280713718589679646221]
    """
    # Obtains a complete factorization of n, yielding the prime factors as they are obtained.
    # If the user explicitly specifies a splitting method, use that method.  Otherwise,
    # 1.  Pull out small factors with trial division.
    # 2.  Do a few rounds of Pollard's Rho algorithm.
    # 3.  Launch multifactor on the remainder.  Note that multifactor's multiprocessing incurs relatively significant overhead.
    
    if n < 0: yield -1; n *= -1
    if n < 2: return
    if primetest(n): yield n; return
    
    # Trial division
    factors, nroot = [], isqrt(n)
    for p in chain(primegen(max(4,trial)), trialextra): # Note that we check for 2 and 3 whether the user wants to or not.
        if n%p == 0:
            while n%p == 0:
                yield p
                n //= p
            nroot = isqrt(n)
        if p > nroot:
            if n != 1: yield n
            return
    if primetest(n): yield n; return
    
    # TODO: Fermat's method?
    
    # Pollard's rho
    factors, difficult = [n], []
    while len(factors) != 0:
        rhocount = 0
        n = factors.pop()
        try:
            g = n
            while g == n:
                x, c, g = randrange(1, n), randrange(1, n), 1
                y = x
                while g==1:
                    if rhocount >= rho: raise Exception
                    rhocount += 1
                    x = (x**2 + c) % n
                    y = (y**2 + c) % n
                    y = (y**2 + c) % n
                    g = gcd(x-y, n)
            # We now have a nontrivial factor g of n.  If we took too long to get here, we are actually at the except statement.
            if primetest(g): yield g
            else: factors.append(g)
            n //= g
            if primetest(n): yield n
            else: factors.append(n)
        except Exception: difficult.append(n) # Factoring n took too long.  We will have multifactor chug on it.
    
    # TODO: ECM by itself?
    
    factors = difficult
    while len(factors) != 0:
        n = factors.pop()
        f = methods[0](n) if len(methods) == 1 else multifactor(n, methods=methods)
        if primetest(f): yield f
        else: factors.append(f)
        n //= f
        if primetest(n): yield n
        else: factors.append(n)

def factorint(n, trial=1000, rho=42000, primetest=isprime, methods=(pollardrho_brent,), trialextra=[]):
    """
    Calls primefac() to get the prime factors of n and compiles the result
    into a nice little dict.
    
    Input: The inputs to this function are identical to those of primefac.
    
    Output: Dictionary.  The keys are the set of distinct prime factors of
            n.  The values are the multiplicities of the keys in n's
            factorization.
    
    Examples:
    
    >>> fac = factorint(40320)
    >>> list(fac.items())
    [(2, 7), (3, 2), (5, 1), (7, 1)]
    """
    fac = {}
    for p in primefac(n,trial=trial,rho=rho,primetest=primetest,methods=methods,trialextra=trialextra): fac[p]=fac.get(p,0)+1
    return fac

def factorsieve(limit=inf):
    """
    A segmented sieve to generate the sequence map(factorint, count(1)),
    up to some limit, far more efficiently than factoring each number.
    
    The time- and space-complexities to iterate over the first n terms
    are within logarithmic factors of O(n) and O(sqrt(n)), respectively.
    
    Input: limit -- a number; default == inf.  We generate factorizations
                    strictly less than this.
    
    Output: a sequence of dicts.
    
    Examples:
    
    >>> list(factorsieve(10))
    [{}, {2: 1}, {3: 1}, {2: 2}, {5: 1}, {2: 1, 3: 1}, {7: 1}, {2: 3}, {3: 2}]
    """
    if limit < 1: return
    yield {}
    pg = primegen()
    primes = [next(pg)]
    nextp = next(pg)
    lo, hi = 2, min(nextp**2, limit)
    # We can sieve up to hi - 1.
    while lo < limit:
        ints = list(range(lo, hi))
        facs = [[] for _ in range(lo, hi)]                              ####
        # facs[n] will contain the factorization of n + lo in the form of a list of primes.
        for p in primes:
            pp = p
            while pp < hi:
                for n in range((-lo) % pp, hi - lo, pp):
                    ints[n] //= p
                    facs[n].append(p)                                   ####
                pp *= p
        # Any entries in ints that are not 1 are prime divisors of their
        # corresponding numbers that were too large to be sieved out.
        for n in range(hi - lo):
            p = ints[n]
            if p != 1:
                facs[n].append(p)                                       ####
        
        for fac in facs:
            """
            Most of our time is spent not in actual computation, but in wrangling the data thus produced.
            It therefore behooves us to optimize the data-wrangling parts.
            In particular, we return dict objects, but dict-y operations are much slower than list-y operations.
            Our code would be sorter and clearer if we had
                facs = [{} for _ in range(lo,hi)]
            and
                facs[n][p] = facs[n].get(p,0) + 1
            and
                facs[n][p] = 1
            at the lines marked with ####; this loop could then just be
                yield from facs
            but this does a lot of dict-y operations.  What we do instead is assemble a list of primes,
            with multiplicity, in increasing order, and then do some computation here to summarize it.
            These lines amount to
                yield collections.Counter(fac)
            but doing it this way avoids bringing in new data types.
            """
            summary = []
            pprev, e = fac[0], 1
            for p in fac[1:]:
                if p != pprev:
                    summary.append((pprev,e))
                    e = 0
                pprev = p
                e += 1
            summary.append((pprev,e))
            yield dict(summary)
        
        primes.append(nextp)
        nextp = next(pg)
        lo, hi = hi, min(nextp**2, limit)

def divisors(n):
    """
    Generates all natural numbers that evenly divide n.  The code is derived
    from https://stackoverflow.com/a/171784.
    
    Do not expect the output to be in any particular order.
    
    Input: n -- an integer or a dict in the format produced by factorint
    
    Output: A sequence of positive integers
    
    Examples:
    
    >>> [sorted(divisors(n)) for n in [0, 1, 10, 28]]
    [[], [1], [1, 2, 5, 10], [1, 2, 4, 7, 14, 28]]
    
    >>> sorted(divisors(496))
    [1, 2, 4, 8, 16, 31, 62, 124, 248, 496]
    
    >>> sorted(divisors(1729))
    [1, 7, 13, 19, 91, 133, 247, 1729]
    
    >>> sorted(divisors({2:3, 3:2}))
    [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]
    """
    if n == 0 or n is {}: return
    if n == 1: yield 1; return
    facs = list((n if isinstance(n, dict) else factorint(n)).items())
    nfacs = len(facs)
    f = [0] * nfacs
    while True:
        yield prod(facs[x][0]**f[x] for x in range(nfacs))
        for i in count():
            if i >= nfacs: return
            f[i] += 1
            if f[i] <= facs[i][1]: break
            f[i] = 0

def divisors_factored(n):
    """
    Yields the divisors of n, in factorint format.
    
    Do not expect the output to be in any particular order.
    
    Input: n -- an integer or the output of factorint
    
    Output: A sequence of factorint outputs
    
    Examples:
    
    >>> list(sorted(x.items()) for x in divisors_factored(12))
    [[], [(2, 1)], [(2, 2)], [(3, 1)], [(2, 1), (3, 1)], [(2, 2), (3, 1)]]
    """
    facs = list((n if isinstance(n, dict) else factorint(n)).items())
    nfacs = len(facs)
    f = [0] * nfacs
    while True:
        yield {facs[x][0]:f[x] for x in range(nfacs) if f[x] != 0}
        for i in count():
            if i >= nfacs: return
            f[i] += 1
            if f[i] <= facs[i][1]: break
            f[i] = 0

def divcount(n):
    """
    Counts the number of divisors of n.
    
    Input: n -- number to consider, or an output from factorint
    
    Output: An integer
    
    Examples:
    
    >>> [divcount(n) for n in (28, 42, 40320, {2:2, 3:1})]
    [6, 8, 96, 6]
    """
    return prod(k+1 for k in (factorint(n) if isinstance(n, inttypes) else n).values())

def divsigma(n, x=1):
    """
    Sum of divisors of a natural number, raised to the xth power.  The
    conventional notation for this in mathematical literature is sigma_x(n),
    hence the name of this function.
    
    Input:
        n -- positve integer or factorint output
        x -- non-negative integer.  Default x == 1.
    
    Output: An integer
    
    Examples:
    
    >>> [divsigma(n) for n in [1, 6, 10, 28, 496, 1024, 1729]]
    [1, 12, 18, 56, 992, 2047, 2240]
    
    >>> [divsigma(n, 2) for n in [1, 6, 10, 28, 496, 1024, 1729]]
    [1, 50, 130, 1050, 328042, 1398101, 3077000]
    """
    if n == 0: return 0
    f = n if isinstance(n, dict) else factorint(n)
    return divcount(n) if x==0 else prod((p**((k+1)*x)-1) // (p**x-1) for (p,k) in f.items())

def divcountsieve(limit=inf):
    """
    Uses a segmented sieve to compute the divisor-count of all positive
    integers strictly less than the input.
    
    The time- and space-complexities to iterate over the first n terms
    are within logarithmic factors of O(n) and O(sqrt(n)), respectively.
    
    Input: limit -- We stop the sieve at this value.  Default = inf.
    
    Output: Sequence of integers
    
    Example:
    
    >>> list(divcountsieve(24))
    [1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4, 5, 2, 6, 2, 6, 4, 4, 2]
    """
    if limit <= 1: return
    yield 1
    pg = primegen()
    primes = [next(pg)]
    nextp = next(pg)
    lo, hi = 2, min(nextp**2, limit)
    # We can sieve up to hi - 1.
    while lo < limit:
        ints = list(range(lo, hi))
        exps = bytearray([0]) * (hi - lo)
        dcs = [1] * (hi - lo)
        for p in primes:
            for n in range((-lo) % p, hi - lo, p):
                ints[n] //= p
                exps[n] = 1
            pp = p*p
            while pp < hi:
                for n in range((-lo) % pp, hi - lo, pp):
                    ints[n] //= p
                    exps[n] += 1
                pp *= p
            for n in range((-lo) % p, hi - lo, p):
                dcs[n] *= exps[n] + 1
        # Any entries in ints that are not 1 are prime divisors of their
        # corresponding numbers that were too large to be sieved out.
        for n in range(hi - lo):
            p = ints[n]
            if p != 1:
                dcs[n] *= 2
        
        yield from dcs
        
        primes.append(nextp)
        nextp = next(pg)
        lo, hi = hi, min(nextp**2, limit)

def divsigmasieve(limit=inf, x=1):
    """
    Uses a segmented sieve to compute the xth-power-sum-of-divisors for all
    positive integers strictly less than the input.
    
    The time- and space-complexities to iterate over the first n terms
    are within logarithmic factors of O(n) and O(sqrt(n)), respectively.
    
    Input: limit -- We stop the sieve at this value.  Default = inf.
           x -- We compute the sums of the xth powers of the divisors.
    
    Output: Sequence of integers.
    
    Examples:
    
    >>> list(divsigmasieve(24, 0))
    [1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4, 5, 2, 6, 2, 6, 4, 4, 2]
    
    >>> list(divsigmasieve(24, 1))
    [1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24, 31, 18, 39, 20, 42, 32, 36, 24]
    
    >>> list(divsigmasieve(24, 2))
    [1, 5, 10, 21, 26, 50, 50, 85, 91, 130, 122, 210, 170, 250, 260, 341, 290, 455, 362, 546, 500, 610, 530]
    
    >>> list(divsigmasieve(24, 3))
    [1, 9, 28, 73, 126, 252, 344, 585, 757, 1134, 1332, 2044, 2198, 3096, 3528, 4681, 4914, 6813, 6860, 9198, 9632, 11988, 12168]
    """
    if x == 0:
        yield from divcountsieve(limit)
        return
    if limit <= 1: return
    yield 1
    pg = primegen()
    primes = [next(pg)]
    nextp = next(pg)
    lo, hi = 2, min(nextp**2, limit)
    # We can sieve up to hi - 1.
    while lo < limit:
        ints = list(range(lo, hi))
        sigs = [1] * (hi - lo)
        for p in primes:
            mults = [1] * (hi - lo)
            px = p**x
            pxe = px
            pp = p
            while pp < hi:
                for n in range((-lo) % pp, hi - lo, pp):
                    ints[n] //= p
                    mults[n] += pxe
                pp *= p
                pxe *= px
            for n in range((-lo) % p, hi - lo, p):
                sigs[n] *= mults[n]
        # Any entries in ints that are not 1 are prime divisors of their
        # corresponding numbers that were too large to be sieved out.
        for n in range(hi - lo):
            p = ints[n]
            if p != 1:
                sigs[n] *= (p**x + 1)
        
        yield from sigs
        
        primes.append(nextp)
        nextp = next(pg)
        lo, hi = hi, min(nextp**2, limit)

def totient(n, k=1):
    """
    Euler's/Jordan's totient function: the number of k-tuples of positive
    integers, all <= n, that form a coprime (k+1)-tuple together with n.
    When k == 1, this is Euler's totient: the number of numbers less than a
    number that are relatively prime to that number.
    
    Input: n, k -- natural numbers.  Default k == 1.
                   n may also be a factorint output.
    
    Output: A natural number
    
    Examples:
    
    >>> [totient(n) for n in range(1, 24)]
    [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22]
    
    >>> [totient(n, 2) for n in range(1, 19)]
    [1, 3, 8, 12, 24, 24, 48, 48, 72, 72, 120, 96, 168, 144, 192, 192, 288, 216]
    
    >>> totient(factorint(120))
    32
    """
    if isinstance(n, inttypes): fac = set(primefac(n))
    else: fac, n = n.keys(), prod(p**e for (p,e) in n.items())
    return n**k * prod(p**k-1 for p in fac) // prod(fac)**k

def totientsieve(limit=inf, k=1):
    """
    Uses a segmented sieve to compute the totients strictly less than limit.
    
    The time- and space-complexities to iterate over the first n terms
    are within logarithmic factors of O(n) and O(sqrt(n)), respectively.
    
    Input: limit -- an integer.  Default = inf.
           k -- a positive integer.  We compute the kth-order Jordan totient
                function.  When k == 1, this is the ordinary Euler totient.
    
    Output: Sequence of integers
    
    Examples:
    
    >>> list(totientsieve(21))
    [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8]
    
    >>> list(totientsieve(18, 2))
    [1, 3, 8, 12, 24, 24, 48, 48, 72, 72, 120, 96, 168, 144, 192, 192, 288]
    
    >>> list(totientsieve(15, 3))
    [1, 7, 26, 56, 124, 182, 342, 448, 702, 868, 1330, 1456, 2196, 2394]
    """
    if limit <= 1: return
    yield 1
    pg = primegen()
    primes = [next(pg)]
    nextp = next(pg)
    lo, hi = 2, min(nextp**2, limit)
    # We can sieve up to hi - 1.
    while lo < limit:
        ints = list(range(lo, hi))
        tots = [n**k for n in range(lo, hi)]
        for p in primes:
            pk = p**k
            for n in range((-lo) % p, hi - lo, p):
                ints[n] //= p
                tots[n] //= pk
                tots[n] *= pk - 1
            pp = p*p
            while pp < hi:
                for n in range((-lo) % pp, hi - lo, pp):
                    ints[n] //= p
                pp *= p
        # Any entries in ints that are not 1 are prime divisors of their
        # corresponding numbers that were too large to be sieved out.
        for n in range(hi - lo):
            p = ints[n]
            if p != 1:
                tots[n] //= p**k
                tots[n] *= p**k - 1
        
        yield from tots
        
        primes.append(nextp)
        nextp = next(pg)
        lo, hi = hi, min(nextp**2, limit)

def totientsum(n):  # TODO: What are the time- and space-complexities?
    """
    Computes sum(totient(n) for n in range(1, n+1)) efficiently.
    Derived from the Project Euler #351 overview.
    
    Input: n -- integer.
    
    Output: an integer
    
    Examples:
    
    >>> [totientsum(n) for n in chain(range(10), (100, 1000, 10000000))]
    [0, 1, 2, 4, 6, 10, 12, 18, 22, 28, 3044, 304192, 30396356427242]
    """
    if n < 12: return sum(totient(x) for x in range(1, n+1))
    L = int((n/log(log(n)))**(2/3))
    sieve = list(range(L+1))
    bigV = [0] * (n//L + 1)
    for p in range(2, L+1):
        if p == sieve[p]:
            for k in range(p, L+1, p): sieve[k] -= sieve[k] // p
        sieve[p] += sieve[p-1]
    for x in range(n//L, 0, -1):
        k = n // x
        res = k * (k+1) // 2
        for g in range(2, isqrt(k)+1): res -= sieve[k//g] if (k//g <= L) else bigV[x*g]
        for z in range(1, isqrt(k)+1):
            if z != k//z: res -= (k//z - k//(z+1)) * sieve[z]
        bigV[x] = res
    return bigV[1]

def mobius(n):
    """
    The Mobius function of n: 1 if n is squarefree with an even number of
    prime factors, -1 if n is squarefree with an odd number of prime
    factors, and 0 if n has a squared prime factor.
    
    Input: n -- positive integer or factorint output
    
    Output: -1, 0, or 1
    
    Examples:
    
    >>> [mobius(n) for n in range(1, 22)]
    [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 1]
    """
    if isinstance(n, dict): return 0 if any(x > 1 for x in n.values()) else (1 - 2 * (len(n) % 2))
    facs = set()
    for p in primefac(n):
        if p in facs: return 0
        facs.add(p)
    return 1 - 2 * (len(facs) % 2)

def mobiussieve(limit=inf):     # TODO: Figure out a way to have the sieve be a bytearray.  This is doable up to 10**25 or so.
    """
    Uses a segmented sieve to compute the Mobius function for all positive
    integers strictly less than the input.
    
    The time- and space-complexities to iterate over the first n terms
    are within logarithmic factors of O(n) and O(sqrt(n)), respectively.
    
    Input: limit -- an integer.  Default == inf.
    
    Output: Sequence of integers
    
    Example:
    
    >>> list(mobiussieve(21))
    [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0]
    """
    if limit <= 1: return
    yield 1
    pg = primegen()
    primes = [next(pg)]
    nextp = next(pg)
    lo, hi = 2, min(nextp**2, limit)
    # We can sieve up to hi - 1.
    while lo < limit:
        mobs = [1] * (hi - lo)
        for p in primes:
            for n in range((-lo) %   p  , hi - lo,  p ): mobs[n] *= -p
            for n in range((-lo) % (p*p), hi - lo, p*p): mobs[n]  =  0
        for n in range(hi - lo):
            m = mobs[n]
            if m == 0: continue
            if -lo-n < m < lo+n:
                if m > 0: mobs[n] = -1
                if m < 0: mobs[n] =  1
            else:
                if m > 0: mobs[n] =  1
                if m < 0: mobs[n] = -1
        
        yield from mobs
        
        primes.append(nextp)
        nextp = next(pg)
        lo, hi = hi, min(nextp**2, limit)

def liouville(n):
    """
    The Liouville lambda function: lambda(n) == (-1)**k, where k is the
    number of prime factors of n, counted with multiplicity.
    
    Input: n -- positive integer or factorint output
    
    Output: An integer.
    
    Examples:
    
    >>> list(liouville(n) for n in range(1, 21))
    [1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1]
    """
    return (-1)**(len(list(primefac(n))) if isinstance(n, inttypes) else sum(n.values()))

def polyroots_prime(f, p, sqfr=False):
    """
    Generates without multiplicity the zeros of a polynomial modulo a prime.
    Coded after algorithm 2.3.10 in Crandall & Pomerance: this uses explicit
    formulas for low-degree polynomials and Cantor-Zassenhaus for cubics and
    higher.
    
    Do not expect the output to be in any particular order.
    
    Input:
        f -- List.  These are the polynomial's coefficients in order of
               increasing degree: f[k] is the coefficient of the x^k term.
        p -- Integer.  Assumed to be prime.
        sqfr -- True if f is known to be squarefree modulo p.
                False (default) if it might not be squarefree.
                If you do not know, then use False.
    
    Output: Finite sequence of integers.  The length is bounded above by
            both the degree of the polynomial and the modulus.
    
    Examples:
    
    >>> sorted(polyroots_prime([1,2,3], 11))
    [6, 8]
    
    >>> sorted(polyroots_prime([3,3,3,3,3,3], 3))
    [0, 1, 2]
    
    >>> sorted(polyroots_prime([3,3,3,3,3,6], 3))
    [0, 1, 2]
    
    >>> sorted(polyroots_prime([1,2,3], 3))
    [1]
    """
    assert isprime(p)
    g = f[:]
    while len(g) > 0 and g[-1] % p == 0: del g[-1]
    if g == []: yield from range(p); return
    if (not sqfr): g = gcmd(g, polysubmodp(polypowmodpmodpoly([0,1], p, p, g), [0,1], p), p) # This makes g squarefree.
    else:
        g = [x % p for x in g]
        while len(g) > 0 and g[-1] == 0: del g[-1]
    assert not (g is None), (G, p)
    if g == []: yield from range(p); return                     # The zero polynomial.
    # At this point, the leading coefficient is guaranteed to be nonzero mod p.
    if g[0] == 0:
        yield 0
        while g[0] == 0: del g[0]
        if g == []: assert False
    if len(g) == 1: return                                          # Constant.  Guaranteed nonzero by this point.
    # In this next line, we do not need to worry about pow raising a ValueError, because g[1] is guaranteed to be nonzero mod p.
    if len(g) == 2: yield (-g[0] * pow(g[1], -1, p)) % p; return    # Linear.
    if len(g) == 3:                                                 # Quadratic.
        if p == 2: yield from (x for x in (0,1) if polyval(g, x, 2) == 0); return
        c, b, a = g             # a * x^2  +  b * x  +  c
        ai = pow(a, -1, p)  # No ValueErrors here: a is guaranteed to be nonzero mod p.
        c, b = (c*ai) % p, (b*ai) % p
        d = b*b-4*c
        l = legendre(d, p)
        if l == -1: return
        sq = sqrtmod_prime(d, p)
        inv2 = (p+1)//2 # inv2 == modinv(2, p)
        yield from {((-b+sq)*inv2) % p, ((-b-sq)*inv2) % p}
        return
    # Brute force or Cantor-Zassenhaus?  The better choice depends on both degree and modulus.                              TODO
    #yield from (x for x in range(p) if polyval(G, x, p) == 0); return
    h = [1]
    while len(h) in (1, len(g)): h = gcmd(polysubmodp(polypowmodpmodpoly([randrange(p),1], (p-1)//2, p, g), [1], p), g, p)
    q, s = polydivmodmodp(g, h, p)
    assert s == []
    yield from polyroots_prime(h, p, True)
    yield from polyroots_prime(q, p, True)
    return

def hensel(f, p, k): # Finds all solutions to f(x) == 0 mod p**k.
    """
    Uses Hensel lifting to generate with some efficiency all zeros of a
    polynomial modulo a prime power.
    
    Do not expect the output to be in any particular order.
    
    Input:
        f -- List.  These are the polynomial's coefficients in order of
             increasing degree.
        p, k -- Integers.  We find zeros mod p**k, where p is assumed prime.
    
    Output: Finite sequence of integers.
    
    Examples:
    
    >>> list(hensel([1,2,3], 3, 27))
    [7195739071075]
    
    >>> f = [3,3,3,3,3,6]
    >>> sorted(hensel(f, 3, 4))
    []
    >>> [x for x in range(3**4) if polyval(f, x, 3**4) == 0]
    []
    
    >>> f = [3,3,3,3,3,3]
    >>> sorted(hensel(f[:], 3, 4))
    [8, 17, 26, 35, 44, 53, 62, 71, 80]
    >>> [x for x in range(3**4) if polyval(f[:], x, 3**4) == 0]
    [8, 17, 26, 35, 44, 53, 62, 71, 80]
    """
    assert k > 0 and isprime(p)
    if k == 1: yield from polyroots_prime(f, p); return
    pk1, df = p**(k-1), [n*c for (n,c) in enumerate(f)][1:]    # df = derivative of f
    pk = pk1 * p
    for n in hensel(f, p, k-1):
        dfn, fn = polyval(df, n, p), polyval(f, n, pk)
        # There is no need to worry about pow throwing a ValueError here, because the conditionals handle that case separately.
        yield from [n + ((-pow(dfn,-1,p) * fn // pk1) % p) * pk1] if dfn else [] if fn else (n + t * pk1 for t in range(p))

def sqrtmod(a, n):
    """
    Generates all square roots of a modulo n.  The heavy lifting is done in
    the integer-factoring functions, in crt(), and in hensel().
    
    Do not expect the output to be in any particular order.
    
    Input: a, n -- integers
    
    Output: list of integers
    
    Examples:
    
    >>> sorted(sqrtmod(100, 187))
    [10, 78, 109, 177]
    
    >>> sorted(sqrtmod(100, {11:1, 17:1}))
    [10, 78, 109, 177]
    
    >>> sorted(sqrtmod(0, 100))
    [0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
    
    >>> sorted(sqrtmod(97, 1009))
    []
    """
    n, nf = (prod(p**e for (p,e) in n.items()), n) if isinstance(n, dict) else (n, None)
    if n <= 10:                                             # This bound is chosen arbitrarily.  TODO: optimize.
        yield from (x for x in range(n) if (x*x - a) % n == 0)
        return
    sqrts = [(list(hensel([-a, 0, 1], p, e)), p**e) for (p,e) in (factorint(n) if nf is None else nf).items()]
    if len(sqrts) == 1:
        yield from sqrts[0][0]
        return
    rems, mods = [], []
    for (rts, m) in sqrts:
        if len(rts) == 0: return
        rems.append(rts)
        mods.append(m)
    yield from (crt(r, mods) for r in product(*rems))      # When crt gets upgraded, use it here.  TODO

def polyrootsmod(pol, n):
    """
    Computes the zeros of a polynomial modulo an integer.  We do this by
    factoring the modulus, solving mod the prime power factors, and putting
    the results together via the Chinese Remainder Theorem.
    
    Do not expect the output to be in any particular order.
    
    Input:
        pol -- List.  These are the polynomial's coefficients in order of
               increasing degree; pol[k] is the coefficient of the x^k term.
        n -- Integer.
    
    Output: List of integers.
    
    Examples:
    """         # TODO
    n, nf = (prod(p**e for (p,e) in n.items()), n) if isinstance(n, dict) else (n, None)
    if n <= 10:                                             # This bound is chosen arbitrarily.  TODO: optimize.
        yield from (x for x in range(n) if polyval(pol, x, n) == 0)
        return
    roots = [(list(hensel(pol, p, e)), p**e) for (p,e) in (factorint(n) if nf is None else nf).items()]
    if len(roots) == 1:
        yield from roots[0][0]
        return
    rems, mods = [], []
    for (rts, m) in roots:
        if len(rts) == 0: return
        rems.append(rts)
        mods.append(m)
    yield from (crt(r, mods) for r in product(*rems))      # When crt gets upgraded, use it here.  TODO

def _PQa(P, Q, D):
    """
    Generates some sequences related to SCF expansions of certain quadratic
    surds.  A helper function for pell().  Let P,Q,D be integers such that
    Q != 0, D > 0 is a nonsquare, and P**2 == D (mod Q). We yield a sequence
    of tuples (Bi, Gi, Pi, Qi) where i is an index counting up from 0,
    x == (P+sqrt(D))/Q == [a0;a1,a2,...], (Pi+Sqrt(D))/Qi is the ith
    complete quotient of x, and Bi is the denominator of the ith convergent
    to x.  For full details, see
    https://web.archive.org/web/20180831180333/http://www.jpr2718.org/pell.pdf.
    """ # TODO What is the G sequence?
    #assert Q != 0 and D > 0 and (P**2 - D) % Q == 0
    d, B0, G0, B1, G1 = isqrt(D), 1, -P, 0, Q
    while True:
        a = (P + d + (0 if Q > 0 else 1)) // Q
        B1, B0, G1, G0 = a * B1 + B0, B1, a * G1 + G0, G1
        yield (B1, G1, P, Q)
        P = a * Q - P
        Q = (D - P**2) // Q

def pell(D, N):                                                                     # TODO this is hideous.
    """
    This function solves the generalized Pell equation: we find all
    non-negative integers (x,y) such that x**2 - D * y**2 == N.
    
    There are several cases:
      Case 1: N == 0.  We solve x**2 == D * y**2.
        (0,0) is always a solution.
        Case 1a: If D is a nonsquare, then there are no further solutions.
        Case 1b: If D is a square, then there are infinitely many solutions,
                 yielded by ((isqrt(D)*t, t) for t in count()).
      Case 2: N != 0 == D.  We solve x**2 == N.
        Case 2a: If N is a nonsquare, then there are no solutions.
        Case 2b: If N is a square, then there are infinitely many solutions,
                 yielded by ((isqrt(N), t) for t in count()).
      Case 3: N != 0 > D.  We solve x**2 + |D| * y**2 == N.
              We are looking for lattice points on an ellipse.  The number
              of solutions will be finite.
      Case 4: N != 0 < D.  We solve x**2 - D * y**2 == N.
        We are looking for lattice points on a hyperbola.  The number of
        solutions can be zero, finite, or infinite.
        Case 4a: If D is a square, then the number of solutions will be at
                 most finite.  This case is solved by factoring.
        Case 4b: If D is a nonsquare, then we run the PQa/LMM algorithms: we
                 produce a set of primitive solutions; if this set is empty,
                 there are no solutions; if this set has members, an ininite
                 solution set can be produced by repeatedly composing them
                 with the fundamental solution of x**2 - D * y**2 == 1.
    
    References:
        https://web.archive.org/web/20180831180333/http://www.jpr2718.org/pell.pdf
        www.offtonic.com/blog/?p=12
        www.offtonic.com/blog/?p=18
    
    Input: D, N -- integers
    
    Output:
        A 3-tuple.
        If the number of solutions is finite, then it is (None, z, None),
            where z is the sorted list of all solutions.
        If the number of solutions is infinite and the equation is
            degenerate, then it is (gen,None,None), where gen yields all
            solutions.
        If the number of solutions is infinite & the equation is
            nondegenerate, then it is (gen, z, f), where z is the set of
            primitive solutions, represented as a sorted list, and f is the
            fundamental solution --- i.e., f is the primitive solution of
            x**2 - D * y**2 == 1.
        We can check the infinitude of solutions via bool(pell(D,N)[0]).
    
    Examples:
    
    >>> pell(2, 0)
    (None, [(0, 0)], None)
    
    >>> pell(4, 0)[1:]
    (None, None)
    
    >>> list(islice(pell(4, 0)[0], 8))
    [(0, 0), (2, 1), (4, 2), (6, 3), (8, 4), (10, 5), (12, 6), (14, 7)]
    
    >>> pell(0, 25 * 169)[1:]
    (None, None)
    
    >>> list(islice(pell(0, 25 * 169)[0], 8))
    [(65, 0), (65, 1), (65, 2), (65, 3), (65, 4), (65, 5), (65, 6), (65, 7)]
    
    >>> pell(0, -25 * 169)
    (None, [], None)
    
    >>> pell(-1, -25 * 169)
    (None, [], None)
    
    >>> pell(-1, 25 * 169)
    (None, [(0, 65), (16, 63), (25, 60), (33, 56), (39, 52), (52, 39), (56, 33), (60, 25), (63, 16), (65, 0)], None)
    
    >>> pell(1, 25 * 169)
    (None, [(65, 0), (97, 72), (169, 156), (425, 420), (2113, 2112)], None)
    
    >>> pell(4, 25 * 169)
    (None, [(65, 0), (97, 36), (169, 78), (425, 210), (2113, 1056)], None)
    
    >>> pell(2, 1)[1:]
    ([(3, 2)], (3, 2))
    
    >>> list(islice(pell(2, 1)[0], 6))
    [(1, 0), (3, 2), (17, 12), (99, 70), (577, 408), (3363, 2378)]
    
    >>> pell(12, 148)[1:]
    ([(14, 2), (16, 3), (40, 11), (50, 14)], (7, 2))
    
    >>> list(islice(pell(12, 148)[0], 7))
    [(14, 2), (16, 3), (40, 11), (50, 14), (146, 42), (184, 53), (544, 157)]
    
    >>> list(islice(pell(3, 1)[0], 7))
    [(1, 0), (2, 1), (7, 4), (26, 15), (97, 56), (362, 209), (1351, 780)]
    
    >>> list(islice(pell(61, 1)[0], 2))[1]
    (1766319049, 226153980)
    
    >>> list(islice(pell(661, 1)[0], 2))[1]
    (16421658242965910275055840472270471049, 638728478116949861246791167518480580)
    """
    if N == 0:          # x**2 == D * y**2
        if D < 0: return (None, [(0,0)], None)
        d = isqrt(D)
        if d*d == D: return (((d*t, t) for t in count()), None, None)
        else: return (None, [(0,0)], None)
    if D == 0:          # x**2 == N != 0
        if N < 0: return (None, [], None)
        n = isqrt(N)
        if n*n == N: return ((( n , t) for t in count()), None, None)
        else: return (None, [], None)
    if D < 0:               # x**2 + abs(D) * y**2 == N != 0.  We are looking for lattice points on an ellipse.  TODO Cornacchia
        # Slightly better than scanning y.  Runs in O(sqrt(N) * len(list(sqrtmod(N, D))) / D) time, plus the time to factor D.
        ans = (None, [], None)
        D *= -1
        if N < 0: return ans
        n = isqrt(N)
        rts = list(sqrtmod(N, D))
        if len(rts) == 0: return ans
        for x in count(0, D):
            for r in rts:
                z = x + r
                Z = z * z
                if Z > N: return ans
                # Z + D * y**2 ?= N
                Y = (N - Z) // D # remainder will be zero
                y = isqrt(Y)
                if y*y == Y: ans[1].append((z,y))
        return ans
    # If we have gotten to this point, then N is nonzero and D is positive.
    d = isqrt(D)
    if d**2 == D:   # (x - d * y) * (x + d * y) == N
        ans = (None, [], None)
        s = 1 if N > 0 else -1
        N *= s
        if N % 4 == 2: return ans
        x = 1 + (N%2)
        if x == 1: N //= 4
        for p in divisors(N):
            q = N // p
            if p <= q and (q-s*p) % (x*d) == 0: ans[1].append(((q+s*p)//x, (q-s*p)//(x*d)))
        ans[1].sort()
        return ans
    # If we have gotten to this point, then N is nonzero and D is a positive nonsquare.  We now proceed with the PQa/LMM method.
    pqa = _PQa(0, 1, D)
    x0 = next(pqa)
    for (k,x) in enumerate(pqa): # k, Bk, Gk, Pk, Qk
        if x[3] == 1: break
        x0 = x
    if k % 2 == 1: pgen = (x0[1], x0[0]); nfun = None
    else:          nfun = (x0[1], x0[0]); pgen = (nfun[0]**2 + nfun[1]**2 * D, 2 * nfun[0] * nfun[1])
    # pgen generates the solutions for x**2 - D * y**2 == +1.
    # nfun is the fundamental solution for x**2 - D * y**2 == -1 (if it exists).
    if N == 1:  # x**2 - D * y**2 == 1
        def gen(D, a, b):
            x, y, t, u = 1, 0, a, b
            while True:
                yield x, y
                x, y = x*t + y*u*D, y*t + x*u
        return (gen(D, *pgen), [pgen], pgen)
    if N == -1: # x**2 - D * y**2 == -1
        if not nfun: return (None, [], None)
        def gen(D, nfun, pgen):
            (x, y), (t, u) = nfun, pgen
            while True:
                assert x**2 - D * y**2 == -1
                yield x, y
                x, y = x*t + y*u*D, y*t + x*u
        return (gen(D, nfun, pgen), [nfun], pgen)
    t, u = pgen
    L1, L2 = (0, isqrt(N * (t-1) // (2 * D))) if N > 0 else (isqrt(-N // D), isqrt(-N * (t+1) // (2 * D)))
    if L2 - L1 < 64:     # Find the primitive set by brute force.
        primitives = set()
        for y in range(L1, L2+1):
            X = N + D * y**2
            if X >= 0:
                x = isqrt(X)
                if x**2 == X: primitives |= {(x,y), (-x,y)}
    else:                   # Find the primitive set by the LMM algorithm.
        n = isqrt(abs(N))
        primitives = {(n,0)} if N == n*n else set()
        if nfun: a, b = nfun
        for f in divisors(N):
            if N % (f**2) != 0: continue
            m = N // (f**2)
            am = abs(m)
            for z in (((z-am) if z > am//2 else z) for z in sqrtmod(D, am)):
                #assert -abs(m) < 2*z <= abs(m)
                #assert z**2 % abs(m) == D % abs(m)
                pqa = _PQa(z, am, D)
                end = None
                xp = next(pqa)
                for x in pqa:     #  x == ( B0 , G1 , P2 , Q3 )
                    P, Q = x[2], x[3]
                    if (P, Q) == end: break
                    #if (not end) and (P + sqrt(D) > Q) and (-Q < P - sqrt(D) < 0): end = (P, Q)
                    # Rewritten without floats, leveraging the fact that D != isqrt(D) == d:
                    if (not end) and d + 1 <= P + Q <= d + Q <= P + 2*d: end = (P, Q)
                    if Q*Q == 1:
                        r, s = xp[1], xp[0]
                        rr_Dss = r*r - D*s*s
                        if rr_Dss == m: r, s = f*r, f*s
                        elif rr_Dss == -m:
                            if nfun: r, s = a*r + D*b*s, a*s + b*r
                            else: break
                        else: break     # TODO: Is this case possible?
                        primitives |= {(r, s), (-r, s)}
                    xp = x
    prims = set()
    P, Q = pgen
    for (x, y) in primitives:
        while not ((x <= 0 >= y) or (x >= 0 <= y)): x, y = P*x + D*Q*y, P*y + Q*x
        if x < 0 or y < 0: x, y = -x, -y
        prims.add((x, y))
    primitives = []
    for (x, y) in sorted(prims):
        for (r, s) in primitives:
            if (x*r - D*y*s) % N == 0 and (x*s - y*r) % N == 0: break
        else:
            if x**2 - D * y**2 == N: primitives.append((x, y))
    if primitives == []: return (None, [], None)
    def gen(D, N, primitives, pgen):
        P, Q = pgen
        while True:
            for (x, (p,q)) in enumerate(primitives):
                assert p**2 - D * q**2 == N
                yield p, q
                primitives[x] = (p*P+q*Q*D, p*Q+q*P)
    return (gen(D, N, primitives[:], pgen), primitives, pgen)

def simplepell(D, bail=inf):
    """
    Generates the positive solutions of x**2 - D * y**2 == 1.  We use some
    optimizations specific to this case of the Pell equation that makes this
    more efficient than calling pell(D,1)[0].  Note that this function is
    not equivalent to calling pell(D,1)[0]: pell() is concerned with the
    general equation, which may or may not have trivial solutions, and as
    such yields all non-negative solutions, whereas this function is
    concerned only with the simple Pell equation, which always has an
    infinite family of positive solutions generated from a single primitive
    solution and always has the trivial solution (1,0); since that trivial
    solution always exists for this function's scope, we omit it from the
    output.
    
    Input:
        D -- an integer, assumed to be positive
        bail -- yield no solutions whose x-coordinate is > this number.
                Default == inf.
    
    Output: sequence of 2-tuples of positive integers
    
    Examples:
    
    >>> list(islice(simplepell(2), 6))
    [(3, 2), (17, 12), (99, 70), (577, 408), (3363, 2378), (19601, 13860)]
    
    >>> list(islice(simplepell(3), 6))
    [(2, 1), (7, 4), (26, 15), (97, 56), (362, 209), (1351, 780)]
    
    >>> next(simplepell(61))
    (1766319049, 226153980)
    
    >>> next(simplepell(661))
    (16421658242965910275055840472270471049, 638728478116949861246791167518480580)
    """
    d = isqrt(D)
    i, B0, G0, P, Q = False, 1, d, d, D - d*d
    if Q == 0: return
    B1 = a = (2*d) // Q
    G1 = a * d + 1
    while Q != 1:
        P = a * Q - P
        Q = (D - P**2) // Q
        a = (P + d) // Q
        i, B1, B0, G1, G0 = not i, a * B1 + B0, B1, a * G1 + G0, G1
        if G0 > bail: return
    x, y = a, b = (G0, B0) if i else (G0**2 + D * B0**2, 2 * G0 * B0)
    while x <= bail:
        yield (x, y)
        x, y = x*a + y*b*D, y*a + x*b

def carmichael(n):
    """
    The Carmichael lambda function: the smallest positive integer m such
    that pow(a,m,n) == 1 for all a such that gcd(a,n) == 1.  Also called the
    reduced totient or least universal exponent.
    
    Input: n -- a natural number
    
    Output: A natural number
    
    Examples:
    
    >>> [carmichael(n) for n in range(1, 23)]
    [1, 1, 2, 2, 4, 2, 6, 2, 6, 4, 10, 2, 12, 6, 4, 4, 16, 6, 18, 4, 6, 10]
    """
    # For general n, carmichael(n) is the lcm of the carmichael of each of its prime power factors.
    # If n is 2, 4, or p**k (for odd p and natural number k), charmichael(n) == totient(n) == p**(k-1) * (p-1).
    # If n is a power of 2 and >= 8, carmichael(n) == totient(n) // 2 == 2**(k-2).
    return lcm(*[(2**(k-2))if(p==2 and k>2)else(p**(k-1)*(p-1))for(p,k)in(factorint(n)if isinstance(n,inttypes)else n).items()])

def multord(b, n):
    """
    Computes the multiplicative order of b modulo n: that is, finds the
    smallest k such that b**k == 1 mod n).
    
    Input:
        b -- integer
        n -- integer or factorint output
    
    Output: An integer
    
    Examples:
    
    >>> multord(12, 97)
    16
    
    >>> multord(61, {2:3, 3:2})
    6
    """
    if isinstance(n, inttypes): nf = factorint(n)
    else: n, nf = prod(p**e for (p,e) in n.items()), n
    if b == 1 or n == 1: return 1
    if gcd(b, n) != 1: return None      # b must be relatively prime to n to have a multiplicative order modulo n
    for d in sorted(divisors(carmichael(nf))):      # This can be done more efficiently.                            TODO
        if pow(b, d, n) == 1: return d              # Also, we can do this repeated powering more efficiently.      TODO

def pythags(maxperim, primitive=False):
    """
    Uses Barning's tree to uniquely generate all Pythagorean triples up to
    and including the user-specified maximum perimeter.  Optionally, the
    non-primitive triples can be omitted.
    
    Do not expect the output to be in any particular order.
    
    Input:
        maxperim -- integer
        primitive -- True or False (default False).  If True, then only the
                     primitive triples are generated.
    
    Output: A sequence of tuples, each of which contains three integers.
    
    Examples:
    
    >>> sorted(pythags(80, primitive=True))
    [(3, 4, 5), (5, 12, 13), (7, 24, 25), (15, 8, 17), (21, 20, 29)]
    
    >>> sorted(pythags(47))
    [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15), (15, 8, 17)]
    """
    stack = [(3,4,5)]
    limit = 2
    while len(stack) > 0:
        a, b, c = stack.pop()
        assert a*a + b*b == c*c, (a,b,c)
        p = a + b + c
        if p > maxperim: continue
        if not primitive: limit = 1 + maxperim//p
        for k in range(1, limit): yield (k*a, k*b, k*c)
        A1, B1, C1 =  1*a - 2*b + 2*c,  2*a - 1*b + 2*c,  2*a - 2*b + 3*c
        A2, B2, C2 =  1*a + 2*b + 2*c,  2*a + 1*b + 2*c,  2*a + 2*b + 3*c
        A3, B3, C3 = -1*a + 2*b + 2*c, -2*a + 1*b + 2*c, -2*a + 2*b + 3*c
        stack.append((A1,B1,C1))
        stack.append((A2,B2,C2))
        stack.append((A3,B3,C3))

def pythags_by_perimeter(p):          # TODO: This is hideous.  Clean it up.
    """
    Generates all Pythagorean triples of a given perimeter.  Does so by
    examining the factors of the perimeter.
    
    Do not expect the output to be in any particular order.
    
    Input: p -- integer
    
    Output: A sequence of 3-tuples of integers.
    
    >>> list(pythags_by_perimeter(720))
    [(72, 320, 328), (45, 336, 339), (120, 288, 312), (270, 144, 306), (315, 80, 325), (180, 240, 300)]
    """
    # k * (m**2 - n**2)  ,  k * 2*m*n  ,  k * (m**2 + n**2)     k,m,n are natural numbers   m > n   gcd(m,n) == 1
    # This parametrizes all Pythagorean triples.
    # Note that the perimeter is  P == 2 * k * m * (m + n).
    # Thus, find all k,m,n satisfying these four conditions --- k,m,n in Z, m>n, gcd(m,n)==1, P==2*k*m*(m+n).
    # For each such triple, yield [k*(m**2-n**2), 2*k*m*n, k*(m**2+n**2)].
    if p%2: return
    p2 = p//2
    p2fac = factorint(p2)      # p/2 == k * m * (m+n)
    for kfac in divisors_factored(p2fac):
        k = prod(a**b for a,b in kfac.items())
        mxmpn, mxmpnfac = p2//k, {f:(g-kfac.get(f,0)) for f,g in p2fac.items() if g != kfac.get(f,0)}
        for mfac in divisors_factored(mxmpnfac):
            m = prod(a**b for a,b in mfac.items())
            mpn = mxmpn//m
            if not m < mpn < 2*m: continue
            n = mpn - m
            if gcd(m,n) != 1 or (m-n) % 2 == 0: continue
            #assert p == 2 * k * m * (m + n) and (m-n) % 2 == 1 and m > n and gcd(m,n) == 1
            a , b , c   =   k * (m**2 - n**2)  ,  2 * k * m * n  ,  k * (m**2 + n**2)
            yield (a,b,c)

def sqrtcfrac(n):
    """
    Computes the simple continued fraction for sqrt(n).  We return the
    answer as (isqrt(n), [a,b,c,...,d]), where [a,b,c,...,d] is the minimal
    reptend.
    
    Input: n -- an integer
    
    Output: a 2-tuple consisting of an integer and a (possibly empty) list
    
    Examples:
    
    >>> sqrtcfrac(114)
    (10, [1, 2, 10, 2, 1, 20])
    
    >>> sqrtcfrac(2)
    (1, [2])
    
    >>> sqrtcfrac(16)
    (4, [])
    """
    m0, d0 = 0, 1
    sr = a0 = isqrt(n)
    ret = (sr, [])
    if sr**2 == n: return ret
    while a0 != 2 * sr:
        m1 = d0*a0-m0
        d1 = (n-m1**2)//d0
        a1 = (sr+m1)//d1
        ret[1].append(a1)
        m0, d0, a0 = m1, d1, a1
    return ret

def convergents(a):
    """
    Generates the convergents of a simple continued fraction.
    
    Input -- a, an iterable that yields the SCF's terms
    
    Output -- a sequence of 2-tuples of integers (numerator, denominator)
    
    Examples:
    
    >>> list(convergents((1,2,2,2,2)))
    [(1, 1), (3, 2), (7, 5), (17, 12), (41, 29)]
    
    >>> list(convergents((2,1,2,1,1,4,1)))
    [(2, 1), (3, 1), (8, 3), (11, 4), (19, 7), (87, 32), (106, 39)]
    
    >>> list(convergents((3,7,15,1,292)))
    [(3, 1), (22, 7), (333, 106), (355, 113), (103993, 33102)]
    
    >>> a, b = sqrtcfrac(13)
    >>> list(islice(convergents(chain([a], cycle(b))), 8))
    [(3, 1), (4, 1), (7, 2), (11, 3), (18, 5), (119, 33), (137, 38), (256, 71)]
    """
    pm1, qm1, pm2, qm2 = 1, 0, 0, 1
    for n in a:
        p, q = n*pm1+pm2, n*qm1+qm2
        yield (p, q)
        pm1, qm1, pm2, qm2 = p, q, pm1, qm1

def contfrac_rat(n, d):
    """
    Returns the simple continued fraction of the rational number n/d.
    
    Input:
        num -- integer
        den -- positive integer coprime to num
    
    Output: sequence of integers
    
    Examples:
    
    >>> list(contfrac_rat(3, 2))
    [1, 2]
    
    >>> list(contfrac_rat(103993, 33102))
    [3, 7, 15, 1, 292]
    
    >>> list(contfrac_rat(*list(convergents((1,2,2,2,2,2,2,2,2,2)))[-1]))
    [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    
    >>> list(convergents(contfrac_rat(103993, 33102)))[-1]
    (103993, 33102)
    """
    while d != 0:
        yield n//d
        n, d = d, n%d

def quadratic_scf(P,Q,D):
    """
    Computes the simple continued fraction of the expression (P+sqrt(D))/Q,
    for any integers P, Q, and D with D >= 0 != Q.  Note that D can be a
    square or a nonsquare.  The continued fraction of any such expression is
    eventually periodic; if the expression is rational, then the periodic
    part has length zero; if the expression is irrational, then the periodic
    part has positive length.
    
    Input: P, Q, D -- integers
    
    Output: a tuple (head, tail), where head and tail are lists.  The
            continued fraction can then be generated with
                chain(head, cycle(tail)).
            If D is rational, then tail will be the empty list.
    
    Examples:
    
    >>> quadratic_scf(13, 8, 0)
    ([1, 1, 1, 1, 2], [])
    
    >>> quadratic_scf(13, 8, 5)
    ([1, 1, 9], [2, 8])
    
    >>> quadratic_scf(13, -8, 5)
    ([-2, 10], [2, 8])
    
    >>> quadratic_scf(13, 8, 25)
    ([2, 4], [])
    """
    # Finds the SCF of (P + sqrt(D)) / Q, for any integers P,Q,D with D >= 0 != Q.
    # Return format: (a,b), where a and b are lists.  The SCF is then chain(a, cycle(b)).
    # Note that (P+sqrt(D))/Q is rational, i.e. D is square, if and only if b is the empty list.
    assert D >= 0 != Q
    d = isqrt(D)
    if d*d == D: return (list(contfrac_rat(P + d, Q)), [])
    history = []
    while True:
        a = (P + d) // Q
        if (a,P,Q,D) in history:
            x = history.index((a,P,Q,D))
            return ([history[t][0] for t in range(x)], [history[t][0] for t in range(x,len(history))])
            #return ([t[0] for t in history[:x]], [t[0] for t in history[x:]])
        history.append((a,P,Q,D))
        P -= a * Q
        # Now replace (P+sqrt(D))/Q with Q/(P+sqrt(D)) == Q * (-P+sqrt(D)) / (D - P^2) and simplify.
        newP, newQ, newD = -P*Q, D - P*P, D*Q*Q
        if Q < 0: newP, newQ = -newP, -newQ
        g = gcd(Q, newQ)
        P, Q, D = newP//g, newQ//g, newD//(g*g)
        d = isqrt(D)

def partgen(n):
    """
    Generates partitions of integers in ascending order via an iterative
    algorithm.  The current algorithm is derived from "accelAsc" in
    http://arxiv.org/pdf/0909.2331v2.pdf, which the authors claim to be
    the fastest-known algorithm as of June 2014.
    
    Input: n -- an integer
    
    Output: Sequence of lists of integers
    
    Examples:
    
    >>> list(partgen(5))
    [[1, 1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 3], [1, 2, 2], [1, 4], [2, 3], [5]]
    
    >>> pg = partgen(50)
    >>> for _ in range(2 * 10**5): x = next(pg)
    >>> next(pg)
    [3, 4, 5, 5, 6, 6, 6, 6, 9]
    """
    a, k, y = [0]*n, 1, n-1
    while k != 0:
        x = a[k - 1] + 1
        k -= 1
        while 2*x <= y:
            a[k] = x
            y -= x
            k += 1
        l = k + 1
        while x <= y:
            a[k], a[l] = x, y
            yield a[:k + 2]
            x += 1
            y -= 1
        a[k] = x + y
        y = x + y - 1
        yield a[:k + 1]

def partconj(p):        # TODO: Can we do better?
    """
    Computes the conjugate of a partition
    
    Input: p -- a list or tuple of natural numbers
    
    Output: A tuple of integers
    
    Examples:
    
    >>> partconj([1, 2, 3, 4, 5])
    [1, 2, 3, 4, 5]
    
    >>> partconj([1, 2, 6, 8])
    [1, 1, 2, 2, 2, 2, 3, 4]
    """
    array, w, h = [], max(p), len(p)
    for n in range(h): array.append([1] * p[n]  +  [0] * (w-p[n]))
    return [sum(array[n][t] for n in range(h)) for t in range(w-1, -1, -1)]

def farey(n):
    """
    Generates the Farey sequence of maximum denominator n.
    Includes 0/1 and 1/1.
    
    Input: n -- a positive integer
    
    Output: Sequence of lists of the form [integer, integer]
    
    Examples:
    
    >>> list(farey(5))
    [(0, 1), (1, 5), (1, 4), (1, 3), (2, 5), (1, 2), (3, 5), (2, 3), (3, 4), (4, 5), (1, 1)]
    """
    a, b, c, d = 0, 1, 1, n
    yield (a, b)
    while c <= n:
        k = (n + b)//d
        a, b, c, d = c, d, k*c-a, k*d-b
        yield (a, b)

def fareyneighbors(n, p, q):
    """
    Returns the neighbors of p/q in the Farey sequence whose maximum
    denominator is n.
    
    Inputs: n, p, q -- positive integers
    
    Output: List of two two-tuples of integers
    
    Examples:
    
    >>> fareyneighbors(5, 1, 3)
    [(1, 4), (2, 5)]
    
    >>> fareyneighbors(121, 5, 121)
    [(4, 97), (1, 24)]
    
    >>> fareyneighbors(121, 74, 95)
    [(81, 104), (67, 86)]
    
    >>> fareyneighbors(121, 67, 86)
    [(74, 95), (60, 77)]
    
    >>> fareyneighbors(121, 16, 21)
    [(83, 109), (77, 101)]
    """
    # Let a/b < c/d.  Then there exists a Farey sequence in which a/b and c/d are neighbors   iff   bc - ad == 1.
    # Futhermore, they are neighbors in F_n where n == max(b,d).
    # The first fraction to split the Farey pair a/b,c/d is their mediant, (a+b)/(c+d).
    div = gcd(p,q)
    p, q = p//div, q//div
    answer = [0, 0]
    # No need to worry about pow raising a ValueError in this next line; p and q are guaranteed to be coprime by now.
    pl, ql = -pow(q, -1, p) % p , pow(p, -1, q)
    pr, qr = p - pl , q - ql
    fl, fr = (n - ql) // q, (n - qr) // q
    return [(pl + p*fl, ql + q*fl) , (pr + p*fr, qr + q*fr)]

def ispractical(n):
    """
    Tests whether n is a practical number -- i.e., whether every integer
    from 1 through n (inclusive) can be written as a sum of divisors of n.
    These are also called panarithmic numbers.
    
    Input: n -- an integer
    
    Output: True or False
    
    Examples:
    """
    # This bit here is an O(n) test that is derived directly from the definition.  Keeping it for some sort of nostalgia.
    #divs = [d for d in divisors(n) if d < n]
    #divsums = set([0]) # divsums will contain those subset sums over the divisors of n that are strictly less than n
    #for d in divs: divsums.update([x+d for x in divsums if x+d < n])
    #return sorted(divsums) == range(n)
    if n < 2 or n%2 == 1: return n == 1
    fac = factorint(n)
    p, k = sorted(fac), len(fac)
    # This next line can be done more efficiently in a procedural manner by accumulating the listprods as we proceed.  Not much
    # of an optimization in relative terms (most of our effort goes into factoring n), but it speeds things up a few percent.
    #return all(p[i] <= 1 + prod(p[j]**(a[j]+1)-1 for j in range(i))/listprod(p[j]-1 for j in range(i)) for i in range(1,k))
    sig = 1
    for i in range(k-1):
        sig *= (p[i]**(fac[p[i]]+1) - 1) // (p[i] - 1)
        if p[i+1] > 1 + sig: return False
    return True

def hamming(ps, *ps2):
    """
    Generates in order all ps-smooth numbers.
    Modified from https://code.activestate.com/recipes/576961/.
    
    Input: ps -- indexable iterable of primes
    
    Output: sequence of integers
    
    Examples:
    
    >>> list(islice(hamming((2,3,5)), 21))
    [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40]
    """
    if isinstance(ps, inttypes): ps = list(set([ps] + list(ps2)))
    def deferred(): yield from output
    t = tee(deferred(), len(ps)+1)
    output = (k for (k,_) in groupby(chain([1], merge(*((lambda p,h:(p*x for x in h))(p,h) for (p,h) in zip(ps,t))))))
    return t[-1]

def perfectpowers():                                                 # TODO This can probably be made more efficient with heapq.
    """
    Generates in order the sequence of perfect powers without multiplicity.
    
    Input: none
    
    Output: sequence of integers
    
    Examples:
    
    >>> list(islice(perfectpowers(), 18))
    [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 81, 100, 121, 125, 128, 144, 169]
    """
    yield from (1,4,8,9)
    pows = [16, 27]
    rts = [4, 3]
    pg = primegen()
    ps = [next(pg), next(pg)]
    while True:
        x = min(pows)
        yield x
        for (n,p) in enumerate(pows):
            if p == x:
                r = rts[n]
                r += 1
                rts[n] = r
                pows[n] = r**ps[n]
                if n+1 == len(pows):
                    rts.append(2)
                    ps.append(next(pg))
                    pows.append(2**ps[-1])

def sqfrgen(ps):
    """
    Generates squarefree products of elements of ps.
    
    Do not expect the output to be in any particular order.
    
    Input: ps -- indexable iterable of primes
    
    Output: sequence of integers
    
    Examples:
    
    >>> sorted(filter(lambda x: x < 75, sqfrgen(list(primegen(12)))))
    [1, 2, 3, 5, 6, 7, 10, 11, 14, 15, 21, 22, 30, 33, 35, 42, 55, 66, 70]
    """
    if len(ps) == 0: yield 1; return
    for n in sqfrgen(ps[1:]): yield n; yield n*ps[0]

def sqfrgenb(ps, b, k=0, m=1):                               # TODO this can be rather more efficient.
    """
    Generates squarefree products of elements of ps that are <= b.  We do
    this with some efficiency by conducting a depth-first search and pruning
    branches of the tree that generate numbers greater than the bound.  For
    fastest results, ps should be sorted in decreasing order.
    
    Do not expect the output to be in any particular order.
    
    Input:
        ps -- indexable iterable of primes
        b -- integer
        k, m -- for internal use only.
    
    Output: sequence of integers
    
    Examples:
    
    >>> sorted(sqfrgenb(list(primegen(18)), 36))
    [1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 21, 22, 26, 30, 33, 34, 35]
    """
    if m > b: return
    if k == len(ps): yield 1; return
    p = ps[k]
    yield from sqfrgenb(ps, b, k=k+1, m=m)
    for x in sqfrgenb(ps, b, k=k+1, m=m*p):
        if x * p <= b: yield x * p

def stormer(ps, *ps2, abc=None, sep=1):
    """
    For any given set ps of prime numbers, there are only finitely many
    pairs of consecutive integers (n,n+1) or (n,n+2) that are both
    ps-smooth.  Stormer's theorem provides a method to find them all.  We
    implement Lehmer's simplification of that method.  It is worth noting
    that the time to complete this iteration for the first n primes appears
    to scale superexponentially in n, while iterating hamming() over the
    nth-prime-smooth numbers up to the largest such value appears to scale
    singly exponentially; however, max(stormer(ps)) cannot yet be computed
    without actually executing the Stormer-Lehmer algorithm.
    
    Do not expect the output to be in any particular order.
    
    Let S be a set of primes, let x and x+{1,2} be S-smooth, and let T be
    the product of the elements of S.  Then on the abc conjecture we have
    x+1 < k * rad(1 * x * (x+1)) ** d < k * T**d
    and
    x+2 < k * rad(2 * x * (x+2)) ** d < k * T**d.
    This enables a major speedup.
    
    Input:
        ps -- indexable iterable of primes
        abc -- Assume an effective abc conjecture of the form
               c < abc[0] * rad(a*b*c)**abc[1].
               Default == None; i.e., make no assumptions.
        sep -- 1 or 2.  We find pairs (n, n+sep).  Default == 1.
    
    Output: finite sequence of pairs of integers
    
    Examples:
    
    >>> sorted(stormer(2,3,5))
    [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (8, 9), (9, 10), (15, 16), (24, 25), (80, 81)]
    
    >>> sorted(stormer(2,3,5, sep=2))
    [(1, 3), (2, 4), (3, 5), (4, 6), (6, 8), (8, 10), (10, 12), (16, 18), (18, 20), (25, 27), (30, 32), (48, 50), (160, 162)]
    
    >>> x = list(stormer(list(primegen(32))))
    >>> (max(x), len(x))
    ((1611308699, 1611308700), 482)
    
    >>> sum(x*y for (x,y) in stormer(2,3,5,7,11,13,17,19,23,29))
    41405478516828404
    """
    if isinstance(ps, inttypes): ps = [ps] + list(ps2)
    if (sep == 1) and (2 not in ps): return
    pl = [mpz(x) for x in set(ps)]
    assert all(isprime(x) for x in pl)
    k = max(3, (max(pl)+1)//2)
    abc = abc[0] * prod(pl)**abc[1] if abc else inf
    bail = abc * 2 + 1
    if sep == 1:
        for sqfr in sqfrgen(pl):
            for (n,(x,y)) in enumerate(simplepell(2 * sqfr, bail=bail)):
                if n >= k: break
                # We now check that we have found a smooth number.  We do not outsource to factorint since we only need to divide
                # out the small primes and check whether anything remains --- we do not need to get stuck factoring RSA numbers.
                z = (x+1) * (x-1) // 4
                for p in pl:
                    while z % p == 0: z //= p
                if z == 1: yield (int((x-1)//2), int((x+1)//2))
                elif n == 0: break  # Pell solutions have some nice divisibility properties that allow us to sieve out
                # subsequent solutions if one of them turns out to have a prime factor not in ps.  In the simplest case, if the
                # fundamental solution produces a rough result, we can skip all subsequent solutions from that Pell equation.
                # This is a major speedup.  See https://projecteuclid.org/download/pdf_1/euclid.ijm/1256067456 page 11/67.
        return
    if sep == 2:
        for sqfr in sqfrgen(pl):
            for (n,(x,y)) in enumerate(simplepell(sqfr, bail=bail)):
                if n >= k: break
                # We now check that we have found a smooth number.  We do not outsource to factorint since we only need to divide
                # out the small primes and check whether anything remains --- we do not need to get stuck factoring RSA numbers.
                z = (x+1) * (x-1)
                for p in pl:
                    while z % p == 0: z //= p
                if z == 1: yield (x-1, x+1)
                elif n == 0: break  # Pell solutions have some nice divisibility properties that allow us sieve out
                # subsequent solutions if one of them turns out to have a prime factor not in ps.  In the simplest case, if the
                # fundamental solution produces a rough result, we can skip all subsequent solutions from that Pell equation.
                # This is a major speedup.  See https://projecteuclid.org/download/pdf_1/euclid.ijm/1256067456 page 11/67.
        return

def quadintroots(a, b, c):
    """
    Given integers a,b,c, we return in a tuple all distinct integers x such
    that a*x^2 + b*x + c == 0.  This is primarily a helper function for
    cubicintrootsgiven and cubicintroots.
    
    Do not expect the output to be in any particular order.
    """
    if a == 0: return () if b == 0 else ((-c//b,) if c % b == 0 else ())
    if c == 0:
        if b == 0: return (0,)
        if b % a == 0: return (0, -b//a)
        return (0,)
    D = b*b - 4*a*c
    if D < 0: return ()
    d = ispower(D, 2)
    if d is None: return ()
    if d == 0: return ((-b//(2*a),) if b % (2*a) == 0 else ())
    r1n, r2n, den = -b + d, -b - d, 2*a
    return tuple(x//den for x in (r1n, r2n) if x % den == 0)

def cubicintrootsgiven(a, b, c, d, r):
    """
    Given integers a,b,c,d,r such that a * r^3 + b * r^2 + c * r + d == 0,
    we find the cubic's other two roots and return in a tuple all distinct
    integer roots (including r).  This is primarily a helper function for
    cubicintroots.  Algorithm: divide (a*x^3 + b*x^2 + c*x + d) by (x - r)
    and use quadintroots on the result.
    
    Do not expect the output to be in any particular order.
    """
    cubic = lambda x: ((a*x + b) * x + c) * x + d
    assert cubic(r) == 0, (a,b,c,d,r)
    # We have 3 distinct real roots.  r is one of them and happens to be an integer.  Divide the polynomial by x-r.
    # The result will be a quadratic with integer coefficients.
    p = b + a*r
    q = c + p*r
    assert d == -q*r, (a,b,c,d,p,q,r)
    # Now solve a * x^2 + p * x + q == 0.
    roots = {r} | set(quadintroots(a, p, q))
    assert all(cubic(r) == 0 for r in roots), (a,b,c,d,r,roots)
    return tuple(roots)

def cubicintroots(a, b, c, d):
    """
    Given integers a,b,c,d, we efficiently find and return in a tuple all
    distinct integer roots of a * x^3 + b * x^2 + c * x + d.
    This is primarily a helper function for isprime_nm1 and isprime_np1.
    
    Do not expect the output to be in any particular order.
    
    Algorithm:
    0.  We could just use the rational roots theorem, but that would require
        factoring the coefficients.  We expect them to be very large, so
        that is not an option.  We cannot use the cubic formula either,
        since that would require the use of floats, and since we are
        sticking with native data types, we cannot trust floats beyond
        2**53.  So we must stick with integer arithmetic, which makes
        some things a bit tricky (especially the interval partitioning in
        the case of positive discriminant).
    1.  If a == 0, then return quadintroots(b,c,d).
    2.  Fiddle with coefficient signs so that a > 0 > d.
    3.  If d == 0, then run quadintroots(a,b,c) and merge 0 into the result.
    4.  Let D be the discriminant.  If D == 0, then we have a repeated root.
        The roots are all rational numbers and can be extracted via simple
        formulas without using radicals.
    5.  By the Rouche theorem, H = 2 + max(abs(b),abs(c),abs(d)) // a is an
        upper bound on the magnitude of any root.
    6.  If D < 0, then we have 1 real and 2 complex roots.  Since a > 0 > d,
        the real root will be in the interval (0, H), and we find it via
        binary splitting.
    7.  We are now in the case of 3 distinct real roots.  They are all in
        the interval (-H,H).  Partition this interval into 3 subintervals,
        using the critical points as the boundaries.  Since we are doing
        this using only integers, there are a lot of subcases to check and
        things get a bit fiddly, but it is doable.
    8.  Use binary splitting on the 3 subintervals.
    """
    # Since we are looking for integer roots, we can just try divisors(d), but we are trying to be efficient.
    if a == 0: return quadintroots(b,c,d)
    if d > 0: return cubicintroots(-a, -b, -c, -d)
    if a < 0: return tuple(-x for x in cubicintroots(-a, b, -c, d))
    if d == 0:
        roots = quadintroots(a,b,c)
        return roots if 0 in roots else (roots + (0,))
    # From here onwards, we assume that a > 0 >= d.
    D = 18*a*b*c*d - 4*b*b*b*d + b*b*c*c - 4*a*c*c*c - 27*a*a*d*d
    cubic = lambda x: ((a*x + b) * x + c) * x + d
    # If D > 0, then we have 3 distinct real roots.
    # If D == 0, then we have a triple root or 2 distinct real roots with multiplicities 1 and 2.
    # If D < 0, then we have 1 real root and two distinct complex roots.
    if D == 0: # We have a triple root or 2 distinct real roots with multiplicities 1 and 2.
        D0 = b*b - 3*a*c
        if D0 == 0: # Triple root!
            num, den = -b, 3*a
            if num % den == 0:
                assert cubic(num//den) == 0, (a,b,c,d)
                return (num//den,)
            return ()
        n1, d1 = 9*a*d - b*c, 2*D0                  # the double root is n1/d1.
        n2, d2 = 4*a*b*c - 9*a*a*d - b*b*b, a*D0    # the single root is n2/d2.
        roots = tuple(x//y for (x,y) in ((n1,d1), (n2,d2)) if x % y == 0)
        assert all(cubic(r) == 0 for r in roots), (a,b,c,d)
        return roots
    H = 2 + max(abs(b),abs(c),abs(d)) // a  # By the Rouche theorem, this is strictly greater than each root's magnitude.
    if D < 0: # 1 real root and 2 complex roots.  Since d < 0 < a, the real root will be positive.
        l, h = 0, H
        while l + 1 < h:
            m = (l + h) // 2
            cu = cubic(m)
            if cu == 0: return (m,)
            if cu > 0: h = m
            if cu < 0: l = m
        return ()   # That one real root turned out to not be an integer, so we are done.
    # So we now have a cubic with positive discriminant and therefore 3 distinct real roots, at least one of which is > 0.
    deriv = lambda x: (3*a*x + 2*b)*x + c
    # Since there are 3 distinct real roots, the cubic's derivative will have two distinct real roots, q1 and q2.
    # The cubic's roots will be found in the intervals (-H, q1), (q1, q2), and (q2, H).
    # The roots will not be at q1 or q2 since we would then have a double root, and we have already handled this case.
    qr = sorted(quadintroots(3*a, 2*b, c))
    if len(qr) == 2: inspect = ((-H,qr[0]), qr, (qr[1],H))
    elif len(qr) == 1:
        qr = qr[0]
        # Since qr is a root of the derivative, we have
        # qr == (-2b +/- sqrt(4b^2 - 12ac)) / (6a)
        #qs = Fraction(-2*b, 3*a) - qr
        #assert deriv(qr) == 0, (a,b,c,d,qr)
        #assert deriv(qs) == 0, (a,b,c,d,qs)
        # qr is the integer critical point, and qs is the non-integer critical point.
        s = -2*b - 3*a*qr
        # So we have one critical point at qr, which is an integer.  The other one is at qs == s/(3*a), which is not an integer.
        #assert s == qs * 3*a
        assert deriv(qr) == 0, (a,b,c,d)
        #assert qs.denominator != 1, (a,b,c,d)
        assert s % (3*a) != 0, (a,b,c,d)
        # The inflection point is -b/(3*a).
        # qs < -b/(3*a) --> (-2b) - 3*a*qr < (-b) --> s < (-b)
        if s < -b: # The nonintegral critical point is below the inflection point.
            inspect = ((qr,H),)
            q1, q2 = s//(3*a), qr # q1 is the floor of the lower critical point.
            cq1 = cubic(q1)
            if cq1 < 0: pass # The lower root is between the lower critical point and its floor and therefore not an integer.
            elif cq1 > 0: inspect += ((-H,q1),)
            else: return cubicintrootsgiven(a,b,c,d,q1)
            # Now for the middle interval:
            q1 += 1 # q1 is now the ceiling of the lower critical point.
            cq1 = cubic(q1)
            if cq1 < 0: pass # The middle root is between the lower critical point and its ceiling and therefore not an integer.
            elif cq1 > 0: inspect += ((q1,q2),)
            else: return cubicintrootsgiven(a,b,c,d,q1)
        else:      # The nonintegral critical point is above the inflection point.
            assert s > -b, (a,b,c,d)
            inspect = ((-H,qr),)
            q1, q2 = qr, s//(3*a) + 1 # q2 is the ceiling of the upper critical point.
            cq2 = cubic(q2)
            #print(q1,q2,cq2)
            if cq2 > 0: pass # The upper root is between the upper critical point and its ceiling and therefore not an integer.
            elif cq2 < 0: inspect += ((q2,H),)
            else: return cubicintrootsgiven(a,b,c,d,q2)
            # Now for the middle interval:
            q2 -= 1 # q2 is now the floor of the upper critical point.
            cq2 = cubic(q2)
            if cq2 > 0: pass # The middle root is between the upper critical point and its floor and therefore not an integer.
            elif cq2 < 0: inspect += ((q1,q2),)
            else: return cubicintrootsgiven(a,b,c,d,q2)
    else: # Neither of the derivative's roots is an integer.
        # The derivative is 3*a*x^2 + 2*b*x + c with roots at (-2b +- sqrt(4b^2-4*3ac)) / (6a) = (-b +- sqrt(b^2 - 3ac)) / (3a).
        dD = b*b - 3*a*c
        qdr1, qdr2 = isqrt(dD-1)+1, isqrt(dD)
        q1, q2 = (-b-qdr1) // (3*a), (-b+qdr2) // (3*a) + 1
        # So now q1 should be the floor of the lower critical point and q2 should be the ceiling of the upper.
        assert deriv(q1) > 0 < deriv(q2), (a,b,c,d,q1,q2,deriv(q1),deriv(q2))
        assert 3*a*q1 < -b < 3*a*q2, (a,b,c,d)
        inspect = ()
        cq2 = cubic(q2)
        if cq2 < 0: inspect += ((q2,H),)
        elif cq2 > 0: pass # The upper root is between the upper critical point and its ceiling and is therefore not an integer.
        else: return cubicintrootsgiven(a,b,c,d,q2)
        cq1 = cubic(q1)
        if cq1 > 0: inspect += ((-H,q1),)
        elif cq1 < 0: pass # The lower root is between the upper critical point and its ceiling and is therefore not an integer.
        else: return cubicintrootsgiven(a,b,c,d,q1)
        cq1p, cq2m = cubic(q1+1), cubic(q2-1)
        if cq1p < 0 < cq2m or cq1p > 0 > cq2m: inspect += ((q1+1,q2-1),)
        elif cq1p == 0 or cq2m == 0: return cubicintrootsgiven(a,b,c,d, q1+1 if cq1p == 0 else q2-1)
        else: pass # The middle root is between the lower CP and its ceiling or between the upper CP and its floor.
    for (l,h) in inspect:
        cul, cuh = cubic(l), cubic(h)
        assert cul < 0 < cuh or cuh < 0 < cul, (a,b,c,d,inspect)
        f = (lambda x: -cubic(x)) if cuh < 0 < cul else cubic
        # f is increasing across the interval.
        # We are looking for a root strictly between l and h.
        while l+1 < h:
            m = (l + h) // 2
            fm = f(m)
            if fm > 0: h = m
            if fm < 0: l = m
            if fm == 0: return cubicintrootsgiven(a,b,c,d,m)
    # If we get to this point, then no root is an integer.
    return ()

def isprime_nm1(n, fac=None): # CranPom Alg 4.1.7, pg 178/190
    """
    The n-1 primality test: given an odd integer n > 214 and a
    fully-factored integer F such that F divides n-1 and F > n**0.3, we
    quickly determine without error whether n is prime.
    For details, see Crandall & Pomerance Alg 4.1.7.
    
    Input:
        n -- integer
        fac -- None or a (partial) factorization of n-1.  If fac == None
               (default), then we compute the factorization ourselves.  If
               fac is provided and is either insufficient (i.e.
               prod(p**e for (p,e) in fac.items()) < n**0.3) or is not a
               (partial) factorization of n-1, then we raise an
               AssertionError.
    
    Output: True or False
    
    Examples:
    
    >>> isprime_nm1(prod(range(1,78))+mpz(1))
    True
    
    >>> isprime_nm1(prod(range(1,79))+mpz(1))
    False
    """
    if n < 214: return (n == 2) if (n % 2 == 0 or n < 3) else (pow(2, n-1, n) == 1)
    n2r = isqrt(n)
    if n2r**2 == n: return False
    n3r = introot(n, 3)
    if n3r**3 == n: return False
    np3 = introot(n**3, 10) # We do not need to check this one's irrationality.
    bnd = np3
    if fac:
        # Do some sorting to select the smallest number of primes that pushes us over bnd.
        # This should minimize the time spent in the Pocklington loops.
        F, faclist, facnew = 1, sorted([(p**e, p, e) for (p,e) in fac.items()]), {}
        for (pe,p,e) in faclist:
            F *= pe
            facnew[p] = e
            if F > bnd:
                fac = facnew
                break
    else:
        F, fac = 1, {}
        for p in primefac(n-1):
            F *= p
            fac[p] = fac.get(p, 0) + 1
            if F > bnd: break
    assert (n-1) % F == 0, "The provided (partial) factorization is not of n-1."
    assert F == prod(p**e for (p,e) in fac.items())
    assert F > bnd, "The provided partial factorization of n-1 is insufficient."
    # 1.  Pocklington test.
    for a in range(2, n-1):
        if pow(a, n-1, n) != 1: return False
        for p in fac:
            g = gcd(n, pow(a, (n-1)//p, n) - 1)
            if 1 < g < n: return False
            if g == n: break # next a-value
        else: break # goto 2
    else: raise Exception
    # 2.  First magnitude test.
    if F > n2r: return True
    # 3.  Second magnitude test.
    if n3r < F:
        c2, c1 = divmod(n//F, F)
        assert (c2 * F + c1) * F + 1 == n
        c = c1**2 - 4 * c2
        return (c < 0) or (c != isqrt(c)**2)
    # Suppose n-1 == F*R with F >= n**0.3.
    # 4.  Third magnitude test.
    # If conditions 1 and 2 of Theorem 4.1.6 (p176/188) hold, return True; otherwise, return False.  To wit:
    # Write n as c3 * F**3 + c2 * F**2 + c1 * F + 1, and let c4 = c3 * F + c2.
    # Condition 1: (c1 + t*F)**2 + 4*t - 4*c4 is not a square for t in (0,1,2,3,4,5).
    # Condition 2: Let u/v be the contfrac convergent to c1/F such that v is maximal subject to v < F**2 / sqrt(n), and let
    # d = (2*c4*v+F) // (2*F).  Then the polynomial v * x**3 + (u*F-c1*v) * x**2 + (c4*v-d*F+u) * x - d has no integral root r
    # such that r*F + 1 is a nontrivial factor of n.
    if np3 < F:
        nn = n
        assert nn % F == 1
        nn //= F
        nn, c1 = divmod(nn, F)
        nn, c2 = divmod(nn, F)
        nn, c3 = divmod(nn, F)
        c4 = c3 * F + c2
        assert (c4 * F + c1) * F + 1 == n
        # Condition 1: (c1 + t*F)**2 + 4*t - 4*c4 is not a square for t in (0,1,2,3,4,5).
        if any(ispower((c1 + t*F)**2 + 4*t - 4*c4, 2) for t in (0,1,2,3,4,5)): return False
        # Condition 2: Let u/v be the contfrac convergent to c1/F such that v is maximal subject to v < F**2 / sqrt(n), and let
        # d = (2*c4*v+F) // (2*F).  Then the polynomial v * x**3 + (u*F-c1*v) * x**2 + (c4*v-d*F+u) * x - d has no integral root
        # r such that r*F + 1 is a nontrivial factor of n.
        F4, u, v = F**4, 0, 0
        for (U,V) in convergents(contfrac_rat(c1,F)):
            if V * V * n >= F4: break
            u, v = U, V
        d = (2*c4*v + F) // (2*F)
        a, b, c, d = v, u*F - c1*v, c4*v - d*F + u, -d
        g = gcd(a,b,c,d)
        a, b, c, d = a//g, b//g, c//g, d//g
        for r in cubicintroots(a,b,c,d):
            print(n)
            f = r*F + 1
            if 1 != f != n and n % f == 0: return False
        return True
    assert False # We should not reach this point.

def isprime_np1(n, fac=None):
    """
    The n+1 primality test: given an odd integer n > 214 and a
    fully-factored integer F such that F divides n+1 and F > n**0.3, we
    quickly determine without error whether n is prime.
    For details, see Crandall & Pomerance section 4.2.
    
    Input:
        n -- integer
        fac -- None or a (partial) factorization of n+1.  If fac == None
               (default), then we compute the factorization ourselves.  If
               fac is provided and is either insufficient (i.e.
               prod(p**e for (p,e) in fac.items()) < n**0.3) or is not a
               (partial) factorization of n+1, then we raise an
               AssertionError.
    
    Output: True or False
    
    Examples:
    
    >>> isprime_np1(prod(range(1,94))-mpz(1))
    False
    
    >>> isprime_np1(prod(range(1,95))-mpz(1))
    True
    """
    if n < 214: return (n == 2) if (n % 2 == 0 or n < 3) else (pow(2, n-1, n) == 1)
    if n % 2 == 0: return False
    n2r = isqrt(n)
    if n2r**2 == n: return False
    n3r = introot(n, 3)
    if n3r**3 == n: return False
    np3 = introot(n**3, 10) # We do not need to check this one's irrationality.
    bnd = np3
    if fac:
        # Do some sorting to select the smallest number of primes that pushes us over bnd.
        # This should minimize the time spent in the Pocklington loops.
        F, faclist, facnew = 1, sorted([(p**e, p, e) for (p,e) in fac.items()]), {}
        for (pe,p,e) in faclist:
            F *= pe
            facnew[p] = e
            if F > bnd:
                fac = facnew
                break
    else:
        F, fac = 1, {}
        for p in primefac(n+1):
            F *= p
            fac[p] = fac.get(p, 0) + 1
            if F > bnd: break
    assert (n+1) % F == 0, "The provided (partial) factorization is not of n+1."
    assert F == prod(p**e for (p,e) in fac.items())
    assert F > bnd, "The provided partial factorization of n+1 is insufficient."
    # 1.  Pocklington test adaptation.
    for a in range(1, n):
        for b in range(1, n):
            D = a*a - 4*b
            g = gcd(n,b)
            if g != 1:
                if g == n: continue # Select another b
                else: assert 1 < g < n and n % g == 0; return False
            j = jacobi(D,n)
            if j == 0:
                g = gcd(D,n)
                if 1 < g < n: assert n % g == 0; return False
                continue    # Select another a,b
            if j == 1: continue # Select another a,b
            # The lucasmod in the next line contains a pow(., -1, .) call.
            # This is guaranteed to not raise a ValueError thanks to the "if j == 0" bit above.
            if lucasmod(n+1, a, b, n)[0] != 0: return False
            for q in fac:
                # The lucasmod in the next line contains a pow(., -1, .) call.
                # This is guaranteed to not raise a ValueError thanks to the "if j == 0" bit above.
                g = gcd(lucasmod((n+1)//q, a, b, n)[0], n)
                if g == 1: continue
                elif g == n: break  # Select another a,b
                else: assert 1 < g < n and n % g == 0; return False
            else: break         # goto 2
        else: continue          # We exhausted all b-values for the current a-value.  Go to the next a.
        break       # If we are here, then we have broken the b-loop, which means that the Pocklington stuff succeeded.  Goto 2.
    else: raise Exception
    # 2.  First magnitude test.
    if F > n2r+1: return True
    # 3.  Second magnitude test.
    if n3r+1 < F:
        R = (n+1) // F
        assert R*F == n+1
        r1, r0 = divmod(R,F)
        assert R == r1 * F + r0
        # n is prime if and only if neither x**2 + r0 * x - r1 nor x**2 + (r0-F) * x - (r1+1) has a positive integral root.
        # Roots of first poly: (-r0 +/- sqrt(D)) / 2, where D = r0**2 + 4*r1
        # Roots of second poly: (F - r0 +/- sqrt(D)) / 2, where D = (r0-F)^2 + 4*(r1+1)
        D = r0*r0 + 4*r1
        d = ispower(D, 2)
        if d: # If the + root is a positive integer, return False
            if d > r0 and (d-r0) % 2 == 0: return False
        D = (r0-F)**2 + 4*r1 + 4
        d = ispower(D, 2)
        if d: # If the + root is a positive integer, return False
            if F + d > r0 and (F - r0 + d) % 2 == 0: return False
        return True
    # Suppose n+1 == F*R with F >= n**0.3.
    # 4.  Third magnitude test.
    # If conditions 1 and 2 of Theorem 4.1.6 (p176/188) hold, return True; otherwise, return False.  To wit:
    # Write n+1 as c3 * F**3 + c2 * F**2 + c1 * F, and let c4 = c3 * F + c2.
    # Condition 1: (c1 + t*F)**2 - 4*t + 4*c4 is not a square for t in (-5,-4,-3,-2,-1,0,1,2,3,4,5).
    # Condition 2: Let u/v be the contfrac convergent to c1/F such that v is maximal subject to v < F**2 / sqrt(n), and let
    # d = (2*c4*v+F) // (2*F).  Then the polynomial v * x**3 - (u*F-c1*v) * x**2 - (c4*v-d*F+u) * x + d has no integral root r
    # such that r*F + 1 is a nontrivial factor of n, and the polynomial v * x**3 + (u*F-c1*v) * x**2 - (c4*v+d*F+u) * x + d has
    # no integral root r such that r*F - 1 is a nontrivial factor of n.
    if np3 < F:
        nn = n + 1
        assert nn % F == 0
        nn //= F
        nn, c1 = divmod(nn, F)
        nn, c2 = divmod(nn, F)
        nn, c3 = divmod(nn, F)
        c4 = c3 * F + c2
        #assert (c4 * F + c1) * F == n + 1
        assert c3 * F**3 + c2 * F**2 + c1 * F == n+1, (n,F,c3,c2,c1, c3 * F**3 + c2 * F**2 + c1 * F)
        # Condition 1: (c1 + t*F)**2 - 4*t + 4*c4 is not a square for t in (-5,-4,-3,-2,-1,0,1,2,3,4,5).
        if any(ispower((c1 + t*F)**2 - 4*t + 4*c4, 2) for t in (-5,-4,-3,-2,-1,0,1,2,3,4,5)): return False
        # Condition 2: Let u/v be the contfrac convergent to c1/F such that v is maximal subject to v < F**2 / sqrt(n), and let
        # d = (2*c4*v+F) // (2*F).  Then the polynomial v*x**3 - (u*F-c1*v)*x**2 - (c4*v-d*F+u)*x + d has no integral root r
        # such that r*F + 1 is a nontrivial factor of n, and the polynomial v*x**3 + (u*F-c1*v)*x**2 - (c4*v+d*F+u)*x + d has no
        # integral root r such that r*F - 1 is a nontrivial factor of n.
        F4, u, v = F**4, 0, 0
        for (U,V) in convergents(contfrac_rat(c1,F)):
            if V * V * n >= F4: break
            u, v = U, V
        D = (2*c4*v + F) // (2*F)
        a, b, c, d = v, u*F - c1*v, c4*v - D*F + u, D
        g = gcd(a,b,c,d)
        a, b, c, d = a//g, b//g, c//g, d//g
        for r in cubicintroots(a,-b,-c,d):
            f = r*F + 1
            if 1 != f != n and n % f == 0: return False
        a, b, c, d = v, u*F - c1*v, c4*v + D*F + u, D
        g = gcd(a,b,c,d)
        a, b, c, d = a//g, b//g, c//g, d//g
        for r in cubicintroots(a,b,-c,d):
            f = r*F - 1
            if 1 != f != n and n % f == 0: return False
        return True
    assert False # We should not reach this point.

def mulparts(n, r=None, nfac=None):
    """
    Generates all multiplicative partitions of n: that is, all ordered
    r-tuples of positive integers whose product is n.
    
    Do not expect the output to be in any particular order.
    
    Input:
        n, r -- integers.
                If r is None and n == 1: yield (1,) and stop.
                If r is None and n != 1: generate all multiplicative
                                         partitions that do not contain 1.
        nfac -- factorint(n), or None (default)
    
    Output: sequence of tuples
    
    Examples:
    
    >>> list(mulparts(12, 1))
    [(12,)]
    
    >>> sorted(mulparts(12, 2))
    [(1, 12), (2, 6), (3, 4), (4, 3), (6, 2), (12, 1)]
    
    >>> sorted(mulparts(12, 3))[:6]
    [(1, 1, 12), (1, 2, 6), (1, 3, 4), (1, 4, 3), (1, 6, 2), (1, 12, 1)]
    
    >>> sorted(mulparts(12))
    [(2, 2, 3), (2, 3, 2), (2, 6), (3, 2, 2), (3, 4), (4, 3), (6, 2), (12,)]
    """
    if n == 1: yield (1,) * (1 if r is None else r); return
    if nfac is None: nfac = factorint(n)
    #else: assert prod(p**e for (p,e) in nfac.items()) == n
    if r == 1: yield (n,); return
    if r == 2: yield from ((d, n//d) for d in divisors(nfac)); return
    for dfac in divisors_factored(nfac):
        d = prod(p**e for (p,e) in dfac.items())
        if d == 1 and r is None: continue
        k, kfac = n//d, {p:e-dfac.get(p,0) for (p,e) in nfac.items() if e != dfac.get(p,0)}
        assert k == prod(p**e for (p,e) in kfac.items()), (k, kfac)
        assert 0 not in kfac.values()
        yield from ((d,) + (() if part==(1,) and r is None else part) for part in mulparts(k, None if r is None else r-1, kfac))

def dirconv(f, g, ffac=False, gfac=False):
    """
    Dirichlet convolution.  When called with the keyword arguments at their
    default values, this is equivalent to the expression
        lambda n: sum(f(d) * g(n//d) for d in divisors(n)).
    If f or g needs to factor its argument, such as if f == totient or
    g == mobius or whatever, then the above expression calls the factorizer
    a lot more than it needs to --- we are already factoring n, so instead
    of feeding those functions the integer forms of n's factors, we can
    instead pass ffac=True or gfac=True when dirconv is called and we will
    call divisors_factored(n) instead of divisors(n) and feed those factored
    divisors into f or g as appropriate.  This optimization becomes more
    noticeable as the factoring becomes more difficult.
    
    Input:
        f, g -- functions of a single variable that can accept integers or
                factorint output.
        ffac, gfac -- booleans.  Set ffac=True if f can accept factorint
                      output, and set gfac=True if g can accept such.
    
    Output: a function of a single variable that can be either an integer or
            factorint output.
    
    Examples:
    
    >>> def one(n): return 1
    >>> def I(n): return n if isinstance(n, inttypes) else prod(p**e for (p,e) in n.items())
    >>> # I(n) is just the compositional identity function modified to
    >>> # convert factorint output into the integer it represents.
    >>> h = dirconv(one, totient, ffac=True, gfac=True) # h(n) == n
    >>> [h(n) for n in range(1, 21)]
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
    >>> h = dirconv(one, mobius, ffac=True, gfac=True)  # h(n) == int(n==1)
    >>> [h(n) for n in range(1, 25)]
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    >>> h = dirconv(one, one, ffac=True, gfac=True)  # h(n) == divsigma(n,0)
    >>> [h(n) for n in range(1, 25)]
    [1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4, 5, 2, 6, 2, 6, 4, 4, 2, 8]
    >>> h = dirconv(I, one, ffac=True, gfac=True)    # h(n) == divsigma(n,1)
    >>> [h(n) for n in range(1, 20)]
    [1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24, 31, 18, 39, 20]
    """
    if (not ffac) and (not gfac): return lambda n: sum(f(d) * g(n//d) for d in divisors(n))
    def result(f, g, ffac, gfac, n):
        if isinstance(n, inttypes): nfac = factorint(n)
        else: n, nfac = prod(p**e for (p,e) in n.items()), n
        total = 0
        for xfac in divisors_factored(nfac):
            x = prod(p**e for (p,e) in xfac.items())
            yfac = {p:(e-xfac.get(p,0)) for (p,e) in nfac.items() if e != xfac.get(p,0)}
            y = prod(p**e for (p,e) in yfac.items())
            assert x * y == n
            total += f(xfac if ffac else x) * g(yfac if gfac else y)
        return total
    return lambda n: result(f, g, ffac, gfac, n)

def dirichletinverse(f):
    """
    Computes the Dirichlet inverse of the input function f.  More precisely,
    if f is a function on the positive integers, then dirichletinverse(f)
    returns the unique function g such that
        dirconv(f, g)(n) == (1 if n == 1 else 0).
    If f(1) == 0, then we will enocounter a ZeroDivisionError.
    
    If f always returns integers and f(1) in (1, -1), then
    dirichletinverse(f) will always return integers.
    
    If f(1) not in (1,-1), then dirichletinverse(f) will return Fraction
    objects (as imported from the fractions module).
    
    Input: f -- a univalent function on the positive integers
    
    Output: a univalent function on the positive integers
    
    Examples:
    
    >>> [dirichletinverse(mobius)(n) for n in range(1, 21)]
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    
    >>> [dirichletinverse(lambda x: 1)(n) for n in range(1, 21)]
    [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0]
    
    >>> [str(dirichletinverse(lambda x: 2)(n)) for n in range(1, 11)]
    ['1/2', '-1/2', '-1/2', '0', '-1/2', '1/2', '-1/2', '0', '0', '1/2']
    """
    def answer(f, n):                                                               # TODO: memoization?
        first = Fraction(1, f(1)) if 1 != f(1) != -1 else 1 // f(1)
        if n == 1: return first
        finv = dirichletinverse(f)
        return (-first) * sum(f(x) * finv(n//x) for x in divisors(n) if x != 1)
    return lambda x: answer(f, x)

def dirichletroot(f, r, val1):
    """
    Computes the rth Dirichlet root of the input function f whose value at 1
    is val1.  More precisely, let f be a function on the positive integers,
    let r be a positive integer, and let val1**r == f(1).  Then we return
    the unique function g such that f = g * g * ... * g, where g appears r
    times and * indicates Dirichlet convolution.  The values returned by the
    output will be Fraction objects (as imported from the fractions module).
    
    Input:
        f -- a function on the positive integers
        r -- a positive integer
        val1 -- a quantity satisfying val1**r == f(1)
    
    Output: a function on the positive integers
    
    Examples:
    
    >>> [str(dirichletroot(divcount, 2, 1)(n)) for n in range(1, 15)]
    ['1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1']
    """
    assert val1**r == f(1), (val1, r, val1**r, f(1), f)
    def answer(f, r, n, val1):
        if n == 1: return Fraction(val1)
        den = r * f(1)
        g = dirichletroot(f, r, val1)
        #num = f(n) - sum(prod(g(d) for d in mulpart) for mulpart in mulparts(n, r) if n not in mulpart)
        gcache = {}
        num = f(n)
        for mulpart in mulparts(n, r):
            if n in mulpart: continue
            term = 1
            for d in mulpart:
                if d not in gcache: gcache[d] = g(d)
                term *= gcache[d]
            num -= term
        num *= val1
        #return num // den if num % den == 0 else num / den
        return Fraction(num, den)
    return lambda x: answer(f, r, x, val1)

def determinant(M):
    """
    Computes the determinant of a matrix via the Schur determinant identity.
    
    Input: M -- square matrix; i.e., a list of lists.
    
    Output: A number.  If all input elements are integers, then this will
            also be an integer.
    
    Examples:
    
    >>> determinant([[1,2,3,4],[1,2,3,5],[1,2,4,4],[4,3,2,1]])
    5
    """
    # TODO: What is the algorithm's complexity?
    k = len(M)
    assert all(len(r) == k for r in M)
    if k == 1: return M[0][0]
    if k == 2: return M[0][0]*M[1][1] - M[0][1]*M[1][0]
    if k == 3:
        a, b, c, d, e, f, g, h, i = M[0][0], M[0][1], M[0][2], M[1][0], M[1][1], M[1][2], M[2][0], M[2][1], M[2][2]
        return a*e*i + b*f*g + c*d*h - a*f*h - b*d*i - c*e*g
    sign = 1
    for r in range(k):
        if M[r][0] != 0: break
    else: return 0
    if r != 0: M[0], M[r], sign = M[r], M[0], -1
    a = M[0][0]
    aD_CB = [[a*M[r][s] - M[r][0]*M[0][s] for s in range(1,k)] for r in range(1,k)]
    d = determinant(aD_CB)
    ints = isinstance(d, inttypes) and isinstance(a, inttypes)
    return sign * d // a**(k-2) if ints else sign * d / a**(k-2)

def discriminant(coefs):  #TODO https://math.stackexchange.com/questions/696335 https://en.wikipedia.org/wiki/B%C3%A9zout_matrix
    """
    Computes the discriminant of a polynomial.  The input is ordered from
    lowest degree to highest so that coefs[k] is the coefficient of the x**k
    term.  We compute it by taking the determinant (using this library's
    determinant() function) of the Sylvester matrix of the input and its
    derivative.  This in turn is calculated by the Schur determinant
    identity.  Note that this has the effect of setting the discriminant of
    a linear polynomial to 1 (which is conventional) and that of a constant
    to 0 (for which there is no conventional value).
    
    Input: coefs -- list of numbers
    
    Output: A number
    
    Examples:
    
    >>> discriminant([1,2,3,4,5])
    10800
    """
    n = len(coefs) - 1  # degree of polynomial
    if n < 2: return n
    if n == 2: return coefs[1]**2 - 4 * coefs[0] * coefs[2]
    if n == 3:
        d, c, b, a = coefs
        return b*b*c*c-4*a*c*c*c-4*b*b*b*d-27*a*a*d*d+18*a*b*c*d
    if n == 4:
        e, d, c, b, a = coefs; cc, dd = c*c, d*d; ddd = dd*d
        return a*a*(e*e*(256*a*e-192*b*d-128*cc)+(144*c*e-27*dd)*dd)+\
               a*(6*b*(b*e*(24*c*e-dd)+3*c*ddd)-4*cc*(4*e*(5*b*d-cc)+c*dd))-\
               b*b*(((27*b*e-18*c*d)*e+4*ddd)*b+cc*(4*c*e-dd))
        return 256*a*a*a*e*e*e-192*a*a*b*d*e*e-128*a*a*c*c*e*e+144*a*a*c*d*d*e-\
               27*a*a*d*d*d*d+144*a*b*b*c*e*e-6*a*b*b*d*d*e-80*a*b*c*c*d*e+\
               18*a*b*c*d*d*d+16*a*c*c*c*c*e-4*a*c*c*c*d*d-27*b*b*b*b*e*e+\
               18*b*b*b*c*d*e-4*b*b*b*d*d*d-4*b*b*c*c*c*e+b*b*c*c*d*d
    r = []
    a = coefs[::-1]
    for x in range(n-1): r.append([0] * x  +  a  +  [0] * (n-2-x))
    del a[-1]
    for x in range(n): a[x] *= n-x
    for x in range(n): r.append([0] * x  +  a  +  [0] * (n-1-x))
    return (-1)**(n*(n-1)//2) * determinant(r) // coefs[-1]
    # TODO: Surely there is a way to take advantage of the matrix's special form.

def egypt_short(n, d, terms=0, minden=1):
    """
    Generates all shortest Egyptian fractions for n/d using at least the
    indicated number of terms and whose denominators are all >= minden.
    This can take impractically long times, even on modest-seeming inputs.
    
    Do not expect the output to be in any particular order.
    
    Input:
        n, d -- integers.
        terms -- integer.  Minimum number of terms to use.  Default == 0.
        minden -- integer.  Minimum denominator to use.  Default == 1.
    
    Examples:
    
    >>> list(egypt_short(5,31))
    [(7, 56, 1736), (7, 62, 434), (8, 28, 1736), (8, 31, 248), (9, 20, 5580)]
    
    >>> list(egypt_short(6,31))
    [(6, 38, 1767), (6, 39, 806), (6, 62, 93)]
    
    >>> list(egypt_short(10,121))
    [(13, 176, 25168), (15, 66, 1210), (17, 42, 86394), (22, 27, 6534)]
    """
    # Generate all Egyptian fractions for n/d using the minimum # of terms that is >= t and with all denominators >= minden.
    g = gcd(n,d)
    n, d = n//g, d//g
    if n == 0: return
    if terms == 0:
        # Yield all EFRs of length 1, then all of length 2, then all of length 3, etc.
        # The first several sets of EFRs will be empty.  Stop after yielding the last EFR from the first nonempty set.
        for t in count(1):
            c = 0
            for f in egypt_short(n, d, t, minden):
                yield f
                c += 1
            if c > 0: return
    if terms == 1:
        if n == 1 and d >= minden: yield (d,)
        return
    if terms == 2:
        # We need to solve n/d == 1/x + 1/y, or equivalently (nx-d) * (ny-d) == d^2.  WOLOG, x < y.
        for z in sorted(divisors({p:e+e for (p,e) in factorint(d).items()})):
            # Calling sorted() is unnecessary, but when we use it, the output of the entire function comes out in sorted order.
            t = d * d // z
            # nx-d = z; ny-d = t
            x, r = divmod(d+z, n)
            if r != 0: continue
            y, r = divmod(d+t, n)
            if r != 0: continue
            if minden <= x < y: yield (x,y)
        return
    # The initial value of x in this loop is the least integer >= d/n and >= minden.
    for x in count(max(minden, -(-d//n))):   # -(-a//b) amounts to ceiling division when a,b > 0.
        q, r = 0, 1
        for t in range(x, x+terms): q, r = q*t+r, t*r        # TODO: for large numbers of terms, this is rather inefficient.
        g = gcd(q,r)
        q, r = q//g, r//g
        # q/r is the largest number with an EFR using the specified constraints.
        if q*d >= n*r: #if q/r >= n/d
            # get the (terms-1)-term expansions of n/d - 1/x.
            a, b = n*x-d, d*x # We do not need to reduce to lowest terms here; that will be handled by the recursive call.
            for f in egypt_short(a, b, terms-1, x+1): yield (x,) + f
        if q*d < n*r: return #if q/r < n/d

def egypt_greedy(n, d):
    """
    The greedy algorithm for Egyptian fraction expansion (also called the
    Fibonacci-Sylvester algorithm): at each step, extract the largest unit
    fraction less than the target and replace the target with the remainder.
    The numerator is guaranteed to decrease with each iteration.
    
    Note that there will be n//d ones leading the output, so if n/d >= 2,
    then the result will have repeated terms and therefore will not be a
    true EFR.
    
    Input: x, y -- integers.  The target fraction is x/y.
    
    Output: List of integers.  These are the denominators of the expansion.
    
    Examples:
    
    >>> egypt_greedy(5, 121)
    [25, 757, 763309, 873960180913, 1527612795642093418846225]
    
    >>> egypt_greedy(9, 10)
    [2, 3, 15]
    
    >>> egypt_greedy(19, 10)
    [1, 2, 3, 15]
    
    >>> egypt_greedy(29, 10)
    [1, 1, 2, 3, 15]
    """
    g = gcd(n, d)
    n, d = n//g, d//g
    efr = []
    while n != 1:
        x = d // n + 1
        efr.append(x)
        n, d = n * x - d, d * x
        g = gcd(n, d)
        n, d = n//g, d//g
    efr.append(d)
    return efr

def rational_in_base(b, p, q):
    """
    Given integers b, p, and q, with b >= 2 and p >= 0 and q > 0, we
    determine the base-b expansion of p/q.  We return a tuple containing
    three lists: the first is the base-b expansion of p//q, the second is
    the pre-reptend part of the fractional part of p/q, and the third is the
    reptend of the fractional part p/q.
    If 0 <= p/q < 1, then the first element is [0].
    If the pre-reptend part has length 0, then the second element is [].
    If the reptend has length zero, then the third element is [].
    In each list, the most significant digit is at index 0.
    
    Copied from Wikipedia: https://en.wikipedia.org/wiki/Repeating_decimal,
    section "Algorithm for positive bases".
    
    Input: b, p, q -- integers
    
    Output: a 3-tuple containing lists
    
    Examples:
    
    >>> rational_in_base(10, 11, 6)
    ([1], [8], [3])
    
    >>> rational_in_base(10, 0, 6)
    ([0], [], [])
    
    >>> rational_in_base(10, 6, 7)
    ([0], [], [8, 5, 7, 1, 4, 2])
    
    >>> rational_in_base(2, 11, 14)
    ([0], [1], [1, 0, 0])
    
    >>> rational_in_base(12, 221, 14)
    ([1, 3], [9], [5, 1, 8, 6, 10, 3])
    
    >>> rational_in_base(12, 221, 1)
    ([1, 6, 5], [], [])
    
    >>> rational_in_base(10, 33, 3)
    ([1, 1], [], [])
    
    >>> rational_in_base(10, 1, 7)
    ([0], [], [1, 4, 2, 8, 5, 7])
    
    >>> rational_in_base(10, 1, 70)
    ([0], [0], [1, 4, 2, 8, 5, 7])
    
    >>> rational_in_base(10, 1, 4)
    ([0], [2, 5], [])
    
    >>> rational_in_base(10, 3, 12)
    ([0], [2, 5], [])
    
    >>> rational_in_base(10, 1, 9)
    ([0], [], [1])
    
    >>> rational_in_base(10, 1, 10)
    ([0], [1], [])
    """
    assert b >= 2
    g = gcd(p, q)
    p, q = p//g, q//g
    ipart = []
    i, p = divmod(p, q)
    mask = b**ilog(i, b)
    while mask > 0:
        if mask > 1: assert mask <= i < mask * b, (b, mask, ipart, ilog(mask, b))
        h, i = divmod(i, mask)
        ipart.append(h)
        mask //= b
    s, pos, occurs = [], 0, {}
    while not (p in occurs):
        occurs[p] = pos
        z, p = divmod(b*p, q)
        if p == 0:
            if z != 0: s.append(z)
            return (ipart, s, [])
        s.append(z)
        pos += 1
    L = pos - occurs[p]    # Length of reptend
    return (ipart, s[:-L], s[-L:])

def sqfrcount(N):                       # TODO: Segmentate.  See https://arxiv.org/pdf/1107.4890 section 4.4.
    """
    Counts the number of squarefree integers in the interval [1,N].
    Uses Pawlewicz's O(N**0.4 * log(log(N))**0.6) algorithm.
    This is the non-segmented version, so memory usage is also
    O(N**0.4)-ish.  This code is derived from the code at
    https://smsxgz.github.io/post/pe/counting_square_free_numbers/.
    
    Input: A positive integer
    
    Output: A positive integer
    
    Examples:
    
    >>> sqfrcount(1)
    1
    
    >>> sqfrcount(10**15)
    607927101854103
    """
    if N < 27: return 0 if N < 0 else (0,1,2,3,3,4,5,6,6,6,7,8,8,9,10,11,11,12,12,13,13,14,15,16,16,16,17,17)[N]
    Imax = int(N**0.2 * log(log(N))**0.8 * 0.45)  # TODO: Experiment with different values for the multiplier.
    D = isqrt(N // Imax)
    
    s1 = 0
    merts = [0] * (D+1)
    for (i,mu_i) in enumerate(mobiussieve(D+1), start=1):
        s1 += mu_i * (N // (i*i))
        merts[i] = merts[i-1] + mu_i
    
    Mxi_list = []
    Mxi_sum = 0
    for i in range(Imax - 1, 0, -1):
        Mxi = 1
        xi = isqrt(N // i)
        sqd = isqrt(xi)
        assert sqd < D <= xi
        for j in range(1, xi // (sqd + 1) + 1): Mxi -= (xi // j - xi // (j + 1)) * merts[j]
        for j in range(2, sqd + 1):
            if xi // j <= D: Mxi -= merts[xi // j]
            else:            Mxi -= Mxi_list[Imax - j*j*i - 1]
        Mxi_list.append(Mxi)
        Mxi_sum += Mxi
    return s1 + Mxi_sum - (Imax - 1) * merts[D]

def powerfulmap(x, h=(lambda a,b: 1)):
    """
    Generates, in no particular order, the sequence (n, f(n)), where n runs
    over the powerful numbers in the interval [1, x], and where f is the
    multiplicative function satisfying f(p**e) == h(p, e).  Derived from
    https://gbroxey.github.io/blog/2023/04/30/mult-sum-1.html.
    
    Input:
        x -- integer
        h -- two-argument function.  The default is the all-ones function.
    
    Output: a sequence of numbers
    
    Examples:
    
    >>> sorted(x for (x,y) in powerfulmap(125))
    [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, 108, 121, 125]
    
    >>> sorted(powerfulmap(81, lambda y,z: 2**z))
    [(1, 1), (4, 4), (8, 8), (9, 4), (16, 16), (25, 4), (27, 8), (32, 32), (36, 16), (49, 4), (64, 64), (72, 32), (81, 16)]
    """
    ps = list(primegen(isqrt(x)+1))
    stk = [(1, 1, 0)]
    while stk:
        n, hn, i = stk.pop()
        if i >= len(ps):
            yield (n, hn)
            continue
        p = ps[i]
        if p*p > x // n:
            yield (n, hn)
            continue
        stk.append((n, hn, i+1))
        pp = p*p
        e = 2
        while pp <= x // n:
            stk.append((n * pp, hn * h(p,e), i + 1))
            if pp > (x // n) // p: break
            pp *= p
            e += 1

def dirichletcharacter(q, n, x, qfac=None):
    """
    The Dirichlet character of modulus q and index n, evaluated at x, using
    the Conrey label.  Instead of returning the actual value of the
    character at x, we return a Fraction object F with 0 <= F < 1 such that
    the value of the Dirichlet character is exp(2*pi * complex(0,1) * F).
    If the value of the Dirichlet character at x is zero, then we return
    F == complex(0,inf), which yields complex zero when filtered through
    exp(2*pi * complex(0,1) * F).  Note that
    complex(0,1) * inf == nan + infj, whereas complex(0, inf) == infj.
    As long as you ensure that q and x are coprime before calling this
    function, then you should not have to worry about that.
    
    For further reading, see
    https://www.lmfdb.org/knowledge/show/character.dirichlet.conrey.
    
    Input:
        q, n, x -- integers
        qfac -- Default None.  If present, assumed to equal factorint(q).
    
    Output: Either a Fraction object or complex(0, inf).
    
    >>> print(dirichletcharacter(40487, 100, 11))
    15653/20243
    
    >>> q = 40
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0 
      0 1/4 1/4 1/2   0 3/4 3/4 1/2 1/2 3/4 3/4   0 1/2 1/4 1/4   0 
      0 1/4 3/4 1/2 1/2 3/4 1/4   0   0 1/4 3/4 1/2 1/2 3/4 1/4   0 
      0 1/2 1/2   0   0 1/2 1/2   0   0 1/2 1/2   0   0 1/2 1/2   0 
      0   0 1/2   0   0 1/2   0   0 1/2 1/2   0 1/2 1/2   0 1/2 1/2 
      0 3/4 3/4 1/2 1/2 3/4 3/4   0 1/2 1/4 1/4   0   0 1/4 1/4 1/2 
      0 3/4 1/4 1/2   0 3/4 1/4 1/2   0 3/4 1/4 1/2   0 3/4 1/4 1/2 
      0 1/2   0   0   0   0 1/2   0 1/2   0 1/2 1/2 1/2 1/2   0 1/2 
      0 1/2   0   0 1/2 1/2   0 1/2 1/2   0 1/2 1/2   0   0 1/2   0 
      0 3/4 1/4 1/2 1/2 1/4 3/4   0   0 3/4 1/4 1/2 1/2 1/4 3/4   0 
      0 3/4 3/4 1/2   0 1/4 1/4 1/2 1/2 1/4 1/4   0 1/2 3/4 3/4   0 
      0   0 1/2   0 1/2   0 1/2 1/2 1/2 1/2   0 1/2   0 1/2   0   0 
      0 1/2 1/2   0 1/2   0   0 1/2   0 1/2 1/2   0 1/2   0   0 1/2 
      0 1/4 3/4 1/2   0 1/4 3/4 1/2   0 1/4 3/4 1/2   0 1/4 3/4 1/2 
      0 1/4 1/4 1/2 1/2 1/4 1/4   0 1/2 3/4 3/4   0   0 3/4 3/4 1/2 
      0   0   0   0 1/2 1/2 1/2 1/2   0   0   0   0 1/2 1/2 1/2 1/2 
    
    >>> q = 24
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0   0   0   0   0 
      0   0   0   0 1/2 1/2 1/2 1/2 
      0   0 1/2 1/2   0   0 1/2 1/2 
      0   0 1/2 1/2 1/2 1/2   0   0 
      0 1/2   0 1/2 1/2   0 1/2   0 
      0 1/2   0 1/2   0 1/2   0 1/2 
      0 1/2 1/2   0 1/2   0   0 1/2 
      0 1/2 1/2   0   0 1/2 1/2   0 
    
    >>> q = 15
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0   0   0   0   0 
      0 3/4 1/2 1/4 1/4 1/2 3/4   0 
      0 1/2   0 1/2 1/2   0 1/2   0 
      0 1/4 1/2 1/4 3/4   0 3/4 1/2 
      0 1/4 1/2 3/4 3/4 1/2 1/4   0 
      0 1/2   0   0 1/2 1/2   0 1/2 
      0 3/4 1/2 3/4 1/4   0 1/4 1/2 
      0   0   0 1/2   0 1/2 1/2 1/2 
    
    >>> q = 5
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0 
      0 1/4 3/4 1/2 
      0 3/4 1/4 1/2 
      0 1/2 1/2   0 
    
    >>> q = 3
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0 
      0 1/2 
    
    >>> q = 9
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0   0   0 
      0 1/6 1/3 5/6 2/3 1/2 
      0 1/3 2/3 2/3 1/3   0 
      0 5/6 2/3 1/6 1/3 1/2 
      0 2/3 1/3 1/3 2/3   0 
      0 1/2   0 1/2   0 1/2 
    
    >>> q = 27
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print(dirichletcharacter(q, i, x), end=' ')
    ...     print()
    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 
    0 1/18 1/9 5/18 8/9 1/6 1/3 13/18 4/9 17/18 2/9 5/6 2/3 7/18 7/9 11/18 5/9 1/2 
    0 1/9 2/9 5/9 7/9 1/3 2/3 4/9 8/9 8/9 4/9 2/3 1/3 7/9 5/9 2/9 1/9 0 
    0 5/18 5/9 7/18 4/9 5/6 2/3 11/18 2/9 13/18 1/9 1/6 1/3 17/18 8/9 1/18 7/9 1/2 
    0 8/9 7/9 4/9 2/9 2/3 1/3 5/9 1/9 1/9 5/9 1/3 2/3 2/9 4/9 7/9 8/9 0 
    0 1/6 1/3 5/6 2/3 1/2 0 1/6 1/3 5/6 2/3 1/2 0 1/6 1/3 5/6 2/3 1/2 
    0 1/3 2/3 2/3 1/3 0 0 1/3 2/3 2/3 1/3 0 0 1/3 2/3 2/3 1/3 0 
    0 13/18 4/9 11/18 5/9 1/6 1/3 7/18 7/9 5/18 8/9 5/6 2/3 1/18 1/9 17/18 2/9 1/2 
    0 4/9 8/9 2/9 1/9 1/3 2/3 7/9 5/9 5/9 7/9 2/3 1/3 1/9 2/9 8/9 4/9 0 
    0 17/18 8/9 13/18 1/9 5/6 2/3 5/18 5/9 1/18 7/9 1/6 1/3 11/18 2/9 7/18 4/9 1/2 
    0 2/9 4/9 1/9 5/9 2/3 1/3 8/9 7/9 7/9 8/9 1/3 2/3 5/9 1/9 4/9 2/9 0 
    0 5/6 2/3 1/6 1/3 1/2 0 5/6 2/3 1/6 1/3 1/2 0 5/6 2/3 1/6 1/3 1/2 
    0 2/3 1/3 1/3 2/3 0 0 2/3 1/3 1/3 2/3 0 0 2/3 1/3 1/3 2/3 0 
    0 7/18 7/9 17/18 2/9 1/6 1/3 1/18 1/9 11/18 5/9 5/6 2/3 13/18 4/9 5/18 8/9 1/2 
    0 7/9 5/9 8/9 4/9 1/3 2/3 1/9 2/9 2/9 1/9 2/3 1/3 4/9 8/9 5/9 7/9 0 
    0 11/18 2/9 1/18 7/9 5/6 2/3 17/18 8/9 7/18 4/9 1/6 1/3 5/18 5/9 13/18 1/9 1/2 
    0 5/9 1/9 7/9 8/9 2/3 1/3 2/9 4/9 4/9 2/9 1/3 2/3 8/9 7/9 1/9 5/9 0 
    0 1/2 0 1/2 0 1/2 0 1/2 0 1/2 0 1/2 0 1/2 0 1/2 0 1/2 
    
    >>> print(dirichletcharacter(2, 1, 1))
    0
    
    >>> q = 4
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0 
      0 1/2 
    
    >>> q = 8
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0 
      0   0 1/2 1/2 
      0 1/2 1/2   0 
      0 1/2   0 1/2 
    
    >>> q = 16
    >>> for i in range(q):
    ...     if gcd(i,q) != 1: continue
    ...     for x in range(q):
    ...         if gcd(x,q) != 1: continue
    ...         print("%3s" % dirichletcharacter(q, i, x), end=' ')
    ...     print()
      0   0   0   0   0   0   0   0 
      0 3/4 3/4   0 1/2 1/4 1/4 1/2 
      0 3/4 1/4 1/2 1/2 1/4 3/4   0 
      0   0 1/2 1/2   0   0 1/2 1/2 
      0 1/2 1/2   0   0 1/2 1/2   0 
      0 1/4 1/4   0 1/2 3/4 3/4 1/2 
      0 1/4 3/4 1/2 1/2 3/4 1/4   0 
      0 1/2   0 1/2   0 1/2   0 1/2 
    """
    x %= q
    if gcd(x, q) != 1: return complex(0, inf)
    if qfac is None: qfac = factorint(q)
    if len(qfac) > 1: return sum(dirichletcharacter(p**e, n % (p**e), x % (p**e), {p:e}) for (p,e) in qfac.items()) % 1
    assert len(qfac) == 1
    p, e = qfac.popitem()
    if n == 1: return complex(0,inf) if x % p == 0 else Fraction(0,1)
    if p == 2:
        if q == 4 and n == 3:
            if x % 4 == 1: return Fraction(0,1)
            if x % 4 == 3: return Fraction(1,2)
            assert False
        assert e > 2
        # TODO: When an efficient discrete logarithm function is available, use it here.
        pow5 = 5
        a, b = 0, 0
        for ab in range(1, q):
            if pow5 == n or q - pow5 == n: a = ab
            if pow5 == x or q - pow5 == x: b = ab
            if a != 0 and b != 0: break
            pow5 = (5 * pow5) % q
        else: assert False
        ea, eb = 1, 1
        if pow(5, a, q) != n: ea = -1
        if pow(5, b, q) != x: eb = -1
        return ( Fraction((1-ea) * (1-eb), 8) + Fraction(a*b, q//4) ) % 1
    # Now we need to find the least primitive root modulo p^2.
    pp = p*p
    ppm1 = pp - 1
    pptot = p*p - p
    for gp in range(2, pp):
        if multord(gp, {p:2}) == pptot: break
    else: assert False
    qtot = (q//p) * (p-1)
    # TODO: When an efficient discrete logarithm function is available, use it here.
    a, b = 0, 0
    gppow = gp
    for ab in range(1, q):
        if n == gppow: a = ab
        if x == gppow: b = ab
        if a != 0 and b != 0: break
        gppow = (gp * gppow) % q
    return Fraction(a*b, qtot) % 1

def partitions(n, parts=None, distinct=False):
    """
    Computes the number of partitions of 0, 1, 2, ..., n with the specified
    parts.  The algorithm is based on the generating function: if we have
    P(x) = (1 + x + x^2 + x^3 + ...) * (1 + x^2 + x^4 + x^6 + ...) * ...
           ... * (1 + x^n + x^2n + x^3n + ...) * ...,
    then the number of partitions of n is the coefficient of the x^n term.
    To compute the number of partitions whose parts come from parts, we just
    omit all factors (1 + x^k + x^2k + x^3k + ...) where k is not in parts.
    
    Optionally, we compute the number of partitions in which the parts are
    required to be distinct.  This is done by having the factors of the
    generating function be (1 + x^k).
    
    Input:
        n -- integer
        parts -- None (default), or a finite iterable.
                 If None, then we use (1, 2, ..., n) as the available parts.
        distinct -- True or False (default).  If True, then we compute the
                    number of partitions into distinct parts.
    
    Output: a list
    
    Examples:
    
    >>> partitions(23, parts=(1,))
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    
    >>> partitions(23, parts=[2])
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
    
    >>> partitions(21, parts=(1,2))
    [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11]
    
    >>> partitions(17, parts=range(1,10))
    [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 41, 54, 73, 94, 123, 157, 201, 252]
    
    >>> partitions(20, parts=primegen(20))
    [1, 0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 9, 10, 12, 14, 17, 19, 23, 26]
    """
    if parts is None: parts = range(1, n+1)
    plist = [1]
    for i in set(parts):
        if i > n: continue
        ans = [0] * (n+1)
        for (x, p) in enumerate(plist):
            for y in range(x, min(n, (x+i) if distinct else inf) + 1, i):
                ans[y] += p
        plist = ans
    return plist

if __name__ == "__main__": import doctest; doctest.testmod()
