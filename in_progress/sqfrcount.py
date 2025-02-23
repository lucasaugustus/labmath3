#! /usr/bin/env python3

from labmath3 import *
from sys import argv

# https://arxiv.org/abs/1107.4890
# https://github.com/jakubpawlewicz/sqrfree/blob/debug/sol5.cpp

def sqfrcount(N):
    """
    Counts the number of squarefree integers in the interval [1,N].
    We use Pawlewicz's algorithm, which takes O(N**0.4)-ish time and
    O(N**0.2)-ish space.  This code is derived from
    https://github.com/jakubpawlewicz/sqrfree/blob/debug/sol5.cpp.
    For further reading, see https://arxiv.org/pdf/1107.4890.
    
    Input: A positive integer
    
    Output: A positive integer
    
    Examples:
    
    >>> sqfrcount(1)
    1
    
    >>> sqfrcount(10)
    7
    
    >>> sqfrcount(10**15)
    607927101854103
    """
    if N < 53: return 0 if N < 0 else (0,1,2,3,3,4,5,6,6,6,7,8,8,9,10,11,11,12,12,13,13,14,15,16,16,16,17,17,17,\
                                       18,19,20,20,21,22,23,23,24,25,26,26,27,28,29,29,29,30,31,31,31,31,32,32)[N]
    I = int(N**(1/5) * log(log(N))**(4/5) * 0.35)       # The 0.35 is a tunable parameter.
    print("I =", I)
    D = isqrt(N // I)
    print("D =", D)
    x = [0] + [isqrt(N//i) for i in range(1, I+1)]  # x[i] = sqrt(N/i).  x[0] is never accessed.
    maxd = x[:-1]   # subtract M(sqrt(N/i/d^2)) from M(sqrt(N/i)) for d <= maxd[i]
    T = [1] * (I+1) # T[i] = M[i] = M(sqrt(N/i))
    B = isqrt(D)           # Block size.  This is not set in stone.  The article says isqrt(D); Pawlewicz's code uses 2**19.
    print("B =", B)
    L = (D + B - 1) // B  # total number of blocks
    print("L =", L)
    next_ = list(range(-1, I-1))    # for lists.  next_[0] is never accessed.
    q = [I - 1] + [0] * (L-1)   # q[l] lists those i that will be processed during block l.
    
    Mi = 0      # will hold mertens(i)
    res = 0
    mobgen = mobiussieve()
    a = 1
    b = min(a + B, D + 1)
    M = [0] * (b - a)   # We will have M[i - a] == mertens(i)
    
    for l in range(L):
        #assert a == 1 + l * B
        #assert b == min(a + B, D + 1), l
        
        for i in range(a, b):
            mu_i = next(mobgen)
            Mi += mu_i                  # Mi == mertens(i)
            M[i - a] = Mi
            if mu_i == 0: continue
            v = N // (i * i)
            if mu_i > 0: res += v
            else:        res -= v
        
        while q[l] != 0:
            i = q[l]
            q[l] = next_[i]
            bD = min(b, D)
            # updates T[i] with M[y] for all a <= y < bD
            d = maxd[i]
            xi = x[i]
            y = xi // d
            #assert y < bD
            while True:
                #assert a <= y and y < bD
                e = xi // (y + 1)
                #assert e < d
                #if i == 2: print("Update M(" + str(x[i]) + ") by -" + str(d - e) + "*M(" + str(y) + ")")
                T[i] -= (d - e) * M[y - a]
                d = e
                #assert xi // d > y
                y = xi // d
                if d <= 1 or y >= bD: break
            if d == 1 or y >= D: continue
            # insert to queue
            maxd[i] = d
            il = (y - 1) // B
            next_[i] = q[il]
            q[il] = i
        
        a, b = b, min(b + B, D + 1)
    
    T[I] = Mi
    res -= (I - 1) * T[I]
    for i in range(I-1, 0, -1):
        d = 2
        while True:
            j = i * d * d
            if j > I: break
            T[i] -= T[j]
            #if i == 2: print("Update M(" + str(x[i]) + ") by -M(" + str(x[j]) + ")")
            d += 1
        res += T[i]
    #for i in range(1, I+1): print("M(" + str(x[i]) + ")=" + str(T[i]))
    return res

print(sqfrcount(int(argv[1])))

def test_sqfrcount():
    for n in range(-10, 1): assert sqfrcount(n) == 0
    total = 0
    for (n,nfac) in enumerate(factorsieve(10000), start=1):
        if all(e == 1 for e in nfac.values()): total += 1
        assert sqfrcount(n) == total, (n, total)
    assert sqfrcount(10**0) == 1
    assert sqfrcount(10**1) == 7
    assert sqfrcount(10**2) == 61
    assert sqfrcount(10**3) == 608
    assert sqfrcount(10**4) == 6083
    assert sqfrcount(10**5) == 60794
    assert sqfrcount(10**6) == 607926
    assert sqfrcount(10**7) == 6079291
    assert sqfrcount(10**8) == 60792694
    assert sqfrcount(10**9) == 607927124
    assert sqfrcount(10**10) == 6079270942
    assert sqfrcount(10**11) == 60792710280
    assert sqfrcount(10**12) == 607927102274
    assert sqfrcount(10**13) == 6079271018294
    assert sqfrcount(10**14) == 60792710185947
    assert sqfrcount(10**15) == 607927101854103
    assert sqfrcount(10**16) == 6079271018540405
#test_sqfrcount()
