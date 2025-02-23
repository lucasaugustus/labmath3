#! /usr/bin/env python3

from labmath3 import isqrt, introot, log, mobiussieve
from sys import argv

# https://arxiv.org/abs/1107.4890
# https://github.com/jakubpawlewicz/sqrfree/blob/debug/sol5.cpp

def sqfrcount(n):
    I = int(n**(1/5) * log(log(n))**(4/5) * 0.35)
    print("I=" + str(I))
    D = isqrt(n // I)
    print("D=" + str(D))
    x = [0] + [isqrt(n//i) for i in range(1, I+1)]  # x[i] = sqrt(n/i)
    maxd = x[:-1]   # subtract M(sqrt(n/i/d^2)) from M(sqrt(n/i)) for d <= maxd[i]
    T = [1] * (I+1) # T[i] = M[i] = M(sqrt(n/i))
    BLOCK_SIZE = 1024 * 1024 * 5 // 10              # TODO: optimize.  Section 4.1 says Theta(sqrt(D)).
    assert BLOCK_SIZE * 0xFFFFFFFF >= D
    L = (D + BLOCK_SIZE - 1) // BLOCK_SIZE  # total number of blocks
    print("L=" + str(L))
    next_ = [0] + list(range(I-1))    # for lists
    q = [I - 1] + [0] * (L-1)   # q[l] lists those i that will be processed during block l
    
    Mi = 0      # will hold mertens(i)
    res = 0
    mobgen = mobiussieve()
    a = 1
    b = min(a + BLOCK_SIZE, D + 1)
    M = [0] * (b - a)   # We will have M[i - a] == mertens(i)
    
    for l in range(L):
        #assert a == 1 + l * BLOCK_SIZE
        #assert b == min(a + BLOCK_SIZE, D + 1), l
        
        for i in range(a, b):
            mu_i = next(mobgen)
            Mi += mu_i                  # Mi == mertens(i)
            M[i - a] = Mi
            if mu_i == 0: continue
            v = n // (i * i)
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
            assert y < bD
            while True:
                assert a <= y and y < bD
                e = xi // (y + 1)
                assert e < d
                #if i == 2: print("Update M(" + str(x[i]) + ") by -" + str(d - e) + "*M(" + str(y) + ")")
                T[i] -= (d - e) * M[y - a]
                d = e
                assert xi // d > y
                y = xi // d
                if d <= 1 or y >= bD: break
            if d == 1 or y >= D: continue
            # insert to queue
            maxd[i] = d
            il = (y - 1) // BLOCK_SIZE
            next_[i] = q[il]
            q[il] = i
        
        a, b = b, min(b + BLOCK_SIZE, D + 1)
    
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
