#! /usr/bin/env python3

from labmath3 import primegen, isqrt, introot, log
from sys import argv

# https://arxiv.org/abs/1107.4890
# https://github.com/jakubpawlewicz/sqrfree/blob/debug/sol5.cpp

def calc_mu(a, b, mu):
    D = b - a
    val = [1] * D
    for i in range(D): mu[i] = 1
    for p in primes:
        for i in range(((a+p-1)//p)*p - a, D, p): mu[i] *= -1; val[i] *= p
        p *= p
        for i in range(((a+p-1)//p)*p - a, D, p): mu[i]  =  0; val[i]  = 0
    for i in range(D):
        if val[i] < a + i:
            mu[i] *= -1

def process_i(M, a, b, i):
    global D, maxd, x, T, BLOCK_SIZE, next_, q
    b = min(b, D)
    # updates T[i] with M[y] for all a <= y < b
    d = maxd[i]
    xi = x[i]
    y = xi // d
    assert y < b
    while True:
        assert a <= y and y < b
        e = xi // (y + 1)
        assert e < d
        #if i == 2: print("Update M(" + str(x[i]) + ") by -" + str(d - e) + "*M(" + str(y) + ")")
        T[i] -= (d - e) * M[y - a]
        d = e
        assert xi // d > y
        y = xi // d
        if d <= 1 or y >= b: break
    if d == 1 or y >= D: return
    # insert to queue
    maxd[i] = d
    l = (y - 1) // BLOCK_SIZE
    next_[i] = q[l]
    q[l] = i

def process_block(l):
    global BLOCK_SIZE, D, mu, n, res, q, Mi
    a = 1 + l * BLOCK_SIZE
    b = min(a + BLOCK_SIZE, D + 1)
    calc_mu(a, b, mu)
    M = [0] * (b - a)   # M[i - a] = M(i)
    
    for i in range(a, b):
        mu_i = mu[i - a]
        Mi += mu_i
        M[i - a] = Mi
        if mu_i == 0: continue
        j = i
        v = n // (j * j)
        if mu_i > 0: res += v
        else:        res -= v
    
    while q[l] != 0:
        i = q[l]
        q[l] = next_[i]
        process_i(M, a, b, i)

def count_():
    global L, T, Mi, res
    Mi = 0
    for l in range(L): process_block(l)
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

BLOCK_SIZE = 1024 * 1024 * 5 // 10
mu = [0] * BLOCK_SIZE

n = int(argv[1])
I = int(n**(1/5) * log(log(n))**(4/5) * 0.35)
print("I=" + str(I))
D = isqrt(n // I)
print("D=" + str(D))
Mi = 0
primes = list(primegen(isqrt(D) + 1))
x = [0] + [isqrt(n//i) for i in range(1, I+1)]  # x[i] = sqrt(n/i)
maxd = x[:-1]   # subtract M(sqrt(n/i/d^2)) from M(sqrt(n/i)) for d <= maxd[i]
T = [1] * (I+1) # T[i] = M[i] = M(sqrt(n/i))
assert BLOCK_SIZE * 0xFFFFFFFF >= D
L = (D + BLOCK_SIZE - 1) // BLOCK_SIZE  # total number of blocks
print("L=" + str(L))
next_ = [0] + list(range(I-1))    # for lists
q = [I - 1] + [0] * (L-1)   # q[l] lists i's to be processed at block l */
res = 0
print(count_())
