#! /usr/bin/env python3

from time import time, process_time
from labmath3 import *

def totientsum(n):
    if n <= 10: return 0 if n < 0 else (0,1,2,4,6,10,12,18,22,28,32)[n]
    
    a = int((n / log(log(n)))**(2/3))
    b = n // a
    nr = isqrt(n)
    if verbose:
        print("ln(ln(n)):", log(log(n)))
        print("sqrt(n)/b:", nr//b)
        print("  sqrt(a):", isqrt(a))
        print("        b:", b)
        print("  sqrt(n):", nr)
        print("        a:", a)
        print("        n:", n)
        starttime = time()
        p2batchnum = 0
    Mover = [0] * (b + 1)  # Mover[n//x] will store Mertens(x) for large x.
    Mblock = []
    
    mert = 0
    X, Y, Z = 0, 0, 0
    
    s = nr - (nr == n//nr)
    chi = n // s
    
    d = b
    xp = isqrt(n//d)
    
    for (x, mu) in enumerate(mobiussieve(a+1), start=1):
        #if x == 100: exit()
        v = int(str(n // x))    # The int(str( ... )) pushes us back down into the 64-bit data types, when applicable.
        mert += mu
        X += mu * (v * (v+1) // 2)
        
        if x <= nr:
            Mblock.append(mert)
            
            if x > 1 and mu != 0:
                if verbose and (x<10*b or x%b<2): print("\b"*80, " Phase 1:", x, "%f%%" % (100*x/nr), end='    ', flush=True)
                if mu > 0:
                    for y in range(1, min(b, v//x) + 1):
                        Mover[y] -= v // y
                else:
                    for y in range(1, min(b, v//x) + 1):
                        Mover[y] += v // y
            
            while x == xp:
                Mover[d] += 1 - (n//d) + x * mert
                d = (d - 1) if d > 1 else n
                xp = isqrt(n//d)
            
            if x % b == 0 or x == nr:
                if verbose: print("\b"*80, " P1 Batch", x//b, "%f%%" % (100*x/nr), end='    ', flush=True)
                A = 1 + (b * (x//b) if x % b != 0 else (x - b))
                for t in range(1, b+1):
                    #if verbose and x < 20*b: print("\b"*80, "         ", x//b, t, "%f%%" % (100*x/a), end='    ', flush=True)
                    nt = n // t
                    lmin = 1 + n // (t * (x+1))
                    lmax = min(isqrt(n//t), nt // A)
                    for l in range(lmin, lmax + 1):
                        k = nt // l
                        assert A <= k <= x
                        Mover[t] -= Mblock[k - A]
                Mblock.clear()
                if verbose and x == nr:
                    phase1time = time()
                    print("\b"*80 + ("Phase 1 took %f seconds.    " % (phase1time - starttime)))
        
        elif x == chi:
            if verbose and len(Mblock) % 100 == 0: print("\b"*80, " Phase 2:", x, "%f%%" % (100*x/a), end='    ', flush=True)
            if v != b:
                if len(Mblock) == 0: A = v
                Mblock.append(mert)
                B = v
            s -= 1
            chi = n // s
        
        if (x == a and len(Mblock) > 0) or (x > nr and len(Mblock) == b):
            if verbose:
                p2batchnum += 1
                print("\b"*80, " P2 Batch", p2batchnum, "%f%%" % (100*x/a), end='    ', flush=True)
            BnBn = B * n // (B + n)
            for y in range(1, b+1):
                ny = n // y
                tmin = max(2, BnBn // y)
                tmax = min(isqrt(ny), (A + 1) // y)
                for t in range(tmin, tmax+1):
                    nty = ny // t
                    if nr < nty:
                        if B <= n // nty <= A:
                            Mover[y] -= Mblock[A - t*y]
                    else: break
            Mblock.clear()
        
    Z = mert * (b * (b+1) // 2)
    
    if verbose:
        phase2time = time()
        print("\b"*80 + ("Phase 2 took %f seconds.    " % (phase2time - phase1time)))
    
    for y in range(b, 0, -1):
        v = n // y
        Mv = 0
        for t in range(2, (n//y) // (n//(b+1) + 1) + 1):
            Mv -= Mover[n//(v//t)]
        # Mv is now Mertens(v).
        Mover[y] += Mv
        Y += y * Mover[y]
    
    if verbose:
        phase3time = time()
        print("\b"*80 + ("Phase 3 took %f seconds." % (phase3time - phase2time)))
    
    return X + Y - Z




def test_totientsum():
    assert list(map(totientsum, range(1, 25))) == [1,2,4,6,10,12,18,22,28,32,42,46,58,64,72,80,96,102,120,128,140,150,172,180]
    assert totientsum(10** 0) == 1
    assert totientsum(10** 1) == 32
    assert totientsum(10** 2) == 3044
    assert totientsum(10** 3) == 304192
    assert totientsum(10** 4) == 30397486
    assert totientsum(10** 5) == 3039650754
    assert totientsum(10** 6) == 303963552392
    assert totientsum(10** 7) == 30396356427242
    assert totientsum(10** 8) == 3039635516365908
    assert totientsum(10** 9) == 303963551173008414
    assert totientsum(10**10) == 30396355092886216366
    assert totientsum(10**11) == 3039635509283386211140
    assert totientsum( 2** 0) == 1
    assert totientsum( 2** 1) == 2
    assert totientsum( 2** 2) == 6
    assert totientsum( 2** 3) == 22
    assert totientsum( 2** 4) == 80
    assert totientsum( 2** 5) == 324
    assert totientsum( 2** 6) == 1260
    assert totientsum( 2** 7) == 5022
    assert totientsum( 2** 8) == 19948
    assert totientsum( 2** 9) == 79852
    assert totientsum( 2**10) == 318964
    assert totientsum( 2**11) == 1275586
    assert totientsum( 2**12) == 5100020
    assert totientsum( 2**13) == 20401610
    assert totientsum( 2**14) == 81599338
    assert totientsum( 2**15) == 326387384
    assert totientsum( 2**16) == 1305514926
    assert totientsum( 2**17) == 5222105724
    assert totientsum( 2**18) == 20888264644
    assert totientsum( 2**19) == 83553060810
    assert totientsum( 2**20) == 334211599246
    assert totientsum( 2**21) == 1336846550416
    assert totientsum( 2**22) == 5347384445830
    assert totientsum( 2**23) == 21389536074738
    assert totientsum( 2**24) == 85558134349728
    assert totientsum( 2**25) == 342232546667490
    assert totientsum( 2**26) == 1368930154035048
    assert totientsum( 2**27) == 5475720575936508
    assert totientsum( 2**28) == 21902882169438118
    assert totientsum( 2**29) == 87611528842621546
    assert totientsum( 2**30) == 350446114666323042
    assert totientsum( 2**31) == 1401784458642683740
    assert totientsum( 2**32) == 5607137832360191416
    assert totientsum( 2**33) == 22428551329120979416
    total = 0
    for (n, tot) in enumerate(totientsieve(10**7), start=1):
        total += tot
        if randrange(100000) == 0:
            totsum = totientsum(n)
            assert total == totsum, (n, total, totientsum)

verbose = True
test_totientsum()

