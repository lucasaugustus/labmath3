#! /usr/bin/env python3

from labmath3 import *

def test_primegen():
    assert list(primegen(97)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
    assert list(primegen(98)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(primegen(99)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(primegen(100)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(primegen(101)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(primegen(102)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101]
    
    pg = primegen()
    for _ in range(99): next(pg)
    assert next(pg) == 541

def test_rpn():
    assert rpn("38 ! 1 +") == [523022617466601111760007224100074291200000001]
    assert rpn("1729 42 %") == [7]
    assert rpn("2 3 xx 5 6 7 +") == [8, 5, 13]
    assert rpn("0 f") == [1]
    assert rpn("1 f") == [1]
    assert rpn("2 f") == [2]
    assert rpn("3 f") == [6]
    assert rpn("4 f") == [24]
    assert rpn("5 f") == [120]
    assert rpn("0 #") == [1]
    assert rpn("1 #") == [1]
    assert rpn("2 #") == [2]
    assert rpn("3 #") == [6]
    assert rpn("4 #") == [6]
    assert rpn("5 #") == [30]
    assert rpn("0 p") == [1]
    assert rpn("1 p") == [1]
    assert rpn("2 p") == [2]
    assert rpn("3 p") == [6]
    assert rpn("4 p") == [6]
    assert rpn("5 p") == [30]

def test_listprod():
    assert listprod([]) == 1
    assert listprod(()) == 1
    assert listprod(range(1,1)) == 1
    assert listprod(range(1,2)) == 1
    assert listprod(range(1,3)) == 2
    assert listprod(range(1,4)) == 6
    assert listprod(range(1,5)) == 24
    assert listprod(range(1,6)) == 120
    assert listprod(range(1,7)) == 720
    assert listprod(range(1,8)) == 5040
    assert listprod(list(range(1,1))) == 1
    assert listprod(list(range(1,2))) == 1
    assert listprod(list(range(1,3))) == 2
    assert listprod(list(range(1,4))) == 6
    assert listprod(list(range(1,5))) == 24
    assert listprod(list(range(1,6))) == 120
    assert listprod(list(range(1,7))) == 720
    assert listprod(list(range(1,8))) == 5040

def test_polyval():
    assert polyval([1], 0) == 1
    assert polyval([1,1], 0) == 1
    assert polyval([1,1], 1) == 2
    assert polyval([1,2], 1) == 3
    assert polyval([1,2], -1) == -1
    assert polyval([1, 2, 3], 1) == 6
    assert polyval([1, 2, 3], -1) == 2
    assert polyval([1, 2, 3], 2) == 17
    assert polyval([1, 2, 3, 4, 1, 2, 1], 3) == 1438
    assert polyval([1, 2, 3, 4, 1, 2, 1], 3, m=17) == 10

def test_powerset():
    assert list(powerset([])) == [[]]
    assert sorted(list(powerset([1]))) == [[], [1]]
    assert sorted(list(powerset([1,2]))) == [[], [1], [1,2], [2]]
    assert sorted(powerset([1,2,3])) == [[], [1], [1,2], [1,2,3], [1,3], [2], [2,3], [3]]
    assert len(list(powerset(range(10)))) == 1024

def test_primesum():
    for n in range(1,100): assert primesum(n) == sum(primegen(n+1))
    assert primesum(1729) == 213538
    assert primesum(10**6) == 37550402023
    # TODO: primesum(<1)

def test_nthprime():
    assert nthprime(0) == None
    assert nthprime(1) == 2
    assert nthprime(2) == 3
    assert nthprime(3) == 5
    assert nthprime(4) == 7
    assert nthprime(25) == 97
    assert nthprime(2**20) == 16290047

def test_fibogen(): assert list(islice(fibogen(), 12)) == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

def test_fibo():
    assert fibo(346) == 912511873855702065852730553217787283194150290277873860991322859307033303
    x = fibo(10**5)
    assert x // 10**20879 == 25974069347221724166
    assert x % 10**20 == 49895374653428746875
    assert [fibo(x) for x in range(17)] == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]

def test_egypt_greedy():
    assert egypt_greedy(1, 1) == [1]
    assert egypt_greedy(9, 10) == [2, 3, 15]
    assert egypt_greedy(5, 121) == [25, 757, 763309, 873960180913, 1527612795642093418846225]

def test_egypt_short():
    assert sorted(egypt_short(5, 31)) == [(7, 56, 1736), (7, 62, 434), (8, 28, 1736), (8, 31, 248), (9, 20, 5580)]
    assert sorted(egypt_short(6,31)) == [(6, 38, 1767), (6, 39, 806), (6, 62, 93)]
    assert sorted(egypt_short(10,121)) == [(13, 176, 25168), (15, 66, 1210), (17, 42, 86394), (22, 27, 6534)]

def test_discriminant():
    assert discriminant([1,2,3]) == -8
    assert discriminant([1,-2,3]) == -8
    assert discriminant([1,-2,-3]) == 16
    assert discriminant([1,2,3,4]) == -200
    assert discriminant([1,2,3,4,5]) == 10800
    assert discriminant([1,2,3,4,5,6]) == 1037232
    assert discriminant([1,2,3,4,5,6,7]) == -157351936

def test_mulparts():
    assert list(mulparts(1)) == [(1,)]
    assert list(mulparts(12, 1)) == [(12,)]
    assert sorted(mulparts(12, 2)) == [(1, 12), (2, 6), (3, 4), (4, 3), (6, 2), (12, 1)]
    assert sorted(mulparts(12, 3)) == [(1, 1, 12), (1, 2, 6), (1, 3, 4), (1, 4, 3), (1, 6, 2), (1, 12, 1), (2, 1, 6), \
                                       (2, 2, 3), (2, 3, 2), (2, 6, 1), (3, 1, 4), (3, 2, 2), (3, 4, 1), (4, 1, 3), (4, 3, 1), \
                                       (6, 1, 2), (6, 2, 1), (12, 1, 1)]
    assert sorted(mulparts(12)) == [(2, 2, 3), (2, 3, 2), (2, 6), (3, 2, 2), (3, 4), (4, 3), (6, 2), (12,)]

def test_quadintroots():
    for _ in range(1000):
        a = randrange(-100, 100)
        b = randrange(-100, 100)
        c = randrange(-100, 100)
        roots = quadintroots(a, b, c)
        if a == 0:
            assert len(roots) in (0,1), (a,b,c)
            if b == 0:
                assert len(roots) == 0
                continue
            if len(roots) == 0:
                assert c % b != 0, (a,b,c)
            if len(roots) == 1:
                x = roots[0]
                assert a*x*x + b*x + c == 0, (a,b,c)
            continue
        D = b*b - 4*a*c
        if D < 0: assert roots == (), (a,b,c)
        if D == 0: assert len(roots) in (0,1), (a,b,c)
        if D == 0 and len(roots) == 0: assert b % (2*a) != 0, (a,b,c)
        if D == 0 and len(roots) == 1: assert len(roots) == 1, (a,b,c)
        for x in roots: assert a*x*x + b*x + c == 0, (a,b,c,x)

def test_cubicintrootsgiven():
    for _ in range(1000):
        a = randrange(-100, 100)
        g = randrange(-100, 100)
        h = randrange(-100, 100)
        r = randrange(-100, 100)
        # (ax^2 + gx + h) * (x - r) == ax^3 + (g - ar)x^2 + (h - gr)x - hr
        b, c, d = g - a*r, h - g*r, -h*r
        roots1 = set(quadintroots(a,g,h)) | {r}
        roots2t = cubicintrootsgiven(a, b, c, d, r)
        roots2s = set(roots2t)
        assert len(roots2t) == len(roots2s), (a,g,h,r)
        assert len(roots2t) >= 1, (a,g,h,r)
        assert roots1 == roots2s, (a,g,h,r)
        for x in roots2s: assert a*x**3 + b*x**2 + c*x + d == 0, (a,g,h,r)

def test_cubicintroots():
    # Three distinct real roots, all integers
    for _ in range(1000):
        a, b, c, d = 0, 0, 0, 0
        while not (a < b < c):
            a = randrange(-100, 100)
            b = randrange(-100, 100)
            c = randrange(-100, 100)
        while d == 0:
            d = randrange(-10, 10)
        # d * (x - a) * (x - b) * (x - c)
        # d * (x^3 - (a+b+c)x^2 + (ab+bc+ca)x - abc)
        assert [a,b,c] == sorted(cubicintroots(d, -d*(a+b+c), d*(a*b+b*c+c*a), -d*a*b*c))
    # Three distinct real roots, two integers
    for _ in range(1000):
        a, b, d = 0, 0, 0
        # For this test, we need c to be a non-integer root, but for the coefficients to still be integers.
        # This demands that c be in Q \ Z.
        while a >= b:
            a = randrange(-100, 100)
            b = randrange(-100, 100)
        f = Fraction(1)
        while f.denominator == 1: f = Fraction(randrange(100), randrange(1, 100))
        f %= 1
        for c in (a - f - 10, a - f, a + f, b - f, (a + b) // 2 + f, b + f, b + f + 10):
            # This loop ensures that the non-integer root will be in several places relative to the others.
            f, g = c.numerator, c.denominator
            while d == 0:
                d = randrange(-10, 10)
            # d * (x - a) * (x - b) * (g*x - f)
            # d * (gx^3 - (f + ag + bg)x^2 + (abg + af + bf)x - abf)
            assert [a,b] == sorted(cubicintroots(d*g, -d*(f+a*g+b*g), d*(a*b*g+a*f+b*f), -d*a*b*f))
    # Three distinct real roots, one integer
    for _ in range(1000):
        a, b, c, d = 0, Fraction(1), Fraction(1), 0
        while b.denominator == 1 or c.denominator == 1:
            a = randrange(-10, 10)
            b = Fraction(randrange(-100, 100), randrange(1, 100))
            c = Fraction(randrange(-100, 100), randrange(1, 100))
        f, g, p, q = b.numerator, b.denominator, c.numerator, c.denominator
        while d == 0:
            d = randrange(-10, 10)
        # d * (x - a) * (gx - f) * (qx - p)
        # d * (gqx^3 + (-fq - gp - agq)x^2 + (fp + afq + agp)x - afp)
        assert (a,) == cubicintroots(d*g*q, -d * (f*q + g*p + a*g*q), d * (f*p + a*f*q + a*g*p), -d*a*f*p)
    # Three distinct real roots, no integers
    for _ in range(1000):
        a, b, c, d = Fraction(1), Fraction(1), Fraction(1), 0
        while a.denominator == 1 or b.denominator == 1 or c.denominator == 1:
            a = Fraction(randrange(-100, 100), randrange(1, 100))
            b = Fraction(randrange(-100, 100), randrange(1, 100))
            c = Fraction(randrange(-100, 100), randrange(1, 100))
        while d == 0:
            d = randrange(-10, 10)
        f = a.denominator * b.denominator * c.denominator
        d, c, b, a = d*f, -d*f * (a + b + c), d*f * (a*b + b*c + c*a), -d*f*a*b*c
        assert () == cubicintroots(int(d), int(c), int(b), int(a))
    # Two distinct real roots, all integers
    for _ in range(1000):
        a, b, d = 0, 0, 0
        while a == b:
            a = randrange(-100, 100)
            b = randrange(-100, 100)
        c = b
        while d == 0:
            d = randrange(-10, 10)
        # d * (x - a) * (x - b) * (x - c)
        assert [min(a,b), max(a,b)] == sorted(cubicintroots(d, -d*(a+b+c), d*(a*b+b*c+c*a), -d*a*b*c))
    # Two distinct real roots, repeated is integer, other is not
    for _ in range(1000):
        a, b, d = 0, Fraction(1), 0
        a = randrange(-100, 100)
        while b.denominator == 1:
            b = Fraction(randrange(-100, 100), randrange(1, 100))
        while d == 0:
            d = randrange(-10, 10)
        f, g = b.numerator, b.denominator
        # d * (x - a) * (x - a) * (g*x - f)
        # d * (gx^3 - (f + ag + ag)x^2 + (aag + af + af)x - aaf)
        assert (a,) == cubicintroots(d*g, -d*(f+a*g+a*g), d*(a*a*g+a*f+a*f), -d*a*a*f)
    # Two distinct real roots, repeated is not integer, other is
    for _ in range(1000):
        a, b, d = 0, Fraction(1), 0
        a = randrange(-10, 10)
        while b.denominator == 1:
            b = Fraction(randrange(-100, 100), randrange(1, 100))
        f, g = b.numerator, b.denominator
        while d == 0:
            d = randrange(-10, 10)
        # d * (x - a) * (gx - f) * (gx - f)
        # d * (ggx^3 + (-fg - gf - agg)x^2 + (ff + afg + agf)x - aff)
        assert (a,) == cubicintroots(d*g*g, -d * (f*g + g*f + a*g*g), d * (f*f + a*f*g + a*g*f), -d*a*f*f)
    # Two distinct real roots, no integers
    for _ in range(1000):
        a, b, d = Fraction(1), Fraction(1), 0
        while a.denominator == 1 or b.denominator == 1:
            a = Fraction(randrange(-100, 100), randrange(1, 100))
            b = Fraction(randrange(-100, 100), randrange(1, 100))
        while d == 0:
            d = randrange(-10, 10)
        f = a.denominator * b.denominator * b.denominator
        d, c, b, a = d*f, -d*f * (a + b + b), d*f * (a*b + b*c + b*a), -d*f*a*b*b
        assert () == cubicintroots(int(d), int(c), int(b), int(a))
    # One real root, integer, triple
    for _ in range(1000):
        a, d = randrange(-100, 100), 0
        while d == 0: d = randrange(-10, 10)
        assert (a,) == cubicintroots(d, -3*a*d, 3*a*a*d, -a*a*a*d)
    # One real root, integer, single
    for _ in range(1000):
        a = randrange(-100, 100)
        while True:
            b = randrange(-100, 100)
            c = randrange(-100, 100)
            d = randrange(-100, 100)
            if c*c - 4*b*d < 0: break
        # (x - a) * (bx^2 + cx + d)
        # bx^3 + (c - ab)x^2 + (d - ac)x - ad
        assert (a,) == cubicintroots(b, c - a*b, d - a*c, -a*d)
    # One real root, not integer
    for _ in range(1000):
        a = Fraction(1)
        while a.denominator == 1:
            a = Fraction(randrange(-100, 100), randrange(1, 100))
        while True:
            b = randrange(-100, 100)
            c = randrange(-100, 100)
            d = randrange(-100, 100)
            if c*c - 4*b*d < 0: break
        f, g = a.numerator, a.denominator
        # (gx - f) * (bx^2 + cx + d)
        # bgx^3 + (cg - bf)x^2 + (dg - cf)x - df
        assert () == cubicintroots(b*g, c*g - b*f, d*g - c*f, -d*f)

def test_sqfrgen():
    assert sorted(sqfrgen(())) == [1]
    assert sorted(sqfrgen((2,))) == [1, 2]
    assert sorted(sqfrgen((2,3))) == [1, 2, 3, 6]
    assert sorted(sqfrgen((2,3,5))) == [1, 2, 3, 5, 6, 10, 15, 30]
    assert sorted(sqfrgen((2,3,5,7))) == [1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210]
    assert sorted(filter(lambda x:x<100,sqfrgen(list(primegen(12))))) == [1,2,3,5,6,7,10,11,14,15,21,22,30,33,35,42,55,66,70,77]

def test_sqfrgenb():
    assert sorted(sqfrgenb((), 70)) == [1]
    assert sorted(sqfrgenb((2,), 70)) == [1, 2]
    assert sorted(sqfrgenb((2,3), 70)) == [1, 2, 3, 6]
    assert sorted(sqfrgenb((2,3,5), 70)) == [1, 2, 3, 5, 6, 10, 15, 30]
    assert sorted(sqfrgenb((2,3,5,7), 70)) == [1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70]
    assert sorted(sqfrgenb(list(primegen(18)), 70)) == [1,2,3,5,6,7,10,11,13,14,15,17,21,22,26,30,33,34,35,39,42,51,55,65,66,70]
    assert sorted(sqfrgenb(list(primegen(18)), 69)) == [1,2,3,5,6,7,10,11,13,14,15,17,21,22,26,30,33,34,35,39,42,51,55,65,66]

def test_sqrtcfrac():
    assert sqrtcfrac(114) == (10, [1, 2, 10, 2, 1, 20])
    assert sqrtcfrac(2) == (1, [2])
    assert sqrtcfrac(16) == (4, [])

def test_convergents():
    assert list(convergents((1,2,2,2,2))) == [(1, 1), (3, 2), (7, 5), (17, 12), (41, 29)]
    assert list(convergents((2,1,2,1,1,4,1))) == [(2, 1), (3, 1), (8, 3), (11, 4), (19, 7), (87, 32), (106, 39)]
    assert list(convergents((3,7,15,1,292))) == [(3, 1), (22, 7), (333, 106), (355, 113), (103993, 33102)]
    a, b = sqrtcfrac(13)
    assert list(islice(convergents(chain([a], cycle(b))), 8)) == [(3,1),(4,1),(7,2),(11,3),(18,5),(119,33),(137,38),(256,71)]

def test_contfrac_rat():
    assert list(contfrac_rat(3, 2)) == [1, 2]
    assert list(contfrac_rat(103993, 33102)) == [3, 7, 15, 1, 292]
    assert list(contfrac_rat(*list(convergents((1,2,2,2,2,2,2,2,2,2)))[-1])) == [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    assert list(convergents(contfrac_rat(103993, 33102)))[-1] == (103993, 33102)

def test_quadratic_scf():
    assert quadratic_scf(13, 8, 0) == ([1, 1, 1, 1, 2], [])
    assert quadratic_scf(13, 8, 5) == ([1, 1, 9], [2, 8])
    assert quadratic_scf(13, -8, 5) == ([-2, 10], [2, 8])
    assert quadratic_scf(13, 8, 25) == ([2, 4], [])

def test_simplepell():
    assert list(islice(simplepell(2), 6)) == [(3, 2), (17, 12), (99, 70), (577, 408), (3363, 2378), (19601, 13860)]
    assert list(islice(simplepell(3), 6)) == [(2, 1), (7, 4), (26, 15), (97, 56), (362, 209), (1351, 780)]
    assert next(simplepell(61)) == (1766319049, 226153980)
    assert next(simplepell(661)) == (16421658242965910275055840472270471049, 638728478116949861246791167518480580)

def test_mobiussieve(): assert list(mobiussieve(22)) == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 1]
def test_divcountsieve(): assert list(divcountsieve(23)) == [1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4, 5, 2, 6, 2, 6, 4, 4]

def test_totientsieve():
    assert list(totientsieve(21)) == [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8]
    assert list(totientsieve(21, 2)) == [1, 3, 8, 12, 24, 24, 48, 48, 72, 72, 120, 96, 168, 144, 192, 192, 288, 216, 360, 288]
    assert list(totientsieve(18, 3)) == [1, 7, 26, 56, 124, 182, 342, 448, 702, 868, 1330, 1456, 2196, 2394, 3224, 3584, 4912]

def test_divsigmasieve():
    assert list(divsigmasieve(30, 0)) == [1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4, 5, 2, 6, 2, 6, 4, 4, 2, 8, 3, 4, 4, 6, 2]
    assert list(divsigmasieve(24, 1)) == [1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24, 31, 18, 39, 20, 42, 32, 36, 24]
    assert list(divsigmasieve(20, 2)) == [1, 5, 10, 21, 26, 50, 50, 85, 91, 130, 122, 210, 170, 250, 260, 341, 290, 455, 362]
    assert list(divsigmasieve(18, 3)) == [1, 9, 28, 73, 126, 252, 344, 585, 757, 1134, 1332, 2044, 2198, 3096, 3528, 4681, 4914]

def test_factorsieve():
    assert [sorted(f.items()) for f in factorsieve(9)] == [[],[(2,1)],[(3,1)],[(2,2)],[(5,1)],[(2,1),(3,1)],[(7,1)],[(2,3)]]
    gen = factorsieve()
    for _ in range(362879): next(gen)
    assert next(gen) == {2:7, 3:4, 5:1, 7:1}

def test_pollardrho_brent():
    n = factorial(20) + 1
    f = pollardrho_brent(n)
    assert n % f == 0
    assert 1 < f < n

def test_cbrtmod_prime():
    assert [cbrtmod_prime(a,11) for a in range(11)] == [[0], [1], [7], [9], [5], [3], [8], [6], [2], [4], [10]]
    assert [cbrtmod_prime(a,19) for a in range(11)] == [[0], [1, 7, 11], [], [], [], [], [], [4, 6, 9], [2, 3, 14], [], []]
    for p in primegen(100):
        for a in range(p):
            assert [x for x in range(p) if pow(x, 3, p) == a] == cbrtmod_prime(a, p), (a, p)

def test_sqrtmod_prime():
    for p in primegen(100):
        for a in range(p):
            if (p != 2) and (legendre(a, p) == -1): continue
            assert sqrtmod_prime(a, p) in [x for x in range(p) if pow(x, 2, p) == a], (a, p)

def test_isprime():
    assert [n for n in range(100) if isprime(n)] == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert [n for n in range(91) if isprime(1000*n+1)] == [3,4,7,9,13,16,19,21,24,28,51,54,55,61,69,70,76,81,88,90]
    assert isprime(factorial(38) + 1) == False
    assert isprime(factorial(38) - 1) == True
    assert isprime(1002261781) == False

def test_qfprp():
    assert [n for n in range(11, 80) if qfprp(n, 1, -1)] == [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79]
    assert [qfprp(n, 1, -1) for n in (factorial(38)+1, factorial(38)-1)] == [False, True]
    for n in (3*3, 5*13, 3*5*7, 3*7*13, 13*37, 7*73, 3*11*17, 3*3*5*13, 7*11*13): assert qfprp(n, 4, 8)     # False positives
    for n in (23*67, 151*3301, 661*1321, 23*199*353, 1153*3457, 919*4591): assert qfprp(n, 7, 5)            # False positives

def test_bpsw():
    assert [n for n in range(100) if bpsw(n)] == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert [n for n in range(91) if bpsw(1000*n+1)] == [3,4,7,9,13,16,19,21,24,28,51,54,55,61,69,70,76,81,88,90]
    assert bpsw(factorial(38) + 1) == False
    assert bpsw(factorial(38) - 1) == True

def test_xslprp():
    assert [n for n in range(31, 100) if xslprp(n, 3)] == [31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    assert [xslprp(n, 3) for n in (factorial(38)+1, factorial(38)-1)] == [False, True]
    false_positives = (17*19, 13*29, 31*61, 43*89, 37*113, 53*109, 7*23*41)
    assert [xslprp(n, 3) for n in false_positives] == [False, False, False, False, True, True, False]

def test_slprp():
    assert [n for n in range(11, 80) if slprp(n, 1, -1)] == [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79]
    assert [slprp(n, 1, -1) for n in (factorial(38)+1, factorial(38)-1)] == [False, True]
    errors = (17*19, 13*29, 31*61, 43*89, 37*113, 53*109, 7*23*41)
    assert [slprp(n, 1, -1) for n in errors] == [False, False, False, False, True, True, False]

def test_lprp():
    assert [n for n in range(11, 85) if lprp(n, 1, -1)] == [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83]
    assert [lprp(n, 1, -1) for n in (factorial(38)+1, factorial(38)-1)] == [False, True]
    false_positives = (17*19, 13*29, 31*61, 43*89, 37*113, 53*109, 7*23*41)
    assert [lprp(n, 1, -1) for n in false_positives] == [True, True, True, True, True, True, True]

def test_miller():
    assert [miller(n) for n in [2,3,5,7,101,127,1009, factorial(38) - 1]] == [True, True, True, True, True, True, True, True]
    assert [miller(n) for n in [28, 36, 72, 98, 105, factorial(38) + 1]] == [False, False, False, False, False, False]

def test_mrab():
    assert     mrab(factorial(38) - 1, (2,3))
    assert not mrab(factorial(38) + 1, (2,3))

def test_sprp():    # TODO: False positives
    assert     sprp(factorial(38) - 1, 2)
    assert not sprp(factorial(38) + 1, 2)

def test_legendre():
    assert [legendre(a, 11) for a in [-10, -7, -4, -2, -1, 0, 1, 2, 4, 7, 10]] == [1, 1, -1, 1, -1, 0, 1, -1, 1, -1, -1]
    assert [legendre(a, 17) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [-1, 1, 1, 1, 1, 0, 1, 1, 1, 1, -1]
    assert [legendre(a, 101) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [-1, 1, 1, -1, 1, 0, 1, -1, 1, 1, -1]

def test_jacobi():
    assert [jacobi(a, 15) for a in [-10, -7, -4, -2, -1, 0, 1, 2, 4, 7, 10]] == [0, 1, -1, -1, -1, 0, 1, 1, 1, -1, 0]
    assert [jacobi(a, 13) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [1, 1, 1, -1, 1, 0, 1, -1, 1, 1, 1]
    assert [jacobi(a, 11) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [1, -1, -1, 1, -1, 0, 1, -1, 1, 1, -1]

def test_kronecker():
    assert [kronecker(a, 15) for a in [-10, -7, -4, -2, -1, 0, 1, 2, 4, 7, 10]] == [0, 1, -1, -1, -1, 0, 1, 1, 1, -1, 0]
    assert [kronecker(a, 14) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [0, -1, 0, 0, -1, 0, 1, 0, 0, 1, 0]
    assert [kronecker(a, 11) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [1, -1, -1, 1, -1, 0, 1, -1, 1, 1, -1]
    assert [kronecker(a, -11) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [-1, 1, 1, -1, 1, 0, 1, -1, 1, 1, -1]
    assert [kronecker(a, 32) for a in [-10, -9, -4, -2, -1, 0, 1, 2, 4, 9, 10]] == [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]

def test_linrec():
    assert [linrec(k, [1, 1], [0, 1]) for k in range(18)] == [0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597]    # Fibo
    assert [linrec(k, [1, 1], [0, 1], 10) for k in range(20)] == [0,1,1,2,3,5,8,3,1,4,5,9,4,3,7,0,7,7,4,1]              # Fibo
    assert [linrec(k, [1, 1], [2, 1], 10) for k in range(20)] ==     [2,1,3,4,7,1,8,9,7,6,3,9,2,1,3,4,7,1,8,9]          # Lucas
    assert [linrec(k, [1, 1], [2, 1]) for k in range(17)] == [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207]   # Lucas
    assert [linrec(k, [1, 1, 0], [3, 0, 2]) for k in range(19)] == [3,0,2,3,2,5,5,7,10,12,17,22,29,39,51,68,90,119,158] # Perrin
    assert [linrec(k, [1, 1, 0], [3, 0, 2], 10) for k in range(20)] == [3,0,2,3,2,5,5,7,0,2,7,2,9,9,1,8,0,9,8,9]        # Perrin
    assert linrec(400, [1, 0, 1], [0, 0, 1]) == 719696709185072238228862568935651761390476159269863132285895106694
    assert linrec(400, [1, 0, 1], [0, 0, 1], 10**10) == 5895106694

def test_linrecgen():
    assert list(islice(linrecgen([1, 1], [0, 1]), 18)) == [0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597]       # Fibo
    assert list(islice(linrecgen([1, 1], [0, 1], 5), 20)) == [0,1,1,2,3,0,3,3,1,4,0,4,4,3,2,0,2,2,4,1]                  # Fibo
    assert list(islice(linrecgen([1, 1], [2, 1]), 17)) == [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207]      # Lucas
    assert list(islice(linrecgen([1, 1], [2, 1], 5), 20)) == [2,1,3,4,2,1,3,4,2,1,3,4,2,1,3,4,2,1,3,4]                  # Lucas
    assert list(islice(linrecgen([1, 1, 0], [3, 0, 2]), 19)) == [3,0,2,3,2,5,5,7,10,12,17,22,29,39,51,68,90,119,158]    # Perrin
    assert list(islice(linrecgen([1, 1, 0], [3, 0, 2], 5), 20)) == [3,0,2,3,2,0,0,2,0,2,2,2,4,4,1,3,0,4,3,4]            # Perrin

def test_binlinrecgen():
    assert list(islice(binlinrecgen(1, -1, 0, 1), 18)) == [0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597]       # Fibo
    assert list(islice(binlinrecgen(1, -1, 2, 1), 17)) == [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207]      # Lucas
    assert list(islice(binlinrecgen(3,  2, 0, 1), 15)) == [0,1,3,7,15,31,63,127,255,511,1023,2047,4095,8191,16383]  # Mersenne

def test_lucas():
    assert [lucas(k, 1, -1)[0] for k in range(18)] == [0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597]           # Fibo
    assert [lucas(k, 1, -1)[1] for k in range(17)] == [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207]          # Lucas
    assert [lucas(k, 6, 9) for k in range(7)] == [(0,2), (1,6), (6,18), (27,54), (108,162), (405,486), (1458,1458)]

def test_binlinrec():
    assert [binlinrec(k, 1, -1, 0, 1) for k in range(18)] == [0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597]    # Fibo
    assert [binlinrec(k, 1, -1, 2, 1) for k in range(17)] == [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207]   # Lucas
    assert [binlinrec(k, 3,  2, 0, 1) for k in range(14)] == [0,1,3,7,15,31,63,127,255,511,1023,2047,4095,8191]     # Mersenne

def test_lucasgen():
    assert list(islice(lucasgen(1, -1), 8)) == [(0,2), (1,1), (1,3), (2,4), (3,7), (5,11), (8,18), (13,29)]     # Fibo & Lucas
    assert list(islice(lucasgen(3,  2), 8)) == [(0,2), (1,3), (3,5), (7,9), (15,17), (31,33), (63,65), (127,129)]   # 2^n +/- 1

def test_lucaschain():
    m, A, n = 10000, 5, 307
    assert lucaschain(m, 2, A, lambda x: (x*x - 2) % n, lambda x,y: (x*y - A) % n) == (154, 132)

def test_fibomod():
    assert fibomod(512, 73) == 8
    assert fibomod(100000, 10**20) == 49895374653428746875

def test_semiprimegen():
    assert list(islice(semiprimegen(), 19)) == [4, 6, 9, 10, 14, 15, 21, 22, 25, 26, 33, 34, 35, 38, 39, 46, 49, 51, 55]
    gen = semiprimegen()
    for _ in range(10**5): next(gen)
    assert next(gen) == 459581

def test_pspgen():
    assert list(islice(pspgen(), 20)) == [2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 25, 26, 29]
    gen = pspgen()
    for _ in range(10**5): next(gen)
    assert next(gen) == 325615

def test_almostprimegen():
    assert list(islice(almostprimegen(1), 24)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
    assert list(islice(almostprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(almostprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(almostprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(almostprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(almostprimegen(1), 26)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101]
    pg = almostprimegen(1)
    for _ in range(99): next(pg)
    assert next(pg) == 541
    assert list(islice(almostprimegen(3), 19)) == [8, 12, 18, 20, 27, 28, 30, 42, 44, 45, 50, 52, 63, 66, 68, 70, 75, 76, 78]
    assert list(islice(almostprimegen(4), 17)) == [16, 24, 36, 40, 54, 56, 60, 81, 84, 88, 90, 100, 104, 126, 132, 135, 136]
    assert list(islice(almostprimegen(3), 100001))[-8:] == [395063, 395066, 395071, 395074, 395075, 395079, 395085, 395090]
    assert list(islice(almostprimegen(4), 100001))[-8:] == [511689, 511692, 511698, 511708, 511716, 511722, 511725, 511730]

def test_nearlyprimegen():
    assert list(islice(nearlyprimegen(1), 24)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
    assert list(islice(nearlyprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(nearlyprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(nearlyprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(nearlyprimegen(1), 25)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    assert list(islice(nearlyprimegen(1), 26)) == [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101]
    pg = nearlyprimegen(1)
    for _ in range(99): next(pg)
    assert next(pg) == 541
    
    assert list(islice(nearlyprimegen(2), 20)) == [2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 25, 26, 29]
    gen = nearlyprimegen(2)
    for _ in range(10**5): next(gen)
    assert next(gen) == 325615
    
    assert list(islice(nearlyprimegen(3), 21)) == [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23]
    assert list(islice(nearlyprimegen(4), 21)) == [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
    assert list(islice(nearlyprimegen(3), 100001))[-8:] == [174442, 174443, 174445, 174446, 174449, 174451, 174452, 174453]
    assert list(islice(nearlyprimegen(4), 100001))[-8:] == [130106, 130107, 130108, 130109, 130110, 130111, 130114, 130115]

def test_ilog():
    assert ilog(263789, 10) == 5
    assert ilog(1023, 2) == 9

def test_ispower():
    assert ispower(64) == (8,2)
    assert ispower(25) == (5,2)
    assert ispower(-729) == (-9,3)
    assert ispower(1729) == None
    assert ispower(64, 0) == (8,2)
    assert ispower(64, 1) == 64
    assert ispower(64, 2) == 8
    assert ispower(64, 3) == 4
    assert ispower(64, 4) == None
    assert ispower(64, 5) == None
    assert ispower(64, 6) == 2

def test_introot():
    assert introot(-729, 3) == -9
    assert introot(-728, 3) == -8
    assert introot(729, 3) == 9
    assert introot(728, 3) == 8
    assert introot(1023, 2) == 31
    assert introot(1024, 2) == 32
    assert introot(-10, 2) == None
    assert introot(-10, 4) == None
    assert introot(-1000000, 6) == None
    for x in range(-10, 10): assert introot(x, 1) == x
    for x in range(10000):
        for y in range(1, 10):
            r = introot(x, y)
            assert r**y <= x < (r+1)**y

def test_crt():
    assert crt((1,2), (3,4)) == 10
    assert crt((4,5), (10,3)) == 14
    assert crt((-1,-1), (100,101)) == 10099
    assert crt((1,2,3), (5,6,7)) == 206

def test_xgcd():
    for a in range(-100, 100):
        for b in range(-100, 100):
            g, x, y = xgcd(a,b)
            assert g == gcd(a,b), (g,x,y,a,b)
            assert g == a*x + b*y, (g,x,y,a,b)

def test_isprimepower():
    assert [isprimepower(n) for n in range(6, 11)] == [None, (7, 1), (2, 3), (3, 2), None]
    pps = set()
    for p in primegen(100):
        for k in range(1, 25):
            assert isprimepower(p**k) == (p, k), (p,k)
            pps.add(p**k)
    for x in range(1000):
        if x not in pps:
            if isprime(x): assert isprimepower(x) == (x, 1), x
            else: assert isprimepower(x) is None, x

def test_nextprime():
    assert [nextprime(n) for n in (0,1,2,3,4,5,6,7)] == [2,2,3,5,5,7,7,11]
    assert [nextprime(n) for n in (540,541,542,543,544,545,546,547)] == [541,547,547,547,547,547,547,557]
    assert nextprime(1425172824437699411) == 1425172824437700887
    assert nextprime(factorial(38)+1) == 523022617466601111760007224100074291200000043

def test_prevprime():
    assert [prevprime(n) for n in [0, 1, 2, 3, 4, 5, 6, 7, 540, 541, 542]] == [None, None, None, 2, 3, 3, 5, 5, 523, 523, 541]
    assert prevprime(factorial(38)) == 523022617466601111760007224100074291199999999

def test_randprime():
    assert randprime(1, base=2) is None
    for b in range(2, 13):
        for d in range(1, 20):
            n = randprime(d, base=b)
            if (b,d) == (2,1): assert n is None; continue
            assert isprime(n)
            assert ilog(n, b) == d - 1, (x, n, b, d)

def test_randomfactored():
    for n in range(1, 256):
        x, xfac = randomfactored(n**5)
        assert x == prod(p**e for (p,e) in xfac.items()), (x, xfac)
        assert 1 <= x <= n**5, (x, xfac, n)

def test_polyaddmodp():
    assert polyaddmodp([1,2,3], [4,5,6], 7) == [5, 0, 2]
    assert polyaddmodp([1,2,3], [4,5,4], 7) == [5]
    assert polyaddmodp([1,2,3], [6,5,4], 7) == []

def test_polysubmodp():
    assert polysubmodp([1,2,3], [4,5,6], 7) == [4, 4, 4]
    assert polysubmodp([1,2,3], [6,5,10], 7) == [2, 4]

def test_polymulmodp():
    assert polymulmodp([1,2,3], [4,5,6], 7) == [4, 6, 0, 6, 4]
    assert polymulmodp([1,2,3], [4,5,6], 9) == [4, 4, 1]
    assert polymulmodp([2,2], [3,3,3], 6) == []

def test_polydivmodmodp():
    assert polydivmodmodp([1,4,6,4,1], [1,2,1], 7) == ([1, 2, 1], [])
    assert polydivmodmodp([4,5,6,4,1], [1,2,1], 7) == ([1, 2, 1], [3, 1])
    assert polydivmodmodp([4,5,6,4,1], [1,2,2], 8) == (None, None)

def test_gcmd():
    assert gcmd([1,4,6,4,1], [2,3,1], 7) == [1, 1]
    assert gcmd([1,6,4,3,7], [1,5,2,4], 8) is None

def test_polypowmodpmodpoly():
    assert polypowmodpmodpoly([1,1], 101, 7, [1,2,3,4,5]) == [1, 6, 0, 2]
    assert polypowmodpmodpoly([1,1], 101, 15, [1,2,3,4,5]) is None

def test_frobenius_prp():
    pseuds = [911*2731,1087*3259,1619*6473,1031*10301,2003*6007,883*25579]
    assert [frobenius_prp(n, [-1, 1, 0], strong=False) for n in pseuds] == [False, False, True, True, False, False]
    assert [frobenius_prp(n, [-1, 1, 0], strong=True) for n in pseuds] == [False, False, True, False, False, False]
    assert [frobenius_prp(n, [-1, 1, 1], strong=False) for n in pseuds] == [True, True, False, False, True, True]
    assert [frobenius_prp(n, [-1, 1, 1], strong=True) for n in pseuds] == [True, True, False, False, True, False]
    assert frobenius_prp(factorial(38)-1, [-1, 1, 0])
    assert not frobenius_prp(factorial(38)+1, [-1, 1, 0])

def test_siqs():
    assert siqs(factorial(24) - 1) in (625793187653, 991459181683)
    #assert siqs(factorial(38) + 1) in (14029308060317546154181, 37280713718589679646221)

def test_polyroots_prime():
    assert sorted(polyroots_prime([1,2,3], 11)) == [6, 8]
    assert sorted(polyroots_prime([3,3,3,3,3,3], 3)) == [0, 1, 2]
    assert sorted(polyroots_prime([3,3,3,3,3,6], 3)) == [0, 1, 2]
    assert sorted(polyroots_prime([1,2,3], 3)) == [1]
    assert sorted(polyroots_prime([1], 101)) == []
    assert sorted(polyroots_prime([1,2], 101)) == [50]
    assert sorted(polyroots_prime([1,2,3], 101)) == []
    assert sorted(polyroots_prime([1,2,3,4], 101)) == [63]
    assert sorted(polyroots_prime([1,2,3,4,5], 101)) == []
    assert sorted(polyroots_prime([1,2,3,4,5,6], 101)) == [27, 76, 96]
    assert sorted(polyroots_prime([1,2,3,4,5,6,7], 101)) == []
    assert sorted(polyroots_prime([1,2,3,4,5,6,7,8], 101)) == [68]
    assert sorted(polyroots_prime([1,2,3,4,5,6,7,8,9], 101)) == [18, 24]
    assert sorted(polyroots_prime([1,2,3,4,5,6,7,8,9,10], 101)) == []
    assert sorted(polyroots_prime([0,1,2,3,4,5,6,7,8,9,10], 101)) == [0]
    
    # Check the fancy algorithm against the brute-force solution:
    for d in range(10):
        for p in primegen(10):
            for _ in range(10):
                poly = [randrange(2*p) for n in range(d+1)]
                assert sorted(polyroots_prime(poly, p)) == [x for x in range(p) if polyval(poly, x, p) == 0], (d, p, poly)

def test_hensel():
    assert sorted(hensel([3,3,3,3,3,6], 3, 4)) == []
    assert sorted(hensel([3,3,3,3,3,3], 3, 4)) == [8, 17, 26, 35, 44, 53, 62, 71, 80]
    
    # Check the fancy algorithm against the brute-force solution:
    for d in range(10):
        for p in primegen(10):
            for e in range(1, 5):
                for _ in range(10):
                    poly = [randrange(2*p) for n in range(d+1)]
                    assert sorted(hensel(poly, p, e)) == [x for x in range(p**e) if polyval(poly, x, p**e) == 0], (d,p,e, poly)

def test_sqrtmod():
    assert sqrtmod(100, 187) == [10, 78, 109, 177]
    assert sqrtmod(100, {11:1, 17:1}) == [10, 78, 109, 177]
    assert sqrtmod(0, 100) == [0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
    assert sqrtmod(97, 1009) == []
    
    # Check the fancy algorithm against the brute-force solution:
    for a in range(42):
        for b in range(1, 400):
            assert sqrtmod(a,b) == [x for x in range(b) if pow(x, 2, b) == a % b], (a,b)

def test_polyrootsmod():
    # Check the fancy algorithm against the brute-force solution:
    for d in range(10):
        for n in range(1, 400):
            poly = [randrange(2*n) for x in range(d+1)]
            assert sorted(polyrootsmod(poly, n)) == [x for x in range(n) if polyval(poly, x, n) == 0], (d,n, poly)

def test_totientsum():
    assert [totientsum(n) for n in range(10)] == [0, 1, 2, 4, 6, 10, 12, 18, 22, 28]
    assert [totientsum(n) for n in (100, 1000, 10000000)] == [3044, 304192, 30396356427242]

def test_carmichael(): assert [carmichael(n) for n in range(1, 23)] == [1,1,2,2,4,2,6,2,6,4,10,2,12,6,4,4,16,6,18,4,6,10]
def test_ispractical(): assert [x for x in range(1, 55) if ispractical(x)] == [1,2,4,6,8,12,16,18,20,24,28,30,32,36,40,42,48,54]
def test_perfectpowers(): assert list(islice(perfectpowers(), 18)) == [1,4,8,9,16,25,27,32,36,49,64,81,100,121,125,128,144,169]

def test_multord():
    for b in range(1, 42):
        for n in range(1, 100):
            if b == 1 or n == 1: assert multord(b,n) == 1, (b,n)
            elif gcd(b,n) != 1: assert multord(b,n) is None, (b,n)
            else:
                for k in range(1, n):
                    if pow(b, k, n) == 1: break
                else: assert False, (b,n)
                assert k == multord(b,n)
    for b in range(1, 42):
        for n in range(1, 100):
            nfac = factorint(n)
            if b == 1 or n == 1: assert multord(b,nfac) == 1, (b,n)
            elif gcd(b,n) != 1: assert multord(b,nfac) is None, (b,n)
            else:
                for k in range(1, n):
                    if pow(b, k, n) == 1: break
                else: assert False, (b,n)
                assert k == multord(b,nfac)

def test_pythags():
    assert sorted(pythags(80, primitive=True)) == [(3, 4, 5), (5, 12, 13), (7, 24, 25), (15, 8, 17), (21, 20, 29)]
    assert sorted(pythags(56)) == [(3, 4, 5), (5, 12, 13), (6, 8, 10), (7, 24, 25), (9, 12, 15), (12, 16, 20), (15, 8, 17)]

def test_partgen():
    assert list(partgen(5)) == [[1, 1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 3], [1, 2, 2], [1, 4], [2, 3], [5]]
    pg = partgen(50)
    for _ in range(2 * 10**5): x = next(pg)
    assert next(pg) == [3, 4, 5, 5, 6, 6, 6, 6, 9]

def test_partconj():
    assert partconj([1, 2, 3, 4, 5]) == [1, 2, 3, 4, 5]
    assert partconj([1, 2, 6, 8]) == [1, 1, 2, 2, 2, 2, 3, 4]

def test_farey():
    assert list(farey(1)) == [(0,1), (1,1)]
    assert list(farey(2)) == [(0,1), (1,2), (1,1)]
    assert list(farey(3)) == [(0,1), (1,3), (1,2), (2,3), (1,1)]
    assert list(farey(4)) == [(0,1), (1,4), (1,3), (1,2), (2,3), (3,4), (1,1)]
    assert list(farey(5)) == [(0,1), (1,5), (1,4), (1,3), (2,5), (1,2), (3,5), (2,3), (3,4), (4,5), (1,1)]
    assert list(farey(6)) == [(0,1), (1,6), (1,5), (1,4), (1,3), (2,5), (1,2), (3,5), (2,3), (3,4), (4,5), (5,6), (1,1)]
    assert len(list(farey(100))) == 1 + totientsum(100)

def test_fareyneighbors():
    assert fareyneighbors(5, 1, 3) == [(1, 4), (2, 5)]
    assert fareyneighbors(121, 5, 121) == [(4, 97), (1, 24)]
    assert fareyneighbors(121, 74, 95) == [(81, 104), (67, 86)]
    assert fareyneighbors(121, 67, 86) == [(74, 95), (60, 77)]
    assert fareyneighbors(121, 16, 21) == [(83, 109), (77, 101)]

def test_hamming():
    assert list(islice(hamming((2,)), 16)) == [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
    assert list(islice(hamming( 2  ), 16)) == [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
    assert list(islice(hamming((2,3)), 21)) == [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54, 64, 72, 81, 96, 108]
    assert list(islice(hamming( 2,3 ), 21)) == [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54, 64, 72, 81, 96, 108]
    assert list(islice(hamming((2,3,5)), 21)) == [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40]
    assert list(islice(hamming( 2,3,5 ), 21)) == [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40]

def test_primefac():
    for n in range(1, 1000):
        nfacs = list(primefac(n, trial=0))
        assert n == prod(nfacs)
    assert list(primefac(1001)) == [7, 11, 13]
    assert list(primefac(1729)) == [7, 13, 19]
    assert list(sorted(primefac(factorial(24) - 1))) == [625793187653, 991459181683]
    assert list(sorted(primefac(factorial(38) + 1, trialextra=[14029308060317546154181]))) == [14029308060317546154181, 37280713718589679646221]

def test_factorint():
    for n in range(1, 1000):
        nfacs = factorint(n, trial=0)
        assert n == prod(p**e for (p,e) in nfacs.items())
    assert factorint(1001) == {7:1, 11:1, 13:1}
    assert factorint(1729) == {7:1, 13:1, 19:1}
    assert factorint(3628800) == {2:8, 3:4, 5:2, 7:1}
    assert factorint(factorial(24) - 1) == {625793187653:1, 991459181683:1}
    assert factorint(factorial(38) + 1, trialextra=[14029308060317546154181]) == {14029308060317546154181:1, 37280713718589679646221:1}

def test_divisors():
    assert [sorted(divisors(n)) for n in [0, 1, 10, 28]] == [[], [1], [1, 2, 5, 10], [1, 2, 4, 7, 14, 28]]
    assert sorted(divisors(496)) == [1, 2, 4, 8, 16, 31, 62, 124, 248, 496]
    assert sorted(divisors(1729)) == [1, 7, 13, 19, 91, 133, 247, 1729]
    assert sorted(divisors({2:3, 3:2})) == [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]

def test_divisors_factored():
    assert list(sorted(x.items()) for x in divisors_factored(12)) == [[],[(2,1)],[(2,2)],[(3,1)],[(2,1),(3,1)],[(2,2),(3,1)]]

def test_divcount(): assert [divcount(n) for n in (28, 42, 40320, {2:2, 3:1})] == [6, 8, 96, 6]
def test_mobius(): assert [mobius(n) for n in range(1, 20)] == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1]
def test_liouville(): assert list(liouville(n) for n in range(1, 22)) == [1,-1,-1,1,-1,1,-1,-1,1,1,-1,-1,-1,1,1,1,-1,-1,-1,-1,1]

def test_divsigma():
    assert [divsigma(n) for n in [1, 6, 10, 28, 496, 1024, 1729]] == [1, 12, 18, 56, 992, 2047, 2240]
    assert [divsigma(n, 2) for n in [1, 6, 10, 28, 496, 1024, 1729]] == [1, 50, 130, 1050, 328042, 1398101, 3077000]

def test_totient():
    assert [totient(n) for n in range(1, 24)] == [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22]
    assert [totient(n, 2) for n in range(1, 19)] == [1, 3, 8, 12, 24, 24, 48, 48, 72, 72, 120, 96, 168, 144, 192, 192, 288, 216]
    assert totient(factorint(120)) == 32

def test_PQa():
    assert list(islice(PQa(1, 1, 2), 5)) == [(1, 1, 1, 1), (2, 3, 1, 1), (5, 7, 1, 1), (12, 17, 1, 1), (29, 41, 1, 1)]
    assert list(islice(PQa(1, 1, 3), 5)) == [(1, 1, 1, 1), (1, 2, 1, 2), (3, 5, 1, 1), (4, 7, 1, 2), (11, 19, 1, 1)]
    assert list(islice(PQa(1, 1, 5), 5)) == [(1, 2, 1, 1), (4, 9, 2, 1), (17, 38, 2, 1), (72, 161, 2, 1), (305, 682, 2, 1)]
    assert list(islice(PQa(1, 2, 3), 5)) == [(1, 1, 1, 2), (2, 4, 1, 1), (3, 5, 1, 2), (8, 14, 1, 1), (11, 19, 1, 2)]
    assert list(islice(PQa(1, 2, 5), 5)) == [(1, 1, 1, 2), (1, 3, 1, 2), (2, 4, 1, 2), (3, 7, 1, 2), (5, 11, 1, 2)]
    assert list(islice(PQa(1, 4, 5), 5)) == [(1, -1, 1, 4), (1, 3, -1, 1), (5, 11, 2, 1), (21, 47, 2, 1), (89, 199, 2, 1)]
    assert list(islice(PQa(2, 2, 2), 5)) == [(1, 0, 2, 2), (1, 2, 0, 1), (3, 4, 1, 1), (7, 10, 1, 1), (17, 24, 1, 1)]
    assert list(islice(PQa(2, 2, 3), 5)) == [(1, 0, 2, 2), (1, 2, 0, 1), (2, 2, 1, 2), (5, 6, 1, 1), (7, 8, 1, 2)]
    assert list(islice(PQa(2, 3, 5), 5)) == [(1, 1, 2, 3), (3, 6, 1, 1), (13, 25, 2, 1), (55, 106, 2, 1), (233, 449, 2, 1)]
    assert list(islice(PQa(2, 4, 2), 5)) == [(1, -2, 2, 4), (0, 4, -2, -1), (1, 2, 2, 2), (1, 6, 0, 1), (3, 14, 1, 1)]
    assert list(islice(PQa(2, 4, 3), 5)) == [(1, -2, 2, 4), (0, 4, -2, -1), (1, 10, 2, 1), (1, 14, 1, 2), (3, 38, 1, 1)]
    assert list(islice(PQa(3, 2, 3), 5)) == [(1, 1, 3, 2), (2, 4, 1, 1), (3, 5, 1, 2), (8, 14, 1, 1), (11, 19, 1, 2)]
    assert list(islice(PQa(3, 2, 5), 5)) == [(1, 1, 3, 2), (1, 3, 1, 2), (2, 4, 1, 2), (3, 7, 1, 2), (5, 11, 1, 2)]
    assert list(islice(PQa(3, 3, 3), 5)) == [(1, 0, 3, 3), (1, 3, 0, 1), (2, 3, 1, 2), (5, 9, 1, 1), (7, 12, 1, 2)]
    assert list(islice(PQa(3, 3, 5), 5)) == [(1, 0, 3, 3), (2, 3, 0, 1), (9, 12, 2, 1), (38, 51, 2, 1), (161, 216, 2, 1)]
    assert list(islice(PQa(3, 4, 5), 5)) == [(1, 1, 3, 4), (3, 7, 1, 1), (13, 29, 2, 1), (55, 123, 2, 1), (233, 521, 2, 1)]
    assert list(islice(PQa(4, 2, 2), 5)) == [(1, 0, 4, 2), (1, 2, 0, 1), (3, 4, 1, 1), (7, 10, 1, 1), (17, 24, 1, 1)]
    assert list(islice(PQa(4, 2, 3), 5)) == [(1, 0, 4, 2), (1, 2, 0, 1), (2, 2, 1, 2), (5, 6, 1, 1), (7, 8, 1, 2)]
    assert list(islice(PQa(4, 4, 5), 5)) == [(1, 0, 4, 4), (2, 4, 0, 1), (9, 16, 2, 1), (38, 68, 2, 1), (161, 288, 2, 1)]

def test_pell():
    assert pell(2, 0) == (None, [(0, 0)], None)
    assert pell(4, 0)[1:] == (None, None)
    assert list(islice(pell(4, 0)[0], 8)) == [(0, 0), (2, 1), (4, 2), (6, 3), (8, 4), (10, 5), (12, 6), (14, 7)]
    assert pell(0, 25 * 169)[1:] == (None, None)
    assert list(islice(pell(0, 25 * 169)[0], 8)) == [(65, 0), (65, 1), (65, 2), (65, 3), (65, 4), (65, 5), (65, 6), (65, 7)]
    assert pell(0, -25 * 169) == (None, [], None)
    assert pell(-1, -25 * 169) == (None, [], None)
    assert pell(-1, 25 * 169) == (None, [(0,65),(16,63),(25,60),(33,56),(39,52),(52,39),(56,33),(60,25),(63,16),(65,0)], None)
    assert pell(1, 25 * 169) == (None, [(65, 0), (97, 72), (169, 156), (425, 420), (2113, 2112)], None)
    assert pell(4, 25 * 169) == (None, [(65, 0), (97, 36), (169, 78), (425, 210), (2113, 1056)], None)
    assert pell(2, 1)[1:] == ([(3, 2)], (3, 2))
    assert list(islice(pell(2, 1)[0], 6)) == [(1, 0), (3, 2), (17, 12), (99, 70), (577, 408), (3363, 2378)]
    assert pell(12, 148)[1:] == ([(14, 2), (16, 3), (40, 11), (50, 14)], (7, 2))
    assert list(islice(pell(12, 148)[0], 7)) == [(14, 2), (16, 3), (40, 11), (50, 14), (146, 42), (184, 53), (544, 157)]
    assert list(islice(pell(3, 1)[0], 7)) == [(1, 0), (2, 1), (7, 4), (26, 15), (97, 56), (362, 209), (1351, 780)]
    assert list(islice(pell(61, 1)[0], 2))[1] == (1766319049, 226153980)
    assert list(islice(pell(661, 1)[0], 2))[1] == (16421658242965910275055840472270471049, 638728478116949861246791167518480580)
    assert pell(2, -1)[1:] == ([(1,1)], (3,2))
    assert list(islice(pell(2, -1)[0], 7)) == [(1, 1), (7, 5), (41, 29), (239, 169), (1393, 985), (8119, 5741), (47321, 33461)]
    assert pell(46, 12)[1:] == ([(14, 2), (10594, 1562)], (24335, 3588))
    assert pell(76, 36)[1:] == ([(6, 0), (44, 5), (70, 8), (1020, 117), (14890, 1708), (23756, 2725)], (57799, 6630))
    assert list(islice(pell(76, 36)[0], 7)) == [(6, 0), (44, 5), (70, 8), (1020, 117), (14890, 1708), (23756, 2725), (346794, 39780)]

def test_dirichletcharacter():
    assert dirichletcharacter(2, 1, 1) == 0
    assert dirichletcharacter(40487, 100, 11) == Fraction(15653, 20243)
    
    data = {
    3: {1:['0',   '0'],
        2:['0', '1/2']},
    
    4: {1:['0',   '0'],
        3:['0', '1/2']},
    
    5: {1:['0',   '0',   '0',   '0'],
        2:['0', '1/4', '3/4', '1/2'],
        3:['0', '3/4', '1/4', '1/2'],
        4:['0', '1/2', '1/2',   '0']},
    
    8: {1:['0',   '0',   '0',   '0'],
        3:['0',   '0', '1/2', '1/2'],
        5:['0', '1/2', '1/2',   '0'],
        7:['0', '1/2',   '0', '1/2']},
    
    9: {1:['0',   '0',   '0',   '0',   '0',   '0'],
        2:['0', '1/6', '1/3', '5/6', '2/3', '1/2'],
        4:['0', '1/3', '2/3', '2/3', '1/3',   '0'],
        5:['0', '5/6', '2/3', '1/6', '1/3', '1/2'],
        7:['0', '2/3', '1/3', '1/3', '2/3',   '0'],
        8:['0', '1/2',   '0', '1/2',   '0', '1/2']},
    
    15:{1:['0',   '0',   '0',   '0',   '0',   '0',   '0',   '0'],
        2:['0', '3/4', '1/2', '1/4', '1/4', '1/2', '3/4',   '0'],
        4:['0', '1/2',   '0', '1/2', '1/2',   '0', '1/2',   '0'],
        7:['0', '1/4', '1/2', '1/4', '3/4',   '0', '3/4', '1/2'],
        8:['0', '1/4', '1/2', '3/4', '3/4', '1/2', '1/4',   '0'],
       11:['0', '1/2',   '0',   '0', '1/2', '1/2',   '0', '1/2'],
       13:['0', '3/4', '1/2', '3/4', '1/4',   '0', '1/4', '1/2'],
       14:['0',   '0',   '0', '1/2',   '0', '1/2', '1/2', '1/2']},
    
    16:{1:['0',   '0',   '0',   '0',   '0',   '0',   '0',   '0'],
        3:['0', '3/4', '3/4',   '0', '1/2', '1/4', '1/4', '1/2'],
        5:['0', '3/4', '1/4', '1/2', '1/2', '1/4', '3/4',   '0'],
        7:['0',   '0', '1/2', '1/2',   '0',   '0', '1/2', '1/2'],
        9:['0', '1/2', '1/2',   '0',   '0', '1/2', '1/2',   '0'],
       11:['0', '1/4', '1/4',   '0', '1/2', '3/4', '3/4', '1/2'],
       13:['0', '1/4', '3/4', '1/2', '1/2', '3/4', '1/4',   '0'],
       15:['0', '1/2',   '0', '1/2',   '0', '1/2',   '0', '1/2']},
    
    24:{1:['0',   '0',   '0',   '0',   '0',   '0',   '0',   '0'],
        5:['0',   '0',   '0',   '0', '1/2', '1/2', '1/2', '1/2'],
        7:['0',   '0', '1/2', '1/2',   '0',   '0', '1/2', '1/2'],
       11:['0',   '0', '1/2', '1/2', '1/2', '1/2',   '0',   '0'],
       13:['0', '1/2',   '0', '1/2', '1/2',   '0', '1/2',   '0'],
       17:['0', '1/2',   '0', '1/2',   '0', '1/2',   '0', '1/2'],
       19:['0', '1/2', '1/2',   '0', '1/2',   '0',   '0', '1/2'],
       23:['0', '1/2', '1/2',   '0',   '0', '1/2', '1/2',   '0']},
    
    27:{1:['0',    '0',  '0',    '0',  '0',  '0',  '0',    '0',  '0',    '0',  '0',  '0',  '0',    '0',  '0',    '0',  '0',  '0'],
        2:['0', '1/18','1/9', '5/18','8/9','1/6','1/3','13/18','4/9','17/18','2/9','5/6','2/3', '7/18','7/9','11/18','5/9','1/2'],
        4:['0',  '1/9','2/9',  '5/9','7/9','1/3','2/3',  '4/9','8/9',  '8/9','4/9','2/3','1/3',  '7/9','5/9',  '2/9','1/9',  '0'],
        5:['0', '5/18','5/9', '7/18','4/9','5/6','2/3','11/18','2/9','13/18','1/9','1/6','1/3','17/18','8/9', '1/18','7/9','1/2'],
        7:['0',  '8/9','7/9',  '4/9','2/9','2/3','1/3',  '5/9','1/9',  '1/9','5/9','1/3','2/3',  '2/9','4/9',  '7/9','8/9',  '0'],
        8:['0',  '1/6','1/3',  '5/6','2/3','1/2',  '0',  '1/6','1/3',  '5/6','2/3','1/2',  '0',  '1/6','1/3',  '5/6','2/3','1/2'],
       10:['0',  '1/3','2/3',  '2/3','1/3',  '0',  '0',  '1/3','2/3',  '2/3','1/3',  '0',  '0',  '1/3','2/3',  '2/3','1/3',  '0'],
       11:['0','13/18','4/9','11/18','5/9','1/6','1/3', '7/18','7/9', '5/18','8/9','5/6','2/3', '1/18','1/9','17/18','2/9','1/2'],
       13:['0',  '4/9','8/9',  '2/9','1/9','1/3','2/3',  '7/9','5/9',  '5/9','7/9','2/3','1/3',  '1/9','2/9',  '8/9','4/9',  '0'],
       14:['0','17/18','8/9','13/18','1/9','5/6','2/3', '5/18','5/9', '1/18','7/9','1/6','1/3','11/18','2/9', '7/18','4/9','1/2'],
       16:['0',  '2/9','4/9',  '1/9','5/9','2/3','1/3',  '8/9','7/9',  '7/9','8/9','1/3','2/3',  '5/9','1/9',  '4/9','2/9',  '0'],
       17:['0',  '5/6','2/3',  '1/6','1/3','1/2',  '0',  '5/6','2/3',  '1/6','1/3','1/2',  '0',  '5/6','2/3',  '1/6','1/3','1/2'],
       19:['0',  '2/3','1/3',  '1/3','2/3',  '0',  '0',  '2/3','1/3',  '1/3','2/3',  '0',  '0',  '2/3','1/3',  '1/3','2/3',  '0'],
       20:['0', '7/18','7/9','17/18','2/9','1/6','1/3', '1/18','1/9','11/18','5/9','5/6','2/3','13/18','4/9', '5/18','8/9','1/2'],
       22:['0',  '7/9','5/9',  '8/9','4/9','1/3','2/3',  '1/9','2/9',  '2/9','1/9','2/3','1/3',  '4/9','8/9',  '5/9','7/9',  '0'],
       23:['0','11/18','2/9', '1/18','7/9','5/6','2/3','17/18','8/9', '7/18','4/9','1/6','1/3', '5/18','5/9','13/18','1/9','1/2'],
       25:['0',  '5/9','1/9',  '7/9','8/9','2/3','1/3',  '2/9','4/9',  '4/9','2/9','1/3','2/3',  '8/9','7/9',  '1/9','5/9',  '0'],
       26:['0',  '1/2',  '0',  '1/2',  '0','1/2',  '0',  '1/2',  '0',  '1/2',  '0','1/2',  '0',  '1/2',  '0',  '1/2',  '0','1/2']},
    
    40:{1:['0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0',  '0'],
        3:['0','1/4','1/4','1/2',  '0','3/4','3/4','1/2','1/2','3/4','3/4',  '0','1/2','1/4','1/4',  '0'],
        7:['0','1/4','3/4','1/2','1/2','3/4','1/4',  '0',  '0','1/4','3/4','1/2','1/2','3/4','1/4',  '0'],
        9:['0','1/2','1/2',  '0',  '0','1/2','1/2',  '0',  '0','1/2','1/2',  '0',  '0','1/2','1/2',  '0'],
       11:['0',  '0','1/2',  '0',  '0','1/2',  '0',  '0','1/2','1/2',  '0','1/2','1/2',  '0','1/2','1/2'],
       13:['0','3/4','3/4','1/2','1/2','3/4','3/4',  '0','1/2','1/4','1/4',  '0',  '0','1/4','1/4','1/2'],
       17:['0','3/4','1/4','1/2',  '0','3/4','1/4','1/2',  '0','3/4','1/4','1/2',  '0','3/4','1/4','1/2'],
       19:['0','1/2',  '0',  '0',  '0',  '0','1/2',  '0','1/2',  '0','1/2','1/2','1/2','1/2',  '0','1/2'],
       21:['0','1/2',  '0',  '0','1/2','1/2',  '0','1/2','1/2',  '0','1/2','1/2',  '0',  '0','1/2',  '0'],
       23:['0','3/4','1/4','1/2','1/2','1/4','3/4',  '0',  '0','3/4','1/4','1/2','1/2','1/4','3/4',  '0'],
       27:['0','3/4','3/4','1/2',  '0','1/4','1/4','1/2','1/2','1/4','1/4',  '0','1/2','3/4','3/4',  '0'],
       29:['0',  '0','1/2',  '0','1/2',  '0','1/2','1/2','1/2','1/2',  '0','1/2',  '0','1/2',  '0',  '0'],
       31:['0','1/2','1/2',  '0','1/2',  '0',  '0','1/2',  '0','1/2','1/2',  '0','1/2',  '0',  '0','1/2'],
       33:['0','1/4','3/4','1/2',  '0','1/4','3/4','1/2',  '0','1/4','3/4','1/2',  '0','1/4','3/4','1/2'],
       37:['0','1/4','1/4','1/2','1/2','1/4','1/4',  '0','1/2','3/4','3/4',  '0',  '0','3/4','3/4','1/2'],
       39:['0',  '0',  '0',  '0','1/2','1/2','1/2','1/2',  '0',  '0',  '0',  '0','1/2','1/2','1/2','1/2']},
    }
    
    for q in data.keys():
        for i in range(q):
            if gcd(i,q) != 1: continue
            testdata = list(map(str, (dirichletcharacter(q,i,x) for x in range(q) if gcd(x,q) == 1)))
            assert testdata == data[q][i], (i, testdata, data[q])

def test_primepi():
    for x in range(-10, 2500):
        print(x)
        assert len(list(primegen(x))) == primepi(x-1), (x, list(primegen(x)), primepi(x-1))
    assert primepi(10**1) == 4
    assert primepi(10**2) == 25
    assert primepi(10**3) == 168
    assert primepi(10**4) == 1229
    assert primepi(10**5) == 9592
    assert primepi(10**6) == 78498
    assert primepi(10**7) == 664579
    assert primepi(10**8) == 5761455
    #assert primepi(10**9) == 50847534
    assert primepi(1234567890) == 62106578
    assert primepi(2**10) == 172
    assert primepi(2**11) == 309
    assert primepi(2**12) == 564
    assert primepi(2**13) == 1028
    assert primepi(2**14) == 1900
    assert primepi(2**15) == 3512
    assert primepi(2**16) == 6542
    assert primepi(2**17) == 12251
    assert primepi(2**18) == 23000
    assert primepi(2**19) == 43390
    assert primepi(2**20) == 82025
    assert primepi(2**21) == 155611
    assert primepi(2**22) == 295947
    assert primepi(2**23) == 564163
    assert primepi(2**24) == 1077871
    assert primepi(2**25) == 2063689
    assert primepi(2**26) == 3957809
    assert primepi(2**27) == 7603553
    #assert primepi(2**28) == 14630843
    #assert primepi(2**29) == 28192750
    #assert primepi(2**30) == 54400028
    #assert primepi(2**31) == 105097565
    #assert primepi(2**32) == 203280221

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

def test_powerfulmap():
    assert sorted(x for (x,y) in powerfulmap(125)) == [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, 108, 121, 125]
    assert sorted(powerfulmap(81, lambda y,z: 2**z)) == [(1,1),(4,4),(8,8),(9,4),(16,16),(25,4),(27,8),(32,32),(36,16),(49,4),(64,64),(72,32),(81,16)]

def test_restrictedpartitions():
    assert restrictedpartitions(23, (1,)) == [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    assert restrictedpartitions(23, [2]) == [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
    assert restrictedpartitions(21, (1,2)) == [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11]
    assert restrictedpartitions(17, range(1,10)) == [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 41, 54, 73, 94, 123, 157, 201, 252]
    assert restrictedpartitions(20, primegen(20)) == [1, 0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 9, 10, 12, 14, 17, 19, 23, 26]

def test_rational_in_base():
    assert rational_in_base(10, 11, 6) == ([1], [8], [3])
    assert rational_in_base(10, 0, 6) == ([0], [], [])
    assert rational_in_base(10, 6, 7) == ([0], [], [8, 5, 7, 1, 4, 2])
    assert rational_in_base(2, 11, 14) == ([0], [1], [1, 0, 0])
    assert rational_in_base(12, 221, 14) == ([1, 3], [9], [5, 1, 8, 6, 10, 3])
    assert rational_in_base(12, 221, 1) == ([1, 6, 5], [], [])
    assert rational_in_base(10, 33, 3) == ([1, 1], [], [])
    assert rational_in_base(10, 1, 7) == ([0], [], [1, 4, 2, 8, 5, 7])
    assert rational_in_base(10, 1, 70) == ([0], [0], [1, 4, 2, 8, 5, 7])
    assert rational_in_base(10, 1, 4) == ([0], [2, 5], [])
    assert rational_in_base(10, 3, 12) == ([0], [2, 5], [])
    assert rational_in_base(10, 1, 9) == ([0], [], [1])
    assert rational_in_base(10, 1, 10) == ([0], [1], [])

def test_determinant():
    assert determinant([[1,2,3,4],
                        [1,2,3,5],
                        [1,2,4,4],
                        [4,3,2,1]]) == 5
    assert determinant([[1,2,3,4],
                        [1,2,3,5],
                        [1,2,4,4],
                        [3,3,2,1]]) == 3
    assert determinant([[1,2,3,4],
                        [5,6,7,8],
                        [9,10,11,12],
                        [13,14,15,16]]) == 0
    assert determinant([[1,2,3],
                        [4,5,6],
                        [3,2,1]]) == 0
    assert determinant([[1,2],
                        [2,1]]) == -3
    assert determinant([[1]]) == 1
    assert determinant([[0,1,2,3],
                        [0,4,5,6],
                        [0,3,2,1],
                        [0,9,7,8]]) == 0

def test_dirconv():
    def one(n): return 1
    def I(n): return n if isinstance(n, inttypes) else prod(p**e for (p,e) in n.items())    # compositional identity
    
    h = dirconv(one, totient, ffac=True, gfac=True) # h(n) == n
    assert all(h(n) == n for n in range(1, 1000))
    
    h = dirconv(one, mobius, ffac=True, gfac=True)  # h(n) == int(n==1) --- the identity element for Dirichlet convolution.
    assert h(1) == 1 and all(h(n) == 0 for n in range(2, 1000))
    
    h = dirconv(one, one, ffac=True, gfac=True)  # h(n) == divsigma(n,0)
    assert all(h(n) == divsigma(n,0) for n in range(1, 1000))
    
    h = dirconv(I, one, ffac=True, gfac=True)    # h(n) == divsigma(n,1)
    assert all(h(n) == divsigma(n,1) for n in range(1, 1000))
    
    h = dirconv(I, mobius, ffac=True, gfac=True)    # h(n) == totient(n)
    assert all(h(n) == totient(n) for n in range(1, 1000))
    
    h = dirconv(totient, divcount, ffac=True, gfac=True)    # h(n) == divsigma(n)
    assert all(h(factorint(n)) == divsigma(n) for n in range(1, 1000))
    
    def f(n): return prod(Fraction(comb(2*e,e), 4**e) for (p,e) in factorint(n).items())    # Dirichlet square root of one
    h = dirconv(f, f)
    assert all(h(n) == 1 for n in range(1, 1000))

def test_dirichletinverse():
    f = dirichletinverse(mobius)
    assert all(f(n) == 1 for n in range(1, 1000))
    
    def one(n): return 1
    f = dirichletinverse(one)
    assert all(f(n) == mobius(n) for n in range(1, 1000))
    
    def two(n): return 2
    f = dirichletinverse(two)
    assert all(f(n) == Fraction(mobius(n), 2) for n in range(1, 1000))

def test_dirichletroot():
    f = dirichletroot(divcount, 2, 1)
    assert all(f(n) == 1 for n in range(1, 1000))
    
    def one(n): return 1
    def f(n): return prod(Fraction(comb(2*e,e), 4**e) for (p,e) in factorint(n).items())    # Dirichlet square root of 1
    r = dirichletroot(one, 2, 1)                                                            # Dirichlet square root of 1
    assert all(r(n) == f(n) for n in range(1, 1000))
    
    r = dirichletroot(one, 3, 1)
    assert r(2**0) == r(3**0) == r(5**0) == 1
    assert r(2**1) == r(3**1) == r(5**1) == Fraction(1,3)
    assert r(2**2) == r(3**2) == r(5**2) == Fraction(2,9)
    assert r(2**3) == r(3**3) == r(5**3) == Fraction(14,81)
    assert r(2**4) == r(3**4) == r(5**4) == Fraction(35,243)
    assert r(2**5) == r(3**5) == r(5**5) == Fraction(91,729)
    assert r(2**6) == r(3**6) == r(5**6) == Fraction(728,6561)
    assert r(2**7) == r(3**7) == r(5**7) == Fraction(1976,19683)
    assert r(2**8) == r(3**8) == r(5**8) == Fraction(5434,59049)
    assert r(2**9) == r(3**9) == r(5**9) == Fraction(135850,1594323)
    f = dirconv(dirconv(r, r), r)
    assert all(f(n) == 1 for n in range(1, 100))
    
    r = dirichletroot(one, 4, 1)
    assert r(2**0) == r(3**0) == r(5**0) == 1
    assert r(2**1) == r(3**1) == r(5**1) == Fraction(1,4)
    assert r(2**2) == r(3**2) == r(5**2) == Fraction(5,32)
    assert r(2**3) == r(3**3) == r(5**3) == Fraction(15,128)
    assert r(2**4) == r(3**4) == r(5**4) == Fraction(195,2048)
    assert r(2**5) == r(3**5) == r(5**5) == Fraction(663,8192)
    assert r(2**6) == r(3**6) == r(5**6) == Fraction(4641,65536)
    assert r(2**7) == r(3**7) == r(5**7) == Fraction(16575,262144)
    assert r(2**8) == r(3**8) == r(5**8) == Fraction(480675,8388608)
    assert r(2**9) == r(3**9) == r(5**9) == Fraction(1762475,33554432)
    f = dirconv(dirconv(dirconv(r, r), r), r)
    assert all(f(n) == 1 for n in range(1, 100))
    
    r = dirichletroot(one, 5, 1)
    assert r(2**0) == r(3**0) == r(5**0) == 1
    assert r(2**1) == r(3**1) == r(5**1) == Fraction(1,5)
    assert r(2**2) == r(3**2) == r(5**2) == Fraction(3,25)
    assert r(2**3) == r(3**3) == r(5**3) == Fraction(11,125)
    assert r(2**4) == r(3**4) == r(5**4) == Fraction(44,625)
    assert r(2**5) == r(3**5) == r(5**5) == Fraction(924,15625)
    assert r(2**6) == r(3**6) == r(5**6) == Fraction(4004,78125)
    assert r(2**7) == r(3**7) == r(5**7) == Fraction(17732,390625)
    assert r(2**8) == r(3**8) == r(5**8) == Fraction(79794,1953125)
    assert r(2**9) == r(3**9) == r(5**9) == Fraction(363506,9765625)
    f = dirconv(dirconv(dirconv(dirconv(r, r), r), r), r)
    assert all(f(n) == 1 for n in range(1, 42))

def test_stormer():
    assert sorted(stormer(2,3,5)) == [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (8, 9), (9, 10), (15, 16), (24, 25), (80, 81)]
    assert sorted(stormer(2,3,5, sep=2)) == [(1,3),(2,4),(3,5),(4,6),(6,8),(8,10),(10,12),(16,18),(18,20),(25,27),(30,32),(48,50),(160,162)]
    x = list(stormer(list(primegen(32))))
    assert (max(x), len(x)) == ((1611308699, 1611308700), 482)
    assert sum(x*y for (x,y) in stormer(2,3,5,7,11,13,17,19,23,29)) == 41405478516828404

def test_pythags_by_perimeter():
    data = {}
    for t in pythags(10000): data[sum(t)] = data.get(sum(t), []) + [t]
    for n in range(1, 10000): assert sorted(data.get(n,[])) == sorted(pythags_by_perimeter(n)), n

def test_pollard_pm1(): assert pollard_pm1((factorial(28) - 1) // 239) == 1224040923709997
def test_williams_pp1(): assert williams_pp1(315951348188966255352482641444979927) == 12403590655726899403

def test_ecm():
    assert ecm(factorial(24) - 1) in (625793187653, 991459181683)
    #assert ecm(factorial(38) + 1) in (14029308060317546154181, 37280713718589679646221)

def test_primephi():
    assert primephi(123456789, 0, [0] + list(primegen(20))) == 123456789
    assert primephi(123456789, 1, [0] + list(primegen(20))) == 61728395
    assert primephi(123456789, 2, [0] + list(primegen(20))) == 41152263
    assert primephi(123456789, 3, [0] + list(primegen(20))) == 32921810
    assert primephi(123456789, 4, [0] + list(primegen(20))) == 28218694
    assert primephi(123456789, 5, [0] + list(primegen(20))) == 25653358

def test_riemannzeta():
    from math import isclose
    assert isclose(riemannzeta(  2), 1.64493406684822643647241516664602518921894990120679843773555822937000747040, rel_tol=1e-15)
    assert isclose(riemannzeta(  3), 1.20205690315959428539973816151144999076498629234049888179227155534183820578, rel_tol=1e-15)
    assert isclose(riemannzeta(  4), 1.08232323371113819151600369654116790277475095191872690768297621544412061618, rel_tol=1e-15)
    assert isclose(riemannzeta(  5), 1.03692775514336992633136548645703416805708091950191281197419267790380358978, rel_tol=1e-15)
    assert isclose(riemannzeta(  6), 1.01734306198444913971451792979092052790181749003285356184240866400433218290, rel_tol=1e-15)
    assert isclose(riemannzeta(  7), 1.00834927738192282683979754984979675959986356056523870641728313657160147831, rel_tol=1e-15)
    assert isclose(riemannzeta(  8), 1.00407735619794433937868523850865246525896079064985002032911020265258295257, rel_tol=1e-15)
    assert isclose(riemannzeta(100), 1.00000000000000000000000000000078886090522101180735205378276604136878962534, rel_tol=1e-15)

def test_zetam1():
    from math import isclose
    assert isclose(zetam1(  2), 0.64493406684822643647241516664602518921894990120679843773555822937000747040, rel_tol=1e-15)
    assert isclose(zetam1(  3), 0.20205690315959428539973816151144999076498629234049888179227155534183820578, rel_tol=1e-15)
    assert isclose(zetam1(  4), 0.08232323371113819151600369654116790277475095191872690768297621544412061618, rel_tol=1e-15)
    assert isclose(zetam1(  5), 0.03692775514336992633136548645703416805708091950191281197419267790380358978, rel_tol=1e-15)
    assert isclose(zetam1(  6), 0.01734306198444913971451792979092052790181749003285356184240866400433218290, rel_tol=1e-15)
    assert isclose(zetam1(  7), 0.00834927738192282683979754984979675959986356056523870641728313657160147831, rel_tol=1e-15)
    assert isclose(zetam1(  8), 0.00407735619794433937868523850865246525896079064985002032911020265258295257, rel_tol=1e-15)
    assert isclose(zetam1(100), 0.00000000000000000000000000000078886090522101180735205378276604136878962534, rel_tol=1e-15)

def test_isprime_nm1():
    n = prod(range(1, 78))
    nfac = factorint(n)
    assert isprime_nm1(n + 1)           == True
    assert isprime_nm1(n + 1, fac=nfac) == True
    n = prod(range(1, 79))
    nfac = factorint(n)
    assert isprime_nm1(n + 1          ) == False
    assert isprime_nm1(n + 1, fac=nfac) == False

def test_isprime_np1():
    n = prod(range(1, 94))
    nfac = factorint(n)
    assert isprime_np1(n - 1,         ) == False
    assert isprime_np1(n - 1, fac=nfac) == False
    n = prod(range(1, 95))
    nfac = factorint(n)
    assert isprime_np1(n - 1,         ) == True
    assert isprime_np1(n - 1, fac=nfac) == True

def test_altseriesaccel(): assert False     # TODO
def test_ecadd(): assert False              # TODO
def test_ecdub(): assert False              # TODO
def test_ecmparams(): assert False          # TODO
def test_ecmul(): assert False              # TODO
def test_lucasmod(): assert False           # TODO
def test_mlucas(): assert False             # TODO
def test_multifactor(): assert False        # TODO
def test_nthprimeapprox(): assert False     # TODO
def test_partitions(): assert False         # TODO
def test_primepi_S1(): assert False         # TODO
def test_riemannR(): assert False           # TODO
def test_secm(): assert False               # TODO

# TODO: For stuff like factorsieve and primegen, implement tests to check that the upper limits are handled correctly.
