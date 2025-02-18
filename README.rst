labmath3
========

This is a module for basic math in the general vicinity of computational number theory. It includes functions associated with primality testing, integer factoring, prime counting, linear recurrences, modular square roots, generalized Pell equations, the classic arithmetical functions, continued fractions, partitions, Størmer's theorem, smooth numbers, and Dirichlet convolution. Integer arithmetic is used wherever feasible.

This library is the successor to ``labmath`` (https://github.com/lucasaugustus/labmath/ and https://pypi.org/project/labmath/).  I broke backwards compatibility, so I started a new repository with a new name for this version.

This library is available via GitHub and PyPI (https://github.com/lucasaugustus/labmath3/ and https://pypi.org/project/labmath3/).

Functions
=========

We make a few imports:

.. code:: python

    from multiprocessing import Process, Queue as mpQueue
    from itertools import chain, count, groupby, islice, tee, cycle, takewhile, compress, product, zip_longest
    from fractions import Fraction
    from random import randrange, random
    from math import pi, log, log2, ceil, sqrt, factorial, comb, prod, gcd, lcm, isqrt; inf = float('inf')
    from heapq import merge
    
    try: from gmpy2 import mpz; mpzv, inttypes = 2, (int, type(mpz(1)))
    except ImportError: mpz, mpzv, inttypes = int, 0, (int,)
    
    __version__ = labmathversion = "3.0.0"

The *new* functions provided by this module are as follows.  Further details, including examples and input details, are available in docstrings and accessible via the built-in ``help`` function.

.. code:: python

    primegen(limit=inf)

Generates primes less than the given limit (which may be infinite) almost-lazily via a segmented sieve of Eratosthenes.  Memory usage depends on the sequence of prime gaps; on Cramér's conjecture, it is *O*\ (√(\ *p*\ ) · log(*p*)\ :sup:`2`).

.. code:: python

    rpn(instr)

Evaluates a string in reverse Polish notation.  The acceptable binary operators are ``+ - * / // % **`` and correspond directly to those same operators in Python3 source code.  The acceptable unary operators are ``! #``.  They are the factorial and primorial, respectively.  There are four aliases: ``x`` for ``*`` , ``xx`` for ``**`` , ``f`` for ``!``, and ``p!`` for ``#``.

.. code:: python

    listprod(l)

Computes the product of the elements of a list.  The product of the empty list is 1.  This function is superior to the built-in ``math.prod`` in situations where the product is very large.  The reason is that algorithm used by ``math.prod(l)`` amounts to ``reduce(lambda x,y:x*y, l)``, which is quadratically slow when the elements of ``l`` are similarly-sized.  The algorithm implemented here splits the list into halves, recursively applies itself to each half, and then returns the product of the results.  This is asymptotically faster for cases where the products get large; however, it takes quite a long list to make this faster than ``math.prod``.

.. code:: python

    polyval(f, x, m=None)

Evaluates a polynomial at a particular point, optionally modulo something.

.. code:: python

    powerset(l)

Generates the powerset of a list, tuple, or string.  The yielded objects are always lists.

.. code:: python

    primephi(x, a, primes)

Legendre's partial sieve function: the number of positive integers ≤ ``x`` with no prime factor ≤ the ``a``\ :sup:`th` prime.

.. code:: python

    primepi(x, alpha=2.5)

Computes the number of primes ≤ ``x`` via the Lagarias-Miller-Odlyzko algorithm.  This function's time- and space-complexities are within logarithmic factors of *O*\ (``x``\ :sup:`2/3`) and *O*\ (``x``\ :sup:`1/3`), respectively.

.. code:: python

    primesum(n)

Computes sum of all primes ≤ ``n``.  The algorithm's time-complexity is sublinear in ``n``.

.. code:: python

    altseriesaccel(a, n)

Convergence acceleration for alternating series.  This is algorithm 1 from *Convergence Acceleration of Alternating Series* by Cohen, Villegas, and Zagier `(pdf)`__, with a minor tweak so that the *d*-value is not computed via floating point.

__ https://people.mpim-bonn.mpg.de/zagier/files/exp-math-9/fulltext.pdf

.. code:: python

    riemannzeta(n, k=24)

Computes the Riemann zeta function by applying ``altseriesaccel`` to the `Dirichlet eta function`__.  Should be rather accurate throughout the complex plane except near ``n`` such that 1 = 2\ :sup:`n–1`.

__ https://en.wikipedia.org/wiki/Dirichlet_eta_function

.. code:: python

    zetam1(n, k=24)

Computes ``riemannzeta(n, k) - 1`` by applying ``altseriesaccel`` to the Dirichlet eta function.  Designed to be accurate even when ``riemannzeta(n)`` is machine-indistinguishable from 1.0 --- in particular, when ``n`` is a large real number.

.. code:: python

    riemannR(x, n=None, zc={})

Uses ``n`` terms of the `Gram series`__ to compute `Riemann's R function`__, which is a rather good approximation to ``primepi``.  The argument ``zc`` is a cache of zeta values.

__ http://mathworld.wolfram.com/GramSeries.html
__ http://mathworld.wolfram.com/RiemannPrimeCountingFunction.html

.. code:: python

    nthprimeapprox(n)

Produces an integer that should be rather close to the ``n``\ :sup:`th` prime by using binary splitting on Riemann's R function.

.. code:: python

    nthprime(n)

Returns the ``n``\ :sup:`th` prime, (counting 2 as #1).  This is done with some efficiency by using ``nthprimeapprox`` as an initial estimate, computing ``primepi`` of that, and then sieving to remove the error.

.. code:: python

    xgcd(a, b)

Extended Euclidean altorithm: returns a tuple (*g*, *x*, *y*) such that *g* = gcd(``a``, ``b``) and *g* = ``a``·*x* + ``b``·*y*.  Note that many possible tuples (*g*, *x*, *y*) exist for a given pair (``a``, ``b``); we make no guarantees about which tuple will be returned.

.. code:: python

    crt(rems, mods)

The Chinese remainder theorem: returns the unique integer *c* in ``range(iterprod(mods))`` such that *c* ≡ *x* (mod *y*) for (*x*, *y*) in ``zip(rems, mods)``.  All elements of ``mods`` must be pairwise coprime.

.. code:: python

    introot(n, r=2)

For non-negative ``n``, returns the greatest integer ≤ the ``r``\ :sup:`th` root of ``n``.  For negative ``n``, returns the least integer ≥ the ``r``\ :sup:`th` root of ``n``, or ``None`` if ``r`` is even.

.. code:: python

    ispower(n, r=0)

If ``r`` = 0: If ``n`` is a perfect power, then return a tuple containing the largest integer that, when squares/cubed/etc, yields ``n`` as the first component and the relevant power as the second component.  If ``n`` is not a perfect power, then return ``None``.

If ``r`` > 0: We check whether ``n`` is a perfect ``r``\ :sup:`th` power; we return its ``r``\ :sup:`th` root if it is and ``None`` if it is not.

.. code:: python

    ilog(x, b)

The floor of the base-``b`` logarithm of ``x``: the greatest integer *k* such that ``b``\ :sup:`k` ≤ ``x``.

.. code:: python

    semiprimegen()

Generates the semiprimes.  This is done by filtering the primes out of the output of ``pspgen``.

.. code:: python

    pspgen()

Generates the primes and semiprimes.  This is done using a segmented sieve based on the sieve of Eratosthenes and the fact that these are precisely the numbers not divisible by any smaller semiprimes.

.. code:: python

    almostprimegen(k)

Generates the ``k``-almost-primes, which are the numbers that have precisely ``k`` prime factors, counted with multiplicity.  This is done by filtering ``nearlyprimegen(k-1)`` out of the output of ``nearlyprimegen(k)``.

.. code:: python

    nearlyprimegen(k)

Generates the numbers (other than 1) that have ``k`` or fewer prime factors, counted with multipicity.  This is done via a segmented sieve based on the sieve of Eratosthenes and the fact that these are precisely the numbers not divisible by any smaller ``k``-almost-primes.

.. code:: python

    fibogen()

Generates the Fibonacci numbers, starting with 0 and 1.

.. code:: python

    fibo(n, f={0:0, 1:1, 2:1})

Efficiently extracts the ``n``\ :sup:`th` Fibonacci number, indexed so that ``fibo(0)`` = 0 and ``fibo(1)`` = ``fibo(2)`` = 1.  The argument ``f`` is used for memoization.  We compute O(log(``n``)) earlier Fibonaccis along the way.  This is, in the big-O sense, just about as fast as possible.

.. code:: python

    fibomod(n, m, f={0:0, 1:1, 2:1})

Efficiently extracts the nth Fibonacci number modulo ``m``, indexed so that ``fibo(0)`` = 0 and ``fibo(1)`` == ``fibo(2)`` = 1.  The argument ``f`` is used for memoization.  We compute O(log(``n``)) earlier Fibonaccis along the way.  This is the asymptotically fastest algorithm.

.. code:: python

    lucaschain(n, x0, x1, op1, op2)

Algorithm 3.6.7 from *Prime Numbers: A Computational Perspective* by Crandall & Pomerance (2\ :sup:`nd` edition): Evaluation of a binary Lucas chain.  To quote their description:

    For a sequence *x*\ :sub:`0`, *x*\ :sub:`1`, ... with a rule for computing *x*\ :sub:`2j` from *x*\ :sub:`j` and a rule for computing *x*\ :sub:`2j+1` from *x*\ :sub:`j` and *x*\ :sub:`j+1`, this algorithm computes (*x*\ :sub:`n`, *x*\ :sub:`n+1`) for a given positive integer *n*.  We have *n* in binary as (*n*\ :sub:`0`, *n*\ :sub:`1`, ..., *n*\ :sub:`b–1`) with *n*\ :sub:`0` being the low-order bit.  We write the rules as follows: *x*\ :sub:`2j` = op1(*x*\ :sub:`j`) and *x*\ :sub:`2j+1` = op2(*x*\ :sub:`j`, *x*\ :sub:`j+1`).

.. code:: python

    lucasgen(P, Q):

Generates the Lucas U- and V-sequences with parameters (``P``, ``Q``).

.. code:: python

    lucas(k, P, Q)

Efficiently computes the ``k``\ :sup:`th` terms in the Lucas U- and V-sequences U(``P``, ``Q``) and V(``P``, ``Q``).  More explicitly, if

    U\ :sub:`0`, U\ :sub:`1`, V\ :sub:`0`, V\ :sub:`1` = 0, 1, 2, ``P``

and we have the recursions

    U\ :sub:`n` = ``P`` · U\ :sub:`n–1` – ``Q`` · U\ :sub:`n–2`

    V\ :sub:`n` = ``P`` · V\ :sub:`n–1` – ``Q`` · V\ :sub:`n–2`

then we compute U\ :sub:`k` and V\ :sub:`k` in O(ln(``k``)) arithmetic operations.  If ``P``\ :sup:`2` ≠ 4·``Q``, then these sequences grow exponentially, so the number of bit operations is anywhere from O(``k`` · ln(``k``)\ :sup:`2`) to O(``k``\ :sup:`2`) depending on how multiplication is handled.  We recommend using MPZs when ``k`` > 100 or so.  We divide by ``P``\ :sup:`2` – 4·``Q`` at the end, so we handle separately the case where this is zero.

.. code:: python

    binlinrecgen(P, Q, a, b)

The general binary linear recursion.  Exactly like ``lucasgen``, except we only compute one sequence, and we supply the seeds.

.. code:: python

    binlinrec(k, P, Q, a, b)

The general binary linear recursion.  Exactly like ``lucas``, except we compute only one sequence, and we supply the seeds.

.. code:: python

    linrecgen(a, b, m=None)

The general homogenous linear recursion: we generate in order the sequence defined by

    *x*\ :sub:`n+1` = ``a``\ :sub:`k` · *x*\ :sub:`n` + ``a``\ :sub:`k–1` · *x*\ :sub:`n–1` + ... + ``a``\ :sub:`0` · *x*\ :sub:`n–k`,

where the initial values are [*x*\ :sub:`0`, ..., *x*\ :sub:`k`] = ``b``.  If ``m`` is supplied, then we compute the sequence modulo ``m``.  The terms of this sequence usually grow exponentially, so computing a distant term incrementally by plucking it out of this generator takes O(``n``\ :sup:`2`) bit operations.  Extractions of distant terms should therefore be done via ``linrec``, which takes anywhere from O(``n`` · ln(``n``)\ :sup:`2`) to O(``n``\ :sup:`2`) bit operations depending on how multiplication is handled.

.. code:: python

    linrec(n, a, b, m=None)

The general homogeneous linear recursion.  If ``m`` is supplied, then terms are computed modulo ``m``.  We use matrix methods to efficiently compute the ``n``\ :sup:`th` term of the recursion

    *x*\ :sub:`n+1` = ``a``\ :sub:`k` · *x*\ :sub:`n` + ``a``\ :sub:`k-1` · *x*\ :sub:`n–1` + ... + ``a``\ :sub:`0` · *x*\ :sub:`n–k`,

where the initial values are [*x*\ :sub:`0`, ..., *x*\ :sub:`k`] = ``b``.

.. code:: python

    legendre(a, p)

The Legendre symbol (``a`` | ``p``): 1 if ``a`` is a quadratic residue mod ``p``, –1 if it is not, and 0 if ``a`` ≡ 0 (mod ``p``).

.. code:: python

    jacobi(a, n)

The Jacobi symbol (``a`` | ``n``).

.. code:: python

    kronecker(a, n)

The Kronecker symbol (``a`` | ``n``).  Note that this is the generalization of the Jacobi symbol, *not* the Dirac-delta analogue.

.. code:: python

    sprp(n, b)

The strong probable primality test (also known as a single round of the Miller-Rabin test).

.. code:: python

    mrab(n, basis)

The Miller-Rabin probable primality test.

.. code:: python

    miller(n)

Miller's primality test.  If the extended Riemann hypothesis (the one about Dirichlet L-functions) is true, then this test is deterministic.

.. code:: python

    lprp(n, a, b)

The Lucas probable primality test as described in *Prime Numbers: A Computational Perspective* by Crandall & Pomerance (2\ :sup:`nd` edition).

.. code:: python

    lucasmod(k, P, Q, m)

Efficiently computes the ``k``\ :sup:`th` terms of Lucas U- and V-sequences modulo ``m`` with parameters (``P``, ``Q``).  Currently just a helper function for ``slprp`` and ``xslprp``.  Will be upgraded to full status when the case gcd(*D*, ``m``) ≠ 1 is handled properly.

.. code:: python

    slprp(n, a, b)

The strong lucas probable primality test.  Its false positives are a strict subset of those for ``lprp`` with the same parameters.

.. code:: python

    xslprp(n, a)

The extra strong Lucas probable primality test.  Its false positives are a strict subset of those for ``slprp`` (and therefore ``lprp``) with parameters (``a``, 1).

.. code:: python

    bpsw(n)

The Baille-Pomerance-Selfridge-Wagstaff probable primality test.  Infinitely many false positives are conjectured to exist, but none are known, and the test is known to be deterministic below 2\ :sup:`64`.

.. code:: python

    qfprp(n, a, b)

The quadratic Frobenius probable primality test as described in *Prime Numbers: A Computational Perspective* by Crandall & Pomerance (2\ :sup:`nd` edition).

.. code:: python

    polyaddmodp(a, b, p)

Adds two polynomials and reduces their coefficients mod ``p``.

.. code:: python

    polysubmodp(a, b, p)

Subtracts the polynomial ``b`` from ``a`` and reduces their coefficients mod ``p``.

.. code:: python

    polymulmodp(a, b, p)

Multiplies the polynomials ``a`` and ``b`` and reduces their coefficients mod ``p``.

.. code:: python

    polydivmodmodp(a, b, p)

Divides the polynomial ``a`` by the polynomial ``b`` and returns the quotient and remainder.  The result is not guaranteed to exist; in such cases we return ``(None, None)``.

.. code:: python

    gcmd(f, g, p)

Computes the greatest common monic divisor of the polynomials ``f`` and ``g``, modulo ``p``.  The result is not guaranteed to exist; in such cases, we return ``None``.  Coded after algorithm 2.2.1 from *Prime Numbers: A Computational Perspective* by Crandall & Pomerance (2\ :sup:`nd` edition).

.. code:: python

    polypowmodpmodpoly(a, e, p, f)

Computes the remainder when the polynomial ``a`` is raised to the ``e``\ :sup:`th` power and reduced modulo ``p`` and ``f``.  The answer is not guaranteed to exist; in such cases, we return ``None``.

.. code:: python

    frobenius_prp(n, poly, strong=False)

Grantham's general Frobenius probable primality test, in both the strong and weak versions, as described in `his paper introducing the test`__.

__ https://doi.org/10.1090/S0025-5718-00-01197-2

.. code:: python

    isprime(n, tb=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59))

The workhorse primality test.  It is a BPSW primality test variant: we use the strong Lucas PRP test and preface the computation with trial division for speed.  No composites are known to pass the test, though it is suspected that infinitely many will do so.  There are definitely no such errors below 2\ :sup:`64`.  This function is mainly a streamlined version of ``bpsw``.

.. code:: python

    isprimepower(n)

Determines whether ``n`` is of the form *p*\ :sup:`e` for some prime number *p* and positive integer *e*, and returns (*p*, *e*) if so.

.. code:: python

    nextprime(n, primetest=isprime)

Smallest prime strictly greater than ``n``.

.. code:: python

    prevprime(n, primetest=isprime)

Largest prime strictly less than ``n``, or ``None`` if no such prime exists.

.. code:: python

    randprime(digits, base=10, primetest=isprime)

Returns a random prime with the specified number of digits when rendered in the specified base.

.. code:: python

    randomfactored(n, method="kalai")

Efficiently generates an integer selected uniformly from the range [1, ``n``] or (``n``/2, ``n``] with its factorization.  Uses Adam Kalai's or Eric Bach's algorithm, respectively, which use *O*\ (log(``n``)\ :sup:`2`) and *O*\ (log(``n``)) primality tests.

.. code:: python

    sqrtmod_prime(a, p)

Finds *x* such that *x*\ :sup:`2` ≡ ``a`` (mod ``p``).  We assume that ``p`` is a prime and ``a`` is a quadratic residue modulo ``p``.  If any of these conditions is false, then the return value is meaningless.

.. code:: python

    cbrtmod_prime(a, p)

Returns in a sorted list all cube roots of ``a`` mod ``p``.  There are a bunch of easily-computed special formulae for various cases with ``p`` ≠ 1 (mod 9); we do those first, and then if ``p`` == 1 (mod 9) we use Algorithm 4.2 in `Taking Cube Roots in Zm`__ by Padro and Saez, which is essentially a variation on the Tonelli-Shanks algorithm for modular square roots.

__ https://doi.org/10.1016/S0893-9659(02)00031-9

.. code:: python

    pollardrho_brent(n)

Factors integers using Brent's variation of Pollard's rho algorithm.  If ``n`` is prime, then we immediately return ``n``; if not, then we keep chugging until a nontrivial factor is found.

.. code:: python

    pollard_pm1(n, B1=100, B2=1000)

Integer factoring function.  Uses Pollard's p–1 algorithm.  Note that this is only efficient if the number to be factored has a prime factor *p* such that *p*–1's largest prime factor is "small".

.. code:: python

    _mlucas(v, a, n)

Helper function for ``williams_pp1``.  Multiplies along a Lucas sequence modulo ``n``.

.. code:: python

    williams_pp1(n)

Integer factoring function.  Uses the single-stage variant of Williams' p+1 algorithm.  Note that this is only efficient when the number to be factored has a prime factor *p* such that *p*\ +1's largest prime factor is "small".

.. code:: python

    _ecadd(p1, p2, p0, n)

Helper function for ``ecm``.  Adds two points on a Montgomery curve modulo ``n``.

.. code:: python

    _ecdub(p, A, n)

Helper function for ``ecm``.  Doubles a point on a Montgomery curve modulo ``n``.

.. code:: python

    _ecmul(m, p, A, n)

Helper function for ``ecm``.  Multiplies a point on Montgomery curve by an integer modulo ``n``.

.. code:: python

    secm(n, B1, B2, seed)

Seeded elliptic curve factoring using the two-phase algorithm on Montgomery curves.  Helper function for ``ecm``.  Returns a possibly-trivial divisor of ``n`` given two bounds and a seed.

.. code:: python

    ecmparams(n)

Generator of parameters to use for ``secm``.

.. code:: python

    ecm(n, paramseq=ecmparams, nprocs=1)

Integer factoring via elliptic curves using the two-phase algorithm on Montgomery curves, and optionally using multiple processes.  This is a shell function that repeatedly calls ``secm`` using parameters provided by ``ecmparams``; the actual factoring work is done there.  Multiprocessing incurs relatively significant overhead, so when ``nprocs==1`` (default), we do not call the multiprocessing functions.

.. code:: python

    siqs(n)

Factors an integer via the self-initializing quadratic sieve.  Most of this function is copied verbatim from https://github.com/skollmann/PyFactorise.

.. code:: python

    multifactor(n, methods)

Integer factoring function.  Uses several methods in parallel.  Waits for one of them to return, kills the rest, and reports.

.. code:: python

    primefac(n, trial=1000, rho=42000, primetest=isprime, methods=(pollardrho_brent,), trialextra=[])

The workhorse integer factorizer.  Generates the prime factors of the input.  Factors that appear *x* times are yielded *x* times.

.. code:: python

    factorint(n, trial=1000, rho=42000, primetest=isprime, methods=(pollardrho_brent,), trialextra=[])

Compiles the output of ``primefac`` into a dictionary with primes as keys and multiplicities as values.

.. code:: python

    factorsieve(limit=inf)

Uses a sieve to compute the factorizations of all positive integers strictly less than the input.  This is a generator; internally, the algorithm is a segmented sieve of Eratosthenes, so memory usage is on the order of the square root of the most-recently-yielded term.

.. code:: python

    divisors(n)

Generates all natural numbers that evenly divide ``n``.  The output is not necessarily sorted.

.. code:: python

    divisors_factored(n)

Generates the divisors of ``n``, written as their prime factorizations in factorint format.

.. code:: python

    divcount(n)

Counts the number of divisors of ``n``.

.. code:: python

    divsigma(n, x=1)

Sum of divisors of a natural number, raised to the *x*\ :sup:`th` power.  The conventional notation for this in mathematical literature is *σ*\ :sub:`x`\ (``n``), hence the name of this function.

.. code:: python

    divcountsieve(limit=inf)

Uses a sieve to compute the divisor-counts of all positive integers strictly less than the input.  This is a generator; internally, the algorithm is a segmented sieve of Eratosthenes, so memory usage is on the order of the square root of the most-recently-yielded term.

.. code:: python

    divsigmasieve(limit=inf, x=1)

Uses a sieve to compute the ``x``\ :sup:`th`-power-sum-of-divisors of all positive integers strictly less than the input.  This is a generator; internally, the algorithm is a segmented sieve of Eratosthenes, so memory usage is on the order of the square root of the most-recently-yielded term.

.. code:: python

    totient(n, k=1)

Euler's/Jordan's totient function: the number of ``k``-tuples of positive integers all ≤ ``n`` that form a coprime (``k``\ +1)-tuple together with ``n``.  When ``k`` = 1, this is Euler's totient: the number of numbers less than a number that are relatively prime to that number.

.. code:: python

    totientsieve(limit-inf, k=1)

Uses a sieve to compute the totients of all positive integers strictly less than the input.  This is a generator; internally, the algorithm is a segmented sieve of Eratosthenes, so memory usage is on the order of the square root of the most-recently-yielded term.

.. code:: python

    totientsum(n)

Computes ``sum(totient(n) for n in range(1, n+1))`` efficiently.

.. code:: python

    mobius(n)

The Möbius function of ``n``: 1 if ``n`` is squarefree with an even number of prime factors, –1 if ``n`` is squarefree with an odd number of prime factors, and 0 if ``n`` has a repeated prime factor.

.. code:: python

    mobiussieve(limit=inf)

Uses a sieve to compute the Möbius function applied to all positive integers strictly less than the input.  This is a generator; internally, the algorithm is a segmented sieve of Eratosthenes, so memory usage is on the order of the square root of the most-recently-yielded term.

.. code:: python

    liouville(n)

The Liouville lambda function of ``n``: the strongly multiplicative function that is –1 on the primes.

.. code:: python

    polyroots_prime(g, p, sqfr=False)

Generates with some efficiency and without multiplicity the zeros of a polynomial modulo a prime.  Coded after algorithm 2.3.10 from *Prime Numbers: A Computational Perspective* by Crandall & Pomerance (2\ :sup:`nd` edition), which is essentially Cantor-Zassenhaus.

.. code:: python

    hensel(f, p, k, given=None)

Uses Hensel lifting to generate with some efficiency all zeros of a polynomial modulo a prime power.

.. code:: python

    sqrtmod(a, n)

Computes all square roots of ``a`` modulo ``n`` and returns them in a sorted list.

.. code:: python

    polyrootsmod(pol, n)

Computes the zeros of a polynomial modulo an integer.  We do this by factoring the modulus, solving modulo the prime power factors, and putting the results back together via the Chinese Remainder Theorem.

.. code:: python

    _PQa(P, Q, D)

Generates some sequences related to simple continued fractions of certain quadratic surds.  A helper function for ``pell``.  Let ``P``, ``Q``, and ``D`` be integers such that ``Q`` ≠ 0, ``D`` > 0 is a nonsquare, and ``P``\ :sup:`2` ≡ ``D`` (mod ``Q``). We yield a sequence of tuples (*B*\ :sub:`i`, *G*\ :sub:`i`, *P*\ :sub:`i`, *Q*\ :sub:`i`) where *i* is an index counting up from 0, *x* = (``P``\ +√\ ``D``)/``Q`` = [*a*\ :sub:`0`; *a*\ :sub:`1`, *a*\ :sub:`2`, ...], (*P*\ :sub:`i`\ +√\ ``D``))/*Q*\ :sub:`i` is the *i*\ :sup:`th` complete quotient of *x*, and *B*\ :sub:`i` is the denominator of the *i*\ :sup:`th` convergent to *x*.  For full details, see https://web.archive.org/web/20180831180333/http://www.jpr2718.org/pell.pdf.

.. code:: python

    pell(D, N)

This function solves the generalized Pell equation: we find all non-negative integers (*x*, *y*) such that *x*\ :sup:`2` – ``D`` · *y*\ :sup:`2` = ``N``.  We have several cases:

Case 1: ``N`` = 0.  We solve *x*\ :sup:`2` = ``D`` · *y*\ :sup:`2`.  (0,0) is always a solution.

    Case 1a: If ``D`` is a nonsquare, then there are no further solutions.

    Case 1b: If ``D`` is a square, then there are infinitely many solutions, parametrized by (*t*·√\ ``D``, *t*).

Case 2: ``N`` ≠ 0 = ``D``.  We solve *x*\ :sup:`2` = ``N``.

    Case 2a: If ``N`` is a nonsquare, then there are no solutions.

    Case 2b: If ``N`` is a square, then there are infinitely many solutions, parametrized by (√\ ``N``, *t*).

Case 3: ``N`` ≠ 0 > ``D``.  We solve *x*\ :sup:`2` + \|\ ``D``\| · *y*\ :sup:`2` = ``N``.  The number of solutions will be finite.

Case 4: ``N`` ≠ 0 < ``D``.  We find lattice points on a hyperbola.

    Case 4a: If ``D`` is a square, then the number of solutions will be at most finite.  This case is solved by factoring.

    Case 4b: If ``D`` is a nonsquare, then we run the PQa/LMM algorithms: we produce a set of primitive solutions; if this set is empty, there are no solutions; if this set has members, an ininite set of solutions can be produced by repeatedly composing them with the fundamental solution of *x*\ :sup:`2` – ``D`` · *y*\ :sup:`2` = 1.

References:

* https://web.archive.org/web/20180831180333/https://www.jpr2718.org/pell.pdf
* http://www.offtonic.com/blog/?p=12
* http://www.offtonic.com/blog/?p=18

Input: ``D``, ``N`` -- integers

Output:

    A 3-tuple.

    If the number of solutions is finite, then it is ``(None, z, None)``, where ``z`` is the sorted list of all solutions.

    If the number of solutions is infinite and the equation is degenerate, then it is ``(gen, None, None)``, where ``gen`` yields all solutions.

    If the number of solutions if infinite and the equation is nondegenerate, then it is ``(gen, z, f)``, where ``z`` is the set of primitive solutions, represented as a sorted list, and ``f`` is the fundamental solution—i.e., ``f`` is the primitive solution of *x*\ :sup:`2` – ``D`` · *y*\ :sup:`2` = 1.

    Note that we can check the infinitude of solutions by calling ``bool(pell(D,N)[0])``.

.. code:: python

    simplepell(D, bail=inf)

Generates the positive solutions of *x*\ :sup:`2` – ``D`` · *y*\ :sup:`2` = 1.  We use some optimizations specific to this case of the Pell equation that makes this more efficient than calling ``pell(D,1)[0]``.  Note that this function is not equivalent to calling ``pell(D,1)[0]``: ``pell`` is concerned with the general equation, which may or may not have trivial solutions, and as such yields all non-negative solutions, whereas this function is concerned only with the simple Pell equation, which always has an infinite family of positive solutions generated from a single primitive solution and always has the trivial solution (1,0).

We yield only those solutions with *x* ≤ ``bail``.

.. code:: python

    carmichael(n)

The Carmichael lambda function: the smallest positive integer *m* such that *a*\ :sup:`m` ≡ 1 (mod ``n``) for all *a* such that gcd(*a*, ``n``) = 1.  Also called the *reduced totient* or *least universal exponent*.

.. code:: python

    multord(b, n)

Computes the multiplicative order of ``b`` modulo ``n``; i.e., finds the smallest *k* such that ``b``\ :sup:`k` ≡ 1 (mod ``n``).

.. code:: python

    pythags(maxperim, primitive=False)

Uses Barning's tree to uniquely generate all Pythagorean triples up to and including the user-specified maximum perimeter.  Optionally, the non-primitive triples can be omitted.

.. code:: python

    pythags_by_perimeter(p)

Generates all Pythagorean triples of a given perimeter by examining the perimeter's factors.

.. code:: python

    sqrtcfrac(n)

Computes the simple continued fraction for √\ ``n``.  We return the answer as ``(isqrt(n), [a,b,c,...,d])``, where ``[a,b,c,...,d]`` is the minimal reptend.

.. code:: python

    convergents(a)

Generates the convergents of a simple continued fraction.

.. code:: python

    contfrac_rat(n, d)

Returns the simple continued fraction of the rational number ``n``/``d``.

.. code:: python

    quadratic_scf(P,Q,D)

Computes the simple continued fraction of the expression (``P`` + sqrt(``D``)) / ``Q``, for any integers ``P``, ``Q``, and ``D`` with ``D`` ≥ 0 ≠ ``Q``.  Note that ``D`` can be a square or a nonsquare.

.. code:: python

    partgen(n)

Generates partitions of integers in ascending order via an iterative algorithm.  It is the fastest known algorithm as of June 2014.

.. code:: python

    partconj(p)

Computes the conjugate of a partition.

.. code:: python

    farey(n)

Generates the Farey sequence of maximum denominator ``n``.  Includes 0/1 and 1/1.

.. code:: python

    fareyneighbors(n, p, q)

Returns the neighbors of ``p``/``q``  in the Farey sequence of maximum denominator ``n``.

.. code:: python

    ispractical(n)

Tests whether ``n`` is a practical number—that is, whether every integer from 1 through ``n`` (inclusive) can be written as a sum of divisors of ``n``.  These are also called panarithmic numbers.

.. code:: python

    hamming(ps, *ps2)

Generates all ``ps``-smooth numbers, where ``ps`` is a list of primes.

.. code:: python

    perfectpowers()

Generates the sequence of perfect powers without multiplicity.

.. code:: python

    sqfrgen(ps)

Generates the squarefree products of the elements of ``ps``.

.. code:: python

    sqfrgenb(ps, b, k=0, m=1)

Generates the squarefree products of elements of ``ps``.  Does not yield anything > ``b``.  For best performance, ``ps`` should be sorted in decreasing order.

.. code:: python

    stormer(ps, *ps2, abc=None, sep=1)

For both choices of ``sep == 1`` and ``sep == 2``, Størmer's theorem asserts that for any given set ``ps`` of prime numbers, there are only finitely many pairs of integers (*x*, *x* + ``sep`` ) that are both ``ps``-smooth; the theorem also gives an effective algorithm for finding them.  We implement Lehmer's improvement to this theorem.

The ``abc`` argument indicates that we are to assume an effective abc conjecture of the form *c* < ``abc[0]`` · rad(*a*·*b*·*c*)\ :sup:`abc[1]`.  This enables major speedups.  If ``abc`` is ``None``, then we make no such assumptions.

.. code:: python

    quadintroots(a, b, c)

Given integers ``a``, ``b``, and ``c``, we return in a tuple all distinct integers *x* such that ``a``·*x*\ :sup:`2` + ``b``·*x* + ``c`` = 0.  This is primarily a helper function for ``cubicintrootsgiven`` and ``cubicintroots``.

.. code:: python

    cubicintrootsgiven(a, b, c, d, r)

Given integers ``a``, ``b``, ``c``, ``d``, and ``r`` such that ``a``·``r``\ :sup:`3` + ``b``·``r``\ :sup:`2` + ``c``·``r`` + ``d`` = 0, we find the cubic's other two roots and return in a tuple all distinct integer roots (including ``r``).  This is primarily a helper function for ``cubicintroots``.

.. code:: python

    cubicintroots(a, b, c, d)

Given integers ``a``, ``b``, ``c``, ``d``, we return in a tuple all distinct integer roots of ``a``·*x*\ :sup:`3` + ``b``·*x*\ :sup:`2` + ``c``·*x* + ``d``.  This is primarily a helper function for ``isprime_nm1``.

.. code:: python

    isprime_nm1(n, fac=None)

The *n*–1 primality test: given an odd integer ``n`` > 214 and a fully-factored integer *F* such that *F* divides ``n``–1 and *F* > ``n``\ :sup:`0.3`, we quickly determine without error whether ``n`` is prime.  If the provided (partial) factorization of ``n``–1 is insufficient, then we compute the factorization ourselves.

.. code:: python

    isprime_np1(n, fac=None)

The *n*\ +1 primality test: given an odd integer ``n`` > 214 and a fully-factored integer *F* such that *F* divides ``n``\ +1 and *F* > ``n``\ :sup:`0.3`, we quickly determine without error whether ``n`` is prime.  If the provided (partial) factorization of ``n``\ +1 is insufficient, then we compute the factorization ourselves.

.. code:: python

    mulparts(n, r=None, nfac=None)

Generates all ordered ``r``-tuples of positive integers whose product is ``n``.  If ``r`` is ``None``, then we generate all such tuples (regardless of size) that do not contain 1.

.. code:: python

    dirconv(f, g, ffac=False, gfac=False)

This returns a function that is the Dirichlet convolution of ``f`` and ``g``.  When called with the keyword arguments at their default values, this is equivalent to the expression ``lambda n: sum(f(d) * g(n//d) for d in divisors(n))``.  If ``f`` or ``g`` needs to factor its argument, such as ``f == totient`` or ``g == mobius`` or something like that, then that lambda expression calls the factorizer a lot more than it needs to—we are already factoring ``n``, so instead of feeding those functions the integer forms of ``n``'s factors, we can instead pass ``ffac=True`` or ``gfac=True`` when ``dirconv`` is called and we will call ``divisors_factored(n)`` instead and feed those factored divisors into ``f`` or ``g`` as appropriate.  This optimization becomes more noticeable as the factoring becomes more difficult.

.. code:: python

    dirichletinverse(f)

Computes the Dirichlet inverse of the input function ``f``.  Mathematically, functions *f* such that *f*\ (1) = 0 have no Dirichlet inverses due to a division by zero.  This is reflected in this implementation by raising a ``ZeroDivisionError`` when attempting to evaluate ``dirichletinverse(f)(n)`` for any such ``f`` and any ``n``.  If ``f``\ (1) is neither 1 nor –1, then ``dirichletinverse(f)`` will return ``Fraction`` objects (as imported from the ``fractions`` module).

.. code:: python

    dirichletroot(f, r, val1)

Computes the ``r``\ :sup:`th` Dirichlet root of the input function ``f`` whose value at 1 is ``val1``.  More precisely, let ``f`` be a function on the positive integers, let ``r`` be a positive integer, and let ``val1``\ :sup:`r` = ``f``\ (1).  Then we return the unique function ``g`` such that ``f`` = ``g`` * ``g`` * ... * ``g``, where ``g`` appears ``r`` times and * represents Dirichlet convolution.  The values returned will be ``Fraction`` objects (as imported from the ``fractions`` module).

.. code:: python

    determinant(M)

Computes the determinant of a matrix via the Schur determinant identity.

.. code:: python

    discriminant(coefs)

Computes the discriminant of a polynomial.  The input list is ordered from lowest degree to highest—i.e., ``coefs[k]`` is the coefficient of the *x*\ :sup:`k` term.  For low-degree polynomials, explicit formulae are used; for degrees 5 and higher, we compute it by taking the determinant (using this package's ``determinant`` function) of the Sylvester matrix of the input and its derivative.  This in turn is calculated by the Schur determinant identity.  Note that this has the effect of setting the discriminant of a linear polynomial to 1 (which is conventional) and that of a constant to 0.

.. code:: python

    egypt_short(n, d, terms=0, minden=1)

Generates all shortest Egyptian fractions for ``n``/``d`` using at least the indicated number of terms and whose denominators are all ≥ ``minden``.  No algorithm is known for this problem that significantly improves upon brute force, so this can take impractically long times on even modest-seeming inputs.

.. code:: python

    egypt_greedy(n, d)

The greedy algorithm for Egyptian fraction expansion; also called the Fibonacci-Sylvester algorithm.

.. code:: python

    rational_in_base(b, p, q)

Given integers ``b`` ≥ 2, ``p`` ≥ 0, and ``q`` > 0, we determine the base-``b`` expansion of ``p``/``q``.

.. code:: python

    sqfrcount(N)

Counts the number of squarefree integers in the interval [1, ``N``] using Pawlewicz's *O*\ (N\ :sup:`0.4` · log(log(``N``))\ :sup:`0.6`) algorithm.  Currently, this is the non-segmented version, so that is both the time- and space-complexity.  A future edition will replace it with the segmented version, which has space complexity *O*\ (N\ :sup:`0.2` · log(log(``N``))\ :sup:`0.3`).

.. code:: python

    powerfulmap(x, h=(lambda a,b:1))

Generates, in no particular order, the sequence (*n*, *f*\ (*n*)), where *n* runs over the powerful numbers in the interval (1, ``x``], and where *f* is the multiplicative function satisfying *f*\ (*p*\ :sup:`e`) = ``h``\ (*p*\ , *e*\).

.. code:: python

    dirichletcharacter(q, n, x, qfac=None)

The Dirichlet character with modulus ``q`` and index ``n``, evaluated at ``x``, using the Conrey label.

.. code:: python

    partitions(n, parts=None, distinct=False)

Computes the number of partitions of 0, 1, 2, ..., ``n`` with the specified parts; optionally, the parts can be required to be distinct.

Dependencies
------------

This package imports items from ``multiprocessing``, ``itertools``, ``fractions``, ``random``, ``math``, and ``heapq``.  These are all in the Python standard library.

We attempt to import ``mpz`` from ``gmpy2``, but this is purely for efficiency: if this import fails, then we simply set ``mpz = int``.
