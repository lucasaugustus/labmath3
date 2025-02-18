Before publishing to PyPI:

* Write more comprehensive tests for pytest.
  * For `cubicintroots` and `quadintroots`, use fully-randomized coefficients and test against a brute-force search over an interval provided by one of the theorems at <https://en.wikipedia.org/wiki/Geometrical_properties_of_polynomial_roots>.
* Write more examples in the docstrings.
  * `randomfactored`
  * `polyrootsmod`
  * `_PQa`
  * `ispractical`
  * `quadintroots`
  * `cubicintrootsgiven`
  * `cubicintroots`
  * `dirichletroot`
  * `determinant`
  * `discriminant`
* Ensure that the examples in the docstrings work.
* Figure out where `riemannzeta` and `zetam1` are accurate.
* For bounded generators like `primegen` and `factorsieve`, implement tests to ensure that the bounds are handled correctly.

General TODOs:

* Implement the segmented version of the `sqfrcount` algorithm.  See section 4.4 of <https://arxiv.org/pdf/1107.4890> and `on_deck/sqfrcount.py`.
* Make `powerset` handle sets.
* Make `_primepi_S1` non-recursive.
* Extend `riemannzeta` to handle more of the complex plane.
* Use sieving in `nextprime`, `prevprime`, and the correction stage of `nthprime`.
* Clean up `xgcd`.
* Implement the precomputed CRT from CranPom Alg 2.1.7 and use it in `sqrtmod`, `polyrootsmod`, and any other places that it applies.
* Figure out when Newton iteration is useful in `introot`, and use it in those cases.
* Write tricks for special cases in `ispower`.
* In `ilog`, investigate optimization starting from `x.bin_length() * 2 // b`.
* For `semiprimegen`, `pspgen`, `almostprimegen`, and `nearlyprimegen`, implement upper bounds as in `primegen`.  Also, write versions of these that are alterations of `factorsieve`, and compare performance.
* Try iteratizing `fibo` and `fibomod`.
* For `linrec`, see <https://projecteuler.net/thread=258#29618>.
* In `lucasmod`, handle the case `gcd(D,m) != 1`.
* Further analyze the bad-parameters cases of `lprp`, `slprp`, and `xslprp`.
* In `polydivmodmodp`, convert the recursion to iteration.
* In `isprime`, optimize the trial-division basis, possibly by varying it with `n`.
* In `pollard_pm1`, what are the best bounds and way to increment them?
* Implement the two-phase version of `williams_pp1`.
* Find a better parameter sequence for `ecmparams`.
* Try using a process pool for the multi-threaded path in `ecm`.
* Figure out why that one line in `siqs` is problematic for small `n`, and fix it.
* In `primefac`, consider some iterations of Fermat's method after trial division, then some amount of P-1 by itself after rho, then some amount of ECM by itself after that.
* Figure out the time- and space-complexities of `totientsum`, and look for more efficient methods.
* In `polyroots_prime`, when should brute force be used, and when should we use Cantor-Zassenhaus?
* In `polyrootsmod`, when should we use brute force?
* In `sqrtmod`, when should we use brute force?
* In `PQa`, figure out what the sequences are, and document that.
* In `pell`, in the case `D < 0 & N != 0`, implement Cornacchia's algorithm.
* Make `multord` more efficient.
* Clean up `pell`.
* Clean up `pythags_by_perimeter`.
* In `partconj`, let *S* and *N* be the sum and number of parts in the partition.  The current algorithm is *O*(*S*&middot;*N*) in time and space.  Do better.
* Figure out how to use `heapq` in `perfectpowers`.
* An old comment on `sqfrgenb` claims that it can be made rather more efficient.  Figure out what I was thinking and do it.
* Try memoizing `dirichletinverse` and `dirichletroot`.
* What is the complexity of the determinant algorithm?
* Currently, `discriminant` uses the determinant formula.  Is there a way to take advantage of the matrix's special form?
* A line in `egypt_short` is marked as being rather inefficient for large numbers of terms.  Figure out why, and improve it.
* In `sqfrcount`, experiment with dfferent values for the multiplier.
* Write an efficient dlog function and use it in `dirichletcharacter`.
* Investigate alternate discriminant algorithms, such as <https://math.stackexchange.com/questions/696335> and <https://en.m.wikipedia.org/wiki/B%C3%A9zout_matrix>.
* Investigate parallelizing `egypt_short`.
* What are the time- and space-complexities of `primesum`?
* Implement the segmented Deleglise-Rivat algorithm for the Mertens function.  This is in progress at `on_deck/mertens.py`.
* Consider importing the Helfgott-Thompson code from <https://github.com/lucasaugustus/mertens>.
