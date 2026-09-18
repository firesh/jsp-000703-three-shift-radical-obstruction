# The three-shift radical problem has no solution: an elementary obstruction

**Result.** There do not exist distinct positive integers $x$ and $y$ such that $x$ and $y$
have the same set of prime divisors, $x+1$ and $y+1$ have the same set of prime divisors,
and $x+2$ and $y+2$ have the same set of prime divisors.

More precisely, if $x,y \ge 1$ satisfy all three conditions then $x = y = 2$. Hence for
**distinct** positive integers the answer to the question is **no**, and this is settled by
an elementary argument. The middle condition plays no role: the first and third conditions
are already contradictory.

This repository contains the self-contained proof, a computational verification, and the
reproduction instructions.

---

## 1. The problem

The statement addressed here is the one recorded as **Erdős problem #850** in the public
Erdős Problems database ([erdosproblems.com/850](https://www.erdosproblems.com/850),
citing Erdős, *Problems and results on the theory of interpolation I*, 1963, Problem 60),
and as **JSP-000703** in the Justin Sun Prize problem bank
([problems/catalog-0701-0800.md](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000703)):

> Can there exist two distinct integers $x$ and $y$ such that $x,y$ have the same prime
> factors, $x+1,y+1$ have the same prime factors, and $x+2,y+2$ also have the same prime
> factors?

Throughout, "same prime factors" is read in the standard sense used by the problem sources
and by the associated formal statement: the two integers have *the same set of prime
divisors*, i.e. equal radicals $\operatorname{rad}(n) = \prod_{p \mid n} p$.

The two-shift version (only the conditions on $x,y$ and on $x+1,y+1$) has infinitely many
solutions, the Benelux pairs

$$x = 2(2^{r}-1), \qquad y = x(x+2) = 2^{r+1}(2^{r}-1) \quad (r \ge 1),$$

together with the exceptional pair $x = 75$, $y = 1215$ found by A. Makowski. The three-shift
version asks whether a pair survives the additional requirement that $x+2$ and $y+2$ share
their prime divisors as well.

## 2. The obstruction

Write $\operatorname{rad}(n)$ for the product of the distinct prime divisors of $n \ge 1$, so
that two positive integers have the same set of prime divisors exactly when their radicals
are equal.

### Lemma 1 (coprime numbers with equal radicals are both $1$)

Let $u, v \ge 1$ be coprime. If $\operatorname{rad}(u) = \operatorname{rad}(v)$, then
$u = v = 1$.

*Proof.* If $u > 1$, pick a prime $p \mid u$. Then $p \mid \operatorname{rad}(u) =
\operatorname{rad}(v)$, so $p \mid v$, contradicting $\gcd(u,v) = 1$. Hence $u = 1$, and
symmetrically $v = 1$. $\square$

### Lemma 2 (no positive integer agrees in radical with its second successor)

There is no $x \ge 1$ with $\operatorname{rad}(x) = \operatorname{rad}(x+2)$ except $x = 2$,
where $x$ and $x+2$ are the two distinct integers $2$ and $4$; in particular there is no
solution with $x$ and $x+2$ equal.

*Proof.* Let $x \ge 1$ and suppose $\operatorname{rad}(x) = \operatorname{rad}(x+2)$.

*Case $x$ odd.* Then $x$ and $x+2$ are odd, and $\gcd(x, x+2) = \gcd(x,2) = 1$. Lemma 1
gives $x = x + 2 = 1$, which is impossible.

*Case $x$ even.* Write $x = 2a$ with $a \ge 1$; then $x+2 = 2(a+1)$ and $\gcd(a,a+1)=1$.
Since
$$\operatorname{rad}(x) = \operatorname{rad}(2a) = \operatorname{rad}(2)\operatorname{rad}(a)
= 2\operatorname{rad}(a),$$
and likewise $\operatorname{rad}(x+2) = 2\operatorname{rad}(a+1)$, equality of the two
radicals is equivalent to $\operatorname{rad}(a) = \operatorname{rad}(a+1)$. As
$\gcd(a, a+1) = 1$, Lemma 1 forces $a = a + 1 = 1$, which is impossible; so no even $x$
satisfies the equality. (The displayed reduction is the only place where the common factor
$2$ is used: $\gcd(a,a+1)=1$ is what makes Lemma 1 applicable.) $\square$

**Remark.** Equivalently: if $\operatorname{rad}(x) = \operatorname{rad}(x+2)$ then the two
numbers have the same *set* of prime divisors while their odd parts are coprime, so both odd
parts must be $1$, i.e. both numbers must be powers of $2$ — and no two powers of $2$ differ
by $2$.

### Theorem (negative answer in the three-shift problem)

There are no distinct positive integers $x, y$ such that
$\operatorname{rad}(x) = \operatorname{rad}(y)$,
$\operatorname{rad}(x+1) = \operatorname{rad}(y+1)$ and
$\operatorname{rad}(x+2) = \operatorname{rad}(y+2)$.

*Proof.* Assume such $x, y$ exist. From the first and third conditions,
$$\operatorname{rad}(x) = \operatorname{rad}(y) = \operatorname{rad}(y+2) = \operatorname{rad}(x+2),$$
so $\operatorname{rad}(x) = \operatorname{rad}(x+2)$. By Lemma 2 this equality cannot hold
for any positive $x$; hence $x, y$ cannot exist. $\square$

Because the additional requirement is contradicted by the first requirement alone, the
problem is *not* merely hard with current methods: **it has no solution, and no search over
$x$ or $y$ can succeed.** In particular the conditional result of Shorey and Tijdeman
(assuming a strong form of the abc conjecture the answer is negative) is superseded for this
statement by an unconditional elementary proof.

## 3. The sharpest true statement, and what remains open

The obstruction is caused by the *third* shift, and it is worth recording why the known
two-shift solutions cannot be repaired:

* the Benelux family $x = 2(2^{r}-1)$, $y = x(x+2)$ satisfies the first two conditions, and
  $x+2 = 2^{r+1}$ while $y + 2 = (x+1)^2 + 1$;
* the exceptional pair $(75, 1215)$ satisfies the first two conditions, while
  $77 = 7 \cdot 11$ and $1217$ is prime, so the prime-divisor sets already differ.

So in every known two-shift solution the third shift fails, and the theorem above shows this
is forced. What remains genuinely open — and is unaffected by the present result — is
Erdős's companion question for the *two-shift* problem: whether
$x = 2(2^r - 1)$, $y = x(x+2)$ and $(75,1215)$ are the only pairs with
$\operatorname{rad}(x) = \operatorname{rad}(y)$ and
$\operatorname{rad}(x+1) = \operatorname{rad}(y+1)$.

## 4. Computational verification

`verify.py` checks the obstruction directly and independently of the proof, by sieving the
radicals of all integers up to a bound and reporting every $x$ with
$\operatorname{rad}(x) = \operatorname{rad}(x+2)$. It also re-checks that the two known
two-shift families satisfy the first two shifts and fail the third.

```
$ python3 verify.py 20000000
verified range: 1 <= x <= 20000000
x with rad(x) == rad(x+2): [2]

known two-shift solutions (x, y, shift0, shift1, shift2):
   (2, 8, True, True, False)
   ...
   (75, 1215, True, True, False)

all shift-2 flags are False: True
all shift-0/1 flags are True: True
```

The single hit $x = 2$ is the degenerate one ($2$ and $4$ share the prime divisor $2$), and
the theorem above shows there are no others at any bound. The search is therefore a
consistency check, not evidence: the mathematical statement is proved, not searched.

## 5. Reproduction

Requirements: Python 3.8 or later, no third-party packages.

```sh
python3 verify.py 20000000          # full sieve, exact radicals
python3 checks/exhaustive_pairs.py  # exhaustive pair search for small x, y (sanity check)
```

## 6. References

1. P. Erdős, *Problems and results on the theory of interpolation I*, Acta Math. Acad. Sci.
   Hungar. **14** (1963), Problem 60.
2. T. F. Bloom (ed.), *Erdős Problem #850*, <https://www.erdosproblems.com/850>.
3. A. Makowski, letter/observation recorded in the problem database above (exceptional pair
   $75$, $1215$).
4. T. N. Shorey and R. Tijdeman, conditional negative solution under a strong form of the
   abc conjecture, as recorded in reference 2.
5. BxMO 2011, *Third Benelux Mathematical Olympiad*, Problem 1 (the two-shift version).
6. OEIS Foundation, sequence [A343101](https://oeis.org/A343101) (two-shift pairs).
7. C. Hercher, *On one of Erdős' Problems — An Efficient Search for Benelux Pairs*,
   [arXiv:2506.01099](https://arxiv.org/abs/2506.01099) (2025) (search up to $1.4\cdot10^{12}$
   for two-shift pairs).
8. The Justin Sun Prize, problem **JSP-000703**,
   <https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000703>.

## 7. License

Text and code in this repository are released under CC BY 4.0 (text) and the MIT License
(code); see `LICENSE`.
