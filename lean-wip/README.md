# Partial Lean 4 formalization (work in progress — NOT a complete proof)

`ThreeShiftRadical.lean` formalizes the **argument structure** of the proof in
`../PROOF.md` in Lean 4, using only Lean core plus `Std` (no Mathlib, no added
axioms). It defines its own notion of primality (`PrimeLike`) because
`Nat.Prime` lives in Mathlib.

**Status: incomplete.** The file contains three `sorry`s and does not yet
compile. It is published because the reduction it formalizes is the substance of
the result, and because an incomplete formalization should be visible rather
than implied. **It must not be cited as a verified proof.**

What is formalized:

- `PrimeLike` and `Dvd`, with `exists_primeLike_and_dvd`;
- Euclid's lemma for prime-like numbers (`PrimeLike.dvd_mul`);
- the coprime lemma `eq_one_of_coprime_of_dvd_eq` (statement and proof skeleton);
- the parity reduction `coprime_odd_odd` (a common divisor of two odd numbers is
  `1`) and `dvd_two_mul_cancel` (cancelling a common factor `2` in radical
  equality);
- `no_dvd_eq_two_step` and the two top-level statements
  `three_shift_radical_obstruction` and `erdos_850_three_shift`.

What is missing (all of it core arithmetic, none of it mathematical):

1. `dvd_of_two_mul_eq`: from `2 * b = 2 * e` conclude `2 ∣ b`.
2. The subtraction identity `2 * b + 1 - 2 * (b - a) = 2 * a + 1` under
   `2 * (b - a) ≤ 2 * b + 1`, used in `coprime_odd_odd`.
3. The bounds `2 ≤ v` / `2 ≤ u` inside the contradiction branches of
   `eq_one_of_coprime_of_dvd_eq`, where `omega` cannot see through the `Dvd`
   unfolding.

Every gap is a statement about `Nat` subtraction, division by `2`, or order that
is proved by hand in `PROOF.md`. Completing them needs a Mathlib-based
development (where `Nat.Prime`, `Nat.primeFactors`, `omega` and `linarith` are
available) rather than the bare core library used here.

To attempt completion (requires a Lean toolchain with Mathlib):

```sh
lake exe cache get
lake build
```
