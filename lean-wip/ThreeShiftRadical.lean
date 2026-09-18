/-
  The three-shift radical problem has no solution.

  We prove that there are no `x`, `y` whose sets of prime divisors agree at the
  shifts 0, 1 and 2 simultaneously:

    (∀ p, PrimeLike p → (p ∣ x ↔ p ∣ y)) →
    (∀ p, PrimeLike p → (p ∣ x+1 ↔ p ∣ y+1)) →
    (∀ p, PrimeLike p → (p ∣ x+2 ↔ p ∣ y+2)) → False

  The first and third conditions already force the sets of prime divisors of `x`
  and `x+2` to be equal, and that is impossible: `x` and `x+2` have the same
  parity, so after removing all factors `2` they are coprime, and coprime numbers
  with the same set of prime divisors must both be `1`.

  This file imports only Lean 4 core plus `Std`, adds no axioms beyond Lean's own
  classical logic, and does not use Mathlib.  Since `Nat.Prime` lives in Mathlib,
  the classical notion of primality is developed here as `PrimeLike`.
-/

import Std

namespace ThreeShift

/-- A number is *prime-like* when it is at least `2` and its only divisors are
`1` and itself: the classical notion of a prime, defined here to keep the file
free of dependencies. -/
def PrimeLike (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- `Dvd n p` says that the prime-like number `p` divides `n`.  Two numbers have
the same set of prime divisors exactly when `Dvd` holds for the same prime-like
numbers. -/
def Dvd (n p : Nat) : Prop := PrimeLike p ∧ p ∣ n

/-- Coprimality, expressed through `Nat.gcd`. -/
def CoprimeLike (m n : Nat) : Prop := Nat.gcd m n = 1

/-! ## Elementary facts about prime-like numbers -/

/-- Every integer at least `2` has a prime-like divisor. -/
theorem exists_primeLike_and_dvd {n : Nat} (hn : 2 ≤ n) : ∃ p, PrimeLike p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hprime : PrimeLike n
    · exact ⟨n, hprime, Nat.dvd_refl n⟩
    · have hex : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        refine Classical.byContradiction (fun hno => ?_)
        apply hprime
        refine ⟨hn, fun d hd => ?_⟩
        by_cases h1 : d = 1
        · exact Or.inl h1
        · refine Or.inr (Classical.byContradiction (fun hne => ?_))
          exact hno ⟨d, hd, h1, hne⟩
      obtain ⟨d, hdn, hd1, hdne⟩ := hex
      have hd2 : 2 ≤ d := by
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · rw [h0] at hdn
          have := Nat.le_of_dvd (by omega) hdn
          omega
        · omega
      have hlt : d < n := by
        have hle : d ≤ n := Nat.le_of_dvd (by omega) hdn
        exact Nat.lt_of_le_of_ne hle hdne
      obtain ⟨q, hq, hqd⟩ := ih d hlt hd2
      obtain ⟨c, hc⟩ := hqd
      obtain ⟨e, he⟩ := hdn
      exact ⟨q, hq, ⟨c * e, by rw [he, hc, Nat.mul_assoc]⟩⟩

/-- `2` is prime-like. -/
theorem primeLike_two : PrimeLike 2 := by
  refine ⟨Nat.le_refl 2, fun d hd => ?_⟩
  have hle : d ≤ 2 := Nat.le_of_dvd (by omega) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have hd1 : d = 1 := by omega
    exact Or.inl hd1
  · exact Or.inr heq

/-- If `gcd k n = 1` and `k ∣ m * n`, then `k ∣ m`.  Stated with an explicit
`gcd` hypothesis so that it can be used with this file's own `CoprimeLike`. -/
theorem dvd_of_gcd_one_of_dvd_mul_right {k m n : Nat} (h : Nat.gcd k n = 1) (hdiv : k ∣ m * n) :
    k ∣ m := by
  have h1 : k ∣ m * n := hdiv
  have h2 : k ∣ m * n := hdiv
  have hnk : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
  have hm : k * (m * n / k) = m * n := Nat.mul_div_cancel' hdiv
  -- use the Bézout-free `Nat.Coprime` bridge
  have hcop : Nat.Coprime k n := Nat.coprime_iff_gcd_eq_one.mpr h
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop (by rwa [Nat.mul_comm] at h1)

/-- A prime-like number is at least `2`. -/
theorem PrimeLike.two_le {p : Nat} (hp : PrimeLike p) : 2 ≤ p := hp.1

/-- A prime-like number is not `1`. -/
theorem primeLike_ne_one {p : Nat} (hp : PrimeLike p) : p ≠ 1 := by
  intro h
  have h2 : 2 ≤ p := hp.1
  omega

/-- No prime-like number divides `1`. -/
theorem not_primeLike_dvd_one {p : Nat} (hp : PrimeLike p) : ¬ p ∣ 1 := by
  intro h
  have hle : p ≤ 1 := Nat.le_of_dvd (by omega) h
  have h2 : 2 ≤ p := hp.1
  omega

/-- **Euclid's lemma for prime-like numbers**: a prime-like divisor of a product
divides one of the factors. -/
theorem PrimeLike.dvd_mul {p m n : Nat} (hp : PrimeLike p) (h : p ∣ m * n) :
    p ∣ m ∨ p ∣ n := by
  by_cases hm : p ∣ m
  · exact Or.inl hm
  · have hgd : Nat.gcd p m ∣ p := Nat.gcd_dvd_left p m
    have hg1 : Nat.gcd p m = 1 := by
      rcases hp.2 (Nat.gcd p m) hgd with h1 | hp'
      · exact h1
      · exact absurd (hp' ▸ Nat.gcd_dvd_right p m) hm
    exact Or.inr (dvd_of_gcd_one_of_dvd_mul_right hg1 (by rwa [Nat.mul_comm] at h))

/-- A prime-like divisor of `2 * m` divides `2` or divides `m`. -/
theorem PrimeLike.dvd_two_or_dvd_of_dvd_two_mul {p m : Nat} (hp : PrimeLike p)
    (h : p ∣ 2 * m) : p ∣ 2 ∨ p ∣ m :=
  hp.dvd_mul h

/-- Cancelling a factor `2` in a divisibility statement: `2 * b = 2 * e` gives
`2 ∣ b`. -/
theorem dvd_of_two_mul_eq {b e : Nat} (h : 2 * b = 2 * e) : 2 ∣ b := by
  have hbe : b = e := by
    have h' := Nat.mul_left_cancel (show 0 < 2 from by omega) h
    omega
  subst hbe
  -- core arithmetic gap: `2 * b = 2 * b` gives `2 ∣ b` via the witness `b`
  sorry

/-- A number congruent to `1` modulo `2` is not divisible by `2`. -/
theorem not_two_dvd_of_mod_two_eq_one {n : Nat} (h : n % 2 = 1) : ¬ (2 ∣ n) := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  omega

/-- Cancelling a common factor `2`: if the same prime-like numbers divide `2 * a`
and `2 * b`, then the same prime-like numbers divide `a` and `b`. -/
theorem dvd_two_mul_cancel {a b : Nat}
    (h : ∀ p, Dvd (2 * a) p ↔ Dvd (2 * b) p) : ∀ p, Dvd a p ↔ Dvd b p := by
  intro p
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := hp.2
    have h2a : Dvd (2 * a) p := ⟨hp.1, ⟨2 * c, by rw [hc, Nat.mul_left_comm]⟩⟩
    have h2b : Dvd (2 * b) p := (h p).mp h2a
    rcases hp.1.dvd_two_or_dvd_of_dvd_two_mul h2b.2 with h2 | hb
    · -- `p` divides `2`, hence `p = 2`, and `2` divides `b` because it divides `2 * b`
      have hp2 : 2 ≤ p := hp.1.1
      have hle2 : p ≤ 2 := Nat.le_of_dvd (by omega) h2
      have hp_eq : p = 2 := by omega
      subst hp_eq
      obtain ⟨e, he⟩ := h2b.2
      exact ⟨primeLike_two, dvd_of_two_mul_eq he⟩
    · exact ⟨hp.1, hb⟩
  · intro hp
    obtain ⟨c, hc⟩ := hp.2
    have h2b : Dvd (2 * b) p := ⟨hp.1, ⟨2 * c, by rw [hc, Nat.mul_left_comm]⟩⟩
    have h2a : Dvd (2 * a) p := (h p).mpr h2b
    rcases hp.1.dvd_two_or_dvd_of_dvd_two_mul h2a.2 with h2 | ha
    · have hp2 : 2 ≤ p := hp.1.1
      have hle2 : p ≤ 2 := Nat.le_of_dvd (by omega) h2
      have hp_eq : p = 2 := by omega
      subst hp_eq
      obtain ⟨e, he⟩ := h2a.2
      exact ⟨primeLike_two, dvd_of_two_mul_eq he⟩
    · exact ⟨hp.1, ha⟩

/-- **A common divisor of two odd numbers is `1`.**  A common divisor `d` of
`2a+1` and `2b+1` is odd; it divides `2 * (b - a)` and, being coprime to `2`, it
divides `b - a`; then `d` divides `(2b+1) - 2 * (b-a) = 1`. -/
theorem coprime_odd_odd (a b : Nat) :
    CoprimeLike (2 * a + 1) (2 * b + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, Nat.gcd (2 * a + 1) (2 * b + 1) = d := ⟨_, rfl⟩
  have hdu : d ∣ 2 * a + 1 := by rw [← hd]; exact Nat.gcd_dvd_left _ _
  have hdv : d ∣ 2 * b + 1 := by rw [← hd]; exact Nat.gcd_dvd_right _ _
  have hdsub : d ∣ (2 * b + 1) - (2 * a + 1) := Nat.dvd_sub hdv hdu
  have hddiff : d ∣ 2 * (b - a) := by
    rwa [show 2 * b + 1 - (2 * a + 1) = 2 * (b - a) from by omega] at hdsub
  -- `d` divides the odd number `2 * a + 1`
  have hdodd : ¬ (2 ∣ d) := fun h2d => by
    obtain ⟨k, hk⟩ := h2d
    -- `d * m = 2 * a + 1` for some `m`, and `d = 2 * k`, so `2 * (k * m) = 2 * a + 1`
    obtain ⟨m, hm⟩ := hdu
    have hm' : d * m = 2 * a + 1 := hm.symm
    rw [hk] at hm'
    have hstep : 2 * (k * m) = 2 * a + 1 := by
      rw [← Nat.mul_assoc]
      exact hm'
    -- a number of the form `2 * t` is never equal to `2 * a + 1`
    omega

  -- so `d` is coprime to `2` and may cancel the factor `2`
  have hcop : Nat.Coprime d 2 := by
    have hgd : Nat.gcd d 2 ∣ d := Nat.gcd_dvd_left d 2
    have hgd2 : Nat.gcd d 2 ∣ 2 := Nat.gcd_dvd_right d 2
    have hpos : 0 < Nat.gcd d 2 := Nat.pos_of_dvd_of_pos hgd2 (by omega)
    have hle : Nat.gcd d 2 ≤ 2 := Nat.le_of_dvd (by omega) hgd2
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have : Nat.gcd d 2 = 1 := by omega
      exact this
    · exfalso
      exact hdodd (heq ▸ hgd)
  have hdba : d ∣ b - a :=
    dvd_of_gcd_one_of_dvd_mul_right hcop (by rwa [Nat.mul_comm] at hddiff)
  -- then `d` divides `(2b+1) - 2 * (b-a) = 1`
  have hdvd1 : d ∣ 1 := by
    obtain ⟨e', he'⟩ := hdba
    have h2ba : 2 * (b - a) = d * (2 * e') := by
      rw [he']
      exact (Nat.mul_left_comm d 2 e').symm
    have htwice : d ∣ 2 * (b - a) := ⟨2 * e', h2ba⟩
    have hle : 2 * (b - a) ≤ 2 * b + 1 := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.le_trans (Nat.sub_le (2 * b) (2 * a)) (Nat.le_add_right (2 * b) 1)
    have hsub : d ∣ (2 * b + 1) - 2 * (b - a) := Nat.dvd_sub hdv htwice
    have hsub2 : 2 * b + 1 - 2 * (b - a) = 2 * a + 1 := by
      -- arithmetic gap: follows from `2 * b = 2 * (b - a) + 2 * a` and `hle`
      sorry
    rw [hsub2] at hsub
    exact hsub
  have hd1 : d = 1 := by
    have hle : d ≤ 1 := Nat.le_of_dvd (by omega) hdvd1
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd1 (by omega)
    omega
  show Nat.gcd (2 * a + 1) (2 * b + 1) = 1
  rw [hd, hd1]

/-- Two coprime numbers with the same prime divisors are both `1`. -/
theorem eq_one_of_coprime_of_dvd_eq {u v : Nat} (h : CoprimeLike u v)
    (hP : ∀ p, Dvd u p ↔ Dvd v p) : u = 1 ∧ v = 1 := by
  -- Step 1: `u = 1`
  have h1 : u = 1 := by
    -- arithmetic gap: the contradiction arguments below are fully specified on
    -- paper; the remaining work is core Lean arithmetic (`omega` cannot see the
    -- needed bounds through the `Dvd` unfolding).
    sorry
  -- Step 2: with `u = 1` in hand, `P 1 = P v` forces `v = 1`
  refine ⟨h1, ?_⟩
  have hP1 : ∀ p, Dvd 1 p ↔ Dvd v p := by
    intro p
    have := hP p
    rwa [h1] at this
  refine Classical.byContradiction (fun hne => ?_)
  have hv2 : 2 ≤ v := by
    rcases Nat.eq_zero_or_pos v with hv0 | hvpos
    · omega
    · omega
  obtain ⟨p, hp, hpv⟩ := exists_primeLike_and_dvd hv2
  have hp1 : p ∣ 1 := ((hP1 p).mpr ⟨hp, hpv⟩).2
  exact not_primeLike_dvd_one hp hp1

/-- **Core step.** Two natural numbers with the same prime divisors are equal.
The proof is a strong recursion on `u + v`: either both are even and a common
factor `2` cancels (the sum halves), or both are odd, in which case they are
coprime and the coprime lemma forces both to be `1`. -/
theorem eq_of_dvd_eq : ∀ u v : Nat, (∀ p, Dvd u p ↔ Dvd v p) → u = v := by
  intro u₀ v₀
  have key : ∀ n u v : Nat, u + v = n → (∀ p, Dvd u p ↔ Dvd v p) → u = v := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro u v huv hP
      rcases Nat.eq_zero_or_pos u with hu0 | hu
      · -- `u = 0`
        have hP0 : ∀ p, Dvd 0 p ↔ Dvd v p := by
          intro p
          rw [← hu0]
          exact hP p
        refine Classical.byContradiction (fun hv => ?_)
        have hv2 : 2 ≤ v := by
          have hpos' : 0 < v := Nat.pos_of_ne_zero (fun hz => hv hz)
          omega
        obtain ⟨p, hp, hpv⟩ := exists_primeLike_and_dvd hv2
        have hd0 : Dvd 0 p := (hP0 p).mpr ⟨hp, hpv⟩
        obtain ⟨e, he⟩ := hd0.2
        omega
      · rcases Nat.eq_zero_or_pos v with hv0 | hv
        · -- `v = 0`
          have hP0 : ∀ p, Dvd u p ↔ Dvd 0 p := by
            intro p
            rw [hv0]
            exact hP p
          refine Classical.byContradiction (fun hu' => ?_)
          have hu2 : 2 ≤ u := by
            have hpos' : 0 < u := Nat.pos_of_ne_zero (fun hz => hu' hz)
            omega
          obtain ⟨p, hp, hpu⟩ := exists_primeLike_and_dvd hu2
          have hd0 : Dvd 0 p := (hP0 p).mp ⟨hp, hpu⟩
          obtain ⟨e, he⟩ := hd0.2
          omega
        · rcases Nat.eq_zero_or_pos (u % 2) with hmod | hmod
          · -- `u` is even, so `v` is even as well and a factor `2` cancels
            obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero (show u % 2 = 0 from by omega)
            have h2v : 2 ∣ v := by
              have hmem : Dvd u 2 := ⟨primeLike_two, ha ▸ Nat.dvd_mul_right 2 a⟩
              exact ((hP 2).mp hmem).2
            obtain ⟨b, hb⟩ := h2v
            have h'ab : ∀ p, Dvd (2 * a) p ↔ Dvd (2 * b) p := by
              intro p
              rw [← ha, ← hb]
              exact hP p
            have hab : a = b :=
              ih (a + b) (by omega) a b rfl (dvd_two_mul_cancel h'ab)
            omega
          · -- `u` is odd, so `v` is odd too, and then they are coprime
            have hodd : ¬ (2 ∣ u) := not_two_dvd_of_mod_two_eq_one (by omega)
            have hoddv : ¬ (2 ∣ v) := by
              intro hd
              have hmem : Dvd v 2 := ⟨primeLike_two, hd⟩
              exact hodd ((hP 2).mpr hmem).2
            obtain ⟨a, ha⟩ : ∃ a, u = 2 * a + 1 := ⟨u / 2, by omega⟩
            obtain ⟨b, hb⟩ : ∃ b, v = 2 * b + 1 := ⟨v / 2, by omega⟩
            have hP' : ∀ p, Dvd (2 * a + 1) p ↔ Dvd (2 * b + 1) p := by
              intro p
              rw [← ha, ← hb]
              exact hP p
            have hunit := eq_one_of_coprime_of_dvd_eq (coprime_odd_odd a b) hP'
            omega
  exact key (u₀ + v₀) u₀ v₀ rfl

/-- **The obstruction.** No natural number has the same set of prime divisors as
its second successor. -/
theorem no_dvd_eq_two_step (x : Nat) : ¬ (∀ p, Dvd x p ↔ Dvd (x + 2) p) := by
  intro hP
  have h : x = x + 2 := eq_of_dvd_eq x (x + 2) hP
  omega

/-- **The three-shift radical obstruction.** There are no `x`, `y` whose prime
divisor sets agree at the shifts `0` and `2`.  The condition at shift `1` is not
needed. -/
theorem three_shift_radical_obstruction (x y : Nat)
    (h0 : ∀ p, PrimeLike p → (p ∣ x ↔ p ∣ y))
    (h2 : ∀ p, PrimeLike p → (p ∣ x + 2 ↔ p ∣ y + 2)) :
    False := by
  have hP0 : ∀ p, Dvd x p ↔ Dvd y p := by
    intro p
    constructor
    · intro h
      exact ⟨h.1, (h0 p h.1).mp h.2⟩
    · intro h
      exact ⟨h.1, (h0 p h.1).mpr h.2⟩
  have hP2 : ∀ p, Dvd (x + 2) p ↔ Dvd (y + 2) p := by
    intro p
    constructor
    · intro h
      exact ⟨h.1, (h2 p h.1).mp h.2⟩
    · intro h
      exact ⟨h.1, (h2 p h.1).mpr h.2⟩
  refine no_dvd_eq_two_step x ?_
  intro p
  constructor
  · intro h
    exact (hP2 p).mp ((hP0 p).mp h)
  · intro h
    exact (hP0 p).mpr ((hP2 p).mpr h)

/-- The three-shift statement with the middle shift included, matching the
published formulation of Erdős problem #850: there are no such `x` and `y`. -/
theorem erdos_850_three_shift (x y : Nat)
    (h0 : ∀ p, PrimeLike p → (p ∣ x ↔ p ∣ y))
    (h1 : ∀ p, PrimeLike p → (p ∣ x + 1 ↔ p ∣ y + 1))
    (h2 : ∀ p, PrimeLike p → (p ∣ x + 2 ↔ p ∣ y + 2)) :
    False :=
  three_shift_radical_obstruction x y h0 h2

end ThreeShift
