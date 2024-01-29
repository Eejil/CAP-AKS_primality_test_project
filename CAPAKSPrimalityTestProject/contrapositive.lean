import Mathlib

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Basic

section
open Polynomial
open BigOperators


lemma asdf {a b : ℤ} {p : ℕ} [hp : Fact p.Prime] : a ≡ b [ZMOD p] ↔ (a : ZMod p) = (b : ZMod p) := by
  have : NeZero p := ⟨Nat.Prime.ne_zero hp.out⟩
  rw [Int.modEq_iff_dvd, ZMod.int_cast_eq_int_cast_iff_dvd_sub]

example (x : ℤ) (p : ℕ) [hp : Fact p.Prime] : (1 + x) ^ (p ^ n) ≡ 1 + x ^ (p ^ n) [ZMOD p] := by
  simp only [asdf]
  simp only [Int.cast_pow]
  simp only [Int.cast_add]
  simp only [Int.cast_one]
  simp only [add_pow_char_pow]
  simp only [one_pow]
  simp
  -- simp only [asdf, Int.cast_pow, Int.cast_add, Int.cast_one, one_pow, add_pow_char_pow]


-- example (n a) : ∀(n : ℕ)(a : ZMod n), (n≥2 ∧ Coprime n a → (Nat.Prime n ↔ (X + C a)^n = X^n + C a) := by
--   sorry

example (n : ℕ)(a : ZMod n) (two_le_n: 2≤n):
  Nat.Prime n ↔ (X + C a)^n = (X^n + C a) := by
  -- First, let's break up the bi-implication
  -- into the two directions
  constructor

  -- we start withthe left-to-right direction
  case mp => -- **Nat.Prime n → (X + C a)^n = (X^n + C a)**
    -- This direction was solved in this way by Anne
    intro hn -- Assume n is prime

    -- We need to convert proposition hn to a fact:
    have : Fact (Nat.Prime n) := Fact.mk hn

    -- Now we can apply three theorems to derive our goal
    rw [add_pow_char, ← map_pow, ZMod.pow_card]

  case mpr => --**(X + C a)^n = (X^n + C a) → Nat.Prime n**
  -- We continue to the right-to-left direction
    contrapose -- We use the contrapositive
    intro hn -- Assume n is not prime

    -- We can apply a theorem that says p < n if n is not prime
    -- where p is defined as the smallest prime factor of n
    apply (Nat.not_prime_iff_minFac_lt two_le_n).mp at hn

    -- To avoid notational clutter, we define p to be this prime
    let p := Nat.minFac n

    -- Now we want to start talking about combinatorics ...
    -- We could use Nat.choose_eq_factorial_div_factorial
    -- It contains the definition of (n choose k) as we know it
    push_neg
    -- apply?
    -- apply add_pow_char (X : (ZMod n)[X]) _


    rw [add_pow]
    rw [Finset.sum_congr rfl]
    swap
    intros x hx
    /-**goal 1**-/
    show _ = X ^ x * C a ^ (n - x) * ↑(Nat.factorial n / (Nat.factorial x * Nat.factorial (n - x)))
    -- show _ = (X + C a) ^ x

    /-**goal 2**-/
    rw [Nat.choose_eq_factorial_div_factorial]
    apply Finset.mem_range.mp at hx
    exact Nat.lt_succ.mp hx

    /-**goal 3**-/
    -- rw [Finset.sum_Ico_succ_top _ _]
    rw [←Finset.sum_range_add_sum_Ico _ n.le_succ ]
    simp
    rw [←Finset.sum_range_add_sum_Ico _ (Nat.le_trans one_le_two two_le_n) ]
    simp

    repeat rw [Nat.div_self (Nat.factorial_pos n)]
    simp
    -- rw [add_comm]
    simp [add_comm, add_right_inj]
    -- apply Nat.add_left_cancel.mp





    -- rw[← map_pow]
    -- push_neg

    -- rw [ZMod.pow_card]

    -- rw [add_pow_char]

    -- rw []

    -- apply?




    rw [←Nat.mul_factorial_pred]
    -- rw []


    -- nth_rw 2 [←Nat.mul_factorial_pred]
    -- rw [←Nat.mul_factorial_pred]


    -- rw [Finset.sum_pow _ _ _]



    -- the proof should continue here
    sorry
    exact Nat.zero_lt_of_lt two_le_n






-- theorem add_pow_char
example [CommSemiring R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_char_of_commute _ _ _ (Commute.all _ _)
#align add_pow_char2 add_pow_char



end
