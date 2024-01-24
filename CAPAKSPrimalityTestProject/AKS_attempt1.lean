import Mathlib
-- import group_theory.order_of_element
-- import Mathlib.RingTheory.Ideal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Basic

section
open Polynomial



-- theorem childBinomial (n : ℕ)(a : ZMod n) (two_le_n: 2≤n):
--   Nat.Prime n ↔ (X + C a)^n = (X^n + C a) := by sorry
theorem childBinomial (n : ℕ)(a : ZMod n) (two_le_n: 2≤n) (np : Nat.Prime n) :
(X + C a)^n = (X^n + C a) := by
    have : Fact (Nat.Prime n) := Fact.mk np
    rw [add_pow_char, ← map_pow, ZMod.pow_card]

-- def I := Ideal.span {X^n + C a, C r}:
-- noncomputable def I := Ideal.span {X^n + C a, C r}:




def notPerfectPow (n : ℕ) : Prop :=
¬∃ (a b : ℕ), (a > 1)  ∧  (b > 1) ∧ (a^b = n)
-- #check notPerfectPow

example
    -- (n m: ℕ)
    -- (r d a : ℤ)
    (n m r: ℕ)
    (d : ℤ)
    (a : ZMod n)
    -- (n m r: ℕ)
    -- (d : ℤ)

    (nOdd : Odd n) (nGT1 : n > 1) (nNotPP : notPerfectPow n)
    (nFinOrder: IsOfFinOrder n) -- (n : Zmod r)
    (nOrderLB : orderOf n > (Nat.log2 n))

    -- (I : Ideal ℤ[X]) (h : I = Ideal.span {X^r + C a, C ↑n})
    (I : Ideal (ZMod n)[X])
     (h : I = Ideal.span {X^r + C a, C ↑n})
    -- (aorder : Order)
    -- (aLB : 1 ≤ a) (aUB : a ≤ round ((Real.sqrt ↑r) * Real.logb 2 ↑n))
    (aLB : 1 ≤ a.val) (aUB : a.val ≤ (Real.sqrt ↑r) * Real.logb 2 ↑n) -- (aUB : a.val ≤ round ((Real.sqrt ↑r) * Real.logb 2 ↑n))

    (mLB : 1 < m) (mUB : m ≤ r) (mCoprimeN : m.Coprime n)
    :
    -- Nat.Prime n ↔ Ideal.Quotient.mk I (X + C a)^n = Ideal.Quotient.mk I  (X^n + C a)
    -- equiv to
    Nat.Prime n ↔ (X + C ↑a)^n - (X^n + C a) ∈ I
  := by

  constructor
  case mp => -- **Show: Nat.Prime n → (X + C ↑a)^n - (X^n + C a) ∈ I**
    rintro hn
    have h₁ : (X + C a)^n - (X^n + C a) ∈ Ideal.span {C ↑↑n} := by
    /- _______ DONE
    Must convert to problem of the form**
    (X + C a) ^ n - (X ^ n + C a) = 0 ∈ (ZMod n)[x]**
    and apply Fermat Little Theorem / Child's Binomial Theorem
    the rest seems trivial.
    _______ -/
      rw [Ideal.mem_span_singleton]
      -- -- apply Ideal.mem_span_singleton.mp ((X + C a)^n - (X^n + C a)) (C r)
      -- -- apply Ideal.mem_span_singleton'.mp
      -- simp

      -- -- rintro Z Z1
      have : Fact (Nat.Prime n) := Fact.mk hn
      rw [childBinomial _ _ nGT1 hn, sub_self];
      -- rw [sub_self]
      simp
      -- show_term {simp}
      -- exact AdjoinRoot.mk_eq_zero.mp rfl -- **This works but I want to know how**

      -- rw [dvd_zero]
      -- simp
      -- apply nGT1
      -- rw [add_pow_char, ← map_pow, ZMod.pow_card]

      -- sorry -- Nat.Prime n ↔ (X + C a)^n - (X^n + C a) ∈ Ideal.span {C r}
    --
    -- have h₂ : Ideal.span {C r} ≤ Ideal.span {X^n + C a, C r} := by sorry
    -- have n : Fact (Nat.Prime n) := Fact.mk hn
    rw [h]
    rw [Ideal.span_insert]
    apply Ideal.mem_sup_right
    exact h₁

    -- have h₃ : (X + C a)^n - (X^n + C a) ∈ Ideal.span {C r}  := ⟨n, h₁⟩

    -- cases h₁ : n with _
    -- apply [n] at h₁

    -- apply Ideal.span_union -- (X^n + C a) (C r)

    -- rw [Ideal.span_union (X^n + C a) (C r)]


    -- apply h₁.mp
    -- exact n

    -- apply Ideal.mem_span_pair
    -- apply Ideal._span_mono
    -- apply Ideal.mem_sup_right

    -- #check Ideal.span {C r}  Ideal.span {X^n + C a, C r}

  case mpr => -- **Show: (X + C ↑a)^n - (X^n + C a) ∈ I → Nat.Prime n**
  rintro hr

  sorry
  -- sorry
    -- have h₃ {R : Type*} [semiRing R] {S T : Ideal R} (b : R) : (S ≤ T ∧ b ∈ S) → b ∈ T :=by sorry

/-
  ToDo / ToCheck
Account for n being in Zmod r sometimes (order of n)
Account for a being in Zmod r sometimes
-/


/-
**Question for Anne**
if we have a statement (hypothesis)
(a = b ↔ c)
and an hypothesis (hc : c)
how can we use the (a = b) in a rw or apply ?
-/
