import Mathlib
-- import group_theory.order_of_element
-- import Mathlib.RingTheory.Ideal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Basic

section
open Polynomial



theorem childBinomial (n : ℕ)(a : ZMod n) (two_le_n: 2≤n):
  Nat.Prime n ↔ (X + C a)^n = (X^n + C a) := by sorry

-- theorem childBinomial (n : ℕ)(a : ZMod n) (two_le_n: 2≤n) (np : Nat.Prime n) :
-- (X + C a)^n = (X^n + C a) := by
--     have : Fact (Nat.Prime n) := Fact.mk np
--     rw [add_pow_char, ← map_pow, ZMod.pow_card]


def notPerfectPow (n : ℕ) : Prop :=
¬∃ (a b : ℕ), (a > 1)  ∧  (b > 1) ∧ (a^b = n)
-- #check notPerfectPow

example
    (n m r: ℕ)
    (d : ℤ)
    -- (a : ZMod n)

    (nOdd : Odd n) (nGT1 : n > 1) (nNotPP : notPerfectPow n)
    (nFinOrder: IsOfFinOrder n) -- (n : Zmod r)
    (nOrderLB : orderOf n > (Nat.log2 n))

    (I : Ideal (ZMod n)[X])
     (h : I = Ideal.span {X^r - 1, C ↑n})
    -- (aLB : 1 ≤ a.val) (aUB : a.val ≤ (Real.sqrt ↑r) * Real.logb 2 ↑n)

    (mLB : 1 < m) (mUB : m ≤ r) (mCoprimeN : m.Coprime n)
    :
    -- Nat.Prime n ↔ Ideal.Quotient.mk I (X + C a)^n = Ideal.Quotient.mk I  (X^n + C a)
    -- equiv to
    Nat.Prime n ↔ ∀ a : ℕ, a ≤ (Real.sqrt ↑r) * Real.logb 2 ↑n → (X + C (a : ZMod n))^n - (X^n + C (a : ZMod n)) ∈ I
  := by

  constructor
  case mp => -- **Show: Nat.Prime n → (X + C ↑a)^n - (X^n + C a) ∈ I**
    rintro hn a ha
    have h₁ : (X + C (a : ZMod n))^n - (X^n + C (a : ZMod n)) ∈ Ideal.span {C ↑↑n} := by
      rw [Ideal.mem_span_singleton]

      have : Fact (Nat.Prime n) := Fact.mk hn
      rw [(childBinomial _ _ nGT1).mp hn, sub_self];
      -- rw [childBinomial _ _ nGT1 hn, sub_self];
      --  simp? -- show_term {simp}
      exact AdjoinRoot.mk_eq_zero.mp rfl

    rw [h]
    rw [Ideal.span_insert]
    apply Ideal.mem_sup_right
    exact h₁

  case mpr => -- **Show: (X + C ↑a)^n - (X^n + C a) ∈ I → Nat.Prime n**
  -- rintro hr
  rw [h]
  contrapose
  rintro nNotP
  apply (Nat.not_prime_iff_minFac_lt _).mp at nNotP
  let p := Nat.minFac n

  rw [Ideal.span_insert]

  have h1 : p ∣ n := by sorry --apply nNotP
  -- apply (Ideal.span_singleton_le_span_singleton h1).mpr

  sorry
  -- sorry
    -- have h₃ {R : Type*} [semiRing R] {S T : Ideal R} (b : R) : (S ≤ T ∧ b ∈ S) → b ∈ T :=by sorry


-- subgroup.closure units
