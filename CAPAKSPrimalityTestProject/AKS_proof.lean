import Mathlib
-- import group_theory.order_of_element
-- import Mathlib.RingTheory.Ideal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Basic

section
open Polynomial




/-
We first attempt to prove **Child's Binomial Theoremn**
Let n an integer greater and equal than twon then
  n is prime if and only if
    (X + C a)^n ≡ (X^n + C a) mod n.
We successfully prove the forward direction.
The backward direction is still incomplete.
-/

theorem childBinomial (n : ℕ)(a : ZMod n) (two_le_n: 2≤n):
-- example (n : ℕ)(a : ZMod n) (two_le_n: 2≤n):
  Nat.Prime n ↔ (X + C a)^n = (X^n + C a) := by
  -- First, let's break up the bi-implication into the two directions
  constructor
  -- we start withthe left-to-right direction
  case mp => -- **Nat.Prime n → (X + C a)^n = (X^n + C a)**
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

    rw [add_pow]
    rw [Finset.sum_congr rfl]
    swap
    intros x hx
    /-subgoal 1-/
    show _ = X ^ x * C a ^ (n - x) * ↑(Nat.factorial n / (Nat.factorial x * Nat.factorial (n - x)))

    /-subgoal 2-/
    rw [Nat.choose_eq_factorial_div_factorial]
    apply Finset.mem_range.mp at hx
    exact Nat.lt_succ.mp hx

    /-subgoal 3-/
    rw [←Finset.sum_range_add_sum_Ico _ n.le_succ ]
    simp
    rw [←Finset.sum_range_add_sum_Ico _ (Nat.le_trans one_le_two two_le_n) ]
    simp

    repeat rw [Nat.div_self (Nat.factorial_pos n)]
    simp
    simp [add_comm, add_right_inj]
    rw [←Nat.mul_factorial_pred]
    sorry
    exact Nat.zero_lt_of_lt two_le_n





/-
Here, we attemps to prove the **main theorem of the AKS algorithm**; that is, we prove the following:
For given integer n ≥ 2, let r be a positive integer < n, for which n has order > (log n)^2 modulo r.
If n is not a prime power and does not have any prime factor ≤ r
then
  n is prime if and only if
    (X + a)^n - (X^n + a) ≡ 0 mod (n, X^r -1)
for all integers 1 < a ≤ sqrt(r)*log2(n).


We successfully prove the forward direction.
The backward direction is still incomplete.
-/

-- We first define the property of an integer to not be a perfect power.
def notPerfectPow (n : ℕ) : Prop :=
¬∃ (a b : ℕ), (a > 1)  ∧  (b > 1) ∧ (a^b = n)
-- #check notPerfectPow


-- Definition of group H and irreducible polynomial h(x)

variable (A r n : ℕ)
[Fact $ Nat.Prime n]

def I : Ideal (ZMod n)[X] :=
  Ideal.span {X^r - 1, C ↑n}
def xSet : Set ((ZMod n)[X] ⧸ (I r n)) :=   ------------------Set of x+1, x+2,...,x+A
  {P | ∃ (a : ℕ), 0 ≤ a ∧ a ≤ A ∧ P = Ideal.Quotient.mk (I r n) (X + C (a : ZMod n)) }

def HSet : (Set ((ZMod n)[X] ⧸ I r n)) := --------------------------------Set H
 {x | x ∈ Submonoid.closure (xSet A r n)}

noncomputable def h_i_ : (ZMod n)[X] :=
  Polynomial.factor ((X^r - 1) : (ZMod n)[X])
  --(h_irr : Irreducible h_i)


theorem AKS
    (n m r: ℕ) (d : ℤ)

    (nOdd : Odd n) (nGT1 : n > 1) (nNotPP : notPerfectPow n)
    (nFinOrder: IsOfFinOrder n)
    (nOrderLB : orderOf n > (Nat.log2 n))

    (I : Ideal (ZMod n)[X]) (h : I = Ideal.span {X^r - 1, C ↑n})

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
      have : Fact (Nat.Prime n) := Fact.mk hn
      rw [(childBinomial _ _ nGT1).mp hn, sub_self];
      exact Ideal.zero_mem _
    rw [h]
    rw [Ideal.span_insert]
    apply Ideal.mem_sup_right
    exact h₁

  case mpr => -- **Show: (X + C ↑a)^n - (X^n + C a) ∈ I → Nat.Prime n**
    rw [h]
    contrapose
    rintro nNotP
    apply (Nat.not_prime_iff_minFac_lt _).mp at nNotP
    let p := Nat.minFac n

    rw [Ideal.span_insert]

    have h1 : p ∣ n := by sorry

    sorry
end
