import Mathlib

section
open Polynomial
open BigOperators

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
    rw [add_pow, Finset.sum_congr rfl]
    swap
    intros x hx
    show _ = X ^ x * C a ^ (n - x) * ↑(Nat.factorial n / (Nat.factorial x * Nat.factorial (n - x)))
    -- show _ = (X + C a) ^ x
    rw [Nat.choose_eq_factorial_div_factorial]
    apply Finset.mem_range.mp at hx
    exact Nat.lt_succ.mp hx
    rw [←Nat.mul_factorial_pred]
    nth_rw 2 [←Nat.mul_factorial_pred]
    rw [←Nat.mul_factorial_pred]


    -- rw [Finset.sum_pow _ _ _]



    -- the proof should continue here
    sorry

end
