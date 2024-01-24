import Mathlib

#check Nat.ModEq.pow_totient
#check add_pow
#check Nat.gcd_eq_gcd_ab

  /-
  the definitions are variantions of this
  -/

open Polynomial

example (a n : ℕ)  (hn : Nat.Prime n) :
    (X + C (a : ZMod n))^n = X^n + C (a : ZMod n) := by
  have : Fact (Nat.Prime n) := Fact.mk hn
  rw [add_pow_char]


example (n : ℕ) (a : ZMod n)  (hn : Fact ( Nat.Prime n)) :
    (X + C a)^n = X^n + C a := by
  rw [add_pow_char, ← map_pow, ZMod.pow_card]
  /-
  congr
  convert ZMod.pow_card a
  -/
