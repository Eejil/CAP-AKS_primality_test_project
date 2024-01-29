import Mathlib

open Polynomial

noncomputable section

variable (n r : ℕ) (d a : ℤ )
--noncomputable
noncomputable def idl := Ideal.span {(X^n + C a : ℤ[X]) , C (r : ℤ)}

example (n : ℕ ) (I: Ideal ℤ[X] ) (h : I = Ideal.span {(X^n + C a : ℤ[X]) , C (r : ℤ)}) :
  --(X + C a) ^n - (X^n + C a) ∈ I := by sorry
  Ideal.Quotient.mk I ((X + C a) ^n) = Ideal.Quotient.mk I ((X^n + C a)) := by sorry

variable (p : ℕ) (hpn : p ∣ n) (hp : Nat.Prime p)

def I₁ := Ideal.span {(C n : ℤ[X]), X^r - 1}
def I₂ := Ideal.span {(C p : ℤ[X]), X^r - 1}

theorem divisibility_lifting :
    Ideal.Quotient.mk (R := ℤ[X]) (I₁ n r) ((X + C a) ^ n) = Ideal.Quotient.mk (R := ℤ[X]) (I₁ n r) (X ^ n + C a) →
    Ideal.Quotient.mk (R := ℤ[X]) (I₂ p r) ((X + C a) ^ n) = Ideal.Quotient.mk (R := ℤ[X]) (I₂ p r) (X ^ n + C a) := by
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]

end
