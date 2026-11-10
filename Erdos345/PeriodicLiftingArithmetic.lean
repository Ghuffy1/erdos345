import Mathlib.Tactic

namespace Erdos345

/-- Arithmetic used to combine one new quotient class with Kneser's
deficit bound. All quantities are natural cardinalities. -/
theorem periodic_lifting_arithmetic (h d x z p r t k a s : ℕ)
    (hh : 0 < h) (ht : 0 < t) (hpr : p + t = r)
    (hz : z ≤ r * d + (h - 1) * d)
    (hbad : r * d + h ≤ x)
    (hk : k + (h + z) = x + h * d + 1)
    (hlift : a + p * d + t * k ≤ s) :
    a + x + 1 ≤ s + h := by
  have hh' : h - 1 + 1 = h := by omega
  have hz' : z + d ≤ r * d + h * d := by nlinarith
  have hdk : d ≤ k := by omega
  have ht' : t - 1 + 1 = t := by omega
  have hmul := Nat.mul_le_mul_left (t - 1) hdk
  nlinarith

end Erdos345
