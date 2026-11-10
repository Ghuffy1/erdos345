import Erdos345.GoodReductionBound
import Erdos345.PolynomialReduction

/-!
A least-degree formulation of the final degree descent. Choosing the smallest
admissible degree turns an affine contraction into a direct bound. The analytic
contraction is an explicit premise, not an axiom or an established result of
this development.
-/

namespace Erdos345

theorem dvd_reductionModulus_self (q k : ℕ) : q ∣ reductionModulus k k := by
  rw [dvd_reductionModulus_iff]
  intro j hj
  rw [powerCoefficient_eq_zero hj]
  exact dvd_zero q

theorem exists_reduction_degree (q k : ℕ) : ∃ d : ℕ, q ∣ reductionModulus k d :=
  ⟨k, dvd_reductionModulus_self q k⟩

def minimalReductionDegree (q k : ℕ) : ℕ := Nat.find (exists_reduction_degree q k)

theorem minimalReductionDegree_spec (q k : ℕ) :
    q ∣ reductionModulus k (minimalReductionDegree q k) :=
  Nat.find_spec (exists_reduction_degree q k)

theorem minimalReductionDegree_le {q k d : ℕ} (hd : q ∣ reductionModulus k d) :
    minimalReductionDegree q k ≤ d := Nat.find_min' (exists_reduction_degree q k) hd

theorem minimalReductionDegree_le_self (q k : ℕ) : minimalReductionDegree q k ≤ k :=
  minimalReductionDegree_le (dvd_reductionModulus_self q k)

theorem minimalReductionDegree_le_iff (q k d : ℕ) :
    minimalReductionDegree q k ≤ d ↔ q ∣ reductionModulus k d := by
  constructor
  · intro h
    exact (minimalReductionDegree_spec q k).trans (reductionModulus_mono_dvd k h)
  · exact minimalReductionDegree_le

theorem minimalReductionDegree_pos {q k : ℕ} (hq : 1 < q) (hk : 0 < k) :
    0 < minimalReductionDegree q k := by
  by_contra h
  have hz : minimalReductionDegree q k = 0 := by omega
  have hd := minimalReductionDegree_spec q k
  rw [hz, reductionModulus_zero hk] at hd
  have := Nat.dvd_one.mp hd
  omega

theorem minimalReductionDegree_polynomial (q k : ℕ) :
    hasGlobalIntegerPolynomialReduction q k (minimalReductionDegree q k) :=
  (hasGlobalIntegerPolynomialReduction_iff_dvd q k _).mpr (minimalReductionDegree_spec q k)

/-- A contraction applied at the least admissible degree bounds that degree
without choosing or iterating a sequence of reductions. -/
theorem minimalReductionDegree_le_of_contraction {q k : ℕ} (hq : 1 < q) (hk : 0 < k)
    {a b : ℝ} (ha : a < 1)
    (hcontract : ∀ d : ℕ, 0 < d → d ≤ k → q ∣ reductionModulus k d →
      ∃ e : ℕ, q ∣ reductionModulus k e ∧ (e : ℝ) ≤ a * (d : ℝ) + b) :
    (minimalReductionDegree q k : ℝ) ≤ b / (1 - a) := by
  obtain ⟨e, he, hbound⟩ := hcontract (minimalReductionDegree q k)
    (minimalReductionDegree_pos hq hk) (minimalReductionDegree_le_self q k)
    (minimalReductionDegree_spec q k)
  have hmin : (minimalReductionDegree q k : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast minimalReductionDegree_le he
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith

/-- The arithmetic envelope can be used at that same least degree. The input
logarithmic envelope and analytic contraction remain visible hypotheses. -/
theorem log_modulus_le_of_contraction {q k : ℕ} (hq : 1 < q) (hk : 0 < k)
    {a b L : ℝ} (ha : a < 1) (hL : 0 ≤ L) (hproper : b / (1 - a) < k)
    (hcontract : ∀ d : ℕ, 0 < d → d ≤ k → q ∣ reductionModulus k d →
      ∃ e : ℕ, q ∣ reductionModulus k e ∧ (e : ℝ) ≤ a * (d : ℝ) + b)
    (henvelope : ∀ d : ℕ, 0 < d → d < k →
      Real.log (reductionModulus k d : ℝ) ≤ L * (d : ℝ)) :
    Real.log (q : ℝ) ≤ L * (b / (1 - a)) := by
  have hbound := minimalReductionDegree_le_of_contraction hq hk ha hcontract
  have hdlt : minimalReductionDegree q k < k := by
    exact_mod_cast hbound.trans_lt hproper
  have hdpos := minimalReductionDegree_pos hq hk
  have hqg : q ≤ reductionModulus k (minimalReductionDegree q k) :=
    Nat.le_of_dvd (reductionModulus_pos hdlt) (minimalReductionDegree_spec q k)
  calc
    Real.log (q : ℝ) ≤ Real.log (reductionModulus k (minimalReductionDegree q k) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) (by exact_mod_cast hqg)
    _ ≤ L * (minimalReductionDegree q k : ℝ) := henvelope _ hdpos hdlt
    _ ≤ L * (b / (1 - a)) := mul_le_mul_of_nonneg_left hbound hL

end Erdos345
