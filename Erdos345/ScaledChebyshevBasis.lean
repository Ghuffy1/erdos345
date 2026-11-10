import Erdos345.FinitePadding

namespace Erdos345

open Finset Polynomial

theorem shiftedChebyshev_expansion_top_coeff {K : Type*} [Field K] [CharZero K]
    {m : ℕ} (a : Fin m → K) (hm : 0 < m) :
    (∑ j, a j • shiftedChebyshev K j).coeff (m - 1) =
      a ⟨m - 1, by omega⟩ * ((2 : K) ^ (m - 1 - 1) * 2 ^ (m - 1)) := by
  rw [finsetSum_coeff, sum_eq_single (⟨m - 1, by omega⟩ : Fin m)]
  · simp only [coeff_smul, smul_eq_mul]
    congr 1
    rw [← shiftedChebyshev_leadingCoeff K (m - 1), leadingCoeff, shiftedChebyshev_natDegree]
  · intro j _ hj
    have hjlt : j.val < m - 1 := by
      have hjne : j.val ≠ m - 1 := fun h => hj (Fin.ext h)
      omega
    rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by rw [shiftedChebyshev_natDegree]; exact hjlt), smul_zero]
  · intro h
    exact False.elim (h (mem_univ _))

theorem exists_supported_chebyshev_expansion {K : Type*} [Field K] [CharZero K]
    (P : K[X]) (m D : ℕ) (hmD : m ≤ D) (hP : P.degree < m) :
    ∃ c : Fin D → K,
      (∀ j : Fin D, m ≤ j.val → c j = 0) ∧
      P = ∑ j, c j • shiftedChebyshev K j ∧
      (∀ hm : 0 < m,
        P.coeff (m - 1) = c ⟨m - 1, by omega⟩ * ((2 : K) ^ (m - 1 - 1) * 2 ^ (m - 1))) := by
  obtain ⟨a, ha⟩ := exists_shiftedChebyshev_expansion P m hP
  refine ⟨padFin a, fun j hj => padFin_eq_zero a j hj, ?_, ?_⟩
  · rw [sum_padFin_smul a hmD]
    exact ha
  · intro hm
    have hc := shiftedChebyshev_expansion_top_coeff a hm
    rw [← ha] at hc
    simpa [padFin, show m - 1 < m by omega] using hc

theorem exists_scaled_chebyshev_expansion {K : Type*} [Field K] [CharZero K]
    (P : K[X]) (s : K) (hs : s ≠ 0) (m D : ℕ) (hmD : m ≤ D) (hP : P.degree < m) :
    ∃ c : Fin D → K,
      (∀ j : Fin D, m ≤ j.val → c j = 0) ∧
      P.comp (C s * X) = ∑ j, c j • shiftedChebyshev K j ∧
      (∀ hm : 0 < m,
        P.coeff (m - 1) * s ^ (m - 1) =
          c ⟨m - 1, by omega⟩ * ((2 : K) ^ (m - 1 - 1) * 2 ^ (m - 1))) := by
  have hcomp : (P.comp (C s * X)).degree < m := by
    rw [degree_comp (by rw [degree_C_mul_X hs]; norm_num), degree_C_mul_X hs, mul_one]
    exact hP
  obtain ⟨c, hc0, hc, hctop⟩ := exists_supported_chebyshev_expansion (P.comp (C s * X)) m D hmD hcomp
  refine ⟨c, hc0, hc, ?_⟩
  intro hm
  simpa only [comp_C_mul_X_coeff] using hctop hm

theorem shiftedChebyshev_topScale_norm_le (b : ℕ) :
    ‖((2 : ℂ) ^ (b - 1) * 2 ^ b)‖ ≤ (4 : ℝ) ^ b := by
  have hn : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [norm_mul, norm_pow, norm_pow, hn]
  calc
    (2 : ℝ) ^ (b - 1) * 2 ^ b ≤ 2 ^ b * 2 ^ b := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le b 1)
    _ = 4 ^ b := by rw [← mul_pow]; norm_num

theorem scaled_chebyshev_top_norm_lower (P : ℂ[X]) (s : ℂ) (b : ℕ) (d : ℂ)
    (htop : P.coeff b * s ^ b = d * ((2 : ℂ) ^ (b - 1) * 2 ^ b)) :
    ‖P.coeff b‖ * ‖s‖ ^ b / (4 : ℝ) ^ b ≤ ‖d‖ := by
  have hn := congrArg norm htop
  simp only [norm_mul, norm_pow] at hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ b)).mpr
  calc
    _ = ‖d‖ * ‖((2 : ℂ) ^ (b - 1) * 2 ^ b)‖ := by simpa only [norm_mul, norm_pow] using hn
    _ ≤ ‖d‖ * (4 : ℝ) ^ b :=
      mul_le_mul_of_nonneg_left (shiftedChebyshev_topScale_norm_le b) (norm_nonneg _)

end Erdos345
