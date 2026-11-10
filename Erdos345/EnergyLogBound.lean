import Erdos345.RecurrenceTranslation

namespace Erdos345

open Finset Polynomial

theorem multiplicity_log_bound_of_energy (m : ℕ) (hm : 0 < m)
    (L K B E : ℝ) (hL : 0 < L) (hK : 0 < K)
    (hscale : 2 * Real.log 4 ≤ Real.log L)
    (henergy : L * K * (Real.exp (-B) * L ^ (m - 1) / (4 : ℝ) ^ (m - 1)) ^ 2 ≤ E) :
    (m : ℝ) * Real.log L ≤ Real.log E + 2 * B - Real.log K := by
  let b := m - 1
  let A := Real.exp (-B) * L ^ b / (4 : ℝ) ^ b
  have hA : 0 < A := by dsimp [A]; positivity
  have hLA : 0 < L * K * A ^ 2 := mul_pos (mul_pos hL hK) (pow_pos hA _)
  have hlog := Real.log_le_log hLA henergy
  have hlogA : Real.log A = -B + (b : ℝ) * Real.log L - (b : ℝ) * Real.log 4 := by
    dsimp [A]
    rw [Real.log_div (ne_of_gt (mul_pos (Real.exp_pos _) (pow_pos hL _)))
      (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)),
      Real.log_mul (ne_of_gt (Real.exp_pos _)) (pow_ne_zero _ (ne_of_gt hL)),
      Real.log_exp, Real.log_pow, Real.log_pow]
  change Real.log (L * K * A ^ 2) ≤ Real.log E at hlog
  rw [Real.log_mul (ne_of_gt (mul_pos hL hK)) (pow_ne_zero _ (ne_of_gt hA)),
    Real.log_mul (ne_of_gt hL) (ne_of_gt hK), Real.log_pow, hlogA] at hlog
  have hm' : (m : ℝ) = (b : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hm : m - 1 + 1 = m).symm
  have hnonneg : 0 ≤ (b : ℝ) * (Real.log L - 2 * Real.log 4) :=
    mul_nonneg (Nat.cast_nonneg b) (sub_nonneg.mpr hscale)
  norm_num only [Nat.cast_ofNat] at hlog
  rw [hm']
  nlinarith

theorem multiplicity_bound_of_energy (m : ℕ) (hm : 0 < m)
    (L K B E : ℝ) (hL : 16 ≤ L) (hK : 0 < K)
    (henergy : L * K * (Real.exp (-B) * L ^ (m - 1) / (4 : ℝ) ^ (m - 1)) ^ 2 ≤ E) :
    (m : ℝ) ≤ (Real.log E + 2 * B - Real.log K) / Real.log L := by
  have hLpos : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hscale : 2 * Real.log 4 ≤ Real.log L := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hL
    have heq : Real.log (16 : ℝ) = 2 * Real.log 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [heq] at h
  exact (le_div_iff₀ hlogL).mpr
    (multiplicity_log_bound_of_energy m hm L K B E hLpos hK hscale henergy)

theorem minimal_integer_primePower_multiplicity_bound
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (p k : ℕ) (hp : p.Prime) (ht : p ^ (k + 1) ∈ Icc 1 N) (hmt : 0 < m (p ^ (k + 1)))
    (L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ n ∈ range L, ‖(f n : ℂ)‖ ^ 2) ≤ E) :
    (m (p ^ (k + 1)) : ℝ) ≤
      (Real.log E + 8 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N -
        Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L := by
  have hLn : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have hN : 0 < N := (pow_pos hp.pos (k + 1)).trans_le (mem_Icc.mp ht).2
  have henergy := (minimal_integer_primePower_energy_lower hw hMass m hm f hminimal
    p k hp ht hmt L hLn hlarge).trans hE
  have h := multiplicity_bound_of_energy (m (p ^ (k + 1))) hmt (L : ℝ)
    (Real.pi / (64 * (N : ℝ))) (4 * ((weightMass N w : ℝ) / (p ^ (k + 1) : ℕ)) * Real.log N)
    E hL (by positivity) henergy
  convert h using 1
  ring

theorem minimal_integer_rootOne_multiplicity_bound
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hMass : weightMass N w ≤ N) (hN : 1 ≤ N) (m : ℕ → ℕ)
    (hm : ∀ n ∈ Icc 1 N, m n ≤ rootSlots N w n)
    (f : ℕ → ℤ)
    (hminimal : (cyclotomicProduct (Icc 1 N) m).map (Int.castRingHom ℚ) =
      minimalAnnihilator (fun n => (f n : ℚ)))
    (hmt : 0 < m 1) (L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ) (hE : (∑ n ∈ range L, ‖(f n : ℂ)‖ ^ 2) ≤ E) :
    (m 1 : ℝ) ≤ (Real.log E + 4 * (weightMass N w : ℝ) * Real.log N -
      Real.log (Real.pi / (64 * (N : ℝ)))) / Real.log L := by
  have hLn : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have henergy := (minimal_integer_rootOne_energy_lower hw hMass hN m hm f hminimal hmt L hLn hlarge).trans hE
  have h := multiplicity_bound_of_energy (m 1) hmt (L : ℝ)
    (Real.pi / (64 * (N : ℝ))) (2 * (weightMass N w : ℝ) * Real.log N)
    E hL (by positivity) henergy
  convert h using 1
  ring

end Erdos345
