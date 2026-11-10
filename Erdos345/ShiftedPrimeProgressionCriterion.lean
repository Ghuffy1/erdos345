import Erdos345.PrimeProgressionAsymptotics

namespace Erdos345

theorem nat_quotient_half_lower (X K : ℕ) (hK : 0 < K) (hX : 2 * K ≤ X) :
    (X : ℝ) / (2 * K) ≤ (X / K : ℕ) := by
  have hq : 1 ≤ X / K := Nat.div_pos (by omega) hK
  have hx := Nat.lt_mul_div_succ X hK
  have hb : X ≤ 2 * K * (X / K) := by nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
  have hb' : X ≤ (X / K) * (2 * K) := by simpa only [mul_comm] using hb
  exact_mod_cast hb'

/-- Many uniformly populated progression classes force one large shifted-prime fiber. -/
theorem shifted_prime_spike_of_many_progressions (K X C : ℕ) (D : Finset ℕ)
    (hK : 0 < K) (hX : 2 * K ≤ X)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ∣ K)
    (hAP : ∀ d ∈ D, (X : ℝ) / (2 * d.totient * Real.log X) ≤ (primesOneMod X d).card)
    (hlarge : 4 * (C : ℝ) * Real.log X < D.card) :
    ∃ n : ℕ, K ≤ n ∧ n ≤ X * X ∧ K ∣ n ∧ C < (shiftedPrimes n).card := by
  have hX2 : 2 ≤ X := by omega
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX2)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hq := nat_quotient_half_lower X K hK hX
  have hterm (d : ℕ) (hd : d ∈ D) :
      (X : ℝ) ^ 2 / (4 * K * Real.log X) ≤
        ((X / K : ℕ) : ℝ) * d.totient * (primesOneMod X d).card := by
    have hphi : (0 : ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr (show 0 < d by have := (hD d hd).1; omega)
    have hp := mul_le_mul_of_nonneg_left (hAP d hd)
      (show 0 ≤ ((X / K : ℕ) : ℝ) * d.totient by positivity)
    have hq' := mul_le_mul_of_nonneg_right hq
      (show 0 ≤ (X : ℝ) / (2 * Real.log X) by positivity)
    calc
      (X : ℝ) ^ 2 / (4 * K * Real.log X) =
          (X / (2 * K)) * (X / (2 * Real.log X)) := by ring
      _ ≤ ((X / K : ℕ) : ℝ) * (X / (2 * Real.log X)) := hq'
      _ = ((X / K : ℕ) : ℝ) * d.totient *
          (X / (2 * d.totient * Real.log X)) := by field_simp
      _ ≤ _ := hp
  have hsum := Finset.sum_le_sum (fun d hd => hterm d hd)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hfirst : ((X * X / K : ℕ) : ℝ) * C ≤ (X : ℝ) ^ 2 / K * C := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg C)
    apply (le_div_iff₀ hKR).mpr
    have hn : (X * X / K) * K ≤ X * X := Nat.div_mul_le_self _ _
    have hn' : (X * X / K) * K ≤ X ^ 2 := by simpa only [pow_two] using hn
    exact_mod_cast hn'
  have hstrict : (X : ℝ) ^ 2 / K * C <
      (D.card : ℝ) * ((X : ℝ) ^ 2 / (4 * K * Real.log X)) := by
    have hh := mul_lt_mul_of_pos_right hlarge
      (show 0 < (X : ℝ) ^ 2 / (4 * K * Real.log X) by positivity)
    convert hh using 1
    field_simp
  have hcountR : ((X * X / K : ℕ) : ℝ) * C <
      ∑ d ∈ D, ((X / K : ℕ) : ℝ) * d.totient * (primesOneMod X d).card :=
    (hfirst.trans_lt hstrict).trans_le hsum
  apply shifted_prime_spike_of_progression_counts K X C D hK hD
  exact_mod_cast hcountR

end Erdos345
