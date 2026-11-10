import Erdos345.NonnegativeSineTail
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Archimedean.Basic

namespace Erdos345

def belovLevelPrimes (q j : ℕ) : Finset ℕ := (Nat.primesLE (q * (j + 1) ^ 2)).erase 2

noncomputable def belovMultiplicity (j : ℕ) : ℕ := 1 + ⌊Real.log ((j + 1 : ℕ) : ℝ)⌋₊

noncomputable def belovSineLevel (q j : ℕ) (x : ℝ) : ℝ :=
  dyadicSineLevel (belovLevelPrimes q) belovMultiplicity j x

noncomputable def belovSineTotal (q : ℕ) (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) + ∑' j, belovSineLevel q j x

theorem belovLevelPrimes_subset (q j : ℕ) : belovLevelPrimes q j ⊆ Finset.Icc 1 (q * (j + 1) ^ 2) := by
  intro p hp
  have hmem := Nat.mem_primesLE.mp (Finset.mem_of_mem_erase hp)
  exact Finset.mem_Icc.mpr ⟨hmem.2.one_le, hmem.1⟩

theorem belovLevelPrimes_zero_nonempty (q : ℕ) (hq : 3 ≤ q) : (belovLevelPrimes q 0).Nonempty := by
  refine ⟨3, Finset.mem_erase.mpr ⟨by decide, ?_⟩⟩
  apply Nat.mem_primesLE.mpr
  exact ⟨by simpa using hq, Nat.prime_three⟩

theorem belovMultiplicity_zero : belovMultiplicity 0 = 1 := by simp [belovMultiplicity]

theorem belovMultiplicity_le (j : ℕ) : belovMultiplicity j ≤ j + 1 := by
  have hnon : 0 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j + 1 by omega))
  have hfloor := Nat.floor_le hnon
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))
  have hh : (⌊Real.log ((j + 1 : ℕ) : ℝ)⌋₊ : ℝ) ≤ j := by
    push_cast at hlog hfloor ⊢
    linarith
  have hn : ⌊Real.log ((j + 1 : ℕ) : ℝ)⌋₊ ≤ j := by exact_mod_cast hh
  unfold belovMultiplicity
  omega

theorem summable_belovSineLevels (q : ℕ) (x : ℝ) : Summable (fun j => belovSineLevel q j x) :=
  summable_dyadicSineLevels (belovLevelPrimes q) belovMultiplicity q x
    (belovLevelPrimes_subset q) belovMultiplicity_le

theorem belovSineTotal_pos_small (q : ℕ) (hq : 3 ≤ q) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < belovSineTotal q x :=
  dyadicSineTotal_pos_small (belovLevelPrimes q) belovMultiplicity q
    (belovLevelPrimes_subset q) belovMultiplicity_le
    (belovLevelPrimes_zero_nonempty q hq) belovMultiplicity_zero hx hx1

theorem belovSineLevels_nonnegative_tail (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℕ, ∀ j, r ≤ j → 0 ≤ belovSineLevel q j x := by
  have ht : Filter.Tendsto (fun r : ℕ => (2 : ℝ) ^ r) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop x)
  have hpow : (2 : ℝ) ^ r ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨r, ?_⟩
  intro j hj
  apply dyadicSineLevel_nonneg_tail (belovLevelPrimes q) belovMultiplicity r j x hx hj ((hr r le_rfl).trans hpow)
  intro p hp
  exact (Finset.mem_Icc.mp (belovLevelPrimes_subset q j hp)).1

theorem belovSineTotal_ge_prefix (q r : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxr : x ≤ 2 ^ (r + 1)) :
    Real.sin (Real.pi * x) + (∑ j ∈ Finset.range r, belovSineLevel q j x) ≤ belovSineTotal q x := by
  apply add_le_add_right
  apply tsum_ge_initial_sum_of_nonnegative_tail _ (summable_belovSineLevels q x) r
  intro j hj
  apply dyadicSineLevel_nonneg_tail (belovLevelPrimes q) belovMultiplicity r j x hx hj hxr
  intro p hp
  exact (Finset.mem_Icc.mp (belovLevelPrimes_subset q j hp)).1

end Erdos345
