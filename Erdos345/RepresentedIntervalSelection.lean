import Erdos345.GcdOneGroupSelection
import Erdos345.GroupRepresentation
import Erdos345.FiniteFamilyInterval
import Erdos345.SharpIntervalParameters

namespace Erdos345

open scoped Classical Pointwise

/-- The actual 128 disjoint groups give a represented interval long
enough for infinite tail completion. Only cosine existence is assumed. -/
theorem good_degrees_represented_interval
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k a L : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧ 2 * k ≤ fourierN k + 1 ∧
      representedInterval k (fourierN k) a L ∧
      (fourierN k + 1) ^ k ≤ L ∧ a ≤ 256 * (fourierN k) ^ (k + 1) := by
  classical
  obtain ⟨K, hK⟩ := good_degrees_gcd_one_groups hinput
  refine ⟨K, ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hk20, hlarge, J, hsub, hdisj, hcard, hspan, hprogression⟩ := hK Y hY
  let N := fourierN k
  let s := reserveGroupSize N k
  let m := s * N ^ k
  let A := fun j : Fin 128 => finitePowerSums (J j) k
  have hN : 40960 ≤ N := by dsimp only [N]; omega
  have hs : 4 ≤ s := by
    change 4 ≤ N / (512 * k)
    apply (Nat.le_div_iff_mul_le (show 0 < 512 * k by omega)).mpr
    dsimp only [N]
    omega
  have hp : N ≤ N ^ k := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (show 1 ≤ N by omega) (show 1 ≤ k by omega))
  have hm : 1536 ≤ m := by
    have hh := Nat.mul_le_mul_right (N ^ k) (show 1 ≤ s by omega)
    dsimp only [m]
    omega
  obtain ⟨hn, hratio⟩ := sharp_interval_ratio m hm
  have hbound : ∀ j, A j ⊆ Finset.Icc 0 (2 * m) := by
    intro j
    apply finitePowerSums_subset_interval
    have hb : ((∑ b ∈ J j, b ^ k : ℕ) : ℝ) < ((2 * m : ℕ) : ℝ) := by
      simpa only [m, s, N, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
        Nat.cast_pow, mul_assoc] using hspan j
    exact_mod_cast hb.le
  have hcardA : ∀ j, m / 16 ≤ (A j).card := by
    intro j
    have hb : (m : ℝ) / 16 ≤ (A j).card := by
      simpa only [A, m, s, N, Nat.cast_mul, Nat.cast_pow] using hcard j
    have hfloor : ((m / 16 : ℕ) : ℝ) ≤ (m : ℝ) / 16 := Nat.cast_div_le
    exact_mod_cast hfloor.trans hb
  obtain ⟨a, L, hL, hI⟩ := interval_for_128_sets A (m / 16) (2 * m) (by omega)
    hcardA (fun j => zero_mem_finitePowerSums (J j) k) hprogression hbound hratio
  have hrep : representedInterval k N a L := by
    intro g hga hgL
    have hg := hI g (Finset.mem_Icc.mpr ⟨hga, hgL⟩)
    obtain ⟨f, hf, hsum⟩ := (mem_indexed_sumset Finset.univ A g).mp hg
    rw [← hsum]
    exact representedUpTo_of_group_sums J k N hsub hdisj f (fun j => hf j (Finset.mem_univ _))
  have hnext : (N + 1) ^ k ≤ L :=
    (lev_interval_covers_next_power N k s (by omega) (by omega)
      (by dsimp only [N]; omega) hs).trans hL
  have haS := hI a (by simp)
  have haBound := (Finset.mem_Icc.mp
    (indexed_sumset_bound Finset.univ A (fun _ => 2 * m) (fun j _ => hbound j) haS)).2
  have ha : a ≤ 256 * N ^ (k + 1) := by
    have ha' : a ≤ 128 * (2 * m) := by simpa using haBound
    have hsN : s ≤ N := Nat.div_le_self N (512 * k)
    calc
      a ≤ 128 * (2 * m) := ha'
      _ = 256 * (s * N ^ k) := by dsimp only [m]; ring
      _ ≤ 256 * (N * N ^ k) := Nat.mul_le_mul_left 256 (Nat.mul_le_mul_right (N ^ k) hsN)
      _ = 256 * N ^ (k + 1) := by rw [pow_succ]; ring
  exact ⟨k, a, L, hkY, hk2Y, hk20, by dsimp only [N] at *; omega, hrep, hnext, ha⟩

end Erdos345
