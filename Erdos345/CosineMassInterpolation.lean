import Erdos345.MonotoneLayers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace Erdos345

def augmentFirstWeight (w : ℕ → ℕ) (r i : ℕ) : ℕ := w i + if i = 0 then r else 0

theorem augmentFirstWeight_antitone {N : ℕ} {w : ℕ → ℕ}
    (hw : AntitoneOn w (Set.Iio N)) (r : ℕ) :
    AntitoneOn (augmentFirstWeight w r) (Set.Iio N) := by
  intro i hi j hj hij
  have h := hw hi hj hij
  dsimp only [augmentFirstWeight]
  split_ifs <;> omega

theorem augmentFirstWeight_mass (N : ℕ) (hN : 0 < N) (w : ℕ → ℕ) (r : ℕ) :
    weightMass N (augmentFirstWeight w r) = weightMass N w + r := by
  classical
  simp [weightMass, augmentFirstWeight, Finset.sum_add_distrib, hN]

theorem augmentFirstWeight_evaluation (N : ℕ) (hN : 0 < N) (w : ℕ → ℕ) (r : ℕ) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (augmentFirstWeight w r i : ℝ) * g i) =
      (∑ i ∈ Finset.range N, (w i : ℝ) * g i) + (r : ℝ) * g 0 := by
  classical
  simp [augmentFirstWeight, Nat.cast_add, add_mul, Finset.sum_add_distrib, hN]

theorem augmentFirstWeight_cosine_nonneg (N : ℕ) (hN : 0 < N) (w : ℕ → ℕ) (a : ℝ)
    (hw : ∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range N,
      (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) (r : ℕ) :
    ∀ θ : ℝ, 0 ≤ (a + r) + ∑ i ∈ Finset.range N,
      (augmentFirstWeight w r i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
  intro θ
  rw [augmentFirstWeight_evaluation N hN w r]
  simp only [Nat.zero_add, Nat.cast_one, one_mul]
  have hb := hw θ
  have hc := Real.neg_one_le_cos θ
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith

/-- Finite exact-mass adjustment in the style of Belov--Konyagin
Lemma 2.1. Analytic positivity is a hypothesis here, not an asserted fact. -/
theorem interpolate_cosine_mass (N : ℕ) (hN : 0 < N) (w : ℕ → ℕ → ℕ) (a : ℕ → ℝ)
    (C : ℕ) (A : ℝ)
    (hzero : weightMass N (w 0) = 0)
    (hgrowth : ∀ m ≤ N, m ≤ weightMass N (w m))
    (hstep : ∀ m < N, weightMass N (w (m + 1)) ≤ weightMass N (w m) + C)
    (hmono : ∀ m ≤ N, AntitoneOn (w m) (Set.Iio N))
    (hpositive : ∀ m ≤ N, ∀ θ : ℝ, 0 ≤ a m + ∑ i ∈ Finset.range N,
      (w m i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ))
    (hcost : ∀ m ≤ N, a m ≤ A) :
    ∃ v : ℕ → ℕ, ∃ b : ℝ,
      AntitoneOn v (Set.Iio N) ∧ weightMass N v = N ∧
      (∀ θ : ℝ, 0 ≤ b + ∑ i ∈ Finset.range N,
        (v i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧ b ≤ A + C := by
  classical
  let S := (Finset.range (N + 1)).filter (fun m => weightMass N (w m) ≤ N)
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨by simp, by rw [hzero]; omega⟩⟩
  let m := S.max' hS
  have hmS : m ∈ S := Finset.max'_mem S hS
  have hmN : m ≤ N := by
    have hm := (Finset.mem_filter.mp hmS).1
    have hh := Finset.mem_range.mp hm
    omega
  have hmass : weightMass N (w m) ≤ N := (Finset.mem_filter.mp hmS).2
  let r := N - weightMass N (w m)
  have hr : r ≤ C := by
    by_cases heq : m = N
    · have hg := hgrowth m hmN
      dsimp only [r]
      omega
    · have hm : m < N := by omega
      have hnext : N < weightMass N (w (m + 1)) := by
        by_contra hh
        have hmem : m + 1 ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), by omega⟩
        have hle := Finset.le_max' S (m + 1) hmem
        change m + 1 ≤ m at hle
        omega
      have hs := hstep m hm
      dsimp only [r]
      omega
  refine ⟨augmentFirstWeight (w m) r, a m + r,
    augmentFirstWeight_antitone (hmono m hmN) r, ?_,
    augmentFirstWeight_cosine_nonneg N hN (w m) (a m) (hpositive m hmN) r, ?_⟩
  · rw [augmentFirstWeight_mass N hN]
    exact Nat.add_sub_of_le hmass
  · have ha := hcost m hmN
    have hrR : (r : ℝ) ≤ C := by exact_mod_cast hr
    linarith

end Erdos345
