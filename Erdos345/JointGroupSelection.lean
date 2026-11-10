import Erdos345.SpanProbabilityDecay
import Erdos345.FiniteRowAverages
import Erdos345.SampledSupportProbability

namespace Erdos345

def groupLabel (j : Fin 128) : Fin 8192 := ⟨j.val, by omega⟩

theorem groupLabel_injective : Function.Injective groupLabel := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 8192 => x.val) h

def supportBad (R : Finset ℕ) (k : ℕ) (ω : R → Fin 8192) (j : Fin 128) (c : ℕ) : Prop :=
  ((representedResidues (sampledBases R ω (groupLabel j)) k (c ^ k)).card : ℝ) <
    ((c ^ k : ℕ) : ℝ) / 4

noncomputable def supportBadFraction (R C : Finset ℕ) (k : ℕ)
    (ω : R → Fin 8192) (j : Fin 128) : ℝ :=
  finiteRowMean C (fun ω c => eventIndicator (supportBad R k ω j c)) ω

/-- A single finite label assignment meets both the averaged support
condition and the span condition for all 128 groups. -/
theorem select_groups_with_support_and_span (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    (C : Finset ℕ) (hC : C.Nonempty)
    (hsupport : ∀ c ∈ C, ∀ j : Fin 128,
      uniformMean (fun ω : unreservedPopulation N k → Fin 8192 =>
        eventIndicator (supportBad (unreservedPopulation N k) k ω j c)) ≤ (1 : ℝ) / 4096)
    (hspan : (8192 : ℝ) * (k : ℝ) ^ 2 / N ≤ (1 : ℝ) / 4096) :
    ∃ ω : unreservedPopulation N k → Fin 8192, ∀ j : Fin 128,
      supportBadFraction (unreservedPopulation N k) C k ω j < (1 : ℝ) / 2 ∧
      sampledPowerSum (unreservedPopulation N k) k ω (groupLabel j) <
        4 * ((N : ℝ) ^ (k + 1) / ((8192 : ℝ) * k)) := by
  classical
  let R := unreservedPopulation N k
  let B := 4 * ((N : ℝ) ^ (k + 1) / ((8192 : ℝ) * k))
  let P := fun (z : Fin 128 × Bool) (ω : R → Fin 8192) =>
    if z.2 then B ≤ sampledPowerSum R k ω (groupLabel z.1)
    else (1 : ℝ) / 2 ≤ supportBadFraction R C k ω z.1
  have hprob : ∀ z : Fin 128 × Bool,
      uniformMean (fun ω : R → Fin 8192 => eventIndicator (P z ω)) ≤ (1 : ℝ) / 2048 := by
    rintro ⟨j, b⟩
    cases b
    · have hrow := mean_bad_row_le C hC (fun ω c => supportBad R k ω j c) (1 / 4096)
        (fun c hc => hsupport c hc j)
      change uniformMean (fun ω : R → Fin 8192 => eventIndicator
        ((1 : ℝ) / 2 ≤ supportBadFraction R C k ω j)) ≤ _
      exact hrow.trans (by norm_num)
    · have hs := (mean_large_span_le N k hk hkN (groupLabel j)).trans hspan
      change uniformMean (fun ω : R → Fin 8192 => eventIndicator
        (B ≤ sampledPowerSum R k ω (groupLabel j))) ≤ _
      exact hs.trans (by norm_num)
  have hsum : (∑ z : Fin 128 × Bool, uniformMean (fun ω : R → Fin 8192 => eventIndicator (P z ω))) < 1 := by
    have h := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin 128 × Bool))) => hprob z)
    norm_num at h
    linarith
  obtain ⟨ω, hω⟩ := finite_bad_event_selection P hsum
  refine ⟨ω, ?_⟩
  intro j
  have hs := hω (j, false)
  have hb := hω (j, true)
  exact ⟨lt_of_not_ge hs, lt_of_not_ge hb⟩

/-- Conditional on cosine existence, each sufficiently large dyadic
interval contains a degree supporting 128 disjoint groups. Every group
has controlled span and is good for at least half of any chosen finite
nonempty collection of candidate moduli c^k with 0<c<=N(k). -/
theorem good_degrees_selected_groups
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ C : Finset ℕ, C.Nonempty → (∀ c ∈ C, 0 < c ∧ c ≤ fourierN k) →
        ∃ G : Fin 128 → Finset ℕ,
          (∀ j, G j ⊆ unreservedPopulation (fourierN k) k) ∧
          (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧
          (∀ j, (∑ n ∈ G j, (n : ℝ) ^ k) <
            4 * ((fourierN k : ℝ) ^ (k + 1) / ((8192 : ℝ) * k))) ∧
          (∀ j, (C.card : ℝ) / 2 ≤
            ((C.filter (fun c => ((c ^ k : ℕ) : ℝ) / 4 ≤ (representedResidues (G j) k (c ^ k)).card)).card : ℝ)) := by
  classical
  obtain ⟨K₁, hK₁⟩ := good_degrees_label_support_small hinput (1 / 4096) (by norm_num)
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.mp (eventually_span_failure_small (1 / 4096) (by norm_num))
  refine ⟨max 20 (max K₁ K₂), ?_⟩
  intro Y hY
  obtain ⟨k, hkY, hk2Y, hsupport⟩ := hK₁ Y (by omega)
  have hk : 0 < k := by omega
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro C hC hCN
  obtain ⟨ω, hω⟩ := select_groups_with_support_and_span (fourierN k) k hk (degree_le_fourierN k) C hC
    (fun c hc j => (hsupport c (hCN c hc).1 (hCN c hc).2 (groupLabel j)).le)
    (hK₂ k (by omega)).le
  let G := fun j : Fin 128 => sampledBases (unreservedPopulation (fourierN k) k) ω (groupLabel j)
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro j
    exact sampledBases_subset _ _ _
  · intro i j hij
    exact sampledBases_disjoint _ _ _ _ (fun h => hij (groupLabel_injective h))
  · intro j
    exact (hω j).2
  · intro j
    have hhalf := complement_filter_half C hC
      (supportBad (unreservedPopulation (fourierN k) k) k ω j) (hω j).1
    simpa only [supportBad, not_lt] using hhalf

end Erdos345
