import Erdos345.ExpansionComparison

namespace Erdos345

open Finset Polynomial

theorem minimal_nonunit_component_comparison {K I : Type*} [Field K] [CharZero K]
    [Fintype I] [DecidableEq I]
    (z : I → K) (m n M : I → ℕ) (hm : ∀ i, m i ≤ M i) (hn : ∀ i, n i ≤ M i)
    (hinj : Function.Injective z) (hz : ∀ i, z i ≠ 0)
    (i₀ : I) (hroot : z i₀ = 1) (P : K[X]) (hP : P.degree < M i₀)
    (f g : ℕ → K) (hfP : f + g = fun j : ℕ => P.eval (j : K))
    (a : (Σ i, Fin (m i)) → K) (b : (Σ i, Fin (n i)) → K)
    (ha : f = ∑ ij, a ij • exponentialPower (z ij.1) ij.2)
    (hb : g = ∑ ij, b ij • exponentialPower (z ij.1) ij.2)
    (hminf : linearFactorProduct z m = minimalAnnihilator f)
    (hming : linearFactorProduct z n = minimalAnnihilator g) :
    (∀ i, i ≠ i₀ → m i = n i) ∧
      (∀ i, i ≠ i₀ → ∀ j : ℕ, ∀ hjm : j < m i, ∀ hjn : j < n i,
        a ⟨i, ⟨j, hjm⟩⟩ + b ⟨i, ⟨j, hjn⟩⟩ = 0) := by
  have ha' : f = ∑ ij : (Σ i, Fin (M i)), padExpansionCoefficient a ij •
      exponentialPower (z ij.1) ij.2 := by rw [pad_exponential_expansion z m M hm a]; exact ha
  have hb' : g = ∑ ij : (Σ i, Fin (M i)), padExpansionCoefficient b ij •
      exponentialPower (z ij.1) ij.2 := by rw [pad_exponential_expansion z n M hn b]; exact hb
  have hcompare := nonunit_expansion_sum_zero z M hinj hz i₀ hroot P hP f g hfP
    (padExpansionCoefficient a) (padExpansionCoefficient b) ha' hb'
  constructor
  · intro i hi
    apply multiplicities_eq_of_padded_sum_zero (fun j => a ⟨i, j⟩) (fun j => b ⟨i, j⟩)
      (hm i) (hn i)
    · intro hp
      exact minimal_split_expansion_top_ne_zero z m f hminf a ha i hp
    · intro hp
      exact minimal_split_expansion_top_ne_zero z n g hming b hb i hp
    · intro j
      exact hcompare i hi j
  · intro i hi j hjm hjn
    have hjM : j < M i := hjm.trans_le (hm i)
    have h := hcompare i hi ⟨j, hjM⟩
    simpa only [padExpansionCoefficient, padFin, dite_eq_left hjm, dite_eq_left hjn] using h

theorem rational_minimal_cyclotomic_complex
    (S : Finset ℕ) (m : ℕ → ℕ) (f : ℕ → ℚ)
    (hminimal : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f) :
    (cyclotomicProduct S m).map (Int.castRingHom ℂ) =
      minimalAnnihilator (fun n => (f n : ℂ)) := by
  have hf : shiftAction ((cyclotomicProduct S m).map (Int.castRingHom ℚ)) f = 0 := by
    rw [hminimal]
    exact minimalAnnihilator_annihilates f
  have hb := minimalAnnihilator_map (L := ℂ) f ((cyclotomicProduct S m).map (Int.castRingHom ℚ))
    ((cyclotomicProduct_monic S m).map _) hf
  rw [← hminimal, Polynomial.map_map] at hb
  exact hb

noncomputable def unitCyclotomicIndex (S : Finset ℕ) (hS : 1 ∈ S) : CyclotomicRootIndex S :=
  ⟨⟨1, hS⟩, ⟨1, by simp [IsPrimitiveRoot.primitiveRoots_one]⟩⟩

theorem unitCyclotomicIndex_value (S : Finset ℕ) (hS : 1 ∈ S) :
    cyclotomicRootValue (unitCyclotomicIndex S hS) = 1 := rfl

theorem cyclotomic_index_ne_unit (S : Finset ℕ) (hS : 1 ∈ S)
    (i : CyclotomicRootIndex S) (hi : (i.1 : ℕ) ≠ 1) : i ≠ unitCyclotomicIndex S hS := by
  intro heq
  have h := congrArg (fun j : CyclotomicRootIndex S => (j.1 : ℕ)) heq
  exact hi h

end Erdos345
