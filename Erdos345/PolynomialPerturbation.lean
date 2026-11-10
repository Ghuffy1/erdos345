import Erdos345.MinimalComponentComparison

namespace Erdos345

open Finset Polynomial

theorem rootSlots_one (N : ℕ) (w : ℕ → ℕ) : rootSlots N w 1 = weightMass N w := by
  simp only [rootSlots, one_dvd, ite_true, weightMass]

theorem rational_polynomial_perturbation_components
    (S : Finset ℕ) (hS : ∀ t ∈ S, 0 < t) (h1 : 1 ∈ S)
    (m n M : ℕ → ℕ) (hm : ∀ t ∈ S, m t ≤ M t) (hn : ∀ t ∈ S, n t ≤ M t)
    (f g : ℕ → ℚ)
    (hminf : (cyclotomicProduct S m).map (Int.castRingHom ℚ) = minimalAnnihilator f)
    (hming : (cyclotomicProduct S n).map (Int.castRingHom ℚ) = minimalAnnihilator g)
    (a : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity m i)) → ℂ)
    (b : (Σ i : CyclotomicRootIndex S, Fin (cyclotomicRootMultiplicity n i)) → ℂ)
    (ha : (fun k => (f k : ℂ)) = ∑ ij, a ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (hb : (fun k => (g k : ℂ)) = ∑ ij, b ij • exponentialPower (cyclotomicRootValue ij.1) ij.2)
    (P : ℂ[X]) (hP : P.degree < M 1)
    (hfg : (fun k => (f k : ℂ)) + (fun k => (g k : ℂ)) = fun k : ℕ => P.eval (k : ℂ)) :
    (∀ t ∈ S, t ≠ 1 → m t = n t) ∧
      (∀ i : CyclotomicRootIndex S, (i.1 : ℕ) ≠ 1 → ∀ j : ℕ,
        ∀ hjm : j < m i.1, ∀ hjn : j < n i.1,
          a ⟨i, ⟨j, hjm⟩⟩ + b ⟨i, ⟨j, hjn⟩⟩ = 0) := by
  classical
  have hcf : linearFactorProduct (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m) =
      minimalAnnihilator (fun k => (f k : ℂ)) :=
    (cyclotomicProduct_split S m hS).trans (rational_minimal_cyclotomic_complex S m f hminf)
  have hcg : linearFactorProduct (@cyclotomicRootValue S) (cyclotomicRootMultiplicity n) =
      minimalAnnihilator (fun k => (g k : ℂ)) :=
    (cyclotomicProduct_split S n hS).trans (rational_minimal_cyclotomic_complex S n g hming)
  have hc := minimal_nonunit_component_comparison (@cyclotomicRootValue S)
    (cyclotomicRootMultiplicity m) (cyclotomicRootMultiplicity n) (cyclotomicRootMultiplicity M)
    (fun i => hm i.1 i.1.property) (fun i => hn i.1 i.1.property)
    (cyclotomicRootValue_injective S) (cyclotomicRootValue_ne_zero S hS)
    (unitCyclotomicIndex S h1) (unitCyclotomicIndex_value S h1) P hP
    (fun k => (f k : ℂ)) (fun k => (g k : ℂ)) hfg a b ha hb hcf hcg
  constructor
  · intro t ht ht1
    have hcard : (primitiveRoots t ℂ).card = t.totient :=
      (Complex.isPrimitiveRoot_exp t (Nat.ne_of_gt (hS t ht))).card_primitiveRoots
    have hpos : 0 < (primitiveRoots t ℂ).card := by rw [hcard]; exact Nat.totient_pos.mpr (hS t ht)
    obtain ⟨z, hz⟩ := card_pos.mp hpos
    let i : CyclotomicRootIndex S := ⟨⟨t, ht⟩, ⟨z, hz⟩⟩
    exact hc.1 i (cyclotomic_index_ne_unit S h1 i ht1)
  · intro i hi j hjm hjn
    exact hc.2 i (cyclotomic_index_ne_unit S h1 i hi) j hjm hjn

theorem complex_polynomial_sum_of_rational (f : ℕ → ℚ) (g : ℕ → ℤ) (P : ℚ[X])
    (hfg : ∀ n : ℕ, f n + (g n : ℚ) = P.eval (n : ℚ)) :
    (fun n => (f n : ℂ)) + (fun n => (g n : ℂ)) =
      fun n : ℕ => (P.map (algebraMap ℚ ℂ)).eval (n : ℂ) := by
  funext n
  have h := congrArg (algebraMap ℚ ℂ) (hfg n)
  have heval : (P.map (algebraMap ℚ ℂ)).eval (n : ℂ) = (algebraMap ℚ ℂ) (P.eval (n : ℚ)) := by
    rw [eval_map, ← map_natCast (algebraMap ℚ ℂ) n, eval₂_at_apply]
  change (f n : ℂ) + (g n : ℂ) = _
  rw [heval]
  simpa only [map_add, map_intCast, eq_ratCast] using h

end Erdos345
