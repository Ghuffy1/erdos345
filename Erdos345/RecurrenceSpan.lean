import Erdos345.ExponentialIndependence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Erdos345

open Finset Polynomial

noncomputable def recurrenceKernel {K : Type*} [Field K] (p : K[X]) :
    Submodule K (ℕ → K) := LinearMap.ker (shiftAction p)

noncomputable def recurrenceInitialMap {K : Type*} [Field K] (p : K[X]) :
    recurrenceKernel p →ₗ[K] (Fin p.natDegree → K) where
  toFun f i := f.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem recurrenceInitialMap_injective {K : Type*} [Field K]
    (p : K[X]) (hp : p.Monic) : Function.Injective (recurrenceInitialMap p) := by
  intro f g heq
  apply Subtype.ext
  exact eq_of_recurrence_initial p p.natDegree le_rfl
    (by simp only [coeff_natDegree, hp.leadingCoeff, one_pow]) f.val g.val f.property g.property
    (fun n hn => congrFun heq ⟨n, hn⟩)

theorem recurrenceKernel_finrank_le {K : Type*} [Field K] (p : K[X]) (hp : p.Monic) :
    Module.finrank K (recurrenceKernel p) ≤ p.natDegree := by
  have h := (recurrenceInitialMap p).finrank_le_finrank_of_injective
    (recurrenceInitialMap_injective p hp)
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, Nat.mul_one] using h

/-- A linearly independent family of the full recurrence order spans all
solutions. The finite-dimensional assertion follows from recurrence uniqueness. -/
theorem recurrence_expansion_of_card {K I : Type*} [Field K] [Fintype I]
    (p : K[X]) (hp : p.Monic) (v : I → ℕ → K)
    (hsol : ∀ i, shiftAction p (v i) = 0) (hli : LinearIndependent K v)
    (hcard : Fintype.card I = p.natDegree)
    (f : ℕ → K) (hf : shiftAction p f = 0) :
    ∃ c : I → K, f = ∑ i, c i • v i := by
  classical
  let w : I → recurrenceKernel p := fun i => ⟨v i, hsol i⟩
  have hw : LinearIndependent K w := hli.of_comp (recurrenceKernel p).subtype
  let : FiniteDimensional K (recurrenceKernel p) :=
    FiniteDimensional.of_injective (recurrenceInitialMap p) (recurrenceInitialMap_injective p hp)
  have hlower := hw.fintype_card_le_finrank
  have hupper := recurrenceKernel_finrank_le p hp
  have hdimension : Fintype.card I = Module.finrank K (recurrenceKernel p) := by omega
  have htop := hw.span_eq_top_of_card_eq_finrank' hdimension
  have hmem : (⟨f, hf⟩ : recurrenceKernel p) ∈ Submodule.span K (Set.range w) := by
    rw [htop]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  refine ⟨c, ?_⟩
  have hval := congrArg (recurrenceKernel p).subtype hc
  simpa [map_sum, map_smul, w] using hval.symm

noncomputable def linearFactorProduct {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) : K[X] := ∏ i, (X - C (z i)) ^ m i

theorem linearFactorProduct_monic {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) : (linearFactorProduct z m).Monic := by
  apply monic_prod_of_monic
  intro i _
  exact (monic_X_sub_C (z i)).pow (m i)

theorem linearFactorProduct_natDegree {K I : Type*} [Field K] [Fintype I]
    (z : I → K) (m : I → ℕ) : (linearFactorProduct z m).natDegree = ∑ i, m i := by
  rw [linearFactorProduct, natDegree_prod_of_monic]
  · apply sum_congr rfl
    intro i _
    simp only [natDegree_pow, natDegree_X_sub_C, Nat.mul_one]
  · intro i _
    exact (monic_X_sub_C (z i)).pow (m i)

theorem linearFactorProduct_annihilates_component
    {K I : Type*} [Field K] [Fintype I] (z : I → K) (m : I → ℕ)
    (i : I) (j : Fin (m i)) :
    shiftAction (linearFactorProduct z m) (exponentialPower (z i) j) = 0 := by
  have hdiv : (X - C (z i)) ^ m i ∣ linearFactorProduct z m :=
    dvd_prod_of_mem _ (mem_univ i)
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, mul_comm, shiftAction_mul, exponentialPower_annihilate (z i) j (m i) j.is_lt,
    shiftAction_zero_sequence]

/-- Every solution of a split recurrence with distinct nonzero roots has its
full exponential-polynomial expansion, including repeated-root degrees. -/
theorem split_recurrence_expansion {K I : Type*} [Field K] [CharZero K] [Fintype I]
    (z : I → K) (m : I → ℕ) (hinj : Function.Injective z) (hz : ∀ i, z i ≠ 0)
    (f : ℕ → K) (hf : shiftAction (linearFactorProduct z m) f = 0) :
    ∃ c : (Σ i, Fin (m i)) → K,
      f = ∑ ij, c ij • exponentialPower (z ij.1) ij.2 := by
  apply recurrence_expansion_of_card (linearFactorProduct z m) (linearFactorProduct_monic z m)
    (fun ij : (Σ i, Fin (m i)) => exponentialPower (z ij.1) ij.2)
  · intro ij
    exact linearFactorProduct_annihilates_component z m ij.1 ij.2
  · exact exponentialPower_family_linearIndependent z m hinj hz
  · simp only [Fintype.card_sigma, Fintype.card_fin, linearFactorProduct_natDegree]
  · exact hf

end Erdos345
