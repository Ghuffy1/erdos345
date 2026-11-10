import Erdos345.ExponentialSequences
import Mathlib.LinearAlgebra.DFinsupp

namespace Erdos345

open Polynomial

theorem exponentialPower_mem_genEigenspace {K : Type*} [Field K]
    (z : K) (j : ℕ) :
    exponentialPower z j ∈ (sequenceShift K).genEigenspace z ⊤ := by
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨j + 1, ?_⟩
  change ((sequenceShift K - z • 1) ^ (j + 1)) (exponentialPower z j) = 0
  have h := exponentialPower_annihilate z j (j + 1) (Nat.lt_succ_self j)
  simpa only [shiftAction, map_pow, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] using h

theorem independent_submodules_linearIndependent_sigma
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    {J : I → Type*} [∀ i, Fintype (J i)] (P : I → Submodule K V)
    (hind : iSupIndep P) (v : ∀ i, J i → V)
    (hmem : ∀ i j, v i j ∈ P i)
    (hli : ∀ i, LinearIndependent K (v i)) :
    LinearIndependent K (fun ij : Sigma J => v ij.1 ij.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc ij
  have htotal : (∑ i, ∑ j, c ⟨i, j⟩ • v i j) = 0 := by
    simpa only [Fintype.sum_sigma] using hc
  have hzero (i : I) : (∑ j, c ⟨i, j⟩ • v i j) = 0 := by
    apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero P).mp hind Finset.univ
      (fun i => ∑ j, c ⟨i, j⟩ • v i j) _ htotal i (Finset.mem_univ i)
    intro a _
    exact (P a).sum_mem (fun b _ => (P a).smul_mem _ (hmem a b))
  exact (Fintype.linearIndependent_iff.mp (hli ij.1) (fun j => c ⟨ij.1, j⟩) (hzero ij.1)) ij.2

/-- Distinct nonzero roots, each with its finite polynomial degrees, give a
linearly independent family of exponential-polynomial sequences. -/
theorem exponentialPower_family_linearIndependent
    {K I : Type*} [Field K] [CharZero K] [Fintype I]
    (z : I → K) (m : I → ℕ) (hinj : Function.Injective z) (hz : ∀ i, z i ≠ 0) :
    LinearIndependent K (fun ij : (Σ i, Fin (m i)) => exponentialPower (z ij.1) ij.2) := by
  have hind : iSupIndep (fun i => (sequenceShift K).genEigenspace (z i) ⊤) :=
    ((sequenceShift K).independent_genEigenspace ⊤).comp hinj
  apply independent_submodules_linearIndependent_sigma (J := fun i => Fin (m i))
    (fun i => (sequenceShift K).genEigenspace (z i) ⊤) hind
    (fun i (j : Fin (m i)) => exponentialPower (z i) j)
  · intro i j
    exact exponentialPower_mem_genEigenspace (z i) j
  · intro i
    exact exponentialPower_linearIndependent (z i) (hz i) (m i)

end Erdos345
