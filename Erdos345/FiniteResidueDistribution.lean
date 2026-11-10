import Erdos345.CyclicParseval

namespace Erdos345

theorem uniformMean_complex_cast {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    ((uniformMean f : ℝ) : ℂ) = uniformMean (fun ω => (f ω : ℂ)) := by
  unfold uniformMean
  push_cast
  rfl

noncomputable def residueMass {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) (r : ZMod q) : ℝ :=
  uniformMean (fun ω => if X ω = r then 1 else 0)

def residueSupport {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) : Finset (ZMod q) := Finset.univ.image X

theorem residueMass_nonneg {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) (r : ZMod q) : 0 ≤ residueMass X r := by
  apply uniformMean_nonneg
  intro ω
  split_ifs <;> norm_num

theorem residueMass_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) : (∑ r : ZMod q, residueMass X r) = 1 := by
  unfold residueMass
  rw [← uniformMean_sum]
  have heq : (fun ω : Ω => ∑ r : ZMod q, if X ω = r then (1 : ℝ) else 0) = fun _ => 1 := by
    funext ω
    simp
  rw [heq, uniformMean_const]

theorem residueMass_zero_outside {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) (r : ZMod q) (hr : r ∉ residueSupport X) : residueMass X r = 0 := by
  have hn : ∀ ω, X ω ≠ r := by
    intro ω h
    exact hr (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, h⟩)
  simp [residueMass, uniformMean, hn]

theorem residueMass_sum_support {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) : (∑ r ∈ residueSupport X, residueMass X r) = 1 := by
  refine Eq.trans ?_ (residueMass_sum X)
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  exact residueMass_zero_outside X r hr

theorem residueMass_fourier {Ω : Type*} [Fintype Ω] {q : ℕ} [NeZero q]
    (X : Ω → ZMod q) (h : ZMod q) :
    cyclicFourier (fun r => (residueMass X r : ℂ)) h =
      uniformMean (fun ω => ZMod.stdAddChar (h * X ω)) := by
  unfold cyclicFourier
  calc
    _ = ∑ r : ZMod q, uniformMean (fun ω : Ω =>
        if X ω = r then ZMod.stdAddChar (h * r) else (0 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro r _
      change ((uniformMean (fun ω : Ω => if X ω = r then (1 : ℝ) else 0) : ℝ) : ℂ) *
        ZMod.stdAddChar (h * r) = _
      rw [uniformMean_complex_cast, ← uniformMean_mul_const]
      congr 1
      funext ω
      split_ifs <;> simp
    _ = uniformMean (fun ω : Ω => ∑ r : ZMod q,
        if X ω = r then ZMod.stdAddChar (h * r) else (0 : ℂ)) := (uniformMean_sum _).symm
    _ = _ := by
      congr 1
      funext ω
      simp

end Erdos345
