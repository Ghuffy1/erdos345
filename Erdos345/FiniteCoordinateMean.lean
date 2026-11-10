import Erdos345.FiniteExpectation

namespace Erdos345

theorem uniformMean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun ω => f ω - g ω) = uniformMean f - uniformMean g := by
  simp only [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_comm {Ω Α : Type*} [Fintype Ω] [Fintype Α] (f : Ω → Α → ℝ) :
    uniformMean (fun ω => uniformMean (f ω)) =
      uniformMean (fun a => uniformMean (fun ω => f ω a)) := by
  simp only [uniformMean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm]

theorem uniformMean_pi_eval {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (i₀ : ι) (f : κ → ℝ) :
    uniformMean (fun ω : ι → κ => f (ω i₀)) = uniformMean f := by
  have hp := uniformMean_pi_prod (fun (i : ι) (a : κ) => if i = i₀ then f a else (1 : ℝ))
  have hleft : (fun ω : ι → κ => ∏ i, if i = i₀ then f (ω i) else (1 : ℝ)) =
      (fun ω : ι → κ => f (ω i₀)) := by
    funext ω
    simp
  have hlocal (i : ι) : uniformMean (fun a : κ => if i = i₀ then f a else (1 : ℝ)) =
      if i = i₀ then uniformMean f else 1 := by
    by_cases hi : i = i₀ <;> simp [hi, uniformMean_const]
  rw [hleft] at hp
  simp_rw [hlocal] at hp
  simpa using hp

/-- Distinct coordinates factor under the explicit uniform product
average. This is the only independence fact needed for the variance. -/
theorem uniformMean_pi_two {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (i j : ι) (hij : i ≠ j) (f g : κ → ℝ) :
    uniformMean (fun ω : ι → κ => f (ω i) * g (ω j)) = uniformMean f * uniformMean g := by
  have hp := uniformMean_pi_prod (fun (l : ι) (a : κ) =>
    (if l = i then f a else (1 : ℝ)) * (if l = j then g a else 1))
  have hleft : (fun ω : ι → κ => ∏ l,
      (if l = i then f (ω l) else (1 : ℝ)) * (if l = j then g (ω l) else 1)) =
      (fun ω : ι → κ => f (ω i) * g (ω j)) := by
    funext ω
    rw [Finset.prod_mul_distrib]
    simp
  have hlocal (l : ι) : uniformMean (fun a : κ =>
      (if l = i then f a else (1 : ℝ)) * (if l = j then g a else 1)) =
      (if l = i then uniformMean f else 1) * (if l = j then uniformMean g else 1) := by
    by_cases hli : l = i
    · subst l
      simp [hij]
    · by_cases hlj : l = j
      · subst l
        simp [hli]
      · simp [hli, hlj, uniformMean_const]
  rw [hleft] at hp
  simp_rw [hlocal] at hp
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq'] at hp
  exact hp

end Erdos345
