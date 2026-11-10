import Erdos345.PrimePowerConjugateNorm

namespace Erdos345

open Finset

theorem primitive_power_norm_coprime_invariant
    (n a u : ℕ) (hn : 0 < n) (hu : u.Coprime n) :
    (∏ w ∈ primitiveRoots n ℂ, ‖w ^ (a * u) - 1‖) =
      ∏ w ∈ primitiveRoots n ℂ, ‖w ^ a - 1‖ := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [← prod_coe_sort (primitiveRoots n ℂ) (fun w : ℂ => ‖w ^ (a * u) - 1‖),
    ← prod_coe_sort (primitiveRoots n ℂ) (fun w : ℂ => ‖w ^ a - 1‖)]
  apply Fintype.prod_equiv (IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime (R := ℂ) hu)
  intro w
  simp only [IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime_apply_coe, ← pow_mul,
    Nat.mul_comm a u]

/-- The nonvanishing factor at a prime-power root has the exact conjugate
product dictated by the prime valuation of its exponent. -/
theorem primePower_general_power_norm_product
    (p k h : ℕ) (hp : p.Prime) (hh : 0 < h) (hnot : ¬p ^ (k + 1) ∣ h) :
    (∏ w ∈ primitiveRoots (p ^ (k + 1)) ℂ, ‖w ^ h - 1‖) =
      (p : ℝ) ^ (p ^ h.factorization p) := by
  let s := h.factorization p
  let u := h / p ^ s
  have hdecomp : p ^ s * u = h := Nat.ordProj_mul_ordCompl_eq_self h p
  have hcoprime : u.Coprime (p ^ (k + 1)) :=
    (Nat.coprime_ordCompl hp (Nat.ne_of_gt hh)).symm.pow_right _
  have hs : s ≤ k := by
    by_contra hsk
    have hle : k + 1 ≤ h.factorization p := by dsimp only [s] at hsk; omega
    exact hnot ((hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hh)).mpr hle)
  have heq := primitive_power_norm_coprime_invariant (p ^ (k + 1)) (p ^ s) u
    (pow_pos hp.pos _) hcoprime
  rw [hdecomp] at heq
  exact heq.trans (primePower_pure_power_norm_product p k s hp hs)

end Erdos345
