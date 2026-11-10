import Erdos345.FiniteExpectation

namespace Erdos345

def labelGroup {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (ω : ι → Fin M) (j : Fin M) : Finset ι := Finset.univ.filter (fun i => ω i = j)

theorem mem_labelGroup {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (ω : ι → Fin M) (j : Fin M) (i : ι) : i ∈ labelGroup ω j ↔ ω i = j := by
  simp only [labelGroup, Finset.mem_filter, Finset.mem_univ, true_and]

theorem labelGroup_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (ω : ι → Fin M) (j l : Fin M) (hjl : j ≠ l) : Disjoint (labelGroup ω j) (labelGroup ω l) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hjl (((mem_labelGroup ω j i).mp hi).symm.trans ((mem_labelGroup ω l i).mp hj))

theorem label_product_mean {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι]
    [Field 𝕂] [CharZero 𝕂] {M : ℕ} (j : Fin M) (w : ι → 𝕂) :
    uniformMean (fun ω : ι → Fin M => ∏ i ∈ labelGroup ω j, w i) =
      ∏ i, (1 - (1 - w i) / (M : 𝕂)) := by
  have heq : (fun ω : ι → Fin M => ∏ i ∈ labelGroup ω j, w i) =
      (fun ω : ι → Fin M => ∏ i, if ω i = j then w i else 1) := by
    funext ω
    simp only [labelGroup, Finset.prod_filter]
  rw [heq, uniformMean_pi_prod (fun (i : ι) (a : Fin M) => if a = j then w i else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Fintype.card_fin] using uniformMean_ite_eq j (w i)

theorem label_product_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℕ} (j : Fin M) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    uniformMean (fun ω : ι → Fin M => ∏ i ∈ labelGroup ω j, w i) ≤
      Real.exp (-(∑ i, (1 - w i)) / (M : ℝ)) := by
  rw [label_product_mean]
  have hfactor : ∀ i, 0 ≤ 1 - (1 - w i) / (M : ℝ) := by
    intro i
    have h := uniformMean_nonneg (fun a : Fin M => if a = j then w i else 1) (by
      intro a
      split_ifs
      · exact hw i
      · norm_num)
    simpa only [uniformMean_ite_eq, Fintype.card_fin] using h
  calc
    _ ≤ ∏ i, Real.exp (-((1 - w i) / (M : ℝ))) := by
      apply Finset.prod_le_prod₀ (fun i _ => hfactor i)
      intro i _
      exact Real.one_sub_le_exp_neg _
    _ = Real.exp (∑ i, -((1 - w i) / (M : ℝ))) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.sum_neg_distrib, ← Finset.sum_div]
      ring

theorem label_cosine_product_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℕ} (j : Fin M) (φ : ι → ℝ) :
    uniformMean (fun ω : ι → Fin M => ∏ i ∈ labelGroup ω j,
      Real.cos (Real.pi * φ i) ^ 2) ≤
      Real.exp (-(∑ i, Real.sin (Real.pi * φ i) ^ 2) / (M : ℝ)) := by
  have h := label_product_exp_bound j (fun i => Real.cos (Real.pi * φ i) ^ 2)
    (fun i => sq_nonneg _)
  have heq : ∀ i, 1 - Real.cos (Real.pi * φ i) ^ 2 = Real.sin (Real.pi * φ i) ^ 2 := by
    intro i
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * φ i)]
  simpa only [heq] using h

def sampledBases (R : Finset ℕ) {M : ℕ} (ω : R → Fin M) (j : Fin M) : Finset ℕ :=
  (labelGroup ω j).image (fun n => n.val)

theorem sampledBases_subset (R : Finset ℕ) {M : ℕ} (ω : R → Fin M) (j : Fin M) :
    sampledBases R ω j ⊆ R := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact i.prop

theorem sampledBases_disjoint (R : Finset ℕ) {M : ℕ} (ω : R → Fin M)
    (j l : Fin M) (hjl : j ≠ l) : Disjoint (sampledBases R ω j) (sampledBases R ω l) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  obtain ⟨i, hi, hni⟩ := Finset.mem_image.mp hn
  obtain ⟨v, hv, hnv⟩ := Finset.mem_image.mp hm
  have hiv : i = v := Subtype.ext (hni.trans hnv.symm)
  subst v
  exact Finset.disjoint_left.mp (labelGroup_disjoint ω j l hjl) hi hv

theorem prod_sampledBases {𝕂 : Type*} [CommMonoid 𝕂] (R : Finset ℕ) {M : ℕ}
    (ω : R → Fin M) (j : Fin M) (w : ℕ → 𝕂) :
    (∏ n ∈ sampledBases R ω j, w n) = ∏ i ∈ labelGroup ω j, w i.val := by
  apply Finset.prod_image
  intro i _ v _ hiv
  exact Subtype.ext hiv

end Erdos345
