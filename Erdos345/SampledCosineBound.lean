import Erdos345.LabelSampling
import Erdos345.FourierDecayLimit

namespace Erdos345

noncomputable def subsetCosineProduct (G : Finset ℕ) (k q h : ℕ) : ℝ :=
  ∏ n ∈ G, Real.cos (Real.pi * ((h : ℝ) / q * (n : ℝ) ^ k)) ^ 2

noncomputable def subsetCosineSum (G : Finset ℕ) (k q : ℕ) : ℝ :=
  ∑ h ∈ nonzeroFrequencies q, subsetCosineProduct G k q h

theorem subsetCosineProduct_nonneg (G : Finset ℕ) (k q h : ℕ) :
    0 ≤ subsetCosineProduct G k q h := Finset.prod_nonneg (fun _ _ => sq_nonneg _)

theorem subsetCosineSum_nonneg (G : Finset ℕ) (k q : ℕ) :
    0 ≤ subsetCosineSum G k q := Finset.sum_nonneg (fun h _ => subsetCosineProduct_nonneg G k q h)

theorem mean_sampled_cosineProduct_le (R : Finset ℕ) (k q h : ℕ) {M : ℕ} (j : Fin M) :
    uniformMean (fun ω : R → Fin M => subsetCosineProduct (sampledBases R ω j) k q h) ≤
      Real.exp (-finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) / M) := by
  calc
    _ = uniformMean (fun ω : R → Fin M => ∏ i ∈ labelGroup ω j,
        Real.cos (Real.pi * ((h : ℝ) / q * (i.val : ℝ) ^ k)) ^ 2) := by
      congr 1
      funext ω
      exact prod_sampledBases R ω j _
    _ ≤ Real.exp (-(∑ i : R, Real.sin (Real.pi * ((h : ℝ) / q * (i.val : ℝ) ^ k)) ^ 2) / M) :=
      label_cosine_product_bound j (fun i : R => (h : ℝ) / q * (i.val : ℝ) ^ k)
    _ = _ := by
      have hs : (∑ i : R, Real.sin (Real.pi * ((h : ℝ) / q * (i.val : ℝ) ^ k)) ^ 2) =
          finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) :=
        Finset.sum_coe_sort R (fun n : ℕ => Real.sin (Real.pi * ((h : ℝ) / q * (n : ℝ) ^ k)) ^ 2)
      rw [hs]

/-- The expected cosine collision expression for the independently
labelled group is controlled by the actual population energy. -/
theorem mean_sampled_cosineSum_le (R : Finset ℕ) (k q : ℕ) {M : ℕ} (j : Fin M)
    (H : ℝ) (hH : ∀ h ∈ nonzeroFrequencies q,
      H ≤ finiteSineEnergy R (fun n => (h : ℝ) / q * (n : ℝ) ^ k)) :
    uniformMean (fun ω : R → Fin M => subsetCosineSum (sampledBases R ω j) k q) ≤
      (q : ℝ) * Real.exp (-H / M) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M from j.isLt.trans_le' (Nat.zero_le _))
  change uniformMean (fun ω : R → Fin M => ∑ h ∈ nonzeroFrequencies q,
    subsetCosineProduct (sampledBases R ω j) k q h) ≤ _
  rw [uniformMean_finset_sum]
  calc
    _ ≤ ∑ _h ∈ nonzeroFrequencies q, Real.exp (-H / M) := by
      apply Finset.sum_le_sum
      intro h hh
      apply (mean_sampled_cosineProduct_le R k q h j).trans
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (neg_le_neg (hH h hh)) hM.le
    _ = ((nonzeroFrequencies q).card : ℝ) * Real.exp (-H / M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_nonzeroFrequencies_le q) (Real.exp_nonneg _)

theorem mean_label_cosine_decay_of_parameters (C : ℝ) (k : ℕ) (w : ℕ → ℕ)
    (hp : FourierParameterConditions C k w)
    (hw : AntitoneOn w (Set.Iio (k + 1))) (hmass : weightMass (k + 1) w = k + 1)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      (k : ℝ) ^ 2 < centerEnergy k u b (quasipolynomialCenterPrefix k C))
    (c : ℕ) (hc : 0 < c) (hcN : c ≤ fourierN k) (j : Fin 8192) :
    uniformMean (fun ω : unreservedPopulation (fourierN k) k → Fin 8192 =>
      subsetCosineSum (sampledBases (unreservedPopulation (fourierN k) k) ω j) k (c ^ k)) ≤
        Real.exp (-(k : ℝ) * logScale k ^ 8) := by
  have he := mean_sampled_cosineSum_le (unreservedPopulation (fourierN k) k) k (c ^ k) j
    (fourierH k - 257) (fun h hh =>
      (uniform_energy_of_parameters C k w hp hw hmass hcenter c hc hcN h hh).le)
  have hk0 : 0 < k := by have := hp.degree_large; omega
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hlogc : Real.log (c : ℝ) ≤ logScale k ^ 8 + 2 :=
    (Real.log_le_log hcR (by exact_mod_cast hcN)).trans (log_fourierN_le k)
  have hlogq : Real.log ((c ^ k : ℕ) : ℝ) ≤ (k : ℝ) * (logScale k ^ 8 + 2) := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left hlogc hkR
  have hK8 : 1 ≤ logScale k ^ 8 := one_le_pow₀ (logScale_ge_one k hk0)
  have hKk := mul_le_mul_of_nonneg_left hK8 hkR
  have hbudget : Real.log ((c ^ k : ℕ) : ℝ) + -(fourierH k - 257) / (8192 : ℝ) ≤
      -(k : ℝ) * logScale k ^ 8 := by
    unfold fourierH
    nlinarith only [hlogq, hKk]
  exact he.trans (nat_mul_exp_le_exp (c ^ k) _ _ hbudget)

end Erdos345
