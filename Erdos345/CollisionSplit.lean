import Erdos345.CosineCollision

namespace Erdos345

/-- Split a Fourier sum into an exceptional set and its complement,
retaining different energy bounds and the actual exceptional count. -/
theorem sum_cosineMean_pow_split (R S A : Finset ℕ) (hR : R.Nonempty) (hAS : A ⊆ S)
    (f : ℕ → ℕ → ℝ) (t : ℕ) (Hhigh Hlow : ℝ)
    (hhigh : ∀ h ∈ S \ A, Hhigh ≤ finiteSineEnergy R (f h))
    (hlow : ∀ h ∈ A, Hlow ≤ finiteSineEnergy R (f h)) :
    (∑ h ∈ S, finiteCosineMean R (f h) ^ t) ≤
      S.card * Real.exp (-(t : ℝ) * Hhigh / R.card) +
      A.card * Real.exp (-(t : ℝ) * Hlow / R.card) := by
  classical
  have hsplit : (∑ h ∈ S \ A, finiteCosineMean R (f h) ^ t) +
      (∑ h ∈ A, finiteCosineMean R (f h) ^ t) =
      ∑ h ∈ S, finiteCosineMean R (f h) ^ t := Finset.sum_sdiff hAS
  calc
    _ = (∑ h ∈ S \ A, finiteCosineMean R (f h) ^ t) +
        (∑ h ∈ A, finiteCosineMean R (f h) ^ t) := hsplit.symm
    _ ≤ (S \ A).card * Real.exp (-(t : ℝ) * Hhigh / R.card) +
        A.card * Real.exp (-(t : ℝ) * Hlow / R.card) :=
      add_le_add (sum_cosineMean_pow_le_of_energy R (S \ A) hR f t Hhigh hhigh)
        (sum_cosineMean_pow_le_of_energy R A hR f t Hlow hlow)
    _ ≤ _ := by
      have hc : (((S \ A).card : ℕ) : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : S \ A ⊆ S)
      exact add_le_add (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)) le_rfl

def nonzeroFrequencies (q : ℕ) : Finset ℕ := (Finset.range q).erase 0

noncomputable def powerCollisionSum (R : Finset ℕ) (k q t : ℕ) : ℝ :=
  ∑ h ∈ nonzeroFrequencies q,
    finiteCosineMean R (fun n => (h : ℝ) / q * (n : ℝ) ^ k) ^ t

theorem mem_nonzeroFrequencies (q h : ℕ) :
    h ∈ nonzeroFrequencies q ↔ h ≠ 0 ∧ h < q := by
  simp only [nonzeroFrequencies, Finset.mem_erase, Finset.mem_range]

theorem card_nonzeroFrequencies_le (q : ℕ) : (nonzeroFrequencies q).card ≤ q := by
  exact (Finset.card_le_card (Finset.erase_subset 0 (Finset.range q))).trans_eq (Finset.card_range q)

theorem powerCollisionSum_nonneg (R : Finset ℕ) (k q t : ℕ) :
    0 ≤ powerCollisionSum R k q t :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg (finiteCosineMean_nonneg _ _) _)

end Erdos345
