import Erdos345.BernoulliFourier
import Erdos345.CyclicFrequencyIndex
import Erdos345.SampledCosineBound

namespace Erdos345

noncomputable def powerBitSum (G : Finset ℕ) (k q : ℕ) (ω : G → Bool) : ZMod q :=
  bitSum (fun i : G => ((i.val ^ k : ℕ) : ZMod q)) ω

theorem powerBit_fourier_norm (G : Finset ℕ) (k q h : ℕ) [NeZero q] :
    ‖cyclicFourier (fun r => (residueMass (powerBitSum G k q) r : ℂ)) (h : ZMod q)‖ ^ 2 =
      subsetCosineProduct G k q h := by
  change ‖cyclicFourier (fun r => (residueMass
    (bitSum (fun i : G => ((i.val ^ k : ℕ) : ZMod q))) r : ℂ)) (h : ZMod q)‖ ^ 2 = _
  rw [bitSum_fourier_product, norm_prod, ← Finset.prod_pow]
  have hterm (i : G) :
      ‖(1 + ZMod.stdAddChar ((h : ZMod q) * ((i.val ^ k : ℕ) : ZMod q))) / 2‖ ^ 2 =
        Real.cos (Real.pi * ((h : ℝ) / q * (i.val : ℝ) ^ k)) ^ 2 := by
    simpa only [Nat.cast_pow] using half_stdAddChar_norm q h (i.val ^ k)
  simp_rw [hterm]
  exact Finset.prod_coe_sort G (fun n : ℕ => Real.cos (Real.pi * ((h : ℝ) / q * (n : ℝ) ^ k)) ^ 2)

theorem powerBit_collision_eq (G : Finset ℕ) (k q : ℕ) [NeZero q] :
    residueCollision (powerBitSum G k q) = subsetCosineSum G k q := by
  unfold residueCollision
  rw [nonzero_zmod_sum_eq_nat]
  apply Finset.sum_congr rfl
  intro h _
  exact powerBit_fourier_norm G k q h

noncomputable def representedResidues (G : Finset ℕ) (k q : ℕ) : Finset (ZMod q) :=
  G.powerset.image (fun S => ∑ n ∈ S, ((n ^ k : ℕ) : ZMod q))

theorem powerBit_support_subset_represented (G : Finset ℕ) (k q : ℕ) [NeZero q] :
    residueSupport (powerBitSum G k q) ⊆ representedResidues G k q := by
  classical
  intro r hr
  obtain ⟨ω, _, hω⟩ := Finset.mem_image.mp hr
  let T : Finset G := Finset.univ.filter (fun i => ω i)
  let S : Finset ℕ := T.image (fun i => i.val)
  have hSG : S ⊆ G := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact i.prop
  have hsum : (∑ n ∈ S, ((n ^ k : ℕ) : ZMod q)) = powerBitSum G k q ω := by
    change (∑ n ∈ T.image (fun i => i.val), ((n ^ k : ℕ) : ZMod q)) = _
    rw [Finset.sum_image (by intro i _ j _ hij; exact Subtype.ext hij)]
    simp only [T, Finset.sum_filter, powerBitSum, bitSum]
  apply Finset.mem_image.mpr
  exact ⟨S, Finset.mem_powerset.mpr hSG, hsum.trans hω⟩

/-- Small Fourier collision guarantees many residue classes represented
by sums of distinct members of G raised to the kth power. -/
theorem representedResidues_large_of_cosineSum (G : Finset ℕ) (k q : ℕ) [NeZero q]
    (hsmall : subsetCosineSum G k q ≤ 3) :
    (q : ℝ) / 4 ≤ (representedResidues G k q).card := by
  have hc : residueCollision (powerBitSum G k q) ≤ 3 := by
    simpa only [powerBit_collision_eq] using hsmall
  have hs := residueSupport_large_of_collision_le_three (powerBitSum G k q) hc
  have hcard : ((residueSupport (powerBitSum G k q)).card : ℝ) ≤
      (representedResidues G k q).card := by
    exact_mod_cast Finset.card_le_card (powerBit_support_subset_represented G k q)
  exact hs.trans hcard

end Erdos345
