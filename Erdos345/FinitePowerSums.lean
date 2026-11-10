import Erdos345.PowerSubsetSupport
import Erdos345.ResidueEndpointGrowth

namespace Erdos345

def finitePowerSums (G : Finset ℕ) (k : ℕ) : Finset ℕ :=
  G.powerset.image (fun S => ∑ n ∈ S, n ^ k)

theorem zero_mem_finitePowerSums (G : Finset ℕ) (k : ℕ) :
    0 ∈ finitePowerSums G k := by
  classical
  exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩

theorem finitePowerSums_mono {G H : Finset ℕ} (h : G ⊆ H) (k : ℕ) :
    finitePowerSums G k ⊆ finitePowerSums H k := by
  classical
  intro m hm
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
  exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS).trans h), rfl⟩

theorem naturalResidueImage_finitePowerSums (G : Finset ℕ) (k q : ℕ) :
    naturalResidueImage (finitePowerSums G k) q = representedResidues G k q := by
  classical
  unfold naturalResidueImage finitePowerSums representedResidues
  rw [Finset.image_image]
  apply Finset.image_congr
  intro S _
  simp only [Function.comp_apply, Nat.cast_sum]

theorem finitePowerSums_insert (G : Finset ℕ) (k b : ℕ) (hb : b ∉ G) :
    finitePowerSums (insert b G) k =
      finitePowerSums G k ∪ (finitePowerSums G k).image (fun a => a + b ^ k) := by
  classical
  unfold finitePowerSums
  rw [Finset.powerset_insert, Finset.image_union, Finset.image_image]
  congr 1
  rw [Finset.image_image]
  apply Finset.image_congr
  intro S hS
  have hbS : b ∉ S := fun h => hb ((Finset.mem_powerset.mp hS) h)
  simp only [Function.comp_apply, Finset.sum_insert hbS, Nat.add_comm]

/-- Appending one unused base increases the number of actual subset
sums by at least the number of occupied residue classes modulo its power. -/
theorem finitePowerSums_insert_growth (G : Finset ℕ) (k b : ℕ)
    (hb0 : 0 < b) (hb : b ∉ G) :
    (finitePowerSums G k).card + (representedResidues G k (b ^ k)).card ≤
      (finitePowerSums (insert b G) k).card := by
  rw [finitePowerSums_insert G k b hb]
  have h := residue_endpoint_card_growth (finitePowerSums G k) (b ^ k) (by positivity)
  simpa only [naturalResidueImage_finitePowerSums] using h

theorem representedResidues_mono {G H : Finset ℕ} (h : G ⊆ H) (k q : ℕ) :
    representedResidues G k q ⊆ representedResidues H k q := by
  classical
  rw [← naturalResidueImage_finitePowerSums, ← naturalResidueImage_finitePowerSums]
  exact Finset.image_subset_image (finitePowerSums_mono h k)

/-- The support gain survives successive additions because the initial
residue support is retained at every stage. -/
theorem finitePowerSums_union_growth (G B : Finset ℕ) (k : ℕ)
    (hdisj : Disjoint G B) (hpos : ∀ b ∈ B, 0 < b) :
    (finitePowerSums G k).card +
      (∑ b ∈ B, (representedResidues G k (b ^ k)).card) ≤
      (finitePowerSums (G ∪ B) k).card := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finitePowerSums]
  | @insert b B hb ih =>
    have hGB : Disjoint G B := hdisj.mono_right (Finset.subset_insert _ _)
    have hbG : b ∉ G := fun h => (Finset.disjoint_left.mp hdisj) h (Finset.mem_insert_self _ _)
    have hbGB : b ∉ G ∪ B := by simp only [Finset.mem_union, not_or]; exact ⟨hbG, hb⟩
    have hbase := ih hGB (fun c hc => hpos c (Finset.mem_insert_of_mem hc))
    have hnew := finitePowerSums_insert_growth (G ∪ B) k b
      (hpos b (Finset.mem_insert_self _ _)) hbGB
    have hres := Finset.card_le_card (representedResidues_mono
      (show G ⊆ G ∪ B from Finset.subset_union_left) k (b ^ k))
    have hset : G ∪ insert b B = insert b (G ∪ B) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [Finset.sum_insert hb, hset]
    omega

end Erdos345
