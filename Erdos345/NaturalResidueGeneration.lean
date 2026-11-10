import Erdos345.ResidueEndpointGrowth
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace Erdos345

theorem natural_gcd_mem_addSubgroup (q : ℕ) (H : AddSubgroup (ZMod q))
    (a b : ℕ) (ha : (a : ZMod q) ∈ H) (hb : (b : ZMod q) ∈ H) :
    (Nat.gcd a b : ZMod q) ∈ H := by
  have heq := congrArg (fun n : ℤ => (n : ZMod q)) (Nat.gcd_eq_gcd_ab a b)
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul] at heq
  rw [heq]
  have hs := H.add_mem (H.zsmul_mem ha (Nat.gcdA a b)) (H.zsmul_mem hb (Nat.gcdB a b))
  simpa only [zsmul_eq_mul, mul_comm] using hs

theorem natural_finset_gcd_mem_addSubgroup (q : ℕ) (H : AddSubgroup (ZMod q))
    (A : Finset ℕ) (hA : ∀ a ∈ A, (a : ZMod q) ∈ H) :
    ((A.gcd id : ℕ) : ZMod q) ∈ H := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.gcd_empty, Nat.cast_zero] using H.zero_mem
  | @insert a A ha ih =>
    rw [Finset.gcd_insert]
    exact natural_gcd_mem_addSubgroup q H a (A.gcd id)
      (hA a (Finset.mem_insert_self _ _))
      (ih (fun b hb => hA b (Finset.mem_insert_of_mem hb)))

theorem natural_residue_generates_of_gcd_one (A : Finset ℕ) (q : ℕ) [NeZero q]
    (hgcd : A.gcd id = 1) :
    AddSubgroup.closure (naturalResidueImage A q : Set (ZMod q)) = ⊤ := by
  let H := AddSubgroup.closure (naturalResidueImage A q : Set (ZMod q))
  have hA : ∀ a ∈ A, (a : ZMod q) ∈ H := by
    intro a ha
    apply AddSubgroup.subset_closure
    exact Finset.mem_image_of_mem _ ha
  have hone : (1 : ZMod q) ∈ H := by
    have h := natural_finset_gcd_mem_addSubgroup q H A hA
    simpa only [hgcd, Nat.cast_one] using h
  apply top_unique
  intro r _
  have hm := H.nsmul_mem hone r.val
  simpa only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using hm

theorem natural_residue_generates_of_no_progression (A : Finset ℕ) (q : ℕ) [NeZero q]
    (hA : ∀ d a : ℕ, (∀ n ∈ A, n % d = a % d) → d = 1) :
    AddSubgroup.closure (naturalResidueImage A q : Set (ZMod q)) = ⊤ := by
  apply natural_residue_generates_of_gcd_one A q
  apply hA (A.gcd id) 0
  intro n hn
  have hd : (A.gcd id : ℕ) ∣ n := Finset.gcd_dvd (f := id) hn
  rw [Nat.mod_eq_zero_of_dvd hd, Nat.zero_mod]

end Erdos345
