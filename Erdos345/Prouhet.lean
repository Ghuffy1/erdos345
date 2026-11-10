import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Positivity

/-!
An explicit finite Prouhet construction. The color classes have equal power
moments through any prescribed degree and are mutually disjoint. This module
contains no analytic input and makes no assertion about the main Erdős theorem.
-/

namespace Erdos345

open Finset

def prouhetBlock (M d : ℕ) (i : ZMod M) (n : ℕ) : ℕ :=
  i.val * M ^ (d + 1) + n

noncomputable def prouhetFamily (M : ℕ) [NeZero M] : ℕ → ZMod M → Finset ℕ
  | 0, r => {r.val}
  | d + 1, r => univ.biUnion fun i =>
      (prouhetFamily M d (r - i)).image (prouhetBlock M d i)

theorem prouhetBlock_injective (M d : ℕ) (i : ZMod M) :
    Function.Injective (prouhetBlock M d i) := by
  intro a b h
  exact Nat.add_left_cancel h

theorem prouhetBlock_unique {M d : ℕ} [NeZero M] {i j : ZMod M} {a b : ℕ}
    (ha : a < M ^ (d + 1)) (hb : b < M ^ (d + 1))
    (h : prouhetBlock M d i a = prouhetBlock M d j b) : i = j ∧ a = b := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hL : 0 < M ^ (d + 1) := pow_pos hM _
  have hdiv := congrArg (fun n => n / M ^ (d + 1)) h
  have hval : i.val = j.val := by
    simpa only [prouhetBlock, Nat.mul_comm i.val, Nat.mul_comm j.val,
      Nat.mul_add_div hL, Nat.div_eq_of_lt ha,
      Nat.div_eq_of_lt hb, Nat.add_zero] using hdiv
  have hij : i = j := ZMod.val_injective M hval
  subst j
  exact ⟨rfl, Nat.add_left_cancel h⟩

theorem prouhetFamily_lt {M : ℕ} [NeZero M] (d : ℕ) (r : ZMod M)
    {n : ℕ} (hn : n ∈ prouhetFamily M d r) : n < M ^ (d + 1) := by
  induction d generalizing r n with
  | zero =>
    have heq : n = r.val := by simpa only [prouhetFamily, mem_singleton] using hn
    simpa only [heq, zero_add, pow_one] using ZMod.val_lt r
  | succ d ih =>
    obtain ⟨i, _, hni⟩ := mem_biUnion.mp hn
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hni
    have haL := ih (r - i) ha
    have hi : i.val + 1 ≤ M := ZMod.val_lt i
    have hle := Nat.mul_le_mul_right (M ^ (d + 1)) hi
    calc
      prouhetBlock M d i a < (i.val + 1) * M ^ (d + 1) := by
        dsimp only [prouhetBlock]
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left haL _
      _ ≤ M * M ^ (d + 1) := hle
      _ = M ^ (d + 1 + 1) := by ring

theorem prouhetFamily_unique {M : ℕ} [NeZero M] (d : ℕ) {r s : ZMod M}
    {n : ℕ} (hr : n ∈ prouhetFamily M d r) (hs : n ∈ prouhetFamily M d s) :
    r = s := by
  induction d generalizing r s n with
  | zero =>
    have hrn : n = r.val := by simpa only [prouhetFamily, mem_singleton] using hr
    have hsn : n = s.val := by simpa only [prouhetFamily, mem_singleton] using hs
    exact ZMod.val_injective M (hrn.symm.trans hsn)
  | succ d ih =>
    obtain ⟨i, _, hni⟩ := mem_biUnion.mp hr
    obtain ⟨j, _, hnj⟩ := mem_biUnion.mp hs
    obtain ⟨a, ha, hna⟩ := mem_image.mp hni
    obtain ⟨b, hb, hnb⟩ := mem_image.mp hnj
    obtain ⟨hij, hab⟩ := prouhetBlock_unique
      (prouhetFamily_lt d _ ha) (prouhetFamily_lt d _ hb) (hna.trans hnb.symm)
    subst j
    subst b
    have hrs := ih ha hb
    exact sub_left_inj.mp hrs

theorem prouhetFamily_disjoint {M : ℕ} [NeZero M] (d : ℕ) {r s : ZMod M}
    (hrs : r ≠ s) : Disjoint (prouhetFamily M d r) (prouhetFamily M d s) := by
  apply disjoint_left.mpr
  intro n hn hs
  exact hrs (prouhetFamily_unique d hn hs)

theorem prouhetFamily_zero_mem {M : ℕ} [NeZero M] (d : ℕ) :
    0 ∈ prouhetFamily M d 0 := by
  induction d with
  | zero => simp [prouhetFamily]
  | succ d ih =>
    apply mem_biUnion.mpr
    refine ⟨0, mem_univ _, ?_⟩
    apply mem_image.mpr
    exact ⟨0, by simpa using ih, by simp [prouhetBlock]⟩

theorem prouhet_block_disjoint {M d : ℕ} [NeZero M] (r : ZMod M)
    {i j : ZMod M} (hij : i ≠ j) :
    Disjoint ((prouhetFamily M d (r - i)).image (prouhetBlock M d i))
      ((prouhetFamily M d (r - j)).image (prouhetBlock M d j)) := by
  apply disjoint_left.mpr
  intro n hn hm
  obtain ⟨a, ha, hna⟩ := mem_image.mp hn
  obtain ⟨b, hb, hnb⟩ := mem_image.mp hm
  exact hij (prouhetBlock_unique (prouhetFamily_lt d _ ha)
    (prouhetFamily_lt d _ hb) (hna.trans hnb.symm)).1

theorem sum_prouhetFamily_succ {M : ℕ} [NeZero M] (d : ℕ) (r : ZMod M)
    (f : ℕ → ℕ) :
    ∑ n ∈ prouhetFamily M (d + 1) r, f n =
      ∑ i : ZMod M, ∑ n ∈ prouhetFamily M d (r - i), f (prouhetBlock M d i n) := by
  classical
  rw [prouhetFamily, sum_biUnion]
  · apply sum_congr rfl
    intro i _
    exact sum_image (fun _ _ _ _ h => prouhetBlock_injective M d i h)
  · intro i _ j _ hij
    exact prouhet_block_disjoint r hij

def powerMoment (S : Finset ℕ) (j : ℕ) : ℕ := ∑ n ∈ S, n ^ j

theorem sum_shift_power (S : Finset ℕ) (t j : ℕ) :
    (∑ n ∈ S, (n + t) ^ j) = powerMoment S j +
      ∑ u ∈ range j, t ^ (j - u) * j.choose u * powerMoment S u := by
  calc
    (∑ n ∈ S, (n + t) ^ j) =
        ∑ u ∈ range (j + 1), t ^ (j - u) * j.choose u * powerMoment S u := by
      simp_rw [add_pow]
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      rw [powerMoment, mul_sum]
      apply sum_congr rfl
      intro n _
      simp only [Nat.cast_id]
      ring
    _ = _ := by
      rw [sum_range_succ]
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, one_mul]
      exact Nat.add_comm _ _

theorem sum_sub_color {M : ℕ} [NeZero M] (r : ZMod M) (f : ZMod M → ℕ) :
    (∑ i : ZMod M, f (r - i)) = ∑ i : ZMod M, f i := by
  let e : ZMod M ≃ ZMod M :=
    { toFun := fun i => r - i
      invFun := fun i => r - i
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  exact Equiv.sum_comp e f

theorem prouhetFamily_moment_step {M : ℕ} [NeZero M] (d j : ℕ) (r : ZMod M)
    (h : ∀ u < j, ∀ c : ZMod M,
      powerMoment (prouhetFamily M d c) u = powerMoment (prouhetFamily M d 0) u) :
    powerMoment (prouhetFamily M (d + 1) r) j =
      (∑ c : ZMod M, powerMoment (prouhetFamily M d c) j) +
      ∑ i : ZMod M, ∑ u ∈ range j,
        (i.val * M ^ (d + 1)) ^ (j - u) * j.choose u *
          powerMoment (prouhetFamily M d 0) u := by
  rw [powerMoment, sum_prouhetFamily_succ]
  have hterm (i : ZMod M) :
      (∑ n ∈ prouhetFamily M d (r - i), (prouhetBlock M d i n) ^ j) =
        powerMoment (prouhetFamily M d (r - i)) j +
        ∑ u ∈ range j, (i.val * M ^ (d + 1)) ^ (j - u) * j.choose u *
          powerMoment (prouhetFamily M d 0) u := by
    simp only [prouhetBlock, Nat.add_comm (i.val * M ^ (d + 1))]
    rw [sum_shift_power]
    congr 1
    apply sum_congr rfl
    intro u hu
    rw [h u (mem_range.mp hu)]
  simp_rw [hterm]
  rw [sum_add_distrib, sum_sub_color r (fun c => powerMoment (prouhetFamily M d c) j)]

/-- All colors have the same moments through degree d. -/
theorem prouhetFamily_moment_eq {M : ℕ} [NeZero M] (d : ℕ) (r s : ZMod M)
    (j : ℕ) (hj : j ≤ d) :
    powerMoment (prouhetFamily M d r) j = powerMoment (prouhetFamily M d s) j := by
  induction d generalizing r s j with
  | zero =>
    have hj0 : j = 0 := by omega
    simp [hj0, powerMoment, prouhetFamily]
  | succ d ih =>
    have hlower : ∀ u < j, ∀ c : ZMod M,
        powerMoment (prouhetFamily M d c) u = powerMoment (prouhetFamily M d 0) u := by
      intro u hu c
      exact ih c 0 u (by omega)
    rw [prouhetFamily_moment_step d j r hlower,
      prouhetFamily_moment_step d j s hlower]

noncomputable def oddProuhetFamily (M : ℕ) [NeZero M] (d : ℕ) (r : ZMod M) : Finset ℕ :=
  (prouhetFamily M d r).image fun n => 2 * n + 1

theorem oddProuhet_positive_odd {M d : ℕ} [NeZero M] (r : ZMod M)
    {b : ℕ} (hb : b ∈ oddProuhetFamily M d r) : 0 < b ∧ Odd b := by
  obtain ⟨n, _, rfl⟩ := mem_image.mp hb
  exact ⟨by omega, n, rfl⟩

theorem oddProuhet_disjoint {M d : ℕ} [NeZero M] {r s : ZMod M} (h : r ≠ s) :
    Disjoint (oddProuhetFamily M d r) (oddProuhetFamily M d s) := by
  apply disjoint_left.mpr
  intro b hbr hbs
  obtain ⟨n, hn, hnb⟩ := mem_image.mp hbr
  obtain ⟨m, hm, hmb⟩ := mem_image.mp hbs
  have hnm : n = m := by omega
  subst m
  exact h (prouhetFamily_unique d hn hm)

theorem oddProuhet_moment_expansion {M d : ℕ} [NeZero M] (r : ZMod M) (j : ℕ) :
    powerMoment (oddProuhetFamily M d r) j =
      ∑ u ∈ range (j + 1), 2 ^ u * j.choose u * powerMoment (prouhetFamily M d r) u := by
  classical
  rw [powerMoment, oddProuhetFamily, sum_image]
  · simp_rw [add_pow, mul_pow, one_pow, mul_one]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    rw [powerMoment, mul_sum]
    apply sum_congr rfl
    intro n _
    simp only [Nat.cast_id]
    ring
  · intro a _ b _ h
    dsimp only at h
    omega

theorem oddProuhet_moment_eq {M : ℕ} [NeZero M] (d : ℕ) (r s : ZMod M)
    (j : ℕ) (hj : j ≤ d) :
    powerMoment (oddProuhetFamily M d r) j =
      powerMoment (oddProuhetFamily M d s) j := by
  rw [oddProuhet_moment_expansion, oddProuhet_moment_expansion]
  apply sum_congr rfl
  intro u hu
  rw [prouhetFamily_moment_eq d r s u (by have := mem_range.mp hu; omega)]

theorem oddProuhet_one_mem {M d : ℕ} [NeZero M] :
    1 ∈ oddProuhetFamily M d 0 := by
  apply mem_image.mpr
  exact ⟨0, prouhetFamily_zero_mem d, by simp⟩

/-- For every number of colors and every degree, explicit disjoint sets of
positive odd bases have the same positive sum of powers. -/
theorem exists_disjoint_odd_equal_powers (M k : ℕ) [NeZero M] :
    ∃ s : ℕ, 0 < s ∧ ∃ F : ZMod M → Finset ℕ,
      (∀ r b, b ∈ F r → 0 < b ∧ Odd b) ∧
      (∀ r t, r ≠ t → Disjoint (F r) (F t)) ∧
      (∀ r, ∑ b ∈ F r, b ^ k = s) := by
  refine ⟨powerMoment (oddProuhetFamily M k 0) k, ?_, oddProuhetFamily M k,
    fun r b hb => oddProuhet_positive_odd r hb, fun r t h => oddProuhet_disjoint h, ?_⟩
  · have hle : 1 ^ k ≤ powerMoment (oddProuhetFamily M k 0) k :=
      single_le_sum (f := fun b => b ^ k) (fun _ _ => Nat.zero_le _) oddProuhet_one_mem
    have : 1 ≤ powerMoment (oddProuhetFamily M k 0) k := by simpa only [one_pow] using hle
    omega
  · intro r
    exact oddProuhet_moment_eq k r 0 k le_rfl

end Erdos345
