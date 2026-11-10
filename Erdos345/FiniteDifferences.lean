import Erdos345.NewtonCoefficients

namespace Erdos345

def difference {R : Type*} [Sub R] (f : ℕ → R) (n : ℕ) : R :=
  f (n + 1) - f n

def iteratedDifference {R : Type*} [Sub R] : ℕ → (ℕ → R) → (ℕ → R)
  | 0, f => f
  | s + 1, f => difference (iteratedDifference s f)

theorem map_iteratedDifference {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (f : ℕ → R) (s n : ℕ) :
    φ (iteratedDifference s f n) =
      iteratedDifference s (fun j => φ (f j)) n := by
  induction s generalizing n with
  | zero => rfl
  | succ s ih =>
    simp only [iteratedDifference, difference, map_sub, ih]

theorem dvd_iteratedDifference (q : ℤ) (f : ℕ → ℤ)
    (h : ∀ n : ℕ, q ∣ f n) (s n : ℕ) :
    q ∣ iteratedDifference s f n := by
  induction s generalizing n with
  | zero => exact h n
  | succ s ih => exact dvd_sub (ih (n + 1)) (ih n)

theorem iteratedDifference_sub {R : Type*} [Ring R]
    (f g : ℕ → R) (s n : ℕ) :
    iteratedDifference s (fun j => f j - g j) n =
      iteratedDifference s f n - iteratedDifference s g n := by
  induction s generalizing n with
  | zero => rfl
  | succ s ih =>
    simp only [iteratedDifference, difference, ih]
    exact sub_sub_sub_comm _ _ _ _

theorem iteratedDifference_zero_of_prefix {R : Type*} [Ring R]
    (f : ℕ → R) (s n : ℕ) (h : ∀ i : ℕ, i ≤ s → f (n + i) = 0) :
    iteratedDifference s f n = 0 := by
  induction s generalizing n with
  | zero => simpa only [iteratedDifference, Nat.add_zero] using h 0 le_rfl
  | succ s ih =>
    have h0 : iteratedDifference s f n = 0 :=
      ih n (fun i hi => h i (by omega))
    have h1 : iteratedDifference s f (n + 1) = 0 := by
      apply ih (n + 1)
      intro i hi
      have he : n + 1 + i = n + (i + 1) := by omega
      rw [he]
      exact h (i + 1) (by omega)
    simp only [iteratedDifference, difference, h0, h1, sub_self]

theorem newtonEval_zero {R : Type*} [Semiring R] (a : ℕ → R) :
    newtonEval a 0 = a 0 := by
  simp [newtonEval]

theorem newtonEval_succ {R : Type*} [Semiring R] (a : ℕ → R) (n : ℕ) :
    newtonEval a (n + 1) = newtonEval a n + newtonEval (fun j => a (j + 1)) n := by
  have hext :
      (∑ j ∈ Finset.range (n + 2), a j * (n.choose j : R)) =
      ∑ j ∈ Finset.range (n + 1), a j * (n.choose j : R) := by
    rw [Finset.sum_range_succ]
    simp
  have hsplit :
      (∑ j ∈ Finset.range (n + 2), a j * (n.choose j : R)) =
      a 0 + ∑ j ∈ Finset.range (n + 1), a (j + 1) * (n.choose (j + 1) : R) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
    ac_rfl
  calc
    newtonEval a (n + 1) =
        a 0 + ∑ j ∈ Finset.range (n + 1), a (j + 1) * ((n + 1).choose (j + 1) : R) := by
      rw [newtonEval, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
      ac_rfl
    _ = a 0 + ∑ j ∈ Finset.range (n + 1),
        (a (j + 1) * (n.choose j : R) + a (j + 1) * (n.choose (j + 1) : R)) := by
      simp only [Nat.choose_succ_succ, Nat.cast_add, mul_add]
    _ = (a 0 + ∑ j ∈ Finset.range (n + 1), a (j + 1) * (n.choose (j + 1) : R)) +
        ∑ j ∈ Finset.range (n + 1), a (j + 1) * (n.choose j : R) := by
      rw [Finset.sum_add_distrib]
      ac_rfl
    _ = (∑ j ∈ Finset.range (n + 2), a j * (n.choose j : R)) +
        ∑ j ∈ Finset.range (n + 1), a (j + 1) * (n.choose j : R) := by
      rw [hsplit]
    _ = newtonEval a n + newtonEval (fun j => a (j + 1)) n := by
      rw [hext]
      rfl

theorem difference_newtonEval {R : Type*} [Ring R] (a : ℕ → R) :
    difference (newtonEval a) = newtonEval (fun j => a (j + 1)) := by
  funext n
  simp only [difference, newtonEval_succ, add_sub_cancel_left]

theorem iteratedDifference_newtonEval {R : Type*} [Ring R] (a : ℕ → R) (s : ℕ) :
    iteratedDifference s (newtonEval a) = newtonEval (fun j => a (j + s)) := by
  induction s with
  | zero => simp [iteratedDifference]
  | succ s ih =>
    rw [iteratedDifference, ih, difference_newtonEval]
    congr 1
    funext j
    congr 1
    omega

theorem iteratedDifference_newtonEval_zero {R : Type*} [Ring R] (a : ℕ → R) (s : ℕ) :
    iteratedDifference s (newtonEval a) 0 = a s := by
  rw [iteratedDifference_newtonEval, newtonEval_zero, Nat.zero_add]

theorem iteratedDifference_power_zero {R : Type*} [Ring R] (k s : ℕ) :
    iteratedDifference s (fun n : ℕ => (n : R) ^ k) 0 = (powerCoefficient k s : R) := by
  have heq : (fun n : ℕ => (n : R) ^ k) =
      newtonEval (fun j => (powerCoefficient k j : R)) := by
    funext n
    exact (newtonEval_powerCoefficient k n).symm
  rw [heq, iteratedDifference_newtonEval_zero]

theorem iteratedDifference_difference {R : Type*} [Sub R]
    (f : ℕ → R) (s : ℕ) :
    iteratedDifference s (difference f) = iteratedDifference (s + 1) f := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [iteratedDifference, ih]

/-- Newton's forward formula holds for every sequence; no polynomial premise. -/
theorem newton_forward_formula {R : Type*} [Ring R] (f : ℕ → R) (n : ℕ) :
    newtonEval (fun j => iteratedDifference j f 0) n = f n := by
  induction n generalizing f with
  | zero => simp [newtonEval_zero, iteratedDifference]
  | succ n ih =>
    rw [newtonEval_succ, ih f]
    have hshift :
        (fun j => iteratedDifference (j + 1) f 0) =
        (fun j => iteratedDifference j (difference f) 0) := by
      funext j
      rw [iteratedDifference_difference]
    rw [hshift, ih (difference f)]
    simp only [difference, add_sub_cancel]

end Erdos345
