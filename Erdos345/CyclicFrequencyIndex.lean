import Erdos345.CyclicSupport

namespace Erdos345

theorem nonzero_zmod_sum_eq_nat {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ z ∈ (Finset.univ : Finset (ZMod q)).erase 0, f z) =
      ∑ h ∈ nonzeroFrequencies q, f (h : ZMod q) := by
  classical
  symm
  apply Finset.sum_bij (fun (h : ℕ) (_ : h ∈ nonzeroFrequencies q) => (h : ZMod q))
  · intro h hh
    have hb := (mem_nonzeroFrequencies q h).mp hh
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hz
    have he := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hb.2, ZMod.val_zero] at he
    exact hb.1 he
  · intro h hh l hl he
    have hhq := ((mem_nonzeroFrequencies q h).mp hh).2
    have hlq := ((mem_nonzeroFrequencies q l).mp hl).2
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt hhq, ZMod.val_natCast_of_lt hlq] using hv
  · intro z hz
    have hz0 := (Finset.mem_erase.mp hz).1
    refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
    apply (mem_nonzeroFrequencies q z.val).mpr
    exact ⟨fun h => hz0 ((ZMod.val_eq_zero z).mp h), ZMod.val_lt z⟩
  · intro h _
    rfl

end Erdos345
