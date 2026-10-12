module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector

theorem one_add_nat_inv_ne_zero (n : ℕ) : (1 + (n : ℂ)⁻¹) ≠ 0 := by
  have hcast : (1 + (n : ℂ)⁻¹) = ((1 + (n : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    simp
  rw [hcast, Complex.ofReal_ne_zero]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    norm_num
  · have hpos : (0 : ℝ) < n := by exact_mod_cast h
    have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hpos
    linarith

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
