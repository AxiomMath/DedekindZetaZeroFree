module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.Hecke

def rationalTracePhase : AddChar ℚ ℂ where
  toFun q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ))
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro q r
    simp only [Rat.cast_add, mul_add, Complex.exp_add]

@[simp] theorem rationalTracePhase_apply (q : ℚ) :
    rationalTracePhase q = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ)) :=
  rfl

theorem rationalTracePhase_apply_real (q : ℚ) :
    rationalTracePhase q =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((q : ℝ) : ℂ)) := by
  simp

theorem rationalTracePhase_eq_one_iff (q : ℚ) :
    rationalTracePhase q = 1 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [rationalTracePhase_apply, Complex.exp_eq_one_iff]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (q : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hc
      simpa only [mul_comm] using hn
    exact_mod_cast h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (n : ℂ) = (q : ℂ) := by exact_mod_cast hn
    rw [← h, mul_comm]

@[simp] theorem norm_rationalTracePhase (q : ℚ) :
    ‖rationalTracePhase q‖ = 1 := by
  rw [rationalTracePhase_apply, Complex.norm_exp]
  simp

theorem rationalTracePhase_ne_zero (q : ℚ) :
    rationalTracePhase q ≠ 0 := by
  exact Complex.exp_ne_zero _

end DedekindZetaZeroFree.Hecke

end
