module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem rootNumber_eq_one_of_positive_scaling
    (c : ℝ) (A B L : ℂ → ℂ) (W : ℂ)
    (hA : ∀ s : ℂ, A s = A (1 - s))
    (hB : ∀ s : ℂ, B s = B (1 - s))
    (hfactor : ∀ s : ℂ, A s = Complex.exp ((c : ℂ) * s) * B s * L s)
    (hL : ∀ s : ℂ, L s = W * L (1 - s))
    (hW : ‖W‖ = 1) (hA2 : A 2 ≠ 0) : W = 1 := by

  have hA21 : A 2 = A (-1) := by
    have h := hA 2
    norm_num at h
    exact h
  have hB21 : B 2 = B (-1) := by
    have h := hB 2
    norm_num at h
    exact h
  have hLm1 : L (-1) = W * L 2 := by
    have h := hL (-1)
    norm_num at h
    exact h

  have hprod : Complex.exp ((c : ℂ) * 2) * B 2 * L 2 ≠ 0 := by
    rw [← hfactor 2]
    exact hA2
  have hB2 : B 2 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hL2 : L 2 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hBL : B 2 * L 2 ≠ 0 := mul_ne_zero hB2 hL2

  have heq :
      Complex.exp ((c : ℂ) * 2) * B 2 * L 2 =
        Complex.exp ((c : ℂ) * (-1)) * B 2 * (W * L 2) := by
    calc Complex.exp ((c : ℂ) * 2) * B 2 * L 2 = A 2 := (hfactor 2).symm
      _ = A (-1) := hA21
      _ = Complex.exp ((c : ℂ) * (-1)) * B (-1) * L (-1) := hfactor (-1)
      _ = Complex.exp ((c : ℂ) * (-1)) * B 2 * (W * L 2) := by rw [← hB21, hLm1]
  have hc' : Complex.exp ((c : ℂ) * 2) = Complex.exp ((c : ℂ) * (-1)) * W := by
    have h := heq
    rw [show Complex.exp ((c : ℂ) * 2) * B 2 * L 2 =
          Complex.exp ((c : ℂ) * 2) * (B 2 * L 2) by ring,
        show Complex.exp ((c : ℂ) * (-1)) * B 2 * (W * L 2) =
          (Complex.exp ((c : ℂ) * (-1)) * W) * (B 2 * L 2) by ring] at h
    exact mul_right_cancel₀ hBL h

  have hW3 : W = Complex.exp ((3 * c : ℝ) : ℂ) := by
    have hm : Complex.exp (c : ℂ) * Complex.exp ((c : ℂ) * 2) =
        Complex.exp (c : ℂ) * (Complex.exp ((c : ℂ) * (-1)) * W) :=
      congrArg (fun z => Complex.exp (c : ℂ) * z) hc'
    have hLHS : Complex.exp (c : ℂ) * Complex.exp ((c : ℂ) * 2) =
        Complex.exp ((3 * c : ℝ) : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hRHS : Complex.exp (c : ℂ) * (Complex.exp ((c : ℂ) * (-1)) * W) = W := by
      rw [← mul_assoc, ← Complex.exp_add,
        show (c : ℂ) + (c : ℂ) * (-1) = 0 by ring, Complex.exp_zero, one_mul]
    rw [hLHS, hRHS] at hm
    exact hm.symm
  have hexp1 : Real.exp (3 * c) = 1 := by
    have h := hW
    rw [hW3, Complex.norm_exp] at h
    simpa using h
  have hc : c = 0 := by
    have h3 := (Real.exp_eq_one_iff (3 * c)).mp hexp1
    linarith
  rw [hW3, hc]
  simp

end DedekindZetaZeroFree.LargeSieve
