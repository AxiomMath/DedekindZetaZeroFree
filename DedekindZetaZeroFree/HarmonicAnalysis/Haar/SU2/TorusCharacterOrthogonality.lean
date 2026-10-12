module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SineOrthogonality
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.WeylCharacterFormula

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

theorem character_symPower_mul_conj_mul_four_mul_sin_sq (m n : ℕ) (θ : ℝ) :
    (symPower m).character (torusExp θ)
        * (starRingEnd ℂ) ((symPower n).character (torusExp θ))
        * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = ((4 * (Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)) : ℝ) : ℂ) := by
  rw [conj_character_symPower_torusExp]
  have habsorb : (symPower m).character (torusExp θ) * (symPower n).character (torusExp θ)
      * (4 * (Real.sin θ : ℂ) ^ 2)
      = 4 * ((Real.sin θ : ℂ) * (symPower m).character (torusExp θ))
          * ((Real.sin θ : ℂ) * (symPower n).character (torusExp θ)) := by
    ring
  rw [show ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) = 4 * (Real.sin θ : ℂ) ^ 2 by push_cast; ring, habsorb,
    sin_mul_character_symPower_torusExp, sin_mul_character_symPower_torusExp]
  push_cast
  ring

theorem character_symPower_orthonormal_torusExp (m n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        (symPower m).character (torusExp θ)
          * (starRingEnd ℂ) ((symPower n).character (torusExp θ))
          * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      = if m = n then 1 else 0 := by

  simp only [character_symPower_mul_conj_mul_four_mul_sin_sq]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]

  have hnorm : ∀ I : ℝ, 1 / (2 * Real.pi) * (4 * I) = 2 / Real.pi * I := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    intro I
    field_simp
    ring
  have hreal : 1 / (2 * Real.pi) * (4 * ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ))
      = if m = n then (1 : ℝ) else 0 := by
    rw [hnorm, two_div_pi_mul_integral_sin_succ_mul_sin_succ]
  rw [show (if m = n then (1 : ℂ) else 0) = ((if m = n then (1 : ℝ) else 0 : ℝ) : ℂ) by
    split <;> simp, ← hreal]
  push_cast
  ring

end SU2

end DedekindZetaZeroFree.TauCeti
