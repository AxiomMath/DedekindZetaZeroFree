module

public import DedekindZetaZeroFree.RepresentationTheory.Compact.InvariantProjection
public import DedekindZetaZeroFree.RepresentationTheory.Invariants.NormMapsAndExactness
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.IrreducibleClassification
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SU2.TorusCharacterOrthogonality

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Weyl/Integration.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open MeasureTheory

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

@[simp]
theorem integral_character_symPower (d : ℕ) :
    ∫ g, (symPower d).character g ∂haarProb SU2 = if d = 0 then 1 else 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · simp only [hd, ↓reduceIte]
    have hbot := Representation.IsIrreducible.invariants_eq_bot_of_finrank_ne_one
      (isIrreducible_symPowerModel d) (by rw [finrank_euclideanSpace_fin]; omega)

    rw [← (ContRepresentation.integral_character_eq_zero_iff (symPowerModel d)
      (continuous_symPowerModel d)).2 ((Submodule.eq_bot_iff _).2 fun v hv =>
        (Submodule.eq_bot_iff _).1 hbot v hv)]
    simp

theorem continuous_weylIntegrand (f : C(SU2, ℂ)) :
    Continuous fun θ : ℝ => f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) :=
  (f.continuous.comp continuous_torusExp).mul
    (Complex.continuous_ofReal.comp (continuous_const.mul (Real.continuous_sin.pow 2)))

noncomputable def weylFunctional : C(SU2, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_mul]
        rw [intervalIntegral.integral_add ((continuous_weylIntegrand f).intervalIntegrable _ _)
          ((continuous_weylIntegrand g).intervalIntegrable _ _), mul_add]
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
          intervalIntegral.integral_const_mul]
        ring }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have hpi : 0 < Real.pi := Real.pi_pos
      have hbound : ‖∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)‖
          ≤ ‖f‖ * (2 * Real.pi) := by
        refine (intervalIntegral.norm_integral_le_integral_norm hpi.le).trans ?_
        have hmass : ∫ θ in (0 : ℝ)..Real.pi, 4 * Real.sin θ ^ 2 = 2 * Real.pi := by
          rw [intervalIntegral.integral_const_mul, integral_sin_sq]
          simp only [Real.sin_zero, Real.sin_pi, zero_mul, sub_zero]
          ring
        rw [← hmass, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on hpi.le
          ((continuous_weylIntegrand f).norm.intervalIntegrable _ _)
          ((continuous_const.mul
            (continuous_const.mul (Real.continuous_sin.pow 2))).intervalIntegrable _ _)
          fun θ _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (by positivity)
      rw [norm_mul, norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hpi.le]
      calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..Real.pi,
              f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)‖
          ≤ 1 / (2 * Real.pi) * (‖f‖ * (2 * Real.pi)) := by gcongr
        _ = ‖f‖ := by field_simp

private theorem weylFunctional_apply (f : C(SU2, ℂ)) :
    weylFunctional f = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) :=
  (rfl)

private theorem weylFunctional_symPowerCharacter (d : ℕ) :
    weylFunctional (symPowerCharacter d) = if d = 0 then 1 else 0 := by
  have h := character_symPower_orthonormal_torusExp d 0
  simp only [character_symPower_zero, map_one, mul_one] at h
  rw [weylFunctional_apply]
  simpa only [symPowerCharacter_apply] using h

theorem weyl_integration_formula {f : SU2 → ℂ} (hf : Continuous f)
    (hconj : ∀ u g : SU2, f (u * g * u⁻¹) = f g) :
    ∫ g, f g ∂haarProb SU2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
  let F : C(SU2, ℂ) := ⟨f, hf⟩
  let D : C(SU2, ℂ) →L[ℂ] ℂ := haarAverage SU2 - weylFunctional
  have hspan : characterSpan ≤ LinearMap.ker (D : C(SU2, ℂ) →ₗ[ℂ] ℂ) :=
    characterSpan_le_iff.2 fun d => LinearMap.mem_ker.2 <| by
      simp only [D, ContinuousLinearMap.coe_coe, sub_apply,
        haarAverage_apply, weylFunctional_symPowerCharacter, symPowerCharacter_apply,
        integral_character_symPower, sub_self]
  have hF : F ∈ LinearMap.ker (D : C(SU2, ℂ) →ₗ[ℂ] ℂ) :=
    Submodule.topologicalClosure_minimal _ hspan D.isClosed_ker
      (mem_topologicalClosure_characterSpan_iff.2 hconj)
  have hD := LinearMap.mem_ker.1 hF
  simp only [D, ContinuousLinearMap.coe_coe, sub_apply,
    haarAverage_apply, sub_eq_zero] at hD
  exact hD.trans (weylFunctional_apply F)

@[simp]
theorem integral_character_symPower_mul_conj (m n : ℕ) :
    ∫ g, (symPower m).character g * (starRingEnd ℂ) ((symPower n).character g) ∂haarProb SU2
      = if m = n then 1 else 0 := by
  rw [weyl_integration_formula
    (f := fun g => (symPower m).character g * (starRingEnd ℂ) ((symPower n).character g))
    ((continuous_character_symPower m).mul
      (Complex.continuous_conj.comp (continuous_character_symPower n)))
    fun u g => by rw [Representation.char_conj, Representation.char_conj]]
  exact character_symPower_orthonormal_torusExp m n

end SU2

end DedekindZetaZeroFree.TauCeti
