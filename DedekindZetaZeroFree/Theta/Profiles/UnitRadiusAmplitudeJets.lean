module

public import DedekindZetaZeroFree.Theta.Profiles.InducedAmplitudeDerivativeBounds
import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ChartJetBounds

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchInducedMajorant

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open scoped ContDiff Matrix.Norms.Elementwise

private lemma unit_diagonal_chart (u : ℂˣ) (x : ℂ) :
    weyl * upperUnipotent x * diagonal u =
      upperTriangular 1 u 0 * (weyl * upperUnipotent (x / (u : ℂ))) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, diagonal, upperTriangular,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

private lemma unitRadius_coordinate (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (x : ℂ) :
    rotatedAmplitude β κ f u 1 x =
      ((κ : ℂ) * (characterScale β / (2 * Real.pi) : ℂ)) *
        openCoordinate (rightTranslate positiveParameter weyl f)
          (((characterRotation β : ℂ) / (u : ℂ)) * x) := by
  have hr : KPCplxRotatedKernelEstimates.radialUnit 1 u = u := by
    apply Units.ext
    simp [KPCplxRotatedKernelEstimates.radialUnit]
  have hw : inductionWeight positiveParameter 1 u = 1 := by
    simp [inductionWeight, complexAbs, hu]
  unfold rotatedAmplitude
  rw [hr, unit_diagonal_chart]
  rw [mul_assoc (upperTriangular 1 u 0), f.property.1, hw]
  simp only [Complex.ofReal_one, one_mul, openCoordinate, rightTranslate]
  have he : (characterRotation β : ℂ) * x / (u : ℂ) =
      (characterRotation β : ℂ) / (u : ℂ) * x := by ring
  rw [he]

theorem norm_iteratedFDeriv_rotatedAmplitude_one_le (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂˣ) (z : ℂ), ‖(u : ℂ)‖ = 1 →
      ‖iteratedFDeriv ℝ h
        (fun x : ℂ => rotatedAmplitude β κ f u 1 x) z‖ ≤
        C * Real.rpow (1 + ‖z‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  let g := rightTranslate positiveParameter weyl f
  let a : ℂ := (κ : ℂ) * (characterScale β / (2 * Real.pi) : ℂ)
  obtain ⟨D, hD, hb⟩ := KPCplxPrincipalSeriesCharts.norm_iteratedFDeriv_openCoordinate_le g h
  refine ⟨(‖a‖ + 1) * D, mul_pos (by positivity) hD, ?_⟩
  intro u z hu
  let v : Circle := ⟨(characterRotation β : ℂ) / (u : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [hu]⟩
  let L : ℂ ≃ₗᵢ[ℝ] ℂ := rotation v
  have hL (x : ℂ) : L x = ((characterRotation β : ℂ) / (u : ℂ)) * x := rfl
  have he : (fun x : ℂ => rotatedAmplitude β κ f u 1 x) =
      (fun x : ℂ => a • (openCoordinate g ∘ L) x) := by
    funext x
    simpa only [a, g, Function.comp_apply, hL, smul_eq_mul] using
      unitRadius_coordinate β κ f u hu x
  have hs : ContDiff ℝ (⊤ : ℕ∞) (openCoordinate g ∘ L) :=
    g.property.2.1.comp L.toContinuousLinearEquiv.contDiff
  rw [he, iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by simp)), norm_smul,
    L.norm_iteratedFDeriv_comp_right]
  have hnorm : ‖L z‖ = ‖z‖ := L.norm_map z
  have hb' := hb (L z)
  rw [hnorm] at hb'
  calc
    ‖a‖ * ‖iteratedFDeriv ℝ h (openCoordinate g) (L z)‖ ≤
        ‖a‖ * (D * Real.rpow (1 + ‖z‖ ^ 2) (-(4 / 3 : ℝ) - (h : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
    _ ≤ (‖a‖ + 1) * (D * Real.rpow (1 + ‖z‖ ^ 2)
        (-(4 / 3 : ℝ) - (h : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      exact mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
    _ = _ := by ring

end DedekindZetaZeroFree.ThetaArchInducedMajorant
