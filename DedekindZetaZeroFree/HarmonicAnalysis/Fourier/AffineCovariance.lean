module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace DedekindZetaZeroFree.AbelianQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def affineSchwartz (f : SchwartzMap E ℂ) (A : E ≃L[ℝ] E) (z : E) :
    SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    ((Function.HasTemperateGrowth.const z).add Function.HasTemperateGrowth.id')
    (IsometryEquiv.addLeft z).isometry.antilipschitz
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f)

@[simp] theorem affineSchwartz_apply (f : SchwartzMap E ℂ)
    (A : E ≃L[ℝ] E) (z x : E) :
    affineSchwartz f A z x = f (A (z + x)) := rfl

private theorem affineFourier_linear_covariance (f : SchwartzMap E ℂ) (A : E ≃L[ℝ] E) (ξ : E) :
    FourierTransform.fourier ((f : E → ℂ) ∘ A) ξ =
      ((|LinearMap.det A.toLinearEquiv.toLinearMap| : ℝ) : ℂ)⁻¹ *
      (FourierTransform.fourier f) (A.symm.toContinuousLinearMap.adjoint ξ) := by
  have hm : Measure.map A volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  have hi := A.toHomeomorph.measurableEmbedding.integral_map
    (fun y : E ↦ Real.fourierChar (-inner ℝ y (A.symm.toContinuousLinearMap.adjoint ξ)) • f y)
    (μ := volume)
  change (∫ y : E, Real.fourierChar (-inner ℝ y (A.symm.toContinuousLinearMap.adjoint ξ)) • f y ∂Measure.map A volume) =
    ∫ x : E, Real.fourierChar (-inner ℝ (A x) (A.symm.toContinuousLinearMap.adjoint ξ)) • f (A x) at hi
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hi
  simp only [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at hi
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  simp only [Function.comp_apply]
  rw [← hi]
  simp only [abs_inv, Complex.real_smul, Complex.ofReal_inv,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe]

theorem affineFourierCovariance (f : SchwartzMap E ℂ)
    (A : E ≃L[ℝ] E) (z ξ : E) :
    (FourierTransform.fourier (affineSchwartz f A z)) ξ =
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ z : ℂ)) *
      ((|LinearMap.det A.toLinearEquiv.toLinearMap| : ℝ) : ℂ)⁻¹ *
      (FourierTransform.fourier f) (A.symm.toContinuousLinearMap.adjoint ξ) := by
  rw [SchwartzMap.fourier_coe]
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ E) ((f : E → ℂ) ∘ A) z) ξ
  change FourierTransform.fourier (((f : E → ℂ) ∘ A) ∘ (fun x : E ↦ x + z)) ξ =
    Real.fourierChar (inner ℝ z ξ) • FourierTransform.fourier ((f : E → ℂ) ∘ A) ξ at ht
  have hc : (affineSchwartz f A z : E → ℂ) =
      ((f : E → ℂ) ∘ A) ∘ (fun x : E ↦ x + z) := by
    ext x
    simp only [affineSchwartz_apply, Function.comp_apply, add_comm]
  rw [hc, ht, affineFourier_linear_covariance]
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  rw [real_inner_comm z ξ]
  push_cast
  rw [show (2 * (Real.pi : ℂ) * (inner ℝ z ξ : ℂ) * Complex.I) =
    (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ z ξ : ℂ)) by ring]
  simp only [mul_assoc]

end DedekindZetaZeroFree.AbelianQuotient

end
