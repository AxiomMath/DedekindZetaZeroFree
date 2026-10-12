module

public import DedekindZetaZeroFree.Theta.Whittaker.Borel.TraceFrequencyReduction

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPWildInverseBorelFrequencyReduction
open KPGlobalTorusFunctionData
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem conjugate_integral (X : Type*) [MeasurableSpace X] (μ : Measure X)
    [AddGroup X] (f : X → ℂ) (χ : AddChar X Circle) :
    (∫ x, starRingEnd ℂ (f x) * (χ x : ℂ) ∂μ) =
      starRingEnd ℂ (∫ x, f x * ((χ x : ℂ)⁻¹) ∂μ) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul]
  congr 1
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  simp

theorem borel_nontrivial_fourier_zero_iff_inverse_standard_trace_zero
    (μ : Measure (KPCompactFourier.AdditiveQuotient F))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (θ : G F ζ hζ → ℂ) (hθcont : Continuous θ)
    (hθrat : ∀ γ g, θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g) :
    (∀ (b : borel F ζ hζ) (χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle),
      Continuous χ → χ ≠ 1 →
        (∫ x, θ (N F ζ hζ (KPCompactFourier.representative F x) * b.val) *
          (χ x : ℂ) ∂μ) = 0) ↔
    (∀ b : borel F ζ hζ,
      (∫ x, θ (N F ζ hζ (KPCompactFourier.representative F x) * b.val) *
        ((adelicTraceQuotientCharacter F x : ℂ)⁻¹) ∂μ) = 0) := by
  constructor
  · intro h b
    simpa only [AddChar.inv_apply', Circle.coe_inv] using
      h b (adelicTraceQuotientCharacter F)⁻¹
        ((continuous_adelicTraceQuotientCharacter F).comp continuous_neg)
        (inv_ne_one.mpr (adelicTraceQuotientCharacter_ne_one F))
  · intro hp
    have hconj := KPWildBorelFrequencyReduction.borel_nontrivial_fourier_zero_iff_standard_trace_zero
      F ζ hζ μ (fun g => starRingEnd ℂ (θ g)) (Complex.continuous_conj.comp hθcont)
      (fun γ g => congrArg (starRingEnd ℂ) (hθrat γ g))
    have hall := hconj.mpr (fun b => by
      rw [conjugate_integral, hp b, map_zero])
    intro b χ hχ hχne
    have h := hall b χ⁻¹ (hχ.comp continuous_neg) (inv_ne_one.mpr hχne)
    rw [conjugate_integral] at h
    have hh := congrArg (starRingEnd ℂ) h
    simpa only [AddChar.inv_apply', Circle.coe_inv, inv_inv, Complex.conj_conj,
      map_zero] using hh

end DedekindZetaZeroFree.KPWildInverseBorelFrequencyReduction

end
