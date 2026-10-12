module

public import DedekindZetaZeroFree.LFunctions.Tate.ComplexTraceFourierMellinNormalization

@[expose] public section

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace

def psi (β z : ℂ) : ℂ :=
  Complex.exp (((2 * Real.pi * (β * z).re : ℝ) : ℂ) * Complex.I)

def mu (β : ℂ) : Measure ℂ :=
  ENNReal.ofReal ‖β‖ • (volume : Measure ℂ)

def F (β : ℂ) (g : ℂ → ℂ) (y : ℂ) : ℂ :=
  ∫ x : ℂ, g x * psi β (-x * y) ∂mu β

def M (β a : ℂ) (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  psi β (a * x ^ 2) * g x

def K (β : ℂ) (ε : ℝ) (a ξ : ℂ) : ℂ :=
  ∫ x : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
    psi β (a * x ^ 2 - x * ξ) ∂mu β

theorem norm_psi (β z : ℂ) : ‖psi β z‖ = 1 := by
  rw [psi, Complex.norm_exp_ofReal_mul_I]

def freqMap (β : ℂ) : ℂ →L[ℝ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.mul ℝ ℂ β)

private lemma freqMap_apply (β y : ℂ) : freqMap β y = (starRingEnd ℂ) (β * y) := rfl

private lemma re_neg_mul_eq_inner (β x y : ℂ) :
    (β * (-x * y)).re = -⟪x, (starRingEnd ℂ) (β * y)⟫_ℝ := by
  rw [Complex.inner]
  have hA : β * (-x * y) = -(β * x * y) := by ring
  have hB : (starRingEnd ℂ) (β * y) * (starRingEnd ℂ) x = (starRingEnd ℂ) (β * x * y) := by
    rw [← map_mul]
    congr 1
    ring
  rw [hA, hB, Complex.neg_re, Complex.conj_re]

private lemma psi_neg_mul_eq_fourierChar (β y x : ℂ) :
    psi β (-x * y) = (Real.fourierChar (-⟪x, (starRingEnd ℂ) (β * y)⟫_ℝ) : ℂ) := by
  rw [psi, Real.fourierChar_apply, re_neg_mul_eq_inner]

theorem F_eq_fourier (β : ℂ) (hβ : β ≠ 0) (g : ℂ → ℂ) (y : ℂ) :
    F β g y = (‖β‖ : ℂ) *
      FourierTransform.fourier g ((starRingEnd ℂ) (β * y)) := by
  rw [F, mu, integral_smul_measure, ENNReal.toReal_ofReal (norm_nonneg β),
    Complex.real_smul, Real.fourier_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [psi_neg_mul_eq_fourierChar β y x, Circle.smul_def]
  ring

theorem integrable_schwartz_mu (β : ℂ) (f : SchwartzMap ℂ ℂ) :
    Integrable (⇑f) (mu β) := by
  rw [mu]
  exact f.integrable.smul_measure ENNReal.ofReal_ne_top

private lemma antilipschitzWith_freqMap {β : ℂ} (hβ : β ≠ 0) :
    AntilipschitzWith (‖β‖₊)⁻¹ (freqMap β) := by
  refine AntilipschitzWith.of_le_mul_nndist fun x y => ?_
  have h : nndist (freqMap β x) (freqMap β y) = ‖β‖₊ * nndist x y := by
    rw [freqMap_apply, freqMap_apply, nndist_eq_nnnorm, nndist_eq_nnnorm]
    rw [← map_sub, ← mul_sub, RCLike.nnnorm_conj, nnnorm_mul]
  rw [h, inv_mul_cancel_left₀]
  exact nnnorm_ne_zero_iff.mpr hβ

theorem integrable_F_schwartz_mu (β : ℂ) (f : SchwartzMap ℂ ℂ) :
    Integrable (F β (⇑f)) (mu β) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [mu]
    simp
  · have hsch : Integrable
        (fun y : ℂ => FourierTransform.fourier (⇑f) ((starRingEnd ℂ) (β * y)))
        (volume : Measure ℂ) := by
      have h := (SchwartzMap.compCLMOfAntilipschitz ℂ (freqMap β).hasTemperateGrowth
        (antilipschitzWith_freqMap hβ) (FourierTransform.fourier f)).integrable (μ := volume)
      simpa only [Function.comp_def, freqMap_apply, SchwartzMap.compCLMOfAntilipschitz_apply,
        SchwartzMap.fourier_coe] using h
    have h2 : Integrable
        (fun y : ℂ => (‖β‖ : ℂ) * FourierTransform.fourier (⇑f)
          ((starRingEnd ℂ) (β * y))) (volume : Measure ℂ) :=
      hsch.const_mul (‖β‖ : ℂ)
    have h3 : Integrable
        (fun y : ℂ => (‖β‖ : ℂ) * FourierTransform.fourier (⇑f)
          ((starRingEnd ℂ) (β * y))) (mu β) :=
      h2.smul_measure ENNReal.ofReal_ne_top
    refine h3.congr ?_
    filter_upwards with y
    exact (F_eq_fourier β hβ (⇑f) y).symm

theorem mu_two : mu (2 : ℂ) = (2 : ℝ≥0∞) • (volume : Measure ℂ) := by
  rw [mu]
  norm_num

end
end DedekindZetaZeroFree.ComplexWeil
