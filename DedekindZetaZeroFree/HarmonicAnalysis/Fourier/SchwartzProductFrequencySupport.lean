module

public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

open Metric MeasureTheory
open scoped FourierTransform Convolution

namespace DedekindZetaZeroFree

private lemma fourier_fourier_apply_neg {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (f : SchwartzMap W ℂ) (x : W) :
    ((𝓕 (𝓕 f) : SchwartzMap W ℂ) : W → ℂ) x = f (-x) := by
  have h := Continuous.fourierInv_fourier_eq f.continuous f.integrable (𝓕 f).integrable
  have hx := congrFun h (-x)
  rw [Real.fourierInv_eq_fourier_neg] at hx
  simpa only [SchwartzMap.fourier_coe, neg_neg] using hx

private lemma schwartz_pairing_fourier_eq_convolution {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (f g : SchwartzMap W ℂ) :
    (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) : SchwartzMap W ℂ)
      = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  have hA : (𝓕 (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g)) : SchwartzMap W ℂ)
      = 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) := by
    ext x
    rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
    rw [fourier_fourier_apply_neg, fourier_fourier_apply_neg]
    rw [fourier_fourier_apply_neg, SchwartzMap.pairing_apply_apply]
  have h2 := congrArg (fun (h : SchwartzMap W ℂ) => (𝓕⁻ h : SchwartzMap W ℂ)) hA
  simpa using h2

theorem schwartz_product_fourier_tsupport_subset_closedBall
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (f g : SchwartzMap W ℂ) (R Q : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hf : tsupport ((𝓕 f : SchwartzMap W ℂ) : W → ℂ) ⊆ closedBall (0 : W) R)
    (hg : tsupport ((𝓕 g : SchwartzMap W ℂ) : W → ℂ) ⊆ closedBall (0 : W) Q) :
    tsupport ((𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) :
      SchwartzMap W ℂ) : W → ℂ) ⊆ closedBall (0 : W) (R + Q) := by
  have hfun : ((𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) : SchwartzMap W ℂ) :
        W → ℂ)
      = fun x => (((𝓕 f : SchwartzMap W ℂ) : W → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
                    ((𝓕 g : SchwartzMap W ℂ) : W → ℂ)) x := by
    rw [schwartz_pairing_fourier_eq_convolution]
    ext x
    exact SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) x
  have hsupp : Function.support ((𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g) :
        SchwartzMap W ℂ) : W → ℂ) ⊆ closedBall (0 : W) (R + Q) := by
    rw [hfun]
    refine (MeasureTheory.support_convolution_subset (L := ContinuousLinearMap.mul ℂ ℂ)
      (f := ((𝓕 f : SchwartzMap W ℂ) : W → ℂ))
      (g := ((𝓕 g : SchwartzMap W ℂ) : W → ℂ))).trans ?_
    refine (Set.add_subset_add ((subset_tsupport _).trans hf)
      ((subset_tsupport _).trans hg)).trans ?_
    intro x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    simp only [mem_closedBall, dist_eq_norm, sub_zero] at ha hb ⊢
    exact (norm_add_le a b).trans (add_le_add ha hb)
  exact closure_minimal hsupp isClosed_closedBall

end DedekindZetaZeroFree
