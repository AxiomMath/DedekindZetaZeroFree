module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.AffineCovariance
public import DedekindZetaZeroFree.Theta.Profiles.RayParityFourierMellin

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.AffineFourier

variable (K : Type) [Field K] [NumberField K]

def positiveScaling (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  Theta.traceRadialScale K q (fun v ↦ ne_of_gt (hq v))

theorem positiveScaling_apply (q : InfinitePlace K → ℝ)
    (hq : ∀ v, 0 < q v) (x : euclidean.mixedSpace K) :
    positiveScaling K q hq x = Q K q x := by
  exact (Q_eq_traceRadialScale K q (fun v ↦ ne_of_gt (hq v)) x).symm

theorem positiveScaling_symm_apply (q : InfinitePlace K → ℝ)
    (hq : ∀ v, 0 < q v) (x : euclidean.mixedSpace K) :
    (positiveScaling K q hq).symm x = Q K (fun v ↦ (q v)⁻¹) x := by
  exact (Theta.traceRadialScale_symm_apply K q (fun v ↦ ne_of_gt (hq v)) x).trans
    (Q_eq_traceRadialScale K (fun v ↦ (q v)⁻¹)
      (fun v ↦ inv_ne_zero (ne_of_gt (hq v))) x).symm

theorem det_positiveScaling (q : InfinitePlace K → ℝ)
    (hq : ∀ v, 0 < q v) :
    LinearMap.det (positiveScaling K q hq).toLinearMap = J K q := by
  rw [positiveScaling, Theta.det_traceRadialScale, J]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace K ↦ IsReal v)]
  simp only [mult_isReal, pow_one]
  congr 1
  exact (Fintype.prod_equiv
    (Equiv.subtypeEquivRight
      (fun v : InfinitePlace K ↦ not_isReal_iff_isComplex))
    (fun v ↦ q v.1 ^ v.1.mult) (fun v ↦ q v.1 ^ 2)
    (fun v ↦ by simp [mult, v.2])).symm

theorem J_pos (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    0 < J K q := by
  exact Finset.prod_pos (fun v _ ↦ pow_pos (hq v) _)

def shiftedSchwartz (δ : Finset (RayCoset.RealPlaces K))
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v)
    (z : euclidean.mixedSpace K) : SchwartzMap (euclidean.mixedSpace K) ℂ :=
  affineSchwartz (rayParitySchwartz K δ) (positiveScaling K q hq) z

theorem shiftedSchwartz_apply (δ : Finset (RayCoset.RealPlaces K))
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v)
    (z x : euclidean.mixedSpace K) :
    shiftedSchwartz K δ q hq z x = gδ K δ (Q K q (z + x)) := by
  rw [shiftedSchwartz, affineSchwartz_apply, rayParitySchwartz_apply,
    positiveScaling_apply]

theorem fourier_shiftedSchwartz (δ : Finset (RayCoset.RealPlaces K))
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v)
    (z ξ : euclidean.mixedSpace K) :
    (FourierTransform.fourier (shiftedSchwartz K δ q hq z)) ξ =
      (J K q : ℂ)⁻¹ * εδ K δ *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ z : ℂ)) *
        gδ K δ (Q K (fun v ↦ (q v)⁻¹) ξ) := by
  have hadj : (positiveScaling K q hq).symm.toContinuousLinearMap.adjoint ξ =
      Q K (fun v ↦ (q v)⁻¹) ξ := by
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ ξ ((positiveScaling K q hq).symm y) = _
    rw [positiveScaling_symm_apply]
    rw [Q_eq_traceRadialScale K (fun v ↦ (q v)⁻¹)
      (fun v ↦ inv_ne_zero (ne_of_gt (hq v))) ξ,
      Q_eq_traceRadialScale K (fun v ↦ (q v)⁻¹)
      (fun v ↦ inv_ne_zero (ne_of_gt (hq v))) y]
    exact (Theta.inner_traceRadialScale K (fun v ↦ (q v)⁻¹)
      (fun v ↦ inv_ne_zero (ne_of_gt (hq v))) ξ y).symm
  rw [shiftedSchwartz, affineFourierCovariance, hadj, det_positiveScaling,
    abs_of_pos (J_pos K q hq)]
  have hf : (rayParitySchwartz K δ : euclidean.mixedSpace K → ℂ) = gδ K δ := by
    ext x
    exact rayParitySchwartz_apply K δ x
  rw [SchwartzMap.fourier_coe, hf, FourierMellin.fourier]
  ring

theorem gδ_zero (δ : Finset (RayCoset.RealPlaces K)) :
    gδ K δ 0 = if δ = ∅ then 1 else 0 := by
  classical
  by_cases hδ : δ = ∅
  · simp [gδ, hδ, Theta.latticeGaussian]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hδ
    have hp : (∏ v ∈ δ, (Theta.traceRealCoordinateCLM K v 0 : ℂ)) = 0 :=
      Finset.prod_eq_zero hv (by simp)
    simp [gδ, hp, hδ]

end DedekindZetaZeroFree.AbelianQuotient.RayParity.AffineFourier

end
