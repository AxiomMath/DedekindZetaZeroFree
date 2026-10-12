module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RealParityGaussian

@[expose] public section

noncomputable section

open Classical MeasureTheory
open scoped RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity

private theorem fourier_tensor {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (ξ : EuclideanSpace ℝ ι) :
    (FourierTransform.fourier (fun x : EuclideanSpace ℝ ι ↦ ∏ i, f i (x i)) :
      EuclideanSpace ℝ ι → ℂ) ξ =
      ∏ i, (FourierTransform.fourier (f i) : ℝ → ℂ) (ξ i) := by
  simp only [Real.fourier_eq', smul_eq_mul]
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    RCLike.star_def, conj_trivial]
  simp only [Pi.star_apply, star_trivial, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [← Finset.prod_mul_distrib]
  simpa only [mul_comm] using (integral_fintype_prod_volume_eq_prod
    (fun i v ↦ Complex.exp (↑(-2 * Real.pi * (ξ i * v)) * Complex.I) * f i v))
 def localParity (odd : Bool) (x : ℝ) : ℂ :=
  (if odd then (x : ℂ) else 1) * Complex.exp (-((Real.pi * x ^ 2 : ℝ) : ℂ))

private theorem localParity_fourier (odd : Bool) :
    (FourierTransform.fourier (localParity odd) : ℝ → ℂ) =
      fun x ↦ (if odd then -Complex.I else 1) * localParity odd x := by
  unfold localParity
  cases odd
  · simpa using real_evenGaussian_fourier
  · simpa using real_oddGaussian_fourier

private theorem parity_tensor_fourier {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset ι) (ξ : EuclideanSpace ℝ ι) :
    (FourierTransform.fourier
      (fun x : EuclideanSpace ℝ ι ↦ ∏ i, localParity (decide (i ∈ D)) (x i)) :
        EuclideanSpace ℝ ι → ℂ) ξ =
      (-Complex.I)^D.card * ∏ i, localParity (decide (i ∈ D)) (ξ i) := by
  rw [fourier_tensor]
  simp_rw [localParity_fourier]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [Finset.prod_ite_mem_eq]

private theorem parity_tensor_eq {ι : Type*} [Fintype ι]
    (D : Finset ι) (x : EuclideanSpace ℝ ι) :
    (∏ i, localParity (decide (i ∈ D)) (x i)) =
      (∏ i ∈ D, (x i : ℂ)) * Theta.latticeGaussian Real.pi x := by
  unfold localParity Theta.latticeGaussian
  rw [Finset.prod_mul_distrib]
  simp only [decide_eq_true_eq, Finset.prod_ite_mem_eq]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp only [Complex.ofReal_sum, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, Finset.mul_sum, ← Finset.sum_neg_distrib, neg_mul]

private theorem gδ_tensor (K : Type) [Field K] [NumberField K]
    (δ : Finset (RayCoset.RealPlaces K)) (x : NumberField.mixedEmbedding.euclidean.mixedSpace K) :
    gδ K δ x =
      ∏ i : NumberField.mixedEmbedding.index K,
        localParity (decide (i ∈ δ.map ⟨Sum.inl, Sum.inl_injective⟩))
          (Theta.traceCoordinates K x i) := by
  have ht := parity_tensor_eq (δ.map (⟨Sum.inl, Sum.inl_injective⟩ :
    RayCoset.RealPlaces K ↪ NumberField.mixedEmbedding.index K)) (Theta.traceCoordinates K x)
  simpa only [Finset.prod_map, gδ, Theta.traceRealCoordinateCLM_apply,
    Theta.latticeGaussian, LinearIsometryEquiv.norm_map, Function.Embedding.coeFn_mk,
    localParity, decide_eq_true_eq] using ht.symm

variable (K : Type) [Field K] [NumberField K]

set_option maxHeartbeats 1000000 in

theorem fourier_gδ (δ : Finset (RayCoset.RealPlaces K))
    (ξ : NumberField.mixedEmbedding.euclidean.mixedSpace K) :
    (FourierTransform.fourier (gδ K δ) :
      NumberField.mixedEmbedding.euclidean.mixedSpace K → ℂ) ξ =
        εδ K δ * gδ K δ ξ := by
  let D : Finset (NumberField.mixedEmbedding.index K) := δ.map ⟨Sum.inl, Sum.inl_injective⟩
  let f : EuclideanSpace ℝ (NumberField.mixedEmbedding.index K) → ℂ :=
    fun x ↦ ∏ i, localParity (decide (i ∈ D)) (x i)
  have hg : gδ K δ = f ∘ Theta.traceCoordinates K := by
    funext x
    exact gδ_tensor K δ x
  rw [hg, Real.fourier_comp_linearIsometry]
  rw [show (FourierTransform.fourier f : _ → ℂ) (Theta.traceCoordinates K ξ) =
    (-Complex.I)^D.card * f (Theta.traceCoordinates K ξ) from parity_tensor_fourier D _]
  simp only [D, Finset.card_map, εδ, Function.comp_apply]

end DedekindZetaZeroFree.AbelianQuotient.RayParity

end
