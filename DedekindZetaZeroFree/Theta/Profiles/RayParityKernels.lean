module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CosetSignsAndNorms
public import DedekindZetaZeroFree.Theta.Profiles.MixedGaussian

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity

variable (K : Type) [Field K] [NumberField K]

def gδ (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K) : ℂ :=
  (∏ v ∈ δ, (Theta.traceRealCoordinateCLM K v x : ℂ)) *
    Theta.latticeGaussian Real.pi x

theorem traceRealCoordinateCLM_eq_traceToMixed
    (v : RayCoset.RealPlaces K) (x : euclidean.mixedSpace K) :
    Theta.traceRealCoordinateCLM K v x = (Theta.traceToMixed K x).1 v := rfl

@[simp] theorem traceRealCoordinateCLM_traceEmbedding
    (v : RayCoset.RealPlaces K) (α : K) :
    Theta.traceRealCoordinateCLM K v (Theta.traceEmbedding K α) =
      RayCoset.realEmbedding K v α := by
  change (Theta.traceToMixed K (Theta.traceEmbedding K α)).1 v = _
  simp only [Theta.traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
  exact mixedEmbedding.mixedEmbedding_apply_isReal K α v

def Q (q : InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) :
    euclidean.mixedSpace K :=
  (Theta.traceToMixed K).symm
    (mixedSpaceOfRealSpace q * Theta.traceToMixed K x)

theorem Q_eq_traceRadialScale (q : InfinitePlace K → ℝ)
    (hq : ∀ v, q v ≠ 0) (x : euclidean.mixedSpace K) :
    Q K q x = Theta.traceRadialScale K q hq x := by
  apply (Theta.traceToMixed K).injective
  simp only [Q, ContinuousLinearEquiv.apply_symm_apply,
    Theta.traceToMixed_traceRadialScale]

def εδ (δ : Finset (RayCoset.RealPlaces K)) : ℂ :=
  (-Complex.I) ^ δ.card

def κδ (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) : ℂ :=
  ((2 : ℂ) ^ nrRealPlaces K)⁻¹ * ((4 : ℂ) ^ nrComplexPlaces K)⁻¹ *
    (∏ v : RayCoset.RealPlaces K,
      Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0)) *
    (Complex.Gammaℂ s) ^ nrComplexPlaces K

def hδ (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ nrRealPlaces K * (4 : ℂ) ^ nrComplexPlaces K *
    (∏ v : RayCoset.RealPlaces K,
      (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹) *
    ((Complex.Gammaℂ s)⁻¹) ^ nrComplexPlaces K

end DedekindZetaZeroFree.AbelianQuotient.RayParity

end
