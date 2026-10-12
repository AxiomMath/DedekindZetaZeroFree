module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.NormalSeries
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordChamber
open KPContActualSphericalRightFieldIdentification
open KPContActualChamberNormalSeries
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def wordReindex (w : List (Fin (groupDimension F))) : Word F :=
  w.map (fun b => actualBasisReindex F (lieEnumeration F b))

theorem actualRightWord_eq_rightWord (w : List (Fin (groupDimension F)))
    (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ) :
    actualRightWord F ζ hζ w u = rightWord F ζ hζ (wordReindex F w) u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change actualRight F ζ hζ b (actualRightWord F ζ hζ w u) = _
    rw [ih]
    funext g
    change deriv (fun t : ℝ => _) 0 = deriv (fun t : ℝ => _) 0
    congr 1
    funext t
    rw [actual_frame_ray_eq_flow F]
    rfl

variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

theorem actualRightWord_eq_tsum (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (w : List (Fin (groupDimension F))) (s : ℂ) (hs : s ∈ V)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    actualRightWord F ζ hζ w (E F ζ hζ U ι f s) g =
      ∑' q : Q F, actualRightWord F ζ hζ w (term F ζ hζ U ι f q s) g := by
  simp_rw [actualRightWord_eq_rightWord]
  simpa only [mixedJet, iteratedDerivWithin_zero] using
    mixedJet_eq_tsum F ζ hζ U ι f hι hf 0 (wordReindex F w) s hs g

theorem actualRightWord_summable (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (w : List (Fin (groupDimension F))) (s : ℂ) (hs : s ∈ V)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    Summable (fun q : Q F => actualRightWord F ζ hζ w (term F ζ hζ U ι f q s) g) := by
  simp_rw [actualRightWord_eq_rightWord]
  simpa only [mixedJet, iteratedDerivWithin_zero] using
    (mixed_summable F ζ hζ U ι f hι hf 0 (wordReindex F w) s hs g).of_norm

theorem actualRightWord_left_translate (w : List (Fin (groupDimension F)))
    (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (a g : KPGlobalTorusFunctionData.G F ζ hζ) :
    actualRightWord F ζ hζ w (fun h => u (a * h)) g =
      actualRightWord F ζ hζ w u (a * g) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simp only [actualRightWord, actualRight]
    congr 1
    funext t
    rw [ih, mul_assoc]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordChamber

end
