module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.OutgoingZeroModeTails

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberMeanZeroAdapter

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev V : Set ℂ := KPContActualChamberNormalSeries.V
abbrev level := KPContActualAllCuspSource.level F ζ hζ C R P H U
abbrev Cusps := KPContActualAllCuspSource.Cusps F ζ hζ C R P H U
abbrev d := KPCuspLogShape.dimension F

variable (a : Cusps F ζ hζ C R P H U)

abbrev geometry := KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a
abbrev KernelTorus := KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a

abbrev fiberMeasure : Measure (KPContActualChamberOutgoingAdapter.KernelTorus F ζ hζ C R P H U a) :=
  KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a

abbrev endMeasure := KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a

abbrev tail (T : ℝ) : Set (KPCuspCharts.Coordinates F) :=
  KPContActualChamberOutgoingAdapter.tail F T

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def meanZeroJetSheet (k : ℕ) (s : ℂ) (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) : ℂ :=
  KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t x b ε -
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
        (fiberMeasure F ζ hζ C R P H U a) k s t b).val (QuotientAddGroup.mk x)

def meanZero (s : ℂ) (p : KPCuspCharts.Coordinates F) : ℂ :=
  meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s p.2 p.1.1 p.1.2 1

def parameterScalar (k : ℕ) (s : ℂ) (z : KPArch.Space (d F)) : ℂ :=
  iteratedDerivWithin k
    (fun w => meanZero F ζ hζ C R P H U a ι f w
      ((KPCuspCharts.toArchHomeomorph F
        (geometry F ζ hζ C R P H U a).positive_dimension).symm z)) V s

end DedekindZetaZeroFree.KPContActualChamberMeanZeroAdapter

end
