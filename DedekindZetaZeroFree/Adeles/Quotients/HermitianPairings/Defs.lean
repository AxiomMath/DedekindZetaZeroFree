module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.SmoothDescent
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.CutoffGraphApproximation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffTestPairingHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev Tests := KPCuspCutoffGraph.scalarTests F ζ hζ H.totallyComplex
  (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)
  (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U))

def testScalar (ψ : Tests F ζ hζ C R P H U) :
    KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ :=
  KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U ⟨ψ.val, ψ.property.1⟩

def testLaplacian (φ : Tests F ζ hζ C R P H U) :
    KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ :=
  ((KPContSectorScalarLineAlgebra.S F ζ hζ
    (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H).symm
    (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)
      (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U))
      ⟨φ.val, φ.property.1⟩)).val

def coveredPair (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U)
    (ψ : KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ) :
    KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ :=
  fun x => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U w x *
    star (ψ x)

def quotientPair (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U)
    (ψ : KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ) :
    KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ :=
  coveredPair F ζ hζ C R P H U w ψ ∘
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)

end DedekindZetaZeroFree.KPContActualCutoffTestPairingHolomorphy

end
