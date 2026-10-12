module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.OperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives.CurrentFirstRoot
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion FourierContinuation.LiteralSource FourierContinuation.HCGeneration
open KPContActualSphericalRightFieldIdentification
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def upperBasis (b : Bool) : Fin 6 := if b then 3 else 2

theorem upper_index (w : InfinitePlace F) (b : Bool) :
    actualLieIndexEquiv (F := F) (RootDerivatives.upperIndex w b) = (w,upperBasis b) := by
  cases b <;> simp [actualLieIndexEquiv,RootDerivatives.upperIndex,actualBasisReindex,
    upperBasis,finProdFinEquiv]

def rootLocal (i : ℤ) : Module.End ℂ KPGlobalResidualConstruction.complexCore :=
  (Complex.I * (4 * Real.pi : ℂ))⁻¹ •
    (complexGenerator (.inr (upperBasis false)) +
      (if i=1 then -Complex.I else Complex.I) • complexGenerator (.inr (upperBasis true)))

end DedekindZetaZeroFree.RootDerivatives.CurrentFirstRoot

end
