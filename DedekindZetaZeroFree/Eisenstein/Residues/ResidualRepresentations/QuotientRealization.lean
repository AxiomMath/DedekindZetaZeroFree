module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryPairings.FiniteCenterPairing
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteRefinedBoundaryCenters
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.CoreCompactCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open KPContSectorCoveredQuotientVocabulary KPContFlatCuspIncomingEvaluation
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
variable (HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
variable (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
variable (U : Level F R.A.zeta12 R.A.primitive_zeta12)
local notation "H" => nativeFamily F ζ hζ HR HP
local notation "V" => EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U
local instance ResidualCoreQuotientMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualCoreQuotientBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

def coreResidueQuotient : Core →ₗ[ℂ] (KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ) where
  toFun x q := coreResidue R P C x (Quotient.out q)
  map_add' := by
    intro x y
    funext q
    exact congrFun (map_add (coreResidue R P C) x y) (Quotient.out q)
  map_smul' := by
    intro a x
    funext q
    exact congrFun (map_smul (coreResidue R P C) a x) (Quotient.out q)

theorem coreResidueQuotient_eq_of_lift (x : Core)
    (f : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ)
    (hf : ∀g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g) :
    coreResidueQuotient R P C x = f := by
  funext q
  change coreResidue R P C x (Quotient.out q)=f q
  rw [←hf]
  exact congrArg f (Quotient.out_eq q)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
