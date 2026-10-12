module

public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.QuotientRealization
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SmoothChartsAndCompactBounds

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
local instance ResidualQuotientWordsMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualQuotientWordsBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

theorem coreResidueQuotient_word_of_raw (x y : Core)
    (b : List (Fin (groupDimension F)))
    (hx : ∀g, coreResidueQuotient R P C x (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g)
    (hy : ∀g, coreResidueQuotient R P C y (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C y g)
    (he : actualRightWord F ζ hζ b (coreResidue R P C x)=coreResidue R P C y) :
    ResidualOutputSobolev.quotientWord b (coreResidueQuotient R P C x)=coreResidueQuotient R P C y := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change ResidualOutputSobolev.quotientWord b (coreResidueQuotient R P C x)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=_
    rw [ResidualOutputSobolev.quotientWord_lift]
    rw [show (fun g => coreResidueQuotient R P C x
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))=coreResidue R P C x from funext hx, he]
    exact (hy g).symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
