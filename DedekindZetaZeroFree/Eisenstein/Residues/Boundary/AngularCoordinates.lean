module

public import DedekindZetaZeroFree.Eisenstein.Residues.UpperConstantTerm.RationalTorusInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource ResidualBoundaryInvariance
open _root_.DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarAngularDescent renaming eqv_eval → eqv_eval
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
local notation "Source" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)

theorem boundaryProduct_rational_unipotent (f : Source) (x : V)
    (y : Fˣ) (a : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    boundaryProduct R P C f x (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ a)*g)=boundaryProduct R P C f x g := by
  unfold boundaryProduct
  rw [KPMsRationalCompactCrossPairingProof.ScalarAngularDescent.source_rational]
  change _ * star (KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
    (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x) _) = _
  rw [mul_assoc,upper_rational _ (coreResidue_raw_automorphic R P C x).1.1
    (coreResidue_rational_subgroup R P C x),upper_unipotent _ (coreResidue_rational_subgroup R P C x)]
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
