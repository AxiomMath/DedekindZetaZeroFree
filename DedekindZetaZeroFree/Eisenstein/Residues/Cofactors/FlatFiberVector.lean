module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.FlatSectionExtension
public import DedekindZetaZeroFree.Eisenstein.Residues.RationalComparison

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages KPLiteralRaw KPAdelicCoverRestrictedProduct
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def coreFlatFiber (x : Core) (z : ℂ) (g : Raw R.A) :=
  Complex.exp (z * (ThetaExpansion.iwasawaLogHeight R
    (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) : ℂ)) •
    PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
      (rawCoreFiber R.A P C g x)

theorem coreFlatFiber_stage
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Plus R.A P C j.val) (g : Raw R.A)
    (htail : ∀ v, v ∉ s.val → localValue R.A P C v (g v)
      (plusReference R.A P C v) = reference R.A P C v)
    (z : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    (coreFlatFiber R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ x)) z g).val.val t =
    Complex.exp (z * (ThetaExpansion.iwasawaLogHeight R
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) : ℂ)) *
    (comparison R.A P C (RestrictedTensorSimple.stageInclusion
      (Fiber R.A P C) (reference R.A P C) (bad R.A P C) s
      (PiTensorProduct.tprod ℂ (fun j => localValue R.A P C j.val (g j.val) (x j))))).val.val t := by
  unfold coreFlatFiber
  rw [rawCoreFiber_stage R.A P C s _ g htail]
  simp only [rawStageFiber, LinearMap.comp_apply, PiTensorProduct.map_tprod]
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
