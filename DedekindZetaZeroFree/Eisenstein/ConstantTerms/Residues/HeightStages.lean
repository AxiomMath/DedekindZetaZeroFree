module

public import DedekindZetaZeroFree.Metaplectic.Iwasawa.LogarithmicModulusSupport
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.FlatFiberVector

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem current_height_stage (s : RestrictedTensorSimple.Level (bad R.A P C))
    (g : Raw R.A)
    (htail : ∀ p, p ∉ s.val → FaithfulSource.RepairedInducing.localLog R P C g p = 0) :
    ThetaExpansion.iwasawaLogHeight R
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      ∑ j : s.val, FaithfulSource.RepairedInducing.localLog R P C g j := by
  let s' : RestrictedTensorSimple.Level (FaithfulSource.RepairedInducing.bad R P C) :=
    ⟨s.val, by
      change PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet F R.A.zeta12
        R.A.primitive_zeta12 P C ⊆ s.val
      rw [PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad]
      exact s.property⟩
  exact FaithfulSource.RepairedInducing.height_eq_stage_localLog R P C s' g htail

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
