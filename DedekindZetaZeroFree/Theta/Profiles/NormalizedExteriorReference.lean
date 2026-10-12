module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct
public import DedekindZetaZeroFree.Metaplectic.Induction.NormalizedPlusSections

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.FourierContinuation.CurrentExteriorReference
open KPLocalPrincipalSeries KPLocalGoodSphericalImage KPGlobalTorusFiniteStages
open KPActualReflectionData
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
 theorem plusReference_eq_normalized (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    LiteralSource.plusReference A P C (Sum.inr q) =
      (CanonicalPlusReferences.normalized_canonical_section A P C q hq).choose := by
  simp only [LiteralSource.plusReference, dite_eq_left hq]
 def profile (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    compactPicture (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus :=
  (compactTrivialization (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .plus 0).symm
      (CanonicalPlusReferences.normalized_canonical_section A P C q hq).choose
 theorem profile_zero (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus 0 (profile A P C q hq) =
        LiteralSource.plusReference A P C (Sum.inr q) := by
  rw [profile, LinearEquiv.apply_symm_apply, plusReference_eq_normalized A P C q hq]
end DedekindZetaZeroFree.FourierContinuation.CurrentExteriorReference

end
