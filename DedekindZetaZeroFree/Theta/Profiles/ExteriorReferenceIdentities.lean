module

public import DedekindZetaZeroFree.Eisenstein.Induction.CanonicalExteriorVectorEulerFactors

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.FourierContinuation.CurrentExteriorReference
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
 theorem profile_eq_exterior (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    profile A P C q hq =
      ExteriorVectorHaar.canonicalProfile F A.zeta12 A.primitive_zeta12 P C q hq := by
  rfl
 theorem plusReference_eq_exterior (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    LiteralSource.plusReference A P C (Sum.inr q) =
      compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0
        (ExteriorVectorHaar.canonicalProfile F A.zeta12 A.primitive_zeta12 P C q hq) := by
  rw [← profile_eq_exterior A P C q hq, profile_zero]
end DedekindZetaZeroFree.FourierContinuation.CurrentExteriorReference

end
