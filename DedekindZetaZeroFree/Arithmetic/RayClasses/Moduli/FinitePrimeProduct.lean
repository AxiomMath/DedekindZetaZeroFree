module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ModulusIdeal

@[expose] public section

namespace DedekindZetaZeroFree.KummerConductorProduct
noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem modulus_eq (F : Type) [Field F] [NumberField F]
    (hc : NumberField.IsTotallyComplex F) (c : ClassFieldTheory.RayClassModulus F) :
    M F (PrimitiveRay.modulusIdeal c.finitePart)
      (PrimitiveRay.modulusIdeal_ne_bot _) = c := by
  letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (hc.isComplex v.val)) v.property⟩
  apply ClassFieldTheory.RayClassModulus.ext
  · exact PrimitiveRay.modulusIdeal_M _
  · exact Subsingleton.elim _ _

end
end DedekindZetaZeroFree.KummerConductorProduct
