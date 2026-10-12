module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FinitePrimeProduct

@[expose] public section

namespace DedekindZetaZeroFree.KummerConductorLeast
noncomputable section
open scoped NumberField Classical

theorem publicIsAbelianConductor (F L : Type) [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [IsAbelianGalois F L]
    (hc : NumberField.IsTotallyComplex F) :
    ClassFieldTheory.IsAbelianConductor F L
      (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F L) := by
  letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (hc.isComplex v.val)) v.property⟩
  have heq : (ClassFieldTheory.RayClassModulus.mk
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
        (K := F) (L := L)).fullConductor.finitePart
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
        (K := F) (L := L)).fullConductor.infinitePart) =
      ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F L := by
    apply ClassFieldTheory.RayClassModulus.ext
    · rfl
    · exact Subsingleton.elim _ _
  rw [← heq]
  exact ClassFieldTheory.normFullConductor_isAbelianConductor F L

end
end DedekindZetaZeroFree.KummerConductorLeast
