module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity

@[expose] public section

namespace DedekindZetaZeroFree.KummerConductorFrobenius
noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem normConductorArtin_prime (F L : Type) [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [IsAbelianGalois F L]
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus
      F L).finitePart.support)
    (w : HeightOneSpectrum (𝓞 L)) (hw : w.asIdeal.LiesOver v.asIdeal) :
    ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin F L
      (ClassFieldTheory.rayClassOfFinitePrime
        (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus F L) v hv) =
      ClassFieldTheory.arithmeticFrobeniusAt (K := F) w := by
  rw [ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin_prime]
  apply ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
    v w hw
  exact (ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus_unramifiedOutside
    F L).1 v hv w.asIdeal inferInstance hw

theorem transport_prime {F : Type} [Field F] [NumberField F]
    {G : Type} [Monoid G] {a b : ClassFieldTheory.RayClassModulus F}
    (h : a = b) (f : ClassFieldTheory.RayClassGroup b →* G)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ a.finitePart.support) :
    (h.symm ▸ f) (ClassFieldTheory.rayClassOfFinitePrime a v hv) =
      f (ClassFieldTheory.rayClassOfFinitePrime b v (h ▸ hv)) := by
  subst b
  rfl

end
end DedekindZetaZeroFree.KummerConductorFrobenius
