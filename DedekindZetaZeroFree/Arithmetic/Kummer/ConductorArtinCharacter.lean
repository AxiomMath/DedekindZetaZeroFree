module

public import DedekindZetaZeroFree.Arithmetic.Kummer.QuadraticRootComplexCharacter
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex
public import DedekindZetaZeroFree.Arithmetic.Kummer.Conductors.LeastConductor
public import DedekindZetaZeroFree.Arithmetic.Kummer.Conductors.ArithmeticFrobenius

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerConductor

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

abbrev E (F : Type) [Field F] [NumberField F]
    (_h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    IntermediateField F (SeparableClosure F) :=
  KummerTheory.chosenSimpleKummerExtension F (2 : ℕ+) (rmKummerTwo_ne_zero F) x

instance extensionFiniteDimensional (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    FiniteDimensional F (E F h12 x) :=
  KummerTheory.chosenSimpleKummerExtension_finiteDimensional F (2 : ℕ+)
    (rmKummerTwo_ne_zero F) x

instance extensionNumberField (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    NumberField (E F h12 x) :=
  NumberField.of_module_finite F (E F h12 x)

instance extensionAbelianGalois (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    IsAbelianGalois F (E F h12 x) :=
  KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F (2 : ℕ+)
    (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) x

def kappa (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    (E F h12 x ≃ₐ[F] E F h12 x) →* ℂˣ :=
  (rmKummerQuadraticRootsComplexMap F h12 (E F h12 x)).comp
    ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity (E F h12 x) 2).toMonoidHom.comp
      (KummerTheory.chosenSimpleKummerRootCharacter F (2 : ℕ+)
        (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) x))

theorem totallyComplex (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) : NumberField.IsTotallyComplex F :=
  primitive12_totallyComplex F h12.choose
    ((mem_primitiveRoots (by decide)).1 h12.choose_spec)

def m (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) : Ideal (𝓞 F) :=
  let c := ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus
    F (E F h12 x)
  c.finitePart.support.prod (fun v => v.asIdeal ^ c.finitePart v)

theorem m_ne_bot (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) : m F h12 x ≠ ⊥ := by
  exact PrimitiveRay.modulusIdeal_ne_bot _

theorem modulus_eq_normConductor (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    M F (m F h12 x) (m_ne_bot F h12 x) =
      ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus
        F (E F h12 x) := by
  exact KummerConductorProduct.modulus_eq F (totallyComplex F h12) _

theorem isAbelianConductor (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    ClassFieldTheory.IsAbelianConductor F (E F h12 x)
      (M F (m F h12 x) (m_ne_bot F h12 x)) := by
  rw [modulus_eq_normConductor F h12 x]
  exact KummerConductorLeast.publicIsAbelianConductor F (E F h12 x)
    (totallyComplex F h12)

@[simp] theorem conductor_infinitePart (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    (M F (m F h12 x) (m_ne_bot F h12 x)).infinitePart = ∅ := rfl

def arithmeticArtin (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    ClassFieldTheory.RayClassGroup (M F (m F h12 x) (m_ne_bot F h12 x)) →*
      (E F h12 x ≃ₐ[F] E F h12 x) :=
  (modulus_eq_normConductor F h12 x).symm ▸
    ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin F (E F h12 x)

def rho (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    ClassFieldTheory.RayClassGroup (M F (m F h12 x) (m_ne_bot F h12 x)) →* ℂˣ :=
  (kappa F h12 x).comp (arithmeticArtin F h12 x)

def Xi (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    RayClassCharacter F (m F h12 x) :=
  frozenRay F (totallyComplex F h12) (m F h12 x) (m_ne_bot F h12 x) (rho F h12 x)

theorem rho_prime (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (M F (m F h12 x) (m_ne_bot F h12 x)).finitePart.support)
    (w : HeightOneSpectrum (𝓞 (E F h12 x)))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    rho F h12 x
        (ClassFieldTheory.rayClassOfFinitePrime
          (M F (m F h12 x) (m_ne_bot F h12 x)) v hv) =
      kappa F h12 x (ClassFieldTheory.arithmeticFrobeniusAt (K := F) w) := by
  change kappa F h12 x (arithmeticArtin F h12 x
    (ClassFieldTheory.rayClassOfFinitePrime
      (M F (m F h12 x) (m_ne_bot F h12 x)) v hv)) = _
  unfold arithmeticArtin
  rw [KummerConductorFrobenius.transport_prime (modulus_eq_normConductor F h12 x)]
  rw [KummerConductorFrobenius.normConductorArtin_prime F (E F h12 x) v _ w hw]

end
end DedekindZetaZeroFree.RMKummerConductor
