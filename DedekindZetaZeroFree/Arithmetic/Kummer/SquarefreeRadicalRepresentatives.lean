module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UniformSquareUnitModulus

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical nonZeroDivisors
open IsDedekindDomain

namespace KummerSquarefreeMembers

variable {F : Type} [Field F] [NumberField F]

theorem exterior_iff (A : SArithmeticData F) (c : Ideal (𝓞 F)) :
    c ⊔ uniformSquareUnitModulus A.Sf = ⊤ ↔ c ⊔ A.cS = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq, uniformSquareUnitModulus,
    squareUnitModulus, SArithmeticData.cS, IsCoprime.prod_right_iff]
  constructor
  · intro h v hv
    exact (IsCoprime.pow_right_iff (squareUnitDepth_bounds v).1).mp (h v hv)
  · intro h v hv
    exact (h v hv).pow_right

def exteriorIndex (A : SArithmeticData F) (c : Ideal (𝓞 F))
    (hc : Squarefree c) (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤) :
    A.Exterior :=
  ⟨c, hc.ne_zero, (exterior_iff A c).mp hcop⟩

@[simp] theorem exteriorIndex_val (A : SArithmeticData F) (c : Ideal (𝓞 F))
    (hc : Squarefree c) (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤) :
    (exteriorIndex A c hc hcop).val = c := rfl

structure AllowedRepresentative (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (I : A.Exterior) where
  integral : A.R
  radical : Fˣ
  generates : A.Generates I integral
  radical_eq : (radical : F) = (integral : F)
  allowed : A.IsAllowed C.correction.B radical

def chooseRepresentative (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (I : A.Exterior) :
    AllowedRepresentative A σ η hS C I :=
  let r := (C.allowed_integral I).choose
  let a := (C.allowed_integral I).choose_spec.choose
  let h := (C.allowed_integral I).choose_spec.choose_spec
  ⟨r, a, h.1, h.2.1, h.2.2⟩

def generator (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (c : Ideal (𝓞 F))
    (hc : Squarefree c) (hcop : c ⊔ uniformSquareUnitModulus A.Sf = ⊤) : Fˣ :=
  (chooseRepresentative A σ η hS C (exteriorIndex A c hc hcop)).radical

theorem AllowedRepresentative.isAllowedGenerator
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS} {I : A.Exterior}
    (a : AllowedRepresentative A σ η hS C I) :
    A.IsAllowedGenerator C.correction.B
      (A.extendIdeal I : FractionalIdeal A.R⁰ F) a.radical := by
  refine ⟨?_, a.allowed⟩
  rw [← a.generates.2, FractionalIdeal.coeIdeal_span_singleton]
  change FractionalIdeal.spanSingleton A.R⁰ (a.integral : F) = _
  rw [← a.radical_eq]

theorem representative_top_square
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS} {I : A.Exterior}
    (a : AllowedRepresentative A σ η hS C I) (hI : I.val = ⊤) :
    ∃ y : Fˣ, a.radical = y ^ 2 := by
  have hone : A.IsAllowedGenerator C.correction.B
      (A.extendIdeal I : FractionalIdeal A.R⁰ F) 1 := by
    constructor
    · simp [SArithmeticData.extendIdeal, hI, FractionalIdeal.spanSingleton_one,
        Ideal.map_top]
    · change A.sClass 1 ∈ C.correction.B
      simp
  have h := C.allowed_unique _ _ _ a.isAllowedGenerator hone
  obtain ⟨u, hu, heq⟩ := h
  change u ^ 6 = a.radical / 1 at heq
  refine ⟨u ^ 3, ?_⟩
  simpa [← pow_mul] using heq.symm

end KummerSquarefreeMembers
end
end DedekindZetaZeroFree
