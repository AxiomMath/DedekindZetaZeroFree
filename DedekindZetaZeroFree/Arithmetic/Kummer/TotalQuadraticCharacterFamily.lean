module

public import DedekindZetaZeroFree.Arithmetic.Kummer.PrimitiveProductCharacterCompatibility

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical

namespace KummerFamilyAssembly
variable {F : Type} [Field F] [NumberField F]

def trivialTop : RayClassCharacter F ⊤ where
  toFun I := if I = ⊥ then 0 else 1
  map_mul' I J := by
    simp only [Ideal.mul_eq_bot]
    by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ]
  map_top' := by simp
  eq_zero_iff' I := by simp
  map_span' α hα _ _ := by
    simp [Ideal.span_singleton_eq_bot, hα]

@[simp] theorem trivialTop_apply (I : Ideal (𝓞 F)) :
    (trivialTop (F := F)) I = if I = ⊥ then 0 else 1 := rfl

@[simp] theorem trivialTop_bottom : (trivialTop (F := F)) ⊥ = 0 := by simp

@[simp] theorem trivialTop_nonzero (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (trivialTop (F := F)) I = 1 := by simp [hI]

def Constrained (A : SArithmeticData F) (c : Ideal (𝓞 F)) : Prop :=
  Squarefree c ∧ c ⊔ uniformSquareUnitModulus A.Sf = ⊤

def totalConductor (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (c : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  if h : Constrained A c then
    m (KummerSquarefreeMembers.generator A σ η hS C c h.1 h.2)
  else ⊤

def totalCharacter (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (Xi : (x : Fˣ) → RayClassCharacter F (m x))
    (c : Ideal (𝓞 F)) : RayClassCharacter F (totalConductor A σ η hS C m c) :=
  if h : Constrained A c then
    KummerProductPrimitive.transport (by simp [totalConductor, h])
      (Xi (KummerSquarefreeMembers.generator A σ η hS C c h.1 h.2))
  else
    KummerProductPrimitive.transport (by simp [totalConductor, h]) (trivialTop (F := F))

@[simp] theorem totalConductor_constrained (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (c : Ideal (𝓞 F)) (h : Constrained A c) :
    totalConductor A σ η hS C m c =
      m (KummerSquarefreeMembers.generator A σ η hS C c h.1 h.2) := by
  simp [totalConductor, h]

@[simp] theorem totalConductor_unconstrained (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (c : Ideal (𝓞 F)) (h : ¬ Constrained A c) :
    totalConductor A σ η hS C m c = ⊤ := by
  simp [totalConductor, h]

@[simp] theorem totalCharacter_constrained_apply
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (Xi : (x : Fˣ) → RayClassCharacter F (m x))
    (c : Ideal (𝓞 F)) (h : Constrained A c) (I : Ideal (𝓞 F)) :
    totalCharacter A σ η hS C m Xi c I =
      Xi (KummerSquarefreeMembers.generator A σ η hS C c h.1 h.2) I := by
  simp [totalCharacter, h]

@[simp] theorem totalCharacter_unconstrained_apply
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (Xi : (x : Fˣ) → RayClassCharacter F (m x))
    (c : Ideal (𝓞 F)) (h : ¬ Constrained A c) (I : Ideal (𝓞 F)) :
    totalCharacter A σ η hS C m Xi c I = if I = ⊥ then 0 else 1 := by
  simp [totalCharacter, h]

end KummerFamilyAssembly
end
end DedekindZetaZeroFree
