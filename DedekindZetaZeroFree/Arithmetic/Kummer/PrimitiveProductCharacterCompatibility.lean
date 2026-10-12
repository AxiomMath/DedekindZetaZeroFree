module

public import DedekindZetaZeroFree.Arithmetic.Kummer.SquarefreeRadicalRepresentatives
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SquareClassImages

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical

namespace KummerProductPrimitive
variable {F : Type} [Field F] [NumberField F]

def transport {m n : Ideal (𝓞 F)} (h : m = n)
    (χ : RayClassCharacter F m) : RayClassCharacter F n :=
  h ▸ χ

@[simp] theorem transport_apply {m n : Ideal (𝓞 F)} (h : m = n)
    (χ : RayClassCharacter F m) (I : Ideal (𝓞 F)) :
    transport h χ I = χ I := by
  subst n
  rfl

theorem transport_primitive {m n : Ideal (𝓞 F)} (h : m = n)
    (χ : RayClassCharacter F m) (hχ : χ.IsPrimitive) :
    (transport h χ).IsPrimitive := by
  subst n
  exact hχ

@[simp] theorem character_bottom {m : Ideal (𝓞 F)} (χ : RayClassCharacter F m) :
    χ ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

def quotientRadical (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (a b : Ideal (𝓞 F)) (ha : Squarefree a) (hb : Squarefree b)
    (hqa : a ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (hqb : b ⊔ uniformSquareUnitModulus A.Sf = ⊤) : Fˣ :=
  KummerSquarefreeMembers.generator A σ η hS C a ha hqa /
    KummerSquarefreeMembers.generator A σ η hS C b hb hqb

def ExactProductOutput (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (m : Fˣ → Ideal (𝓞 F)) (Xi : (x : Fˣ) → RayClassCharacter F (m x)) : Prop :=
  ∀ (a b : Ideal (𝓞 F)) (ha : Squarefree a)
    (hqa : a ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (hb : Squarefree b) (hqb : b ⊔ uniformSquareUnitModulus A.Sf = ⊤),
    a ⊔ b = ⊤ → C.integralCls a = C.integralCls b →
    ∃ hcond : m (quotientRadical A σ η hS C a b ha hb hqa hqb) = a * b,
      (transport hcond (Xi (quotientRadical A σ η hS C a b ha hb hqa hqb))).IsPrimitive ∧
      ∀ n : Ideal (𝓞 F),
        n ⊔ (m (KummerSquarefreeMembers.generator A σ η hS C a ha hqa) *
          m (KummerSquarefreeMembers.generator A σ η hS C b hb hqb)) = ⊤ →
        transport hcond (Xi (quotientRadical A σ η hS C a b ha hb hqa hqb)) n =
          Xi (KummerSquarefreeMembers.generator A σ η hS C a ha hqa) n *
            (starRingEnd ℂ) (Xi (KummerSquarefreeMembers.generator A σ η hS C b hb hqb) n)

end KummerProductPrimitive
end
end DedekindZetaZeroFree
