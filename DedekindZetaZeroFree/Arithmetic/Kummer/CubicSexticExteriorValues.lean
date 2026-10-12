module

public import DedekindZetaZeroFree.Arithmetic.Kummer.SquarefreeRadicalRepresentatives

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical

namespace KummerExteriorValues

variable {F : Type} [Field F] [NumberField F]

def exteriorIndex (A : SArithmeticData F) (d : Ideal (𝓞 F))
    (hd : d ≠ ⊥) (hcop : d ⊔ uniformSquareUnitModulus A.Sf = ⊤) : A.Exterior :=
  ⟨d, hd, (KummerSquarefreeMembers.exterior_iff A d).mp hcop⟩

@[simp] theorem exteriorIndex_val (A : SArithmeticData F) (d : Ideal (𝓞 F))
    (hd : d ≠ ⊥) (hcop : d ⊔ uniformSquareUnitModulus A.Sf = ⊤) :
    (exteriorIndex A d hd hcop).val = d := rfl

def sexticValue (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (c d : A.Exterior) : ℂ :=
  σ (A.sexticResidue d
    (KummerSquarefreeMembers.chooseRepresentative A σ η hS C c).integral)

def cubicSexticValue (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (c d : A.Exterior) : ℂ :=
  sexticValue A σ η hS C c d ^ 3

theorem cubicSexticValue_symmetry (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (c d : A.Exterior)
    (hcop : c.val ⊔ d.val = ⊤) :
    cubicSexticValue A σ η hS C c d = cubicSexticValue A σ η hS C d c := by
  let a := KummerSquarefreeMembers.chooseRepresentative A σ η hS C c
  let b := KummerSquarefreeMembers.chooseRepresentative A σ η hS C d
  have h := C.reciprocity.1 c d a.integral b.integral a.radical b.radical
    a.generates b.generates a.radical_eq b.radical_eq a.allowed b.allowed hcop
  exact congrArg (fun z : F => σ z ^ 3) h.symm

theorem cubicSexticValue_shared_zero (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (c d : A.Exterior)
    (hshared : c.val ⊔ d.val ≠ ⊤) :
    cubicSexticValue A σ η hS C c d = 0 ∧
      cubicSexticValue A σ η hS C d c = 0 := by
  let a := KummerSquarefreeMembers.chooseRepresentative A σ η hS C c
  let b := KummerSquarefreeMembers.chooseRepresentative A σ η hS C d
  have h := C.reciprocity.2.2.2 c d a.integral b.integral
    a.generates b.generates hshared
  constructor
  · change σ (A.sexticResidue d a.integral) ^ 3 = 0
    rw [h.2, map_zero, zero_pow (by decide)]
  · change σ (A.sexticResidue c b.integral) ^ 3 = 0
    rw [h.1, map_zero, zero_pow (by decide)]

def ExteriorValuesSpec (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (Xi : Fˣ → Ideal (𝓞 F) → ℂ) : Prop :=
  (∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
      (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤),
    Xi (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) d =
      cubicSexticValue A σ η hS C
        (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
        (exteriorIndex A d hd hcopd)) ∧
  (∀ (c : Ideal (𝓞 F)) (hc : Squarefree c)
      (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (d : Ideal (𝓞 F)) (hd : d ≠ ⊥)
      (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤), c ⊔ d ≠ ⊤ →
    Xi (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) d = 0 ∧
      cubicSexticValue A σ η hS C
        (KummerSquarefreeMembers.exteriorIndex A c hc hcopc)
        (exteriorIndex A d hd hcopd) = 0) ∧
  (∀ (c d : Ideal (𝓞 F)) (hc : Squarefree c) (hd : Squarefree d)
      (hcopc : c ⊔ uniformSquareUnitModulus A.Sf = ⊤)
      (hcopd : d ⊔ uniformSquareUnitModulus A.Sf = ⊤), c ⊔ d = ⊤ →
    Xi (KummerSquarefreeMembers.generator A σ η hS C c hc hcopc) d =
      Xi (KummerSquarefreeMembers.generator A σ η hS C d hd hcopd) c)

end KummerExteriorValues
end
end DedekindZetaZeroFree
