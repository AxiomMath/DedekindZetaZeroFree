module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

structure RayClassCharacter (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) where
  toFun : Ideal (𝓞 F) → ℂ
  map_mul' : ∀ I J, toFun (I * J) = toFun I * toFun J
  map_top' : toFun ⊤ = 1
  eq_zero_iff' : ∀ I, toFun I = 0 ↔ (I = ⊥ ∨ I ⊔ 𝔪 ≠ ⊤)
  map_span' : ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 → (∀ φ : F →+* ℝ, 0 < φ (α : F)) →
    toFun (Ideal.span {α}) = 1

instance (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) :
    CoeFun (RayClassCharacter F 𝔪) (fun _ => Ideal (𝓞 F) → ℂ) :=
  ⟨RayClassCharacter.toFun⟩

def RayClassCharacter.IsPrimitive {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
    (η : RayClassCharacter F 𝔪) : Prop :=
  ∀ 𝔣 : Ideal (𝓞 F), 𝔪 < 𝔣 → ∃ α : 𝓞 F, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧ (∀ φ : F →+* ℝ, 0 < φ (α : F)) ∧
    Ideal.span {α} ⊔ 𝔪 = ⊤ ∧ η (Ideal.span {α}) ≠ 1

def RayClassCharacter.IsPrincipal {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
    (η : RayClassCharacter F 𝔪) : Prop :=
  ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ 𝔪 = ⊤ → η I = 1

structure QuadraticHeckeFamily (F : Type) [Field F] [NumberField F] (𝔠 : Ideal (𝓞 F)) where
  cond : Ideal (𝓞 F) → Ideal (𝓞 F)
  χ : (𝔞 : Ideal (𝓞 F)) → RayClassCharacter F (cond 𝔞)
  primitive : ∀ 𝔞, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → cond 𝔞 ≠ ⊥ ∧ (χ 𝔞).IsPrimitive
  quadratic : ∀ 𝔞 𝔟, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → (χ 𝔞) 𝔟 ^ 3 = (χ 𝔞) 𝔟
  G : Type
  instGroup : Group G
  instFinite : Finite G
  cls : Ideal (𝓞 F) → G
  cls_top : cls ⊤ = 1
  cls_mul : ∀ 𝔞 𝔟, 𝔞 ⊔ 𝔠 = ⊤ → 𝔟 ⊔ 𝔠 = ⊤ → cls (𝔞 * 𝔟) = cls 𝔞 * cls 𝔟
  C : G → G → ℂ
  C_sq : ∀ g h, C g h ^ 2 = 1
  reciprocity : ∀ 𝔞 𝔟, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → Squarefree 𝔟 → 𝔟 ⊔ 𝔠 = ⊤ → 𝔞 ⊔ 𝔟 = ⊤ →
    (χ 𝔞) 𝔟 = (χ 𝔟) 𝔞 * C (cls 𝔞) (cls 𝔟)
  product_primitive : ∀ 𝔞 𝔟, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → Squarefree 𝔟 → 𝔟 ⊔ 𝔠 = ⊤ →
    𝔞 ⊔ 𝔟 = ⊤ → cls 𝔞 = cls 𝔟 →
    ∃ ψ : RayClassCharacter F (𝔞 * 𝔟), ψ.IsPrimitive ∧
      ∀ 𝔫, 𝔫 ⊔ (cond 𝔞 * cond 𝔟) = ⊤ → ψ 𝔫 = (χ 𝔞) 𝔫 * (starRingEnd ℂ) ((χ 𝔟) 𝔫)

end

end DedekindZetaZeroFree
