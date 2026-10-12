module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.ClassTwists

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

instance familyGroup (Q : QuadraticHeckeFamily F c) : Group Q.G := Q.instGroup

instance familyFinite (Q : QuadraticHeckeFamily F c) : Finite Q.G := Q.instFinite

theorem C_eq_one_or_neg_one (Q : QuadraticHeckeFamily F c) (g h : Q.G) :
    Q.C g h = 1 ∨ Q.C g h = -1 := by
  have hprod : (Q.C g h - 1) * (Q.C g h + 1) = 0 := by
    have hs := Q.C_sq g h
    calc (Q.C g h - 1) * (Q.C g h + 1) = Q.C g h ^ 2 - 1 := by ring
      _ = 0 := by rw [hs]; ring
  rcases mul_eq_zero.mp hprod with h1 | h2
  · left; exact sub_eq_zero.mp h1
  · right; exact add_eq_zero_iff_eq_neg.mp h2

theorem norm_C (Q : QuadraticHeckeFamily F c) (g h : Q.G) :
    ‖Q.C g h‖ = 1 := by
  rcases C_eq_one_or_neg_one Q g h with h | h <;> rw [h] <;> simp

theorem cls_mul_eq_iff (Q : QuadraticHeckeFamily F c) (d b₁ b₂ : Ideal (𝓞 F))
    (hdc : d ⊔ c = ⊤) (hb₁c : b₁ ⊔ c = ⊤) (hb₂c : b₂ ⊔ c = ⊤)
    (hdb₁c : (d * b₁) ⊔ c = ⊤) (hdb₂c : (d * b₂) ⊔ c = ⊤) :
    Q.cls (d * b₁) = Q.cls (d * b₂) ↔ Q.cls b₁ = Q.cls b₂ := by
  constructor
  · intro h
    rw [Q.cls_mul d b₁ hdc hb₁c, Q.cls_mul d b₂ hdc hb₂c] at h
    exact mul_left_cancel h
  · intro h
    rw [Q.cls_mul d b₁ hdc hb₁c, Q.cls_mul d b₂ hdc hb₂c, h]

end DedekindZetaZeroFree.LargeSieve.ClassTwists
