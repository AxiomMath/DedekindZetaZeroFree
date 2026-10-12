module

public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualsAndFractionalQuotients

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

theorem residueFractionalIdeal_le_one (m : Ideal (NumberField.RingOfIntegers F)) :
    (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) ≤ 1 := by
  exact FractionalIdeal.coeIdeal_le_one

theorem residueFractionalIdeal_ne_zero_iff (m : Ideal (NumberField.RingOfIntegers F)) :
    (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) ≠ 0 ↔ m ≠ ⊥ := by
  exact FractionalIdeal.coeIdeal_ne_zero

def residueUnitLinearEquiv {F : Type} [Field F] :
    NumberField.RingOfIntegers F ≃ₗ[NumberField.RingOfIntegers F]
      (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F).coeToSubmodule := by
  let f := LinearMap.codRestrict
    (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F).coeToSubmodule
    (Algebra.linearMap (NumberField.RingOfIntegers F) F)
    (FractionalIdeal.coe_mem_one (NumberField.RingOfIntegers F)⁰)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hv : (algebraMap (NumberField.RingOfIntegers F) F) x =
        (algebraMap (NumberField.RingOfIntegers F) F) y :=
      congrArg (fun z : (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F).coeToSubmodule => (z : F)) h
    exact Subtype.ext hv
  · intro x
    obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff
      (NumberField.RingOfIntegers F)⁰).mp x.property
    exact ⟨y, Subtype.ext hy⟩

theorem residueUnitLinearEquiv_map {F : Type} [Field F]
    (m : Ideal (NumberField.RingOfIntegers F)) :
    Submodule.map (residueUnitLinearEquiv (F := F)).toLinearMap m =
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F).coeToSubmodule.comap
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F).coeToSubmodule.subtype := by
  ext x
  rw [Submodule.mem_map]
  change (∃ y ∈ m, residueUnitLinearEquiv y = x) ↔
    (x : F) ∈ (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
  rw [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, congrArg Subtype.val h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, Subtype.ext h⟩

def residueFractionalOneEquiv (m : Ideal (NumberField.RingOfIntegers F)) :
    (NumberField.RingOfIntegers F ⧸ m) ≃ₗ[NumberField.RingOfIntegers F]
      fractionalIdealQuotient
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
        (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) := by
  exact Submodule.Quotient.equiv m _ residueUnitLinearEquiv (residueUnitLinearEquiv_map m)

@[simp] theorem residueFractionalOneEquiv_apply_mk
    (m : Ideal (NumberField.RingOfIntegers F)) (α : NumberField.RingOfIntegers F) :
    residueFractionalOneEquiv m (Ideal.Quotient.mk m α) =
      fractionalIdealQuotientMk
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
        (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
        ⟨algebraMap (NumberField.RingOfIntegers F) F α, FractionalIdeal.coe_mem_one (NumberField.RingOfIntegers F)⁰ α⟩ := by
  rfl

end DedekindZetaZeroFree.Hecke

end
