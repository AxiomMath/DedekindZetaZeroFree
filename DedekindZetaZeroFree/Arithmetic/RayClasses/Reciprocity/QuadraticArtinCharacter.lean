module

public import DedekindZetaZeroFree.Algebra.QuadraticCharacterKernelIndex
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquiv

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

theorem quadraticCharacter_of_rayClassRealization
    {F : Type} [Field F] [NumberField F]
    (m : ClassFieldTheory.RayClassModulus F)
    (ψ : ClassFieldTheory.RayClassGroup m →* ℂˣ)
    (hsq : ∀ x, ψ x ^ 2 = 1) (hn : ψ ≠ 1)
    (R : ClassFieldTheory.RayClassSubgroupRealization F m ψ.ker) :
    ∃ χ : (R.extension ≃ₐ[F] R.extension) →* ℂˣ,
      Function.Injective χ ∧
      (∀ σ, χ σ ^ 2 = 1) ∧
      (∀ x : ClassFieldTheory.RayClassGroup m, χ (R.artin x) = ψ x) ∧
      Module.finrank F R.extension = 2 := by
  classical
  let e : (ClassFieldTheory.RayClassGroup m ⧸ ψ.ker) ≃*
      (R.extension ≃ₐ[F] R.extension) :=
    ClassFieldTheory.rayClassSubgroupQuotientEquiv F m ψ.ker R
  let j : (ClassFieldTheory.RayClassGroup m ⧸ ψ.ker) ≃* ψ.range :=
    QuotientGroup.quotientKerEquivRange ψ
  let χ₀ : (R.extension ≃ₐ[F] R.extension) →* ψ.range :=
    j.toMonoidHom.comp e.symm.toMonoidHom
  let χ : (R.extension ≃ₐ[F] R.extension) →* ℂˣ :=
    ψ.range.subtype.comp χ₀
  have hval : ∀ σ, χ σ = (χ₀ σ : ℂˣ) := fun σ => rfl
  have he : ∀ x : ClassFieldTheory.RayClassGroup m,
      e (QuotientGroup.mk x) = R.artin x := by
    intro x
    have : QuotientGroup.quotientKerEquivOfSurjective R.artin R.artin_surjective
        (QuotientGroup.mk x) = R.artin x := by
      change (QuotientGroup.kerLift R.artin) (QuotientGroup.mk x) = R.artin x
      rw [QuotientGroup.kerLift_mk]
    simpa only [e, ClassFieldTheory.rayClassSubgroupQuotientEquiv, MulEquiv.trans_apply,
      QuotientGroup.quotientMulEquivOfEq_mk] using this
  have hj : ∀ x : ClassFieldTheory.RayClassGroup m,
      j (QuotientGroup.mk x) = ⟨ψ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ := by
    intro x
    change (QuotientGroup.quotientKerEquivRange ψ) (QuotientGroup.mk x) =
      ψ.rangeRestrict x
    rfl
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : χ₀ a = χ₀ b := Subtype.ext hab
    exact e.symm.injective (j.injective h1)
  · intro σ
    obtain ⟨x, hx⟩ := (χ₀ σ).2
    rw [hval σ, ← hx, hsq x]
  · intro x
    have hsymm : e.symm (R.artin x) = QuotientGroup.mk x := by
      rw [← he x, MulEquiv.symm_apply_apply]
    have h1 : χ₀ (R.artin x) = ⟨ψ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ := by
      rw [show χ₀ (R.artin x) = j (e.symm (R.artin x)) from rfl, hsymm, hj x]
    rw [hval (R.artin x), h1]
  · have hcard : Nat.card (ClassFieldTheory.RayClassGroup m ⧸ ψ.ker) = 2 :=
      quadraticCharacter_quotient_card_two ψ hsq hn
    have hgal : Nat.card (R.extension ≃ₐ[F] R.extension) = 2 :=
      (Nat.card_congr e.symm.toEquiv).trans hcard
    rw [← IsGalois.card_aut_eq_finrank F R.extension]
    exact hgal

end DedekindZetaZeroFree.LargeSieve
