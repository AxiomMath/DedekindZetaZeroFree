module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.GaloisCharacterRealization
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.TrivialCharacter

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

theorem conductorRayRealization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃ m : ComplexDual (L ≃ₐ[K] L) → Ideal (𝓞 K),
    ∃ χ : (ρ : ComplexDual (L ≃ₐ[K] L)) → DedekindZetaZeroFree.RayClassCharacter K (m ρ),
      (∀ ρ, m ρ ≠ ⊥) ∧
      m 1 = ⊤ ∧
      (∀ I : Ideal (𝓞 K), χ 1 I = if I = ⊥ then 0 else 1) ∧
      (∀ ρ, ρ ≠ 1 → ¬ (χ ρ).IsPrincipal) ∧
      (∀ (ρ : ComplexDual (L ≃ₐ[K] L))
        (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
        W.asIdeal.LiesOver p.asIdeal → χ ρ p.asIdeal = primeArtinValue ρ W) := by
  classical
  let F : ComplexDual (L ≃ₐ[K] L) → Σ m : Ideal (𝓞 K), RayClassCharacter K m :=
    fun ρ =>
      if h : ρ = 1 then ⟨⊤, trivialRayCharacter K⟩
      else
        let m := Classical.choose (singleCharacterExactRayRealization K L ρ h)
        ⟨m, Classical.choose
          (Classical.choose_spec (singleCharacterExactRayRealization K L ρ h))⟩
  have hF1 : F 1 = ⟨⊤, trivialRayCharacter K⟩ := dif_pos rfl
  refine ⟨fun ρ => (F ρ).1, fun ρ => (F ρ).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ
    change (F ρ).1 ≠ ⊥
    by_cases h : ρ = 1
    · subst h
      rw [hF1]
      exact top_ne_bot
    · have hF : F ρ = ⟨Classical.choose (singleCharacterExactRayRealization K L ρ h),
          Classical.choose (Classical.choose_spec (singleCharacterExactRayRealization K L ρ h))⟩ :=
        dif_neg h
      rw [hF]
      exact (Classical.choose_spec
        (Classical.choose_spec (singleCharacterExactRayRealization K L ρ h))).1
  · change (F 1).1 = ⊤
    rw [hF1]
  · intro I
    change (F 1).2 I = if I = ⊥ then 0 else 1
    rw [hF1]
    exact trivialRayCharacter_apply K I
  · intro ρ hρ
    change ¬ (F ρ).2.IsPrincipal
    have hF : F ρ = ⟨Classical.choose (singleCharacterExactRayRealization K L ρ hρ),
        Classical.choose (Classical.choose_spec (singleCharacterExactRayRealization K L ρ hρ))⟩ :=
      dif_neg hρ
    rw [hF]
    exact (Classical.choose_spec
      (Classical.choose_spec (singleCharacterExactRayRealization K L ρ hρ))).2.1
  · intro ρ p W hW
    change (F ρ).2 p.asIdeal = primeArtinValue ρ W
    by_cases h : ρ = 1
    · subst h
      rw [hF1]
      exact trivialRayCharacter_eq_primeArtinValue K L p W hW
    · have hF : F ρ = ⟨Classical.choose (singleCharacterExactRayRealization K L ρ h),
          Classical.choose (Classical.choose_spec (singleCharacterExactRayRealization K L ρ h))⟩ :=
        dif_neg h
      rw [hF]
      exact (Classical.choose_spec
        (Classical.choose_spec (singleCharacterExactRayRealization K L ρ h))).2.2.2 p W hW

end DedekindZetaZeroFree.AbelianQuotient
