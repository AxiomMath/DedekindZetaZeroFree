module

public import DedekindZetaZeroFree.Arithmetic.Galois.CharacterFixedFieldDescent
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.GaloisCharacterAtFieldConductor
public import DedekindZetaZeroFree.Arithmetic.LocalFields.InertiaRestriction
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ArithmeticFrobeniusRestriction

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

theorem singleCharacterExactRayRealization_normConductor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (ρ : ComplexDual (L ≃ₐ[K] L)) (hρ : ρ ≠ 1) :
    let c := ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus
      K (characterFixedField ρ)
    let m := finiteRayModulusIdeal K c.finitePart
    ∃ χ : DedekindZetaZeroFree.RayClassCharacter K m,
      m ≠ ⊥ ∧ ¬ χ.IsPrincipal ∧
      (∀ (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
        W.asIdeal.LiesOver p.asIdeal →
          (p.asIdeal ⊔ m = ⊤ ↔ Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
        W.asIdeal.LiesOver p.asIdeal → χ p.asIdeal = primeArtinValue ρ W) := by
  intro c m
  let E := characterFixedField ρ
  obtain ⟨χ, hχ, hprime⟩ := faithfulConductorRayCharacter K E
    (characterOnFixedField ρ) (characterOnFixedField_ne_one ρ hρ)
  have hsupport : ∀ (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
      W.asIdeal.LiesOver p.asIdeal →
      (p.asIdeal ⊔ m = ⊤ ↔ Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker) := by
    intro p W hW
    let wE : HeightOneSpectrum (𝓞 E) := W.under (𝓞 E)
    haveI : W.asIdeal.LiesOver p.asIdeal := hW
    haveI hwL : W.asIdeal.LiesOver wE.asIdeal := ⟨rfl⟩
    have hwE : wE.asIdeal.LiesOver p.asIdeal :=
      Ideal.LiesOver.tower_bot W.asIdeal wE.asIdeal p.asIdeal
    calc
      p.asIdeal ⊔ m = ⊤ ↔ Algebra.IsUnramifiedAt (𝓞 K) wE.asIdeal :=
        (normConductorIdeal_coprime K E p).trans
          (unramifiedAtAllPrimesAboveIff p wE hwE)
      _ ↔ Ideal.inertia (E ≃ₐ[K] E) wE.asIdeal = ⊥ :=
        unramifiedIffInertiaBot p wE hwE
      _ ↔ Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker := by
        rw [← inertiaRestrictIntermediate E wE W hwL, Subgroup.map_eq_bot_iff]
        change _ ≤ (characterFixedFieldRestriction ρ).ker ↔ _
        rw [characterFixedFieldRestriction_ker]
  refine ⟨χ, finiteRayModulusIdeal_ne_bot K c.finitePart, hχ, hsupport, ?_⟩
  intro p W hW
  by_cases hi : Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker
  · have hp : p.asIdeal ⊔ m = ⊤ := (hsupport p W hW).mpr hi
    let wE : HeightOneSpectrum (𝓞 E) := W.under (𝓞 E)
    haveI : W.asIdeal.LiesOver p.asIdeal := hW
    haveI hwL : W.asIdeal.LiesOver wE.asIdeal := ⟨rfl⟩
    have hwE : wE.asIdeal.LiesOver p.asIdeal :=
      Ideal.LiesOver.tower_bot W.asIdeal wE.asIdeal p.asIdeal
    have hu : Algebra.IsUnramifiedAt (𝓞 K) wE.asIdeal :=
      (normConductorIdeal_coprime K E p).mp hp wE hwE
    rw [primeArtinValue, ite_eq_left hi, hprime p wE hwE hp]
    have hf := arithmeticFrobeniusRestrictUnramifiedBottom E p wE W hwE hwL hu
    rw [← hf]
    exact congrArg (fun z : ℂˣ => (z : ℂ))
      (DFunLike.congr_fun (characterOnFixedField_comp_restriction ρ)
        (ClassFieldTheory.arithmeticFrobeniusAt (K := K) W))
  · rw [primeArtinValue, ite_eq_right hi]
    exact (χ.eq_zero_iff' p.asIdeal).mpr
      (Or.inr (fun hp => hi ((hsupport p W hW).mp hp)))

theorem singleCharacterExactRayRealization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (ρ : ComplexDual (L ≃ₐ[K] L)) (hρ : ρ ≠ 1) :
    ∃ m : Ideal (𝓞 K), ∃ χ : DedekindZetaZeroFree.RayClassCharacter K m,
      m ≠ ⊥ ∧ ¬ χ.IsPrincipal ∧
      (∀ (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
        W.asIdeal.LiesOver p.asIdeal →
          (p.asIdeal ⊔ m = ⊤ ↔ Ideal.inertia (L ≃ₐ[K] L) W.asIdeal ≤ ρ.ker)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
        W.asIdeal.LiesOver p.asIdeal → χ p.asIdeal = primeArtinValue ρ W) := by
  exact ⟨_, singleCharacterExactRayRealization_normConductor K L ρ hρ⟩

end DedekindZetaZeroFree.AbelianQuotient

end
