module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnramifiedInertiaCriterion
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassFieldReciprocity
public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.HeckeCorollary

open AbelianQuotient

theorem rayCharacter_eq_zero_of_mem_modulus_support
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (narrowIdealModulus K m hm).finitePart.support) :
    χ p.asIdeal = 0 := by
  have hcount : Multiset.count p.asIdeal (normalizedFactors m) ≠ 0 := by
    simpa only [narrowIdealModulus_finitePart] using Finsupp.mem_support_iff.mp hp
  have hmp : m ≤ p.asIdeal :=
    ((Ideal.mem_normalizedFactors_iff hm).mp (Multiset.count_ne_zero.mp hcount)).2
  apply (χ.eq_zero_iff' p.asIdeal).mpr
  exact Or.inr (by simpa only [sup_eq_left.mpr hmp] using p.isPrime.ne_top)

theorem rayCharacter_galoisRealization
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m)
    (R : ClassFieldTheory.RayClassFieldRealization K (narrowIdealModulus K m hm)) :
    ∃ ρ : ComplexDual (R.extension ≃ₐ[K] R.extension),
      (ρ = 1 ↔ χ.IsPrincipal) ∧
      ∀ (p : HeightOneSpectrum (𝓞 K))
        (_hp : p ∉ (narrowIdealModulus K m hm).finitePart.support)
        (W : HeightOneSpectrum (𝓞 R.extension)),
        W.asIdeal.LiesOver p.asIdeal →
          χ p.asIdeal = primeArtinValue ρ W := by
  obtain ⟨ψ, hψ, hprincipal⟩ := rayCharacterDescent K m hm χ
  let ρ : ComplexDual (R.extension ≃ₐ[K] R.extension) :=
    ψ.toHomUnits.comp R.artinEquiv.symm.toMonoidHom
  refine ⟨ρ, ?_, ?_⟩
  · constructor
    · intro hρ
      apply hprincipal.mpr
      apply MonoidHom.ext
      intro c
      have h := DFunLike.congr_fun hρ (R.artinEquiv c)
      have h' := congrArg (fun z : ℂˣ ↦ (z : ℂ)) h
      simpa [ρ] using h'
    · intro hχ
      have hψone := hprincipal.mp hχ
      apply MonoidHom.ext
      intro σ
      apply Units.ext
      simp [ρ, hψone]
  · intro p hp W hW
    have hu : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
      R.unramifiedOutsideModulus.1 p hp W.asIdeal W.isPrime hW
    have hi : Ideal.inertia (R.extension ≃ₐ[K] R.extension) W.asIdeal = ⊥ :=
      (unramifiedIffInertiaBot p W hW).mp hu
    rw [primeArtinValue, hi, ite_eq_left bot_le]
    rw [hψ, rayIdealClass_of_finitePrime K m hm p hp]
    change ψ (ClassFieldTheory.rayClassOfFinitePrime _ p hp) =
      (ψ.toHomUnits (R.artinEquiv.symm
        (ClassFieldTheory.arithmeticFrobeniusAt (K := K) W)) : ℂ)
    rw [← R.artin_frobenius p hp W hW, R.artinEquiv.symm_apply_apply]
    rfl

theorem exists_rayCharacter_galoisRealization
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ R : ClassFieldTheory.RayClassFieldRealization K (narrowIdealModulus K m hm),
    ∃ ρ : ComplexDual (R.extension ≃ₐ[K] R.extension),
      (ρ = 1 ↔ χ.IsPrincipal) ∧
      ∀ (p : HeightOneSpectrum (𝓞 K))
        (_hp : p ∉ (narrowIdealModulus K m hm).finitePart.support)
        (W : HeightOneSpectrum (𝓞 R.extension)),
        W.asIdeal.LiesOver p.asIdeal →
          χ p.asIdeal = primeArtinValue ρ W := by
  obtain ⟨R⟩ := ClassFieldTheory.rayClassField_reciprocity K (narrowIdealModulus K m hm)
  exact ⟨R, rayCharacter_galoisRealization K m hm χ R⟩

end DedekindZetaZeroFree.HeckeCorollary
