module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField
public import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusRestrictTower

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField
open IsDedekindDomain

theorem artin_at_containing_modulus {K : Type} [Field K] [NumberField K]
    (E : ClassFieldTheory.FiniteAbelianExtension K)
    (m : ClassFieldTheory.RayClassModulus K)
    (hemb : ClassFieldTheory.EmbedsInRayClassField K E m) :
    ∃ A : ClassFieldTheory.RayClassGroup m →* (E ≃ₐ[K] E),
      Function.Surjective A ∧
        ∀ (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ m.finitePart.support)
          (Q : HeightOneSpectrum (𝓞 E)),
          Q.asIdeal.LiesOver p.asIdeal →
            A (ClassFieldTheory.rayClassOfFinitePrime m p hp) =
              ClassFieldTheory.arithmeticFrobeniusAt (K := K) Q := by
  classical

  obtain ⟨R, ⟨i⟩⟩ := hemb

  letI : Algebra E R.extension := i.toRingHom.toAlgebra
  haveI htow : IsScalarTower K E R.extension :=
    IsScalarTower.of_algebraMap_eq (fun x => (i.commutes x).symm)

  let A : ClassFieldTheory.RayClassGroup m →* (E ≃ₐ[K] E) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := R.extension) E).comp
      R.artinEquiv.toMonoidHom
  refine ⟨A, ?_, ?_⟩
  ·
    intro σ
    obtain ⟨τ, hτ⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := K) (E := R.extension) (K₁ := E) σ
    refine ⟨R.artinEquiv.symm τ, ?_⟩
    simp only [A, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hτ
  ·
    intro p hp Q hQ

    obtain ⟨Q', hQ'ge, hQ'prime, hQ'under⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := 𝓞 E) (S := 𝓞 R.extension)
        Q.asIdeal (⊥ : Ideal (𝓞 R.extension))
        (by
          rw [Ideal.under_def,
            ← RingHom.ker_eq_comap_bot (algebraMap (𝓞 E) (𝓞 R.extension)),
            NumberField.RingOfIntegers.ker_algebraMap_eq_bot]
          exact bot_le)
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      have hbot : Q.asIdeal = ⊥ := by
        rw [← hQ'under, h, Ideal.under_def,
          ← RingHom.ker_eq_comap_bot (algebraMap (𝓞 E) (𝓞 R.extension)),
          NumberField.RingOfIntegers.ker_algebraMap_eq_bot]
      exact Q.ne_bot hbot
    let Q'₀ : HeightOneSpectrum (𝓞 R.extension) := ⟨Q', hQ'prime, hQ'ne⟩
    haveI hQlies : Q'₀.asIdeal.LiesOver Q.asIdeal := ⟨hQ'under.symm⟩
    haveI hpQ : Q.asIdeal.LiesOver p.asIdeal := hQ
    have hliesp : Q'₀.asIdeal.LiesOver p.asIdeal :=
      Ideal.LiesOver.trans Q'₀.asIdeal Q.asIdeal p.asIdeal

    have hunram : Algebra.IsUnramifiedAt (𝓞 K) Q'₀.asIdeal :=
      (R.unramifiedOutsideModulus.1 p hp) Q'₀.asIdeal Q'₀.isPrime hliesp

    have hfrob :=
      ClassFieldTheory.arithmeticFrobeniusAt_restrict_tower (K := K) (E := E)
        (L := R.extension) p Q Q'₀ hQ hQlies hunram
    simp only [A, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [R.artin_frobenius p hp Q'₀ hliesp]
    exact hfrob

end DedekindZetaZeroFree.LargeSieve.RootNumber
