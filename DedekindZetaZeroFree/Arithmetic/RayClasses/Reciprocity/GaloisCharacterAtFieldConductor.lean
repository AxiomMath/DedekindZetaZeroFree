module

public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.NormConductorFiniteSupport
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOfGroupCharacter

@[expose] public section

noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

 def rayClassGroupCast
    {K : Type} [Field K] [NumberField K]
    {m₁ m₂ : ClassFieldTheory.RayClassModulus K} (h : m₁ = m₂) :
    ClassFieldTheory.RayClassGroup m₁ ≃* ClassFieldTheory.RayClassGroup m₂ := by
  cases h
  exact MulEquiv.refl _

private theorem rayClassGroupCast_prime
    {K : Type} [Field K] [NumberField K]
    {m₁ m₂ : ClassFieldTheory.RayClassModulus K} (h : m₁ = m₂)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m₁.finitePart.support) :
    rayClassGroupCast h (ClassFieldTheory.rayClassOfFinitePrime m₁ v hv) =
      ClassFieldTheory.rayClassOfFinitePrime m₂ v (by rw [← h]; exact hv) := by
  cases h
  rfl

theorem faithfulConductorRayCharacter
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E]
    (σ : ComplexDual (E ≃ₐ[K] E)) (hσ : σ ≠ 1) :
    let c := ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus K E
    let m := finiteRayModulusIdeal K c.finitePart
    ∃ χ : DedekindZetaZeroFree.RayClassCharacter K m,
      ¬χ.IsPrincipal ∧
        ∀ p : HeightOneSpectrum (𝓞 K), ∀ w : HeightOneSpectrum (𝓞 E),
          w.asIdeal.LiesOver p.asIdeal → p.asIdeal ⊔ m = ⊤ →
            χ p.asIdeal = (σ (ClassFieldTheory.arithmeticFrobeniusAt (K := K) w) : ℂ) := by
  classical
  dsimp only
  set c := ClassFieldTheory.GlobalClassFieldComparison.normConductorRayClassModulus K E
    with hcdef
  set m : Ideal (𝓞 K) := finiteRayModulusIdeal K c.finitePart with hmdef
  have hm : m ≠ ⊥ := finiteRayModulusIdeal_ne_bot K c.finitePart
  have h : narrowIdealModulus K m hm = c := narrowIdealModulus_normConductor K E
  let e : RayIdealClass K m hm ≃* ClassFieldTheory.RayClassGroup c := rayClassGroupCast h
  let artin : RayIdealClass K m hm →* (E ≃ₐ[K] E) :=
    (ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin K E).comp e.toMonoidHom
  let ψ : RayIdealClass K m hm →* ℂˣ := σ.comp artin
  refine ⟨rayCharacterOfGroupCharacter K m hm ψ, ?_, ?_⟩
  · rw [rayCharacterOfGroupCharacter_isPrincipal_iff K m hm ψ]
    intro hψ
    have hg : ∃ g : E ≃ₐ[K] E, σ g ≠ 1 := by
      by_contra hcon
      exact hσ (MonoidHom.ext fun x => by simpa using not_exists.mp hcon x)
    obtain ⟨g, hg⟩ := hg
    have hsurj : Function.Surjective artin :=
      (ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin_surjective K E).comp
        e.surjective
    obtain ⟨x, hx⟩ := hsurj g
    have h1 : ψ x = 1 := by rw [hψ]; rfl
    change σ (artin x) = 1 at h1
    rw [hx] at h1
    exact hg h1
  · intro p w hw hcop
    have hcount : c.finitePart p = 0 :=
      (finiteRayModulusIdeal_coprime K c.finitePart p).mp hcop
    have hp : p ∉ (narrowIdealModulus K m hm).finitePart.support := by
      simp only [Finsupp.mem_support_iff, not_not, narrowIdealModulus_finitePart, hmdef,
        finiteRayModulusIdeal_count]
      exact hcount
    have hp' : p ∉ c.finitePart.support := by rw [← h]; exact hp
    have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
      (normConductorIdeal_coprime K E p).mp hcop w hw
    have hprim : ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin K E
        (ClassFieldTheory.rayClassOfFinitePrime c p hp') =
        ClassFieldTheory.arithmeticFrobeniusAt (K := K) w := by
      rw [ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin_prime K E p hp']
      exact ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := E) p w hw hunram
    have hcast : e (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm) p hp)
        = ClassFieldTheory.rayClassOfFinitePrime c p hp' := rayClassGroupCast_prime h p hp
    rw [rayCharacterOfGroupCharacter_finitePrime K m hm ψ p hp]
    have hval : ψ (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm) p hp)
        = σ (ClassFieldTheory.arithmeticFrobeniusAt (K := K) w) := by
      change σ ((ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin K E)
        (e (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm) p hp)))
        = σ (ClassFieldTheory.arithmeticFrobeniusAt (K := K) w)
      rw [hcast]
      change σ (ClassFieldTheory.GlobalClassFieldComparison.normConductorArtin K E
        (ClassFieldTheory.rayClassOfFinitePrime c p hp')) = _
      rw [hprim]
    rw [hval]

end DedekindZetaZeroFree.AbelianQuotient

end
