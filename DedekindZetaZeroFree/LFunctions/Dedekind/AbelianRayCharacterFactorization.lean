module

public import DedekindZetaZeroFree.LFunctions.Dedekind.GaloisCharacterFactorization
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.ConductorRealization

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

theorem nontrivialCharacterFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (m : ComplexDual (L ≃ₐ[K] L) → Ideal (𝓞 K))
    (χ : (ρ : ComplexDual (L ≃ₐ[K] L)) → DedekindZetaZeroFree.RayClassCharacter K (m ρ))
    (hm : ∀ ρ, m ρ ≠ ⊥)
    (hprime : ∀ (ρ : ComplexDual (L ≃ₐ[K] L))
      (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
      W.asIdeal.LiesOver p.asIdeal → χ ρ p.asIdeal = primeArtinValue ρ W)
    (hχ1 : ∀ I : Ideal (𝓞 K), χ 1 I = if I = ⊥ then 0 else 1)
    (s : ℂ) (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏ ρ : {ρ : ComplexDual (L ≃ₐ[K] L) // ρ ≠ 1},
        ∑' I : Ideal (𝓞 K), χ ρ.1 I * (Ideal.absNorm I : ℂ) ^ (-s)) *
          NumberField.dedekindZeta K s := by
  classical
  let D := ComplexDual (L ≃ₐ[K] L)
  let E := {ρ : D // ρ ≠ 1}
  let F : D → ℂ := fun ρ =>
    ∑' I : Ideal (𝓞 K), χ ρ I * (Ideal.absNorm I : ℂ) ^ (-s)
  have htrivial : F 1 = NumberField.dedekindZeta K s := by
    have hsub : (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥},
        χ 1 I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)) = F 1 := by
      apply tsum_subtype_eq_of_support_subset
        (f := fun I : Ideal (𝓞 K) => χ 1 I * (Ideal.absNorm I : ℂ) ^ (-s))
        (s := {I : Ideal (𝓞 K) | I ≠ ⊥})
      intro I hI
      change I ≠ ⊥
      intro h
      subst I
      simpa [hχ1] using hI
    rw [← hsub]
    have hterms : (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        χ 1 I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)) =
        (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
          (Ideal.absNorm I.1 : ℂ) ^ (-s)) := by
      funext I
      simp [hχ1, I.2]
    rw [hterms]
    exact (dedekindZeta_hasSum_nonzeroIdeals K s hs).tsum_eq
  have hsplit : (∏ ρ : D, F ρ) = (∏ ρ : E, F ρ.1) * F 1 := by
    rw [← Finset.prod_erase_mul _ F (Finset.mem_univ (1 : D))]
    rw [Finset.prod_subtype (p := fun ρ : D => ρ ≠ 1)
      (Finset.univ.erase 1) (by simp)]
  calc NumberField.dedekindZeta L s
      = ∏ ρ : D, F ρ := allCharacterFactorization K L m χ hm hprime s hs
    _ = (∏ ρ : E, F ρ.1) * NumberField.dedekindZeta K s := by
      rw [hsplit, htrivial]

theorem abelianFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) :
    ∃ (n : ℕ) (m : Fin n → Ideal (𝓞 K))
      (χ : (i : Fin n) → DedekindZetaZeroFree.RayClassCharacter K (m i)),
      (∀ i, m i ≠ ⊥ ∧ ¬ (χ i).IsPrincipal) ∧
      ∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta L s =
          (∏ i : Fin n, ∑' I : Ideal (𝓞 K),
            χ i I * (Ideal.absNorm I : ℂ) ^ (-s)) *
              NumberField.dedekindZeta K s := by
  classical
  letI : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨hcomm⟩⟩
  letI : IsAbelianGalois K L := {}
  letI : CommGroup (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := hcomm }
  obtain ⟨m, χ, hm, hm1, hχ1, hnonprincipal, hprime⟩ := conductorRayRealization K L
  let D := ComplexDual (L ≃ₐ[K] L)
  let E := {ρ : D // ρ ≠ 1}
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  refine ⟨Fintype.card E, (fun i => m (e i).1), (fun i => χ (e i).1), ?_, ?_⟩
  · intro i
    exact ⟨hm (e i).1, hnonprincipal (e i).1 (e i).2⟩
  · intro s hs
    let F : D → ℂ := fun ρ =>
      ∑' I : Ideal (𝓞 K), χ ρ I * (Ideal.absNorm I : ℂ) ^ (-s)
    have hreindex : (∏ i : Fin (Fintype.card E), F (e i).1) =
        ∏ ρ : E, F ρ.1 := e.prod_comp (fun ρ => F ρ.1)
    calc NumberField.dedekindZeta L s
        = (∏ ρ : E, F ρ.1) * NumberField.dedekindZeta K s :=
          nontrivialCharacterFactorization K L m χ hm hprime hχ1 s hs
      _ = (∏ i : Fin (Fintype.card E), F (e i).1) * NumberField.dedekindZeta K s := by
        rw [hreindex]

end DedekindZetaZeroFree.AbelianQuotient
