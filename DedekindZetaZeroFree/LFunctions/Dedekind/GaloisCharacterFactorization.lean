module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.ConductorRealization
public import DedekindZetaZeroFree.LFunctions.Dedekind.LocalEulerPolynomial
public import DedekindZetaZeroFree.LFunctions.Dedekind.EulerProductRegrouping
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField BigOperators
open IsDedekindDomain

 instance allCharacterFactorizationCommGroup (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAbelianGalois K L] : CommGroup (L ≃ₐ[K] L) :=
  { (inferInstance : Group (L ≃ₐ[K] L)) with
    mul_comm := fun σ τ => mul_comm' σ τ }

theorem allCharacterFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (m : ComplexDual (L ≃ₐ[K] L) → Ideal (𝓞 K))
    (χ : (ρ : ComplexDual (L ≃ₐ[K] L)) → DedekindZetaZeroFree.RayClassCharacter K (m ρ))
    (hm : ∀ ρ, m ρ ≠ ⊥)
    (hprime : ∀ (ρ : ComplexDual (L ≃ₐ[K] L))
      (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L)),
      W.asIdeal.LiesOver p.asIdeal → χ ρ p.asIdeal = primeArtinValue ρ W)
    (s : ℂ) (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏ ρ : ComplexDual (L ≃ₐ[K] L), ∑' I : Ideal (𝓞 K),
        χ ρ I * (Ideal.absNorm I : ℂ) ^ (-s) := by
  classical

  have hρ : ∀ ρ : ComplexDual (L ≃ₐ[K] L),
      HasProd
        (fun P : HeightOneSpectrum (𝓞 K) =>
          (1 - χ ρ P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
        (∑' I : Ideal (𝓞 K), χ ρ I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
    intro ρ
    refine weightedIdealEulerProduct_hasProd K (fun I => χ ρ I) ?_ ?_ ?_ ?_ s hs
    · exact fun I J => (χ ρ).map_mul' I J
    · exact (χ ρ).map_top'
    · exact ((χ ρ).eq_zero_iff' ⊥).2 (Or.inl rfl)
    · intro I
      obtain ⟨ψ, hψ, -⟩ := rayCharacterDescent K (m ρ) (hm ρ) (χ ρ)
      rw [hψ I]
      cases h : rayIdealClass K (m ρ) (hm ρ) I with
      | none => simp
      | some c =>
        exact le_of_eq <|
          IsOfFinOrder.norm_eq_one (ψ.isOfFinOrder (isOfFinOrder_of_finite c))

  have hA := hasProd_prod
    (f := fun (ρ : ComplexDual (L ≃ₐ[K] L)) (P : HeightOneSpectrum (𝓞 K)) =>
      (1 - χ ρ P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
    (a := fun ρ : ComplexDual (L ≃ₐ[K] L) =>
      ∑' I : Ideal (𝓞 K), χ ρ I * (Ideal.absNorm I : ℂ) ^ (-s))
    (s := Finset.univ) (fun ρ _ => hρ ρ)

  have hpoint : ∀ p : HeightOneSpectrum (𝓞 K),
      (∏ ρ : ComplexDual (L ≃ₐ[K] L),
        (1 - χ ρ p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹) =
      ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
        (1 - (Ideal.absNorm Q : ℂ) ^ (-s))⁻¹ := by
    intro p
    obtain ⟨Q₀⟩ := Ideal.nonempty_primesOver (R := 𝓞 K) (S := 𝓞 L) p.asIdeal
    have hne : Q₀.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver p.ne_bot Q₀.2
    let W : HeightOneSpectrum (𝓞 L) := ⟨Q₀.1, Q₀.2.1, hne⟩
    have hW : W.asIdeal.LiesOver p.asIdeal := Q₀.2.2
    set x : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ (-s) with hx

    have hinv : (∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
          (1 - x ^ Q.inertiaDeg (𝓞 K))⁻¹) =
        ∏ ρ : ComplexDual (L ≃ₐ[K] L), (1 - primeArtinValue ρ W * x)⁻¹ := by
      rw [Finset.prod_inv_distrib, localEulerPolynomial K L p W hW x,
        ← Finset.prod_inv_distrib]

    have hfac : ∀ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
        x ^ Q.inertiaDeg (𝓞 K) = (Ideal.absNorm Q : ℂ) ^ (-s) := by
      intro Q hQ
      obtain ⟨hQp, hQL⟩ :=
        (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 L) p.ne_bot).mp hQ
      have hN : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (Q.inertiaDeg (𝓞 K)) =
          (Ideal.absNorm Q : ℂ) := by
        rw [← Nat.cast_pow, Ideal.absNorm_pow_inertiaDeg (p := p.asIdeal) (q := Q)
          (R := 𝓞 K) (S := 𝓞 L)]
      rw [hx]
      calc ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ Q.inertiaDeg (𝓞 K)
          = (Ideal.absNorm p.asIdeal : ℂ) ^ ((Q.inertiaDeg (𝓞 K)) * (-s)) := by
            rw [Complex.cpow_nat_mul]
        _ = (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (Q.inertiaDeg (𝓞 K))) ^ (-s) := by
            rw [Complex.natCast_cpow_natCast_mul]
        _ = (Ideal.absNorm Q : ℂ) ^ (-s) := by rw [hN]
    have hprod_fac : (∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
          (1 - x ^ Q.inertiaDeg (𝓞 K))⁻¹) =
        ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
          (1 - (Ideal.absNorm Q : ℂ) ^ (-s))⁻¹ :=
      Finset.prod_congr rfl fun Q hQ => by rw [hfac Q hQ]
    have hpav : (∏ ρ : ComplexDual (L ≃ₐ[K] L), (1 - primeArtinValue ρ W * x)⁻¹) =
        ∏ ρ : ComplexDual (L ≃ₐ[K] L), (1 - χ ρ p.asIdeal * x)⁻¹ :=
      Finset.prod_congr rfl fun ρ _ => by rw [← hprime ρ p W hW]
    rw [hx] at hpav
    calc (∏ ρ : ComplexDual (L ≃ₐ[K] L),
          (1 - χ ρ p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹)
        = ∏ ρ : ComplexDual (L ≃ₐ[K] L),
            (1 - primeArtinValue ρ W * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹ := by
          rw [hpav]
      _ = ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
            (1 - x ^ Q.inertiaDeg (𝓞 K))⁻¹ := by rw [hx]; exact hinv.symm
      _ = ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
            (1 - (Ideal.absNorm Q : ℂ) ^ (-s))⁻¹ := hprod_fac

  have hA' : HasProd
      (fun P : HeightOneSpectrum (𝓞 K) =>
        ∏ Q ∈ IsDedekindDomain.primesOverFinset P.asIdeal (𝓞 L),
          (1 - (Ideal.absNorm Q : ℂ) ^ (-s))⁻¹)
      (∏ ρ : ComplexDual (L ≃ₐ[K] L),
        ∑' I : Ideal (𝓞 K), χ ρ I * (Ideal.absNorm I : ℂ) ^ (-s)) :=
    hA.congr_fun fun P => (hpoint P).symm
  exact (hA'.unique (primeEulerRegroup K L s hs)).symm

end DedekindZetaZeroFree.AbelianQuotient
