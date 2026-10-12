module

public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalQuotientSums

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

abbrev exponent (p : ExteriorPrime A) (I : A.Exterior) : ℕ :=
  idealPrimeExponent p.val.asIdeal I.val

abbrev PrimePowerProduct (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (P : Finset (ExteriorPrime A)) :=
  (p : P) → Residue C p.val (exponent p.val I)

open UniqueFactorizationMonoid

private theorem support_factor_aux (I : A.Exterior) (P : Finset (ExteriorPrime A))
    (hP : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P) :
    I.val = ∏ p ∈ P, p.val.asIdeal ^ exponent p I := by
  let Q := P.image (fun p => p.val.asIdeal)
  have hsub : idealPrimeSupport I.val ⊆ Q := by
    intro p hp
    have hp' : p ∈ normalizedFactors I.val := Multiset.mem_toFinset.mp hp
    have hprime := prime_of_normalized_factor p hp'
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
    have hv : p ⊔ A.cS = ⊤ := by
      apply top_unique
      rw [← I.property.2]
      exact sup_le_sup_right (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hp')) _
    let ep : ExteriorPrime A := ⟨v, hv⟩
    have hep : ep ∈ P := hP ep (Multiset.count_ne_zero.mpr hp')
    exact Finset.mem_image.mpr ⟨ep, hep, rfl⟩
  have hq : I.val = ∏ p ∈ Q, p ^ idealPrimeExponent p I.val := by
    calc
      I.val = ∏ p ∈ idealPrimeSupport I.val, p ^ idealPrimeExponent p I.val :=
        ((Finset.prod_multiset_count (normalizedFactors I.val)).symm.trans
          (Ideal.prod_normalizedFactors_eq_self I.property.1)).symm
      _ = ∏ p ∈ Q, p ^ idealPrimeExponent p I.val := by
        apply Finset.prod_subset hsub
        intro p hp hpn
        rw [show idealPrimeExponent p I.val = 0 from Multiset.count_eq_zero.mpr
          (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hpn), pow_zero]
  refine hq.trans ?_
  exact Finset.prod_image (f := fun p => p ^ idealPrimeExponent p I.val)
    (g := fun p : ExteriorPrime A => p.val.asIdeal) (fun a ha b hb hab => by
      apply Subtype.ext
      exact HeightOneSpectrum.asIdeal_injective hab)

 theorem principal_span_factorization (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (x : A.R) (hx : A.Generates I x)
    (P : Finset (ExteriorPrime A))
    (hP : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P) :
    Ideal.span ({x} : Set A.R) =
      ∏ p ∈ P, Ideal.span ({generator C p ^ exponent p I} : Set A.R) := by
  rw [hx.2]
  unfold SArithmeticData.extendIdeal
  rw [support_factor_aux I P hP]
  change Ideal.mapHom (algebraMap (𝓞 F) A.R) _ = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  change Ideal.map (algebraMap (𝓞 F) A.R) (p.val.asIdeal ^ exponent p I) = _
  rw [Ideal.map_pow]
  change A.extendIdeal (primeIdeal p) ^ exponent p I = _
  rw [← (generator_generates C p).2, Ideal.span_singleton_pow]

 theorem prime_power_spans_coprime (C : A.GeneralArithmeticContext σ η hS)
    (p q : ExteriorPrime A) (hpq : p ≠ q) (k t : ℕ) :
    IsCoprime (Ideal.span ({generator C p ^ k} : Set A.R))
      (Ideal.span ({generator C q ^ t} : Set A.R)) := by
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow,
    (generator_generates C p).2, (generator_generates C q).2]
  apply IsCoprime.pow
  rw [Ideal.isCoprime_iff_sup_eq]
  unfold SArithmeticData.extendIdeal
  rw [← Ideal.map_sup]
  have hne : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  change Ideal.map (algebraMap (𝓞 F) A.R) (p.val.asIdeal ⊔ q.val.asIdeal) = ⊤
  rw [(HeightOneSpectrum.isCoprime_of_ne _ _ hne).sup_eq, Ideal.map_top]

 def quotientPiEquiv (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (x : A.R) (hx : A.Generates I x)
    (P : Finset (ExteriorPrime A))
    (hP : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P) :
    FiniteTransform.Residue A.R.toSubring x ≃+*
      ((p : P) → Residue C p.val (exponent p.val I)) := by
  let f : P → Ideal A.R := fun p => Ideal.span {generator C p.val ^ exponent p.val I}
  have hc : Pairwise (fun p q => IsCoprime (f p) (f q)) := by
    intro p q hpq
    exact prime_power_spans_coprime C p.val q.val (fun h => hpq (Subtype.ext h)) _ _
  have he : Ideal.span ({x} : Set A.R) = ⨅ p, f p := by
    rw [principal_span_factorization C I x hx P hP, ← Finset.prod_coe_sort]
    simpa only [Finset.mem_univ, iInf_true] using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime (hc.set_pairwise (↑(Finset.univ : Finset P))))
  exact (Ideal.quotEquivOfEq he).trans (Ideal.quotientInfRingEquivPiQuotient f hc)

private theorem quotientPiEquiv_mk (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (x : A.R) (hx : A.Generates I x)
    (P : Finset (ExteriorPrime A))
    (hP : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P) (y : A.R) :
    quotientPiEquiv C I x hx P hP (FiniteTransform.residueMap A.R.toSubring x y) =
      fun p : P => Ideal.Quotient.mk
        (Ideal.span ({generator C p.val ^ exponent p.val I} : Set A.R)) y := by
  ext p
  change Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ y
  rfl

theorem quotient_crt (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (s : A.R) (hs : A.Generates I s)
    (P : Finset (ExteriorPrime A))
    (hSupport : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P) :
    ∃ E : FiniteTransform.Residue A.R.toSubring s ≃+* PrimePowerProduct C I P,
      ∀ (r : A.R) (p : P),
        E (FiniteTransform.residueMap A.R.toSubring s r) p =
          LocalFiniteSums.residueMap C p.val (exponent p.val I) r := by
  refine ⟨quotientPiEquiv C I s hs P hSupport, ?_⟩
  intro r p
  exact congrFun (quotientPiEquiv_mk C I s hs P hSupport r) p

end DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization

end
