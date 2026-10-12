module

public import DedekindZetaZeroFree.CharacterSums.Gauss.GeneratorInvariance
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.LocalCharacterCompatibility
public import DedekindZetaZeroFree.CharacterSums.Gauss.TracePhaseChineseRemainder

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
open UniqueFactorizationMonoid
noncomputable section
namespace DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization
open LocalFiniteSums LocalFiniteSumCompatibility
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem transport_apply_mk (J K : Ideal A.R) (h : J = K)
    (χ : MulChar (A.R ⧸ J) ℂ) (x : A.R) :
    GeneratorInvariance.transportCharacter J K h χ (Ideal.Quotient.mk K x) =
      χ (Ideal.Quotient.mk J x) := by
  subst h; rfl

private theorem sexticExponent_intNat (n : ℕ) :
    SArithmeticData.sexticExponent (n : ℤ) = n % 6 := by
  simp only [SArithmeticData.sexticExponent]
  have h : ((n : ℤ) % 6) = ((n % 6 : ℕ) : ℤ) := by norm_num
  rw [h, Int.toNat_natCast]

private theorem gaussCRT_char_base (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R) :
    MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I))
      (Ideal.Quotient.mk (A.extendIdeal I) x) = σ (A.sexticResidue I x) := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]

private theorem sexticPowerChar_one_apply (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R) :
    (A.sexticResiduePowerChar σ I 1) (Ideal.Quotient.mk (A.extendIdeal I) x) =
      (σ (A.sexticResidue I x) : ℂ) := by
  unfold SArithmeticData.sexticResiduePowerChar
  rw [show SArithmeticData.sexticExponent 1 = 1 by decide, pow_one]
  exact gaussCRT_char_base A σ I x

private theorem gaussCRT_char_unit (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R) (hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x))
    (j : ℤ) : A.sexticResiduePowerChar σ I j (Ideal.Quotient.mk (A.extendIdeal I) x) =
    σ (A.sexticResidue I x) ^ SArithmeticData.sexticExponent j := by
  unfold SArithmeticData.sexticResiduePowerChar
  rw [← hx.unit_spec, MulChar.pow_apply_coe]
  rw [hx.unit_spec, gaussCRT_char_base]

private theorem sexticResidue_unit_six (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R) (hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)) :
    (σ (A.sexticResidue I x)) ^ 6 = 1 := by
  have hv : A.sexticResidue I x = (A.sexticResidueFamily I hx.unit : F) :=
    (congrArg (MulChar.ofUnitHom (A.sexticResidueFamily I)) hx.unit_spec.symm).trans
      (MulChar.ofUnitHom_coe _ _)
  rw [hv, ← map_pow, ← Units.val_pow_eq_pow_val,
    A.sexticResidueFamily_normalized.1 I hx.unit, Units.val_one, map_one]

private theorem maskedPower_apply (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (r : A.R) :
    maskedPower C p n (n : ℤ) (residueMap C p n r)
      = (σ (A.sexticResidue (primeIdeal p) r)) ^ n := by
  by_cases hn : n = 0
  · subst hn
    rw [maskedPower_zero_depth]
    simp
  · rw [maskedPower_eq_reduction C p n hn (n : ℤ) (residueMap C p n r),
      ← sexticPower_eq_chi_pow]
    rw [show reduction C p n hn (residueMap C p n r) =
        Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r from by
      rw [residueMap, reduction]; exact Ideal.Quotient.factor_mk _ _]
    by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r)
    · rw [gaussCRT_char_unit A σ (primeIdeal p) r hx (n : ℤ), sexticExponent_intNat]
      exact (pow_eq_pow_mod n (sexticResidue_unit_six A σ (primeIdeal p) r hx)).symm
    · rw [A.sexticResiduePowerChar_nonunit σ (primeIdeal p) (n : ℤ) _ hx,
        ArithmeticContext.actual_sextic_nonunit A (primeIdeal p) r hx]
      simp [hn]

private theorem sexticResidue_finset_prod (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (P : Finset (ExteriorPrime A))
    (hSupport : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P) (r : A.R) :
    A.sexticResidue I r =
      ∏ p : P, (A.sexticResidue (primeIdeal p.val) r) ^ (exponent p.val I) := by
  classical
  let g : HeightOneSpectrum (𝓞 F) → F := fun v =>
    if h : v.asIdeal ⊔ A.cS = ⊤ then A.sexticResidue ⟨v.asIdeal, v.ne_bot, h⟩ r else 1
  have hg : ∀ (Q : A.Exterior) (v : HeightOneSpectrum (𝓞 F)), Q.val = v.asIdeal →
      g v = A.sexticResidue Q r := by
    intro Q v hQ
    have h : v.asIdeal ⊔ A.cS = ⊤ := by rw [← hQ]; exact Q.property.2
    simp only [g, dif_pos h]
    congr 1
    exact Subtype.ext hQ.symm
  have hfac := ArithmeticContext.actual_sextic_factorization_finprod A r g hg I
  let f : HeightOneSpectrum (𝓞 F) → F := fun v => g v ^ idealPrimeExponent v.asIdeal I.val
  have hsub : Function.mulSupport f ⊆ (P.image (fun p : ExteriorPrime A => p.val)) := by
    intro v hv
    have he : idealPrimeExponent v.asIdeal I.val ≠ 0 := by
      intro h0
      exact hv (by simp [f, h0])
    have hmem : v.asIdeal ∈ normalizedFactors I.val :=
      Multiset.count_pos.mp (Nat.pos_of_ne_zero he)
    have hdvd : v.asIdeal ∣ I.val := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
    have htop : v.asIdeal ⊔ A.cS = ⊤ := by
      rw [eq_top_iff, ← I.property.2]
      exact sup_le_sup_right (Ideal.dvd_iff_le.mp hdvd) A.cS
    let q : ExteriorPrime A := ⟨v, htop⟩
    have hqP : q ∈ P := by
      apply hSupport q
      change idealPrimeExponent q.val.asIdeal I.val ≠ 0
      exact he
    exact Finset.mem_image.mpr ⟨q, hqP, rfl⟩
  have h1 : A.sexticResidue I r = ∏ v ∈ (P.image (fun p : ExteriorPrime A => p.val)), f v :=
    hfac.trans (finprod_eq_prod_of_mulSupport_subset f hsub)
  rw [h1, Finset.prod_image (s := P) (g := fun p : ExteriorPrime A => p.val)
      (fun p _ q _ h => Subtype.ext h)]
  rw [Finset.univ_eq_attach]
  rw [Finset.prod_attach P (fun p : ExteriorPrime A =>
    (A.sexticResidue (primeIdeal p) r) ^ (exponent p I))]
  apply Finset.prod_congr rfl
  intro p _
  simp only [f, hg (primeIdeal p) p rfl, exponent, primeIdeal]

theorem character_crt (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) (s : A.R) (hs : A.Generates I s)
    (P : Finset (ExteriorPrime A))
    (hSupport : ∀ p : ExteriorPrime A, exponent p I ≠ 0 → p ∈ P)
    (E : FiniteTransform.Residue A.R.toSubring s ≃+* PrimePowerProduct C I P)
    (hE : ∀ (r : A.R) (p : P),
      E (FiniteTransform.residueMap A.R.toSubring s r) p =
        LocalFiniteSums.residueMap C p.val (exponent p.val I) r)
    (d : FiniteTransform.Residue A.R.toSubring s) :
    GeneratorInvariance.transportCharacter _ _ hs.2.symm
        (A.sexticResiduePowerChar σ I 1) d =
      ∏ p : P, maskedPower C p.val (exponent p.val I) (exponent p.val I) (E d p) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
  have htr : GeneratorInvariance.transportCharacter (A.extendIdeal I) (Ideal.span {s}) hs.2.symm
      (A.sexticResiduePowerChar σ I 1) (Ideal.Quotient.mk (Ideal.span {s}) r)
      = (A.sexticResiduePowerChar σ I 1) (Ideal.Quotient.mk (A.extendIdeal I) r) :=
    transport_apply_mk _ _ _ _ _
  refine htr.trans ?_
  rw [sexticPowerChar_one_apply]
  symm
  trans ∏ p : P, (σ (A.sexticResidue (primeIdeal p.val) r)) ^ (exponent p.val I)
  · exact Finset.prod_congr rfl (fun p _ => by
      change maskedPower C (↑p) (exponent (↑p) I) (↑(exponent (↑p) I))
        (E (FiniteTransform.residueMap A.R.toSubring s r) p) =
        σ (A.sexticResidue (primeIdeal ↑p) r) ^ exponent (↑p) I
      rw [hE r p, maskedPower_apply])
  · rw [show (∏ p : P, (σ (A.sexticResidue (primeIdeal p.val) r)) ^ (exponent p.val I))
        = ∏ p : P, σ ((A.sexticResidue (primeIdeal p.val) r) ^ (exponent p.val I)) from
      Finset.prod_congr rfl (fun p _ => (map_pow σ _ _).symm)]
    rw [← map_prod, sexticResidue_finset_prod A σ I P hSupport r]

end DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization

end

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

 def quo (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) :
    LocalIntegers p →+* Residue C p n :=
  (LocalFiniteSumCompatibility.residueEquiv C p n).symm.toRingHom.comp (Ideal.Quotient.mk _)

private lemma quo_integer (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (x : A.R) :
    quo C p n (LocalFiniteSumCompatibility.integerMap p x) = residueMap C p n x := by
  apply (LocalFiniteSumCompatibility.residueEquiv C p n).injective
  change (LocalFiniteSumCompatibility.residueEquiv C p n)
    ((LocalFiniteSumCompatibility.residueEquiv C p n).symm
      (Ideal.Quotient.mk _ (LocalFiniteSumCompatibility.integerMap p x))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (LocalFiniteSumCompatibility.residueEquiv_mk C p n x).symm

private lemma quo_eq_iff (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (x y : LocalIntegers p) :
    quo C p n x = quo C p n y ↔
      CompatiblePrimeRawLocal.Congruent C p n (x : LocalField p) (y : LocalField p) := by
  change (LocalFiniteSumCompatibility.residueEquiv C p n).symm (Ideal.Quotient.mk _ x) =
    (LocalFiniteSumCompatibility.residueEquiv C p n).symm (Ideal.Quotient.mk _ y) ↔ _
  rw [(LocalFiniteSumCompatibility.residueEquiv C p n).symm.injective.eq_iff,
    Ideal.Quotient.eq]
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have hh := congrArg (fun z : LocalIntegers p => (z : LocalField p)) hr
    simpa [LocalFiniteSumCompatibility.localUniformizer, LocalFiniteSumCompatibility.integerMap,
      uniformizer, mul_comm] using hh.symm
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    simpa [LocalFiniteSumCompatibility.localUniformizer, LocalFiniteSumCompatibility.integerMap,
      uniformizer, mul_comm] using hr.symm

private lemma uniformizer_ne_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : uniformizer C p ≠ 0 := by
  rw [uniformizer]
  intro h0
  have h0' : (generator C p : F) = 0 :=
    (algebraMap F (LocalField p)).injective (by rw [h0, map_zero])
  exact (generator_generates C p).1 (Subtype.ext h0')

private lemma numerator_crt_point
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (t k J : ℕ) (a h : A.R) (aU hU : (LocalIntegers p)ˣ)
    (haU : ((aU : LocalIntegers p) : LocalField p) =
      algebraMap F (LocalField p) (a : F) / uniformizer C p ^ t)
    (hhU : ((hU : LocalIntegers p) : LocalField p) =
      algebraMap F (LocalField p) (h : F) / uniformizer C p ^ J)
    (d : Residue C p k) :
    CompatiblePrimeRawLocal.numeratorCongruence C p t k J aU hU
        (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p k d) ↔
      residueMap C p k h = residueMap C p k a * d := by
  have hπ : uniformizer C p ≠ 0 := uniformizer_ne_zero C p
  have hXi : (hU : LocalIntegers p) *
      (LocalFiniteSumCompatibility.localUniformizer C p) ^ J =
      LocalFiniteSumCompatibility.integerMap p h := by
    apply Subtype.ext
    change (hU : LocalField p) *
      (LocalFiniteSumCompatibility.localUniformizer C p : LocalField p) ^ J =
      algebraMap F (LocalField p) (h : F)
    rw [show ((hU : LocalIntegers p) : LocalField p) =
        algebraMap F (LocalField p) (h : F) / uniformizer C p ^ J from hhU]
    rw [show ((LocalFiniteSumCompatibility.localUniformizer C p : LocalIntegers p) : LocalField p)
        = uniformizer C p from rfl]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hπ)
  have hYi : (aU : LocalIntegers p) *
      (LocalFiniteSumCompatibility.localUniformizer C p) ^ t *
      LocalFiniteSumCompatibility.integerMap p ((lifts C p k).val d) =
      LocalFiniteSumCompatibility.integerMap p (a * (lifts C p k).val d) := by
    apply Subtype.ext
    change (aU : LocalField p) *
      (LocalFiniteSumCompatibility.localUniformizer C p : LocalField p) ^ t *
      algebraMap F (LocalField p) (((lifts C p k).val d : A.R) : F) =
      algebraMap F (LocalField p) ((a : F) * (((lifts C p k).val d : A.R) : F))
    rw [show ((aU : LocalIntegers p) : LocalField p) =
        algebraMap F (LocalField p) (a : F) / uniformizer C p ^ t from haU]
    rw [show ((LocalFiniteSumCompatibility.localUniformizer C p : LocalIntegers p) : LocalField p)
        = uniformizer C p from rfl]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hπ), map_mul]
  have hdrep : CompatiblePrimeRawLocal.canonicalLocalRepresentative C p k d =
      ((LocalFiniteSumCompatibility.integerMap p ((lifts C p k).val d) : LocalIntegers p)
        : LocalField p) := rfl
  have hkey : CompatiblePrimeRawLocal.numeratorCongruence C p t k J aU hU
        (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p k d) ↔
      quo C p k ((hU : LocalIntegers p) *
        (LocalFiniteSumCompatibility.localUniformizer C p) ^ J) =
      quo C p k ((aU : LocalIntegers p) *
        (LocalFiniteSumCompatibility.localUniformizer C p) ^ t *
        LocalFiniteSumCompatibility.integerMap p ((lifts C p k).val d)) := by
    rw [CompatiblePrimeRawLocal.numeratorCongruence, quo_eq_iff, hdrep]
    rfl
  rw [hkey, hXi, hYi, quo_integer, quo_integer]
  rw [map_mul]
  rw [show residueMap C p k ((lifts C p k).val d) = d from (lifts C p k).property d]

theorem numerator_crt (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R) (hs : A.Generates Is s)
    (P : Finset (ExteriorPrime A))
    (hSupportS : ∀ p : ExteriorPrime A, exponent p Is ≠ 0 → p ∈ P)
    (E : FiniteTransform.Residue A.R.toSubring s ≃+* PrimePowerProduct C Is P)
    (hE : ∀ (r : A.R) (p : P),
      E (FiniteTransform.residueMap A.R.toSubring s r) p =
        LocalFiniteSums.residueMap C p.val (exponent p.val Is) r)
    (aU hU : (p : P) → (LocalIntegers p.val)ˣ)
    (haU : ∀ p : P, ((aU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (a : F) / uniformizer C p.val ^ exponent p.val Ia)
    (hhU : ∀ p : P, ((hU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (h : F) / uniformizer C p.val ^ exponent p.val Ih)
    (d : FiniteTransform.Residue A.R.toSubring s) :
    (FiniteTransform.residueMap A.R.toSubring s h =
      FiniteTransform.residueMap A.R.toSubring s a * d) ↔
    ∀ p : P, CompatiblePrimeRawLocal.numeratorCongruence C p.val
      (exponent p.val Ia) (exponent p.val Is) (exponent p.val Ih) (aU p) (hU p)
      (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val
        (exponent p.val Is) (E d p)) := by
  constructor
  · intro hg p
    have h1 : E (FiniteTransform.residueMap A.R.toSubring s h) =
        E (FiniteTransform.residueMap A.R.toSubring s a) * E d := by
      rw [hg, map_mul]
    have hp : E (FiniteTransform.residueMap A.R.toSubring s h) p =
        E (FiniteTransform.residueMap A.R.toSubring s a) p * E d p := by
      rw [h1, Pi.mul_apply]
    rw [hE h p, hE a p] at hp
    exact (numerator_crt_point C p.val (exponent p.val Ia) (exponent p.val Is)
      (exponent p.val Ih) a h (aU p) (hU p) (haU p) (hhU p) (E d p)).mpr hp
  · intro hl
    have h1 : E (FiniteTransform.residueMap A.R.toSubring s h) =
        E (FiniteTransform.residueMap A.R.toSubring s a) * E d := by
      funext p
      rw [Pi.mul_apply, hE h p, hE a p]
      exact (numerator_crt_point C p.val (exponent p.val Ia) (exponent p.val Is)
        (exponent p.val Ih) a h (aU p) (hU p) (haU p) (hhU p) (E d p)).mp (hl p)
    have h2 := congrArg (fun z => E.symm z) h1
    simpa only [RingEquiv.symm_apply_apply, map_mul] using h2

end DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization

end

end

section

open scoped BigOperators Classical
noncomputable section
namespace DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization

theorem constrained_sum_crt
    {W ι D V : Type*} [CommSemiring W] [Fintype ι] [Fintype D] [Fintype V]
    {Dp Vp : ι → Type*} [∀ i, Fintype (Dp i)] [∀ i, Fintype (Vp i)]
    (Ed : D ≃ ((i : ι) → Dp i)) (Ev : V ≃ ((i : ι) → Vp i))
    (c : D → Prop) [DecidablePred c]
    (cs : ∀ i, Dp i → Prop) [∀ i, DecidablePred (cs i)]
    (χd : D → W) (χv : V → W) (φ : D → V → W)
    (χdp : ∀ i, Dp i → W) (χvp : ∀ i, Vp i → W)
    (φp : ∀ i, Dp i → Vp i → W)
    (hc : ∀ d, c d ↔ ∀ i, cs i (Ed d i))
    (hχd : ∀ d, χd d = ∏ i, χdp i (Ed d i))
    (hχv : ∀ v, χv v = ∏ i, χvp i (Ev v i))
    (hφ : ∀ d v, c d → φ d v = ∏ i, φp i (Ed d i) (Ev v i)) :
    (∑ d, if c d then χd d * ∑ v, χv v * φ d v else 0) =
      ∏ i, ∑ d : Dp i, if cs i d then
        χdp i d * ∑ v : Vp i, χvp i v * φp i d v else 0 := by
  classical
  have hprod (d : (i : ι) → Dp i) :
      (if ∀ i, cs i (d i) then
        (∏ i, χdp i (d i)) * ∑ v : (i : ι) → Vp i,
          (∏ i, χvp i (v i)) * ∏ i, φp i (d i) (v i) else 0) =
        ∏ i, if cs i (d i) then
          χdp i (d i) * ∑ v : Vp i, χvp i v * φp i (d i) v else 0 := by
    split_ifs with hd
    · simp only [hd, ↓reduceIte]
      simp_rw [← Finset.prod_mul_distrib]
      rw [← Fintype.prod_sum (fun i v => χvp i v * φp i (d i) v),
        ← Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp hd
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  calc
    _ = ∑ d : (i : ι) → Dp i,
        if ∀ i, cs i (d i) then
          (∏ i, χdp i (d i)) * ∑ v : (i : ι) → Vp i,
            (∏ i, χvp i (v i)) * ∏ i, φp i (d i) (v i) else 0 := by
      apply Fintype.sum_equiv Ed
      intro d
      by_cases hd : c d
      · rw [if_pos hd, if_pos ((hc d).mp hd)]
        rw [hχd]
        congr 1
        apply Fintype.sum_equiv Ev
        intro v
        rw [hχv, hφ d v hd]
      · rw [if_neg hd, if_neg (fun h => hd ((hc d).mpr h))]
    _ = ∑ d : (i : ι) → Dp i, ∏ i, if cs i (d i) then
          χdp i (d i) * ∑ v : Vp i, χvp i v * φp i (d i) v else 0 := by
      exact Finset.sum_congr rfl (fun d _ => hprod d)
    _ = _ := (Fintype.prod_sum (fun i (d : Dp i) => if cs i d then
      χdp i d * ∑ v : Vp i, χvp i v * φp i d v else 0)).symm

end DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization

end

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.MaskedQuotientCRT
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def primeExponent (p : ExteriorPrime A) (I : A.Exterior) : ℕ :=
  idealPrimeExponent p.val.asIdeal I.val

 theorem prime_outside (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have hc : A.cS ≤ p.val.asIdeal := Ideal.IsPrime.prod_le p.val.isPrime |>.mpr ⟨p.val, hp, le_rfl⟩
  apply p.val.isPrime.ne_top
  apply top_le_iff.mp
  calc
    ⊤ = p.val.asIdeal ⊔ A.cS := p.property.symm
    _ ≤ p.val.asIdeal := sup_le le_rfl hc

 def boundIdeal (p : ExteriorPrime A) (n : ℕ) : Ideal A.R where
  carrier := {a | p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change p.val.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change p.val.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property p.val (prime_outside p)) zero_le).trans (by simpa using hb)

private theorem generates_valuation (p : ExteriorPrime A)
    (I : A.Exterior) (r : A.R) (hr : A.Generates I r) :
    p.val.valuation F (r : F) = WithZero.exp (-(primeExponent p I : ℤ)) := by
  let n := primeExponent p I
  have hdvd (k : ℕ) : p.val.asIdeal ^ k ∣ I.val ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors p.val.irreducible I.property.1]
    simp [n, primeExponent, idealPrimeExponent]
  have hIn : I.val ≤ p.val.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I.val ≤ p.val.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  have hmap : A.extendIdeal I ≤ boundIdeal p n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))
    rw [p.val.valuation_of_algebraMap]
    exact (p.val.intValuation_le_pow_iff_mem a n).mpr (hIn ha)
  have hrv : p.val.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hr.2]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨a, ha, han⟩ : ∃ a : 𝓞 F, a ∈ I.val ∧ a ∉ p.val.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have ham : algebraMap (𝓞 F) A.R a ∈ Ideal.span ({r} : Set A.R) := by
    rw [hr.2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ham
  have hav : p.val.valuation F (a : F) ≤ p.val.valuation F (r : F) := by
    have hh := congrArg (fun t : A.R => (t : F)) hy
    change (a : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property p.val (prime_outside p)) zero_le).trans (by simp)
  have hrv' : ¬ p.val.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply han
    apply (p.val.intValuation_le_pow_iff_mem a (n + 1)).mp
    rw [← p.val.valuation_of_algebraMap (K := F)]
    exact hav.trans h
  have hnz : p.val.valuation F (r : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hr.1)
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  have hv : WithZero.log (p.val.valuation F (r : F)) = -(n : ℤ) := by
    push_cast at hrv'
    omega
  rw [← WithZero.exp_log hnz, hv]

theorem localUnitPart_exists (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (I : A.Exterior) (x : A.R) (hx : A.Generates I x) :
    ∃ u : (LocalIntegers p)ˣ,
      (u.val : LocalField p) = algebraMap F (LocalField p) (x : F) /
        uniformizer C p ^ primeExponent p I := by
  have hvx := generates_valuation p I x hx
  have hvπ := generates_valuation p (primeIdeal p) (generator C p) (generator_generates C p)
  have hp : primeExponent p (primeIdeal p) = 1 := by
    simp [primeExponent, primeIdeal, idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]
  rw [hp] at hvπ
  let z : LocalField p := algebraMap F (LocalField p) (x : F) /
    uniformizer C p ^ primeExponent p I
  have hz : Valued.v z = 1 := by
    dsimp [z, uniformizer]
    rw [map_div₀, map_pow]
    change Valued.v ((x : F) : LocalField p) /
        Valued.v (((generator C p : A.R) : F) : LocalField p) ^ primeExponent p I = 1
    rw [p.val.valuedAdicCompletion_eq_valuation',
      p.val.valuedAdicCompletion_eq_valuation', hvx, hvπ]
    rw [← WithZero.exp_nsmul]
    simp
  let r : LocalIntegers p := ⟨z, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hz]⟩
  have hu : IsUnit r := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hz
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]

def localUnitPart (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (I : A.Exterior) (x : A.R) (hx : A.Generates I x) :
    (LocalIntegers p)ˣ :=
  Classical.choose (localUnitPart_exists C p I x hx)

theorem localUnitPart_spec (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (I : A.Exterior) (x : A.R) (hx : A.Generates I x) :
    ((localUnitPart C p I x hx).val : LocalField p) =
      algebraMap F (LocalField p) (x : F) / uniformizer C p ^ primeExponent p I :=
  Classical.choose_spec (localUnitPart_exists C p I x hx)

def coefficient (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) : ℂ := by
  letI : Finite (FiniteTransform.Residue A.R.toSubring s) := by
    change Finite (A.R ⧸ Ideal.span {s})
    rw [hs.2]
    exact A.exteriorResidue_finite Is
  letI : Finite (FiniteTransform.Residue A.R.toSubring a) := by
    change Finite (A.R ⧸ Ideal.span {a})
    rw [ha.2]
    exact A.exteriorResidue_finite Ia
  letI : Fintype (FiniteTransform.Residue A.R.toSubring s) := Fintype.ofFinite _
  letI : Fintype (FiniteTransform.Residue A.R.toSubring a) := Fintype.ofFinite _
  exact FiniteTransform.finiteCoefficient A.R.toSubring s a h
    (GeneratorInvariance.transportCharacter _ _ hs.2.symm
      (A.sexticResiduePowerChar σ Is 1))
    (GeneratorInvariance.transportCharacter _ _ ha.2.symm
      (A.sexticResiduePowerChar σ Ia 1))
    (Circle.coeHom.compAddChar A.fieldTraceCharacter)

open UniqueFactorizationMonoid

theorem full_prime_power_crt (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a) (hh : A.Generates Ih h)
    (hsAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (s : F) (by exact_mod_cast hs.1)))
    (haAllowed : A.IsAllowed C.correction.B
      (Units.mk0 (a : F) (by exact_mod_cast ha.1)))
    (P : Finset (ExteriorPrime A))
    (hSupportS : ∀ p : ExteriorPrime A, primeExponent p Is ≠ 0 → p ∈ P)
    (hSupportA : ∀ p : ExteriorPrime A, primeExponent p Ia ≠ 0 → p ∈ P)
    (hSupportH : ∀ p : ExteriorPrime A, primeExponent p Ih ≠ 0 → p ∈ P) :
    coefficient C Is Ia s a h hs ha =
      ∏ p ∈ P, CompatiblePrimeRawLocal.R C p
        (primeExponent p Ia) (primeExponent p Is) (primeExponent p Ih)
        (localUnitPart C p Is s hs) (localUnitPart C p Ia a ha)
        (localUnitPart C p Ih h hh) := by
  letI : Finite (FiniteTransform.Residue A.R.toSubring s) := by
    change Finite (A.R ⧸ Ideal.span {s})
    rw [hs.2]
    exact A.exteriorResidue_finite Is
  letI : Finite (FiniteTransform.Residue A.R.toSubring a) := by
    change Finite (A.R ⧸ Ideal.span {a})
    rw [ha.2]
    exact A.exteriorResidue_finite Ia
  letI : Fintype (FiniteTransform.Residue A.R.toSubring s) := Fintype.ofFinite _
  letI : Fintype (FiniteTransform.Residue A.R.toSubring a) := Fintype.ofFinite _
  obtain ⟨Es, hEs⟩ := MaskedPrimePowerCRTFactorization.quotient_crt C Is s hs P hSupportS
  obtain ⟨Ea, hEa⟩ := MaskedPrimePowerCRTFactorization.quotient_crt C Ia a ha P hSupportA
  let sU := fun p : P => localUnitPart C p.val Is s hs
  let aU := fun p : P => localUnitPart C p.val Ia a ha
  let hU := fun p : P => localUnitPart C p.val Ih h hh
  have hsU : ∀ p : P, ((sU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (s : F) /
        uniformizer C p.val ^ MaskedPrimePowerCRTFactorization.exponent p.val Is :=
    fun p => localUnitPart_spec C p.val Is s hs
  have haU : ∀ p : P, ((aU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (a : F) /
        uniformizer C p.val ^ MaskedPrimePowerCRTFactorization.exponent p.val Ia :=
    fun p => localUnitPart_spec C p.val Ia a ha
  have hhU : ∀ p : P, ((hU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (h : F) /
        uniformizer C p.val ^ MaskedPrimePowerCRTFactorization.exponent p.val Ih :=
    fun p => localUnitPart_spec C p.val Ih h hh
  have H := MaskedPrimePowerCRTFactorization.constrained_sum_crt Es.toEquiv Ea.toEquiv
    (fun d => FiniteTransform.residueMap A.R.toSubring s h =
      FiniteTransform.residueMap A.R.toSubring s a * d)
    (fun p d => CompatiblePrimeRawLocal.numeratorCongruence C p.val
      (primeExponent p.val Ia) (primeExponent p.val Is) (primeExponent p.val Ih)
      (aU p) (hU p) (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val
        (primeExponent p.val Is) d))
    (GeneratorInvariance.transportCharacter _ _ hs.2.symm
      (A.sexticResiduePowerChar σ Is 1))
    (GeneratorInvariance.transportCharacter _ _ ha.2.symm
      (A.sexticResiduePowerChar σ Ia 1))
    (fun d v => (Circle.coeHom.compAddChar A.fieldTraceCharacter)
      (((h : F) - (a : F) * ((FiniteTransform.canonicalLifts A.R.toSubring s).val d : F)) *
        ((FiniteTransform.canonicalLifts A.R.toSubring a).val v : F) / ((s : F) * (a : F))))
    (fun p d => maskedPower C p.val (primeExponent p.val Is) (primeExponent p.val Is) d)
    (fun p v => maskedPower C p.val (primeExponent p.val Ia) (primeExponent p.val Ia) v)
    (fun p d v => CompatiblePrimeRawLocal.rawPhase C p.val
      (primeExponent p.val Ia) (primeExponent p.val Is) (primeExponent p.val Ih)
      (sU p) (aU p) (hU p)
      (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val (primeExponent p.val Is) d)
      (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val (primeExponent p.val Ia) v))
    (fun d => MaskedPrimePowerCRTFactorization.numerator_crt C Is Ia Ih s a h hs P hSupportS
      Es hEs aU hU haU hhU d)
    (fun d => MaskedPrimePowerCRTFactorization.character_crt C Is s hs P hSupportS Es hEs d)
    (fun v => MaskedPrimePowerCRTFactorization.character_crt C Ia a ha P hSupportA Ea hEa v)
    (fun d v hc => MaskedPrimePowerCRTFactorization.phase_crt C Is Ia Ih s a h hs ha P
      hSupportS hSupportA Es Ea hEs hEa sU aU hU hsU haU hhU d v hc)
  rw [← Finset.prod_coe_sort P (fun p => CompatiblePrimeRawLocal.R C p
    (primeExponent p Ia) (primeExponent p Is) (primeExponent p Ih)
    (localUnitPart C p Is s hs) (localUnitPart C p Ia a ha)
    (localUnitPart C p Ih h hh))]
  convert H using 1 <;>
    simp only [coefficient, FiniteTransform.finiteCoefficient,
      FiniteTransform.finiteCoefficientWithLifts, CompatiblePrimeRawLocal.R,
      CompatiblePrimeRawLocal.RWithLifts, CompatiblePrimeRawLocal.canonicalLocalLifts,
      sU, aU, hU]
  all_goals
    congr 1

end DedekindZetaZeroFree.MaskedQuotientCRT

end

end
