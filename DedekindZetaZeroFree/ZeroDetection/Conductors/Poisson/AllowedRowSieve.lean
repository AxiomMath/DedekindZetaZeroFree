module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ActualConductorSieve

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

section Copied

open DedekindZetaZeroFree DedekindZetaZeroFree.Detector IsDedekindDomain
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem primitive_sieve_finset_transfer_of_property
    (F : Type) [Field F] [NumberField F]
    (C Ccond N X ε : ℝ)
    (P : PrimitiveFrequencyCharacter F → Prop)
    (hbound : ∀ (n : ℕ) (ω : Fin n → PrimitiveFrequencyCharacter F),
      Pairwise (fun i j => ¬ samePrimitiveFrequencyCharacter F (ω i) (ω j)) →
      (∀ i, (Ideal.absNorm (ω i).conductor : ℝ) ≤ Ccond * X) →
      (∀ i, P (ω i)) →
      ∀ c : NonzeroIdeal F →₀ ℂ,
        (∀ I ∈ c.support, (Ideal.absNorm I.val : ℝ) ≤ N) →
        (∑ i, ‖∑ I ∈ c.support, c I * (ω i).character I.val‖ ^ 2) ≤
          C * (N + X ^ (2 : ℕ)) * (N * X) ^ ε * ∑ I ∈ c.support, ‖c I‖ ^ 2)
    {α : Type} (J : Finset α) (ω : α → PrimitiveFrequencyCharacter F)
    (hdist : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ¬ samePrimitiveFrequencyCharacter F (ω i) (ω j))
    (hcond : ∀ i ∈ J, (Ideal.absNorm (ω i).conductor : ℝ) ≤ Ccond * X)
    (hP : ∀ i ∈ J, P (ω i))
    (B : Finset (Ideal (𝓞 F)))
    (hB : ∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (b : Ideal (𝓞 F) → ℂ) :
    (∑ i ∈ J, ‖∑ I ∈ B, b I * (ω i).character I‖ ^ 2) ≤
      C * (N + X ^ (2 : ℕ)) * (N * X) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  let D : Finset (NonzeroIdeal F) := B.attach.image (fun I => (⟨I.val, (hB I.val I.property).1⟩ : NonzeroIdeal F))
  have hD (I : NonzeroIdeal F) : I ∈ D ↔ I.val ∈ B := by
    simp only [D, Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨I, rfl⟩
      exact I.property
    · intro hI
      exact ⟨⟨I.val, hI⟩, Subtype.ext rfl⟩
  let c : NonzeroIdeal F →₀ ℂ := Finsupp.onFinset D
    (fun I => if I ∈ D then b I.val else 0) (by
      intro I hI
      by_contra hn
      simp [hn] at hI)
  have hc : c.support ⊆ D := Finsupp.support_onFinset_subset
  have hcval (I : NonzeroIdeal F) (hI : I ∈ D) : c I = b I.val := by
    simp [c, hI]
  have sumD {M : Type} [AddCommMonoid M] (f : Ideal (𝓞 F) → M) :
      (∑ I ∈ D, f I.val) = ∑ I ∈ B, f I := by
    dsimp only [D]
    rw [Finset.sum_image]
    · exact Finset.sum_attach B f
    · intro I hI K hK h
      exact Subtype.ext (congrArg (fun I : NonzeroIdeal F => I.val) h)
  have sumChar (χ : PrimitiveFrequencyCharacter F) :
      (∑ I ∈ c.support, c I * χ.character I.val) =
        ∑ I ∈ B, b I * χ.character I := by
    calc
      _ = ∑ I ∈ D, c I * χ.character I.val := by
        apply Finset.sum_subset hc
        intro I hI hn
        rw [Finsupp.notMem_support_iff.mp hn, zero_mul]
      _ = ∑ I ∈ D, b I.val * χ.character I.val :=
        Finset.sum_congr rfl (fun I hI => by rw [hcval I hI])
      _ = _ := sumD (fun I => b I * χ.character I)
  have sumEnergy : (∑ I ∈ c.support, ‖c I‖ ^ 2) = ∑ I ∈ B, ‖b I‖ ^ 2 := by
    calc
      _ = ∑ I ∈ D, ‖c I‖ ^ 2 := by
        apply Finset.sum_subset hc
        intro I hI hn
        simp [Finsupp.notMem_support_iff.mp hn]
      _ = ∑ I ∈ D, ‖b I.val‖ ^ 2 :=
        Finset.sum_congr rfl (fun I hI => by rw [hcval I hI])
      _ = _ := sumD (fun I => ‖b I‖ ^ 2)
  let e := (Fintype.equivFin J).symm
  have h := hbound (Fintype.card J) (fun i => ω (e i).val)
    (fun i j hij => hdist _ (e i).property _ (e j).property
      (fun hh => hij (e.injective (Subtype.ext hh))))
    (fun i => hcond _ (e i).property) (fun i => hP _ (e i).property) c
    (fun I hI => (hB I.val ((hD I).mp (hc hI))).2)
  simp only [sumChar, sumEnergy] at h
  rw [e.sum_comp (fun i : J => ‖∑ I ∈ B, b I * (ω i.val).character I‖ ^ 2)] at h
  rw [Finset.sum_coe_sort J (fun i => ‖∑ I ∈ B, b I * (ω i).character I‖ ^ 2)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem frequency_denominator_full_local_tuples
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η)
    (A : SArithmeticData F) (hAS : (A.Sf : Set (HeightOneSpectrum (𝓞 F))) = S) :
    ∃ L : Set (FixedSResidue.FullLocalCharacters A), L.Finite ∧
      (∀ σ ∈ L, FixedSResidue.HasFiniteOrder A σ) ∧
      ∀ (U : FrequencyRepresentatives F S)
        (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η) (u : U.carrier),
        ∃ σ ∈ L, HasFixedFullSLocalTuple F A (T.denominator u) σ := by
  classical
  obtain ⟨P, Q, hfin, hlocal⟩ :=
    frequency_rows_finite_ramified_local_types F ζ12 hζ12 ι S hS hSix η hηS
  let index : {v // v ∈ A.Sf} → S := fun v => ⟨v.val, hAS ▸ v.property⟩
  let R := Set.univ.pi (fun v : {v // v ∈ A.Sf} => Q (index v))
  have hR : R.Finite := Set.Finite.pi (fun v => (hfin (index v)).2)
  let tuple : ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ →ₜ* ℂˣ) →
      FixedSResidue.FullLocalCharacters A :=
    fun δ => (fun _ => 1, fun v => (δ v).toMonoidHom)
  let L := (tuple '' R) ∩ {σ | FixedSResidue.HasFiniteOrder A σ}
  refine ⟨L, (hR.image tuple).inter_of_left _, fun σ hσ => hσ.2, ?_⟩
  intro U K T u
  choose δ hδmem hδlocal using fun v : {v // v ∈ A.Sf} =>
    (hlocal U K T u (index v)).2
  have hδR : δ ∈ R := by
    intro v hv
    exact hδmem v
  have hfiniteOrder : FixedSResidue.HasFiniteOrder A (tuple δ) := by
    let χ := T.denominator u
    let hc := primitive12_totallyComplex F ζ12 hζ12
    let k := Nat.card (ClassFieldTheory.RayClassGroup
      (RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero))
    refine ⟨k, RayClassBridge.ideleClassCharacter_exponent_pos F χ.conductor
      χ.conductor_ne_zero, ?_, ?_⟩
    · intro w x
      simp [tuple]
    · intro v x
      have hcan : Conductor.Raw.IsFrequencyLocalComponent F χ v.val
          (Conductor.canonicalFrequencyLocalCharacter F hc χ v.val) :=
        Conductor.LocalTwistSteps.idelic_restriction_is_raw_local_component
          F hc χ v.val _ (by intro x; rfl)
      have heq := Conductor.LocalTwistSteps.raw_local_component_unique
        F χ v.val (δ v) _ (hδlocal v) hcan
      change δ v x ^ k = 1
      rw [heq]
      exact Conductor.canonicalFrequencyLocalCharacter_pow_card F hc χ v.val x
  refine ⟨tuple δ, ⟨⟨δ, hδR, rfl⟩, hfiniteOrder⟩, ?_, ?_⟩
  · intro w
    rfl
  · intro v
    exact ⟨δ v, rfl, hδlocal v⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem unrestricted_balanced_section
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) [IsPrincipalIdealRing A.R] :
    ∃ K_bal : Set A.G, IsCompact K_bal ∧
      Nonempty (A.BalancedIdealSection ⊤ K_bal) := by
  classical
  obtain ⟨K, hK, hcover⟩ := A.exists_compact_balanced_cover
  let K_bal : Set A.G := Subtype.val '' K
  have hcompact : IsCompact K_bal := hK.image continuous_subtype_val
  have hex : ∀ I : A.Exterior, ∃ (r : A.R) (a : Fˣ),
      A.Generates I r ∧ (a : F) = (r : F) ∧
      A.diagonal a / A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I) ∈ K_bal := by
    intro I
    let J := A.extendIdeal I
    let r := Submodule.IsPrincipal.generator J
    have hspan : Ideal.span {r} = J := Submodule.IsPrincipal.span_singleton_generator J
    have hr : r ≠ 0 := by
      intro h
      have hJ : J = ⊥ := by rw [← hspan, h]; simp
      have hJ0 : J ≠ ⊥ := A.extendIdeal_ne_zero I
      exact hJ0 hJ
    let a := Units.mk0 (r : F) (by exact_mod_cast hr)
    have ha : (a : F) = (r : F) := rfl
    have hg : A.Generates I r := ⟨hr, hspan⟩
    let y : A.G1 := ⟨A.diagonal a /
      A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I),
        A.normalized_generator_mem_G1 I r hg a ha⟩
    obtain ⟨γ, hγ⟩ := hcover y
    have hΓ : (γ.val : A.G) ∈ A.Gamma := γ.property
    obtain ⟨v, hv, hvγ⟩ := hΓ
    obtain ⟨u, hu, huv⟩ := hv
    let ε : A.U := ⟨u, hu⟩
    let r' : A.R := r * (A.unitEquiv ε ^ 6 : A.Rˣ)
    let a' : Fˣ := a * u ^ 6
    have ha' : (a' : F) = (r' : F) := by
      simp [a', r', ha, SArithmeticData.unitEquiv, ε]
    have hr' : A.Generates I r' := by
      refine ⟨mul_ne_zero hr (Units.ne_zero _), ?_⟩
      rw [Ideal.span_singleton_mul_right_unit (Units.isUnit _) r]
      exact hspan
    refine ⟨r', a', hr', ha', ?_⟩
    refine ⟨γ.val * y, hγ, ?_⟩
    change (γ.val : A.G) * (y : A.G) = _
    rw [← hvγ, ← huv]
    simp only [y, a', map_mul, map_pow, powMonoidHom_apply, div_eq_mul_inv]
    ac_rfl
  choose r a hr ha hb using hex
  refine ⟨K_bal, hcompact, ⟨{
    generator := r
    fieldUnit := a
    generates := hr
    fieldUnit_coe := ha
    allowed := ?_
    balanced := hb}⟩⟩
  intro I
  trivial

end Copied

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def dyadNonprincipal (U : ℝ) : Set D.Row :=
  {u | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U}

theorem actual_conductor_sieve :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (J : Finset D.Row), (∀ u ∈ J, u ∈ dyadNonprincipal D U) →
        ∀ (B : Finset (Ideal (𝓞 F))),
          (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∑ u ∈ J, ‖∑ I ∈ B, b I * (D.omega u).character I‖ ^ 2) ≤
              C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  intro ε hε
  letI : IsPrincipalIdealRing D.recipe.A.R :=
    D.recipe.A.principalIdealRing_of_classGroup_subsingleton D.recipe.classKilled
  letI : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) := by
    intro v hv
    by_contra h
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six D.recipe.A v h)
  obtain ⟨Vr, e, he, hSnorm⟩ :=
    PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.actual_detector_frequency_representatives
      D.recipe
  obtain ⟨η0, hη0S, _, htarget⟩ :=
    PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.target_primitive_inducer
      D.recipe
  have cop : ∀ m : Ideal (𝓞 F), m ≠ ⊥ →
      ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.asIdeal ⊔ m = ⊤ := by
    intro m hm
    apply Filter.eventually_cofinite.mpr
    apply (Ideal.finite_factors hm).subset
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    apply Ideal.dvd_iff_le.mpr
    have hvmax : v.asIdeal.IsMaximal := v.isMaximal
    exact (hvmax.eq_of_le hv (show v.asIdeal ≤ v.asIdeal ⊔ m from le_sup_left)).symm ▸
      (show m ≤ v.asIdeal ⊔ m from le_sup_right)

  let f : D.Row → PrincipalMellinComparison.Frequency D.recipe :=
    fun r => ⟨⟨r.u, r.isRep.choose⟩, r.isRep.choose_spec⟩
  have hinj : ∀ r r' : D.Row, e (f r) = e (f r') → r = r' := by
    intro r r' h
    apply FixedData.Row.u_injective
    exact congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe =>
      (x.val.val : D.recipe.A.R)) (e.injective h)
  obtain ⟨K0⟩ := Detector.kummer_frequency_family_exists F D.recipe.A.zeta12
    D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix Vr
  let K : Detector.KummerFrequencyFamily F D.recipe.A.zeta12 D.recipe.σ
      (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) Vr :=
    { numerator := fun w =>
        if h : ∃ r : D.Row, e (f r) = w then (D.inducers h.choose).plus else K0.numerator w
      kummer := by
        intro w
        by_cases h : ∃ r : D.Row, e (f r) = w
        · have hk := (D.inducers h.choose).kummer
          have hw : w.val = Units.mk0 ((h.choose.u : D.recipe.A.R) : F)
              (by exact_mod_cast h.choose.generates.1) := by
            have hw0 : w.val = (e (f h.choose)).val := congrArg Subtype.val h.choose_spec.symm
            rw [hw0, he]
            exact Units.ext rfl
          show Detector.IsKummerFrequencyCharacter F D.recipe.A.zeta12 D.recipe.σ _ w.val
            (if h : ∃ r : D.Row, e (f r) = w then (D.inducers h.choose).plus
              else K0.numerator w)
          rw [dif_pos h, hw]
          exact hk
        · show Detector.IsKummerFrequencyCharacter F D.recipe.A.zeta12 D.recipe.σ _ w.val
            (if h : ∃ r : D.Row, e (f r) = w then (D.inducers h.choose).plus
              else K0.numerator w)
          rw [dif_neg h]
          exact K0.kummer w }
  have hKnum : ∀ r : D.Row, K.numerator (e (f r)) = (D.inducers r).plus := by
    intro r
    have h : ∃ r' : D.Row, e (f r') = e (f r) := ⟨r, rfl⟩
    show (if h : ∃ r' : D.Row, e (f r') = e (f r) then (D.inducers h.choose).plus
      else K0.numerator (e (f r))) = _
    rw [dif_pos h, hinj _ _ h.choose_spec]
  obtain ⟨T⟩ := Detector.twisted_frequency_family_exists F D.recipe.A.zeta12
    D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix Vr K η0
  have hω : ∀ r : D.Row, D.omega r = T.denominator (e (f r)) := by
    intro r
    apply PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.primitive_inducers_eq_of_cofinite_prime_values
    filter_upwards [cop (D.recipe.A.modulus * (D.inducers r).plus.conductor *
        (D.inducers r).minus.conductor)
        (mul_ne_zero (mul_ne_zero D.recipe.A.modulus_ne_zero
          (D.inducers r).plus.conductor_ne_zero) (D.inducers r).minus.conductor_ne_zero),
      cop (η0.conductor * (K.numerator (e (f r))).conductor * (T.denominator (e (f r))).conductor)
        (mul_ne_zero (mul_ne_zero η0.conductor_ne_zero
          (K.numerator (e (f r))).conductor_ne_zero) (T.denominator (e (f r))).conductor_ne_zero),
      cop (D.recipe.A.modulus * η0.conductor)
        (mul_ne_zero D.recipe.A.modulus_ne_zero η0.conductor_ne_zero)] with v h1 h2 h3
    have twist1 := (D.inducers r).twist v.asIdeal v.ne_bot h1
    have twist2 := T.induces (e (f r)) v.asIdeal v.ne_bot h2
    have ht := htarget v.asIdeal v.ne_bot h3
    rw [twist2, hKnum r, ht]
    exact twist1

  obtain ⟨K_bal, hK, ⟨s⟩⟩ := unrestricted_balanced_section F D.recipe.A
  obtain ⟨L, hL, hOrder, hType⟩ :=
    frequency_denominator_full_local_tuples F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
      D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix η0 hη0S D.recipe.A rfl
  obtain ⟨Cd, hCd, hcond⟩ :=
    Detector.frequency_denominator_conductor_bound F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
      D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix η0 hη0S
  have hCcond : 0 < 2 * Cd := by positivity
  have hDyadic : ∀ sigma ∈ L, Detector.HasExteriorDyadicConductorSieve F D.recipe.A sigma (2 * Cd) :=
    fun sigma hsigma =>
      Detector.hasExteriorDyadicConductorSieve_of_balancedSection F D.recipe.A ⊤ K_bal hK s sigma
        (hOrder sigma hsigma) (2 * Cd) hCcond
  obtain ⟨C, hC, hbound⟩ :=
    Detector.detector_logarithmic_sieve_gluing_epsilon F D.recipe.A (2 * Cd) hCcond L hL hDyadic ε hε
  refine ⟨C, hC, ?_⟩
  intro U N hU hN J hJ B hB b
  have hcondJ : ∀ r ∈ J,
      (Ideal.absNorm (D.omega r).conductor : ℝ) ≤ (2 * Cd) * U := by
    intro r hr
    have hq : D.q r < 2 * U := (hJ r hr).2.2
    have hsn : (Detector.frequencySNorm F
        (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) Vr (e (f r)) : ℝ) =
        D.q r := hSnorm (f r)
    rw [hω r]
    calc (Ideal.absNorm (T.denominator (e (f r))).conductor : ℝ)
        ≤ Cd * (Detector.frequencySNorm F
          (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) Vr (e (f r)) : ℝ) :=
          hcond Vr K T (e (f r))
      _ = Cd * D.q r := by rw [hsn]
      _ ≤ Cd * (2 * U) := mul_le_mul_of_nonneg_left hq.le hCd.le
      _ = (2 * Cd) * U := by ring
  apply primitive_sieve_finset_transfer_of_property F C (2 * Cd) N U ε
    (fun ω => ∃ sigma ∈ L, Detector.HasFixedFullSLocalTuple F D.recipe.A ω sigma)
    (fun n ω hω' hcondω htype c hc => hbound N U hN hU n ω hω' htype hcondω c hc)
    J D.omega ?_ hcondJ ?_ B hB b
  · intro u _ v _ huv hsame
    apply huv
    rw [hω u, hω v] at hsame
    exact hinj _ _ (Detector.twisted_frequency_character_injective F D.recipe.A.zeta12
      D.recipe.A.primitive_zeta12 D.recipe.σ _ D.recipe.A.Sf.finite_toSet hSix
      Vr K η0 T _ _ hsame)
  · intro r _
    show ∃ sigma ∈ L, Detector.HasFixedFullSLocalTuple F D.recipe.A (D.omega r) sigma
    rw [hω r]
    exact hType Vr K T (e (f r))

theorem actual_conductor_sieve_finsum
    (hfin : ∀ U : ℝ, (dyadNonprincipal D U).Finite) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ b : Ideal (𝓞 F) → ℂ,
          (∀ I, b I ≠ 0 → I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            (∑ u ∈ (hfin U).toFinset,
              ‖∑ᶠ I : Ideal (𝓞 F), b I * (D.omega u).character I‖ ^ 2) ≤
              C * (N + U ^ 2) * (N * U) ^ ε * ∑ᶠ I : Ideal (𝓞 F), ‖b I‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hsieve⟩ := actual_conductor_sieve D ε hε
  refine ⟨C, hC, ?_⟩
  intro U N hU hN b hb
  have hF : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊N⌋₊}.Finite :=
    Ideal.finite_setOfPred_absNorm_le _
  let B : Finset (Ideal (𝓞 F)) := hF.toFinset.filter (fun I => I ≠ ⊥)
  have hBmem : ∀ I, I ∈ B ↔ I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊N⌋₊ := by
    intro I
    simp only [B, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hB : ∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N := by
    intro I hI
    obtain ⟨h1, h2⟩ := (hBmem I).1 hI
    refine ⟨h1, ?_⟩
    have : (Ideal.absNorm I : ℝ) ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast h2
    exact this.trans (Nat.floor_le (by linarith))
  have hsupp : ∀ I, b I ≠ 0 → I ∈ B := by
    intro I hI
    obtain ⟨h1, h2⟩ := hb I hI
    refine (hBmem I).2 ⟨h1, ?_⟩
    exact Nat.le_floor h2
  have hsumb : ∀ (f : Ideal (𝓞 F) → ℂ), (∀ I, f I ≠ 0 → b I ≠ 0) →
      ∑ᶠ I : Ideal (𝓞 F), f I = ∑ I ∈ B, f I := by
    intro f hf
    apply finsum_eq_sum_of_support_subset
    intro I hI
    exact hsupp I (hf I (Function.mem_support.mp hI))
  have hsumb2 : ∑ᶠ I : Ideal (𝓞 F), ‖b I‖ ^ 2 = ∑ I ∈ B, ‖b I‖ ^ 2 := by
    apply finsum_eq_sum_of_support_subset
    intro I hI
    exact hsupp I (by
      intro h0
      apply Function.mem_support.mp hI
      simp [h0])
  have hmem : ∀ u ∈ (hfin U).toFinset, u ∈ dyadNonprincipal D U := by
    intro u hu
    exact (Set.Finite.mem_toFinset _).1 hu
  have key := hsieve U N hU hN (hfin U).toFinset hmem B hB b
  have hterm : ∀ u ∈ (hfin U).toFinset,
      ‖∑ᶠ I : Ideal (𝓞 F), b I * (D.omega u).character I‖ ^ 2 ≤
        ‖∑ I ∈ B, b I * (D.omega u).character I‖ ^ 2 := by
    intro u _
    exact le_of_eq (congrArg (fun x : ℂ => ‖x‖ ^ 2)
      (hsumb (fun I => b I * (D.omega u).character I) (fun I h => left_ne_zero_of_mul h)))
  rw [hsumb2]
  exact (Finset.sum_le_sum hterm).trans key

end

end DedekindZetaZeroFree.Quantitative.ActualConductorSieve
