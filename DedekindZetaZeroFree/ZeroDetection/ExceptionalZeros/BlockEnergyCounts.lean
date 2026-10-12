module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.HeightPrefixMaximalBounds
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.SmoothedZeroPrefixes
public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyDyadCounts
public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ExteriorDyadicConductorBounds
public import DedekindZetaZeroFree.Adeles.Quotients.SixthPowerCompactCover

@[expose] public section

section

namespace DedekindZetaZeroFree.Detector.ExceptionalBlockEnergy

noncomputable section
open scoped NumberField Classical

def blockCoefficients (F : Type) [Field F] [NumberField F]
    (X N : ℝ) (n : Ideal (𝓞 F)) : ℂ :=
  if n ≠ ⊥ ∧ N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N then
    (truncatedIdealMoebius F X n : ℂ) *
      (Ideal.absNorm n : ℂ) ^ (-(249 / 250 : ℂ))
  else 0

def blockEnergy (F : Type) [Field F] [NumberField F]
    (ω : Ideal (𝓞 F) → ℂ) (ρ X : ℝ) (j : ℕ) : ℝ :=
  detectorHeightPrefixMaximum F (blockCoefficients F X ((2 : ℝ)^j)) ω
    ((2 : ℝ)^j) (4 * X^ρ)

end
end DedekindZetaZeroFree.Detector.ExceptionalBlockEnergy

end

section

namespace DedekindZetaZeroFree.Detector.ExceptionalBlockEnergy

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem uniform_zero_block_detection
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η) :
    ∃ (ρ X₀ c : ℝ), 0 < ρ ∧ ρ < 1 / 10 ∧ 2 ≤ X₀ ∧ 0 < c ∧
      ∀ (U : FrequencyRepresentatives F S)
        (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η)
        (X : ℝ), X₀ ≤ X →
        ∀ u : U.carrier, u ∈ frequencyDyad F S U X →
          ¬ (T.denominator u).character.IsPrincipal →
          (∃ D : NonprincipalRayHeckeData F (T.denominator u).conductor
              (T.denominator u).character,
            ∃ s : ℂ, (249 / 250 : ℝ) ≤ s.re ∧
              |s.im| ≤ 4 * X ^ ρ ∧ D.L s = 0) →
          ∃ j ∈ detector_sz_dyadicIndices X,
            (c / (1 + Real.log X))^2 ≤
              blockEnergy F (T.denominator u).character ρ X j := by
  classical
  have htc : NumberField.IsTotallyComplex F :=
    NumberField.nrRealPlaces_eq_zero_iff.mp
      (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
        (by norm_num) hζ12)
  obtain ⟨C, hC, hcond⟩ :=
    frequency_denominator_conductor_bound F ζ12 hζ12 ι S hS hSix η hηS
  let C₀ : ℝ := 2 * C
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let A : ℝ := (detector_convexity_bridge F htc C₀ hC₀).choose
  have hA : 0 ≤ A :=
    (detector_convexity_bridge F htc C₀ hC₀).choose_spec.1
  let ρ : ℝ := min (1 / 10) (1 / (A + 1)) / 2
  have hm : 0 < min (1 / 10 : ℝ) (1 / (A + 1)) := by
    apply lt_min <;> positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρhi : ρ < min (1 / 10) (1 / (A + 1)) := by dsimp [ρ]; linarith
  obtain ⟨c, hc, X₀, hX₀, hdetect⟩ :=
    detector_smoothed_zero F htc C₀ hC₀ ρ hρ hρhi
  refine ⟨ρ, X₀, c, hρ, hρhi.trans_le (min_le_left _ _), hX₀, hc, ?_⟩
  intro U K T X hX u hu hnon hzero
  have hX2 : 2 ≤ X := hX₀.trans hX
  have hnorm : (Ideal.absNorm (T.denominator u).conductor : ℝ) ≤ C₀ * X := by
    have hu' : (frequencySNorm F S U u : ℝ) < 2 * X := hu.2
    calc
      _ ≤ C * (frequencySNorm F S U u : ℝ) := hcond U K T u
      _ ≤ C * (2 * X) := mul_le_mul_of_nonneg_left hu'.le hC.le
      _ = C₀ * X := by dsimp [C₀]; ring
  obtain ⟨D, s, hsre, hsim, hs⟩ := hzero
  have hsform : (s.re : ℂ) + Complex.I * (s.im : ℂ) = s := by
    simpa only [mul_comm] using Complex.re_add_im s
  obtain ⟨j, hj, hlo, hhi, y, hy, hprefix⟩ :=
    hdetect X hX (T.denominator u).conductor (T.denominator u).conductor_ne_zero
      (T.denominator u).character (T.denominator u).primitive hnon hnorm
      D s.re s.im hsre hsim (by rwa [hsform])
  have hN : 2 ≤ (2 : ℝ)^j := by nlinarith [sq_nonneg (X - 2)]
  have hy' : y ∈ Set.Icc ((2 : ℝ)^j) (2 * (2 : ℝ)^j) := by
    simpa only [pow_succ, mul_comm] using hy
  have hT : 1 ≤ 4 * X ^ ρ := by
    have := Real.one_le_rpow (show 1 ≤ X by linarith) hρ.le
    linarith
  have ht : s.im ∈ Set.Icc (-(4 * X ^ ρ)) (4 * X ^ ρ) := abs_le.mp hsim
  have heq : detectorDyadicPrefix F (blockCoefficients F X ((2 : ℝ)^j))
      (T.denominator u).character ((2 : ℝ)^j) y s.im =
      ∑ n ∈ (ideals_bounded_norm_finite F y).toFinset.filter
          (fun n => (2 : ℝ)^j < (Ideal.absNorm n : ℝ)),
        (truncatedIdealMoebius F X n : ℂ) * (T.denominator u).character n *
          (Ideal.absNorm n : ℂ) ^
            (-(249 / 250 : ℂ) - Complex.I * (s.im : ℂ)) := by
    unfold detectorDyadicPrefix
    rw [finsum_eq_sum_of_support_subset _ (s := (ideals_bounded_norm_finite F y).toFinset)]
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ y := by simpa using hn
      by_cases hnj : (2 : ℝ)^j < (Ideal.absNorm n : ℝ)
      · have hn2 : (Ideal.absNorm n : ℝ) ≤ 2 * (2 : ℝ)^j := hn'.2.trans hy'.2
        have hn0 : (Ideal.absNorm n : ℂ) ≠ 0 := by
          exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hn'.1)
        simp only [blockCoefficients, hn'.1, hnj, hn'.2, hn2, ne_eq,
          not_false_eq_true, and_self, and_true, ↓reduceIte]
        rw [sub_eq_add_neg, Complex.cpow_add _ _ hn0]
        ring
      · simp [hnj]
    · intro n hn
      have hn' : n ≠ ⊥ ∧ (2 : ℝ)^j < (Ideal.absNorm n : ℝ) ∧
          (Ideal.absNorm n : ℝ) ≤ y := by
        by_contra hh
        simp [hh, Function.mem_support] at hn
      simpa using And.intro hn'.1 hn'.2.2
  obtain ⟨z, hz, hez, hmax⟩ := detectorPrefixMaximum_attained F
    (blockCoefficients F X ((2 : ℝ)^j)) (T.denominator u).character
    ((2 : ℝ)^j) s.im hN
  obtain ⟨t, ht', het, hheight⟩ := detectorHeightPrefixMaximum_attained F
    (blockCoefficients F X ((2 : ℝ)^j)) (T.denominator u).character
    ((2 : ℝ)^j) (4 * X ^ ρ) hN hT
  refine ⟨j, hj, ?_⟩
  have hlog : 0 < 1 + Real.log X := by
    have := Real.log_nonneg (show 1 ≤ X by linarith)
    linarith
  calc
    (c / (1 + Real.log X))^2 ≤
        ‖detectorDyadicPrefix F (blockCoefficients F X ((2 : ℝ)^j))
          (T.denominator u).character ((2 : ℝ)^j) y s.im‖^2 := by
      apply pow_le_pow_left₀ (by positivity)
      rwa [heq]
    _ ≤ detectorPrefixMaximum F (blockCoefficients F X ((2 : ℝ)^j))
        (T.denominator u).character ((2 : ℝ)^j) s.im := hmax y hy'
    _ ≤ blockEnergy F (T.denominator u).character ρ X j := hheight s.im ht

end
end DedekindZetaZeroFree.Detector.ExceptionalBlockEnergy

end

section

namespace DedekindZetaZeroFree.Detector.ExceptionalBlockEnergy

noncomputable section
open scoped NumberField Classical BigOperators
open IsDedekindDomain

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

private theorem raw_arithmetic_data_exists
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S) :
    ∃ A : SArithmeticData F, (A.Sf : Set (HeightOneSpectrum (𝓞 F))) = S := by
  classical
  refine ⟨{
    zeta12 := ζ12
    primitive_zeta12 := hζ12
    Sf := hS.toFinset
    S₀ := ∅
    bad_subset := Finset.empty_subset _
    modulus := ⊤
    modulus_ne_zero := top_ne_bot
    above_six := ?_
    modulus_support := ?_ }, hS.coe_toFinset⟩
  · intro v hv
    rw [hS.mem_toFinset]
    apply hSix
    letI : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨p, n, hn, hpI, hp, hq⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
    intro hcop
    have hpc : p.Coprime 6 := (Nat.coprime_pow_left_iff hn p 6).mp (hq ▸ hcop)
    obtain ⟨a, b, hab⟩ := (hpc.cast : IsCoprime (p : 𝓞 F) 6)
    have hone : (1 : 𝓞 F) ∈ v.asIdeal := by
      rw [← hab]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpI) (v.asIdeal.mul_mem_left b hv)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  · intro v hv
    exact False.elim (v.isPrime.ne_top (top_le_iff.mp hv))

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

private theorem frequency_conductor_sieve
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U : FrequencyRepresentatives F S)
        (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η)
        (X N : ℝ), 2 ≤ X → 2 ≤ N →
        ∀ (J : Finset U.carrier),
          (∀ u ∈ J, u ∈ frequencyDyad F S U X) →
          ∀ (B : Finset (Ideal (𝓞 F))),
            (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            ∀ b : Ideal (𝓞 F) → ℂ,
              (∑ u ∈ J, ‖∑ I ∈ B, b I * (T.denominator u).character I‖ ^ 2) ≤
                C * (N + X ^ (2 : ℕ)) * (N * X) ^ ε *
                  ∑ I ∈ B, ‖b I‖ ^ 2 := by
  classical
  obtain ⟨A, hAS⟩ := raw_arithmetic_data_exists F ζ12 hζ12 S hS hSix
  have hR : A.R = S.integer F := by rw [SArithmeticData.R, hAS]
  letI : IsPrincipalIdealRing A.R := hR ▸ inferInstance
  obtain ⟨K_bal, hK, ⟨s⟩⟩ := unrestricted_balanced_section F A
  obtain ⟨L, hL, hOrder, hType⟩ :=
    frequency_denominator_full_local_tuples F ζ12 hζ12 ι S hS hSix η hηS A hAS
  obtain ⟨Cd, hCd, hcond⟩ :=
    frequency_denominator_conductor_bound F ζ12 hζ12 ι S hS hSix η hηS
  have hCcond : 0 < 2 * Cd := by positivity
  have hDyadic : ∀ sigma ∈ L, HasExteriorDyadicConductorSieve F A sigma (2 * Cd) :=
    fun sigma hsigma =>
      hasExteriorDyadicConductorSieve_of_balancedSection F A ⊤ K_bal hK s sigma
        (hOrder sigma hsigma) (2 * Cd) hCcond
  intro ε hε
  obtain ⟨C, hC, hbound⟩ :=
    detector_logarithmic_sieve_gluing_epsilon F A (2 * Cd) hCcond L hL hDyadic ε hε
  refine ⟨C, hC, ?_⟩
  intro U K T X N hX hN J hJ B hB b
  have hcondJ : ∀ u ∈ J,
      (Ideal.absNorm (T.denominator u).conductor : ℝ) ≤ (2 * Cd) * X := by
    intro u hu
    have hq : (frequencySNorm F S U u : ℝ) < 2 * X := (hJ u hu).2
    calc
      (Ideal.absNorm (T.denominator u).conductor : ℝ) ≤
          Cd * (frequencySNorm F S U u : ℝ) := hcond U K T u
      _ ≤ Cd * (2 * X) := mul_le_mul_of_nonneg_left hq.le hCd.le
      _ = (2 * Cd) * X := by ring
  apply primitive_sieve_finset_transfer_of_property F C (2 * Cd) N X ε
    (fun ω => ∃ sigma ∈ L, HasFixedFullSLocalTuple F A ω sigma)
    (fun n ω hω hcondω htype c hc => hbound N X hN hX n ω hω htype hcondω c hc)
    J T.denominator ?_ hcondJ (fun u _ => hType U K T u) B hB b
  intro u hu v hv huv hsame
  exact huv (twisted_frequency_character_injective F ζ12 hζ12 ι S hS hSix
    U K η T u v hsame)

private theorem block_support (F : Type) [Field F] [NumberField F] (X N : ℝ) :
    detectorDyadicSupport F (blockCoefficients F X N) N := by
  intro n hn
  simp [blockCoefficients, hn]

private theorem block_mass (F : Type) [Field F] [NumberField F]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X N : ℝ, 2 ≤ X → 2 ≤ N →
      detectorDyadicCoefficientMass F (blockCoefficients F X N) N ≤
        C * N ^ (1 - 2 * (249 / 250 : ℝ) + ε) := by
  obtain ⟨C, hC, hdiv⟩ := ideal_divisor_bound F (ε / 2) (by positivity)
  obtain ⟨K, hK, hcount⟩ := ideal_norm_summation_bounds F
  refine ⟨C^2 * 2^ε * (2 * K), by positivity, ?_⟩
  intro X N hX hN
  have hN0 : 0 < N := by linarith
  let B := (ideals_bounded_norm_finite F (2 * N)).toFinset
  have hB (n : Ideal (𝓞 F)) : n ∈ B ↔ n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N := by
    simp [B]
  have hpoint (n : Ideal (𝓞 F)) (hn : n ∈ B) :
      (if n ≠ ⊥ ∧ N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N then
        ‖blockCoefficients F X N n‖^2 else 0) ≤
        C^2 * (2 * N)^ε * N^(-2 * (249 / 250 : ℝ)) := by
    split_ifs with ha
    · have hn0 : 0 < (Ideal.absNorm n : ℝ) := lt_trans hN0 ha.2.1
      have hm : ‖(truncatedIdealMoebius F X n : ℂ)‖ ≤
          C * (Ideal.absNorm n : ℝ)^(ε/2) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (truncatedIdealMoebius_abs_le F X hX n ha.1).trans (hdiv n ha.1)
      have hp : ‖(Ideal.absNorm n : ℂ)^(-(249 / 250 : ℂ))‖ =
          (Ideal.absNorm n : ℝ)^(-(249 / 250 : ℝ)) := by
        change ‖((Ideal.absNorm n : ℝ) : ℂ)^(-(249 / 250 : ℂ))‖ = _
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
        norm_num
      rw [blockCoefficients, if_pos ha, norm_mul, hp, mul_pow]
      have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
      rw [mul_pow] at hm2
      rw [← Real.rpow_natCast ((Ideal.absNorm n : ℝ)^(ε/2)) 2, ← Real.rpow_mul hn0.le] at hm2
      have he : ε / 2 * (2 : ℝ) = ε := by ring
      norm_num only [Nat.cast_ofNat] at hm2
      rw [he] at hm2
      have hd : ((Ideal.absNorm n : ℝ)^(-(249 / 250 : ℝ)))^2 ≤
          N^(-2 * (249 / 250 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        convert Real.rpow_le_rpow_of_nonpos hN0 ha.2.1.le (by norm_num : -2 * (249 / 250 : ℝ) ≤ 0) using 1 <;> norm_num <;> ring
      have hu := Real.rpow_le_rpow (by positivity : 0 ≤ (Ideal.absNorm n : ℝ)) ha.2.2 hε.le
      exact (mul_le_mul hm2 hd (by positivity) (by positivity)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (sq_nonneg C)) (by positivity))
    · positivity
  unfold detectorDyadicCoefficientMass
  rw [finsum_eq_sum_of_support_subset _ (s := B)]
  · calc
      _ ≤ ∑ n ∈ B, C^2 * (2 * N)^ε * N^(-2 * (249 / 250 : ℝ)) := Finset.sum_le_sum hpoint
      _ = (B.card : ℝ) * (C^2 * (2 * N)^ε * N^(-2 * (249 / 250 : ℝ))) := by simp
      _ ≤ (K * (2 * N)) * (C^2 * (2 * N)^ε * N^(-2 * (249 / 250 : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc := (hcount (2 * N) (by linarith)).1
        change (B.card : ℝ) ≤ _
        convert hc using 1
        congr 1
        exact (Set.ncard_eq_toFinset_card _ (ideals_bounded_norm_finite F (2 * N))).symm
      _ = (C^2 * 2^ε * (2 * K)) * N^(1 - 2 * (249 / 250 : ℝ) + ε) := by
        rw [Real.mul_rpow (by norm_num) hN0.le]
        rw [show 1 - 2 * (249 / 250 : ℝ) + ε = 1 + ε + (-2 * (249 / 250 : ℝ)) by ring,
          Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
        ring
  · intro n hn
    by_contra hnot
    have hb := mt (hB n).2 hnot
    have ha : ¬ (n ≠ ⊥ ∧ N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N) :=
      fun ha => hb ⟨ha.1, ha.2.2⟩
    simp [Function.mem_support, ha] at hn

theorem uniform_row_block_energy_bound
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ρ : ℝ), 0 ≤ ρ →
      ∀ (U : FrequencyRepresentatives F S)
        (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η)
        (X : ℝ), 2 ≤ X →
        ∀ (J : Finset U.carrier), (↑J : Set U.carrier) ⊆ frequencyDyad F S U X →
          ∀ j ∈ detector_sz_dyadicIndices X,
            (∑ u ∈ J, blockEnergy F (T.denominator u).character ρ X j) ≤
              D * X^(11 * (2 - 2 * (249 / 250 : ℝ)) + ρ + 23 * ε) := by
  obtain ⟨C₀, hC₀, hsieve⟩ := frequency_conductor_sieve F ζ12 hζ12 ι S hS hSix η hηS
    (ε / 2) (by positivity)
  obtain ⟨C, hC, hmax⟩ := detector_maximal_sieve F ε C₀ hε hC₀
  obtain ⟨Kc, hKc, hmass⟩ := block_mass F ε hε
  refine ⟨15 * C * Kc, by positivity, ?_⟩
  intro ρ hρ U K T X hX J hJ j hj
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  let N : ℝ := (2 : ℝ)^j
  have hband : X^2 / 2 < N ∧ N ≤ X^11 :=
    (detector_sz_dyadic_cover X hX).2.2.2.2.2.1 j hj
  have hN : 2 ≤ N := by
    have hx2 : 4 ≤ X^2 := by nlinarith
    linarith [hband.1]
  have hN0 : 0 < N := by linarith
  have hheight : 1 ≤ 4 * X^ρ := by
    have := Real.one_le_rpow hX1 hρ
    linarith
  have hop : ∀ (M : ℝ) (c : Ideal (𝓞 F) → ℂ), 2 ≤ M →
      (∀ n, ¬ (n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ M) → c n = 0) →
      (∑ u : J, ‖∑ᶠ n : Ideal (𝓞 F),
        if n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ M then
          c n * (T.denominator u.val).character n else 0‖^2) ≤
        C₀ * (M + X^2) * (M * X)^(ε/2) *
          (∑ᶠ n : Ideal (𝓞 F),
            if n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ M then ‖c n‖^2 else 0) := by
    intro M c hM hc
    let B := (ideals_bounded_norm_finite F M).toFinset
    have hB (n : Ideal (𝓞 F)) : n ∈ B ↔ n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ M := by
      simp [B]
    have hpoly (u : U.carrier) :
        (∑ᶠ n : Ideal (𝓞 F), if n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ M then
          c n * (T.denominator u).character n else 0) =
            ∑ n ∈ B, c n * (T.denominator u).character n := by
      rw [finsum_eq_sum_of_support_subset _ (s := B)]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos ((hB n).mp hn)]
      · intro n hn
        by_contra hb
        simp [Function.mem_support, mt (hB n).mpr hb] at hn
    have hm : (∑ᶠ n : Ideal (𝓞 F), if n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ M then ‖c n‖^2 else 0) =
        ∑ n ∈ B, ‖c n‖^2 := by
      rw [finsum_eq_sum_of_support_subset _ (s := B)]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos ((hB n).mp hn)]
      · intro n hn
        by_contra hb
        simp [Function.mem_support, mt (hB n).mpr hb] at hn
    simp_rw [hpoly, hm]
    rw [Finset.sum_coe_sort J (fun u => ‖∑ n ∈ B, c n * (T.denominator u).character n‖^2)]
    exact hsieve U K T X M hX hM J (fun u hu => hJ hu) B (fun n hn => (hB n).mp hn) c
  have hb := hmax J (fun u n => (T.denominator u.val).character n) X N (4 * X^ρ)
    (blockCoefficients F X N) hX hN hheight hop (block_support F X N)
  change (∑ u : J, blockEnergy F (T.denominator u.val).character ρ X j) ≤ _ at hb
  rw [Finset.sum_coe_sort J (fun u => blockEnergy F (T.denominator u).character ρ X j)] at hb
  change (∑ u ∈ J, blockEnergy F (T.denominator u).character ρ X j) ≤ _ at hb
  have hm := hmass X N hX hN
  have hbase : N + X^2 ≤ 3 * N := by linarith [hband.1]
  have ht : 4 * X^ρ + 1 ≤ 5 * X^ρ := by linarith [Real.one_le_rpow hX1 hρ]
  have hNU : (N * X)^ε ≤ X^(12 * ε) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ N * X)
      (mul_le_mul_of_nonneg_right hband.2 hX0.le) hε.le
    have he : X^11 * X = X^(12 : ℝ) := by
      rw [show (12 : ℝ) = (11 : ℝ) + 1 by norm_num, Real.rpow_add hX0,
        Real.rpow_one]
      norm_num
    rw [he, ← Real.rpow_mul hX0.le] at h
    exact h
  have hpow : N^(2 - 2 * (249 / 250 : ℝ) + ε) ≤
      X^(11 * (2 - 2 * (249 / 250 : ℝ) + ε)) := by
    have h := Real.rpow_le_rpow hN0.le hband.2 (by linarith : 0 ≤ 2 - 2 * (249 / 250 : ℝ) + ε)
    rw [← Real.rpow_natCast X 11, ← Real.rpow_mul hX0.le] at h
    exact h
  have hmass0 : 0 ≤ detectorDyadicCoefficientMass F (blockCoefficients F X N) N := by
    unfold detectorDyadicCoefficientMass
    apply finsum_nonneg
    intro n
    split_ifs <;> positivity
  calc
    _ ≤ C * (4 * X^ρ + 1) * (N + X^2) * (N * X)^ε *
        detectorDyadicCoefficientMass F (blockCoefficients F X N) N := hb
    _ ≤ C * (5 * X^ρ) * (3 * N) * X^(12 * ε) *
        (Kc * N^(1 - 2 * (249 / 250 : ℝ) + ε)) := by
      gcongr
    _ = (15 * C * Kc) * X^ρ * X^(12 * ε) * N^(2 - 2 * (249 / 250 : ℝ) + ε) := by
      rw [show 2 - 2 * (249 / 250 : ℝ) + ε = 1 + (1 - 2 * (249 / 250 : ℝ) + ε) by ring,
        Real.rpow_add hN0 1 (1 - 2 * (249 / 250 : ℝ) + ε), Real.rpow_one]
      ring
    _ ≤ (15 * C * Kc) * X^ρ * X^(12 * ε) * X^(11 * (2 - 2 * (249 / 250 : ℝ) + ε)) := by
      gcongr
    _ = _ := by
      rw [mul_assoc (15 * C * Kc), ← Real.rpow_add hX0,
        mul_assoc (15 * C * Kc), ← Real.rpow_add hX0]
      congr 2
      ring

end
end DedekindZetaZeroFree.Detector.ExceptionalBlockEnergy

end

section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector

noncomputable section
open scoped Classical

namespace ExceptionalCount
open scoped BigOperators
noncomputable section

theorem finite_row_chebyshev {α β : Type*} (J : Finset α) (B : Finset β)
    (energy : α → β → ℝ) (a M : ℝ) (ha : 0 < a)
    (hnonneg : ∀ u ∈ J, ∀ j ∈ B, 0 ≤ energy u j)
    (hdetect : ∀ u ∈ J, ∃ j ∈ B, a ≤ energy u j)
    (henergy : ∀ j ∈ B, ∑ u ∈ J, energy u j ≤ M) :
    (J.card : ℝ) ≤ (B.card : ℝ) * M / a := by
  have hrow : ∀ u ∈ J, a ≤ ∑ j ∈ B, energy u j := by
    intro u hu
    obtain ⟨j, hj, hbig⟩ := hdetect u hu
    exact hbig.trans (Finset.single_le_sum (fun k hk => hnonneg u hu k hk) hj)
  have hsum : (J.card : ℝ) * a ≤ (B.card : ℝ) * M := by
    calc
      (J.card : ℝ) * a = ∑ u ∈ J, a := by simp
      _ ≤ ∑ u ∈ J, ∑ j ∈ B, energy u j := Finset.sum_le_sum hrow
      _ = ∑ j ∈ B, ∑ u ∈ J, energy u j := Finset.sum_comm
      _ ≤ ∑ j ∈ B, M := Finset.sum_le_sum henergy
      _ = (B.card : ℝ) * M := by simp
  exact (le_div_iff₀ ha).mpr hsum

theorem logarithmic_power_absorption (m : ℕ) (hm : 0 < m)
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      (1 + Real.log X)^m ≤ C * X^e := by
  let d := e / (m : ℝ)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < d := div_pos he hmR
  refine ⟨(1 + 1 / d)^m, pow_pos (by positivity) _, ?_⟩
  intro X hX
  have hX0 : 0 ≤ X := by linarith
  have hpow : 1 ≤ X^d := Real.one_le_rpow (by linarith) hd.le
  have hlog := Real.log_le_rpow_div hX0 hd
  have hbase : 1 + Real.log X ≤ (1 + 1 / d) * X^d := by
    calc
      1 + Real.log X ≤ X^d + X^d / d := add_le_add hpow hlog
      _ = (1 + 1 / d) * X^d := by ring
  have h := pow_le_pow_left₀
    (by linarith [Real.log_nonneg (show 1 ≤ X by linarith)]) hbase m
  rw [mul_pow] at h
  have hp : (X^d)^m = X^e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    congr 1
    dsimp [d]
    field_simp
  rwa [hp] at h

theorem count_of_logarithmic_block_energy {α β : Type*}
    (J : Finset α) (B : Finset β) (energy : α → β → ℝ)
    (X c D q : ℝ) (hX : 2 ≤ X) (hc : 0 < c) (hD : 0 ≤ D)
    (hblocks : (B.card : ℝ) ≤ 16 * (1 + Real.log X))
    (hnonneg : ∀ u ∈ J, ∀ j ∈ B, 0 ≤ energy u j)
    (hdetect : ∀ u ∈ J, ∃ j ∈ B, (c / (1 + Real.log X))^2 ≤ energy u j)
    (henergy : ∀ j ∈ B, ∑ u ∈ J, energy u j ≤ D * X^q) :
    (J.card : ℝ) ≤ (16 * D / c^2) * (1 + Real.log X)^3 * X^q := by
  have hl : 0 < 1 + Real.log X := by
    linarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have ha : 0 < (c / (1 + Real.log X))^2 := sq_pos_of_pos (div_pos hc hl)
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  have h := finite_row_chebyshev J B energy _ _ ha hnonneg hdetect henergy
  have hb : (B.card : ℝ) * (D * X^q) ≤
      (16 * (1 + Real.log X)) * (D * X^q) := by
    exact mul_le_mul_of_nonneg_right hblocks (mul_nonneg hD (Real.rpow_nonneg (by linarith) _))
  calc
    (J.card : ℝ) ≤ (B.card : ℝ) * (D * X^q) / (c / (1 + Real.log X))^2 := h
    _ ≤ (16 * (1 + Real.log X)) * (D * X^q) / (c / (1 + Real.log X))^2 :=
      div_le_div_of_nonneg_right hb ha.le
    _ = (16 * D / c^2) * (1 + Real.log X)^3 * X^q := by
      field_simp
      <;> ring

theorem square_root_count_of_block_energy {α β : Type*}
    (c D q : ℝ) (hc : 0 < c) (hD : 0 < D) (hq : q < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X →
      ∀ (J : Finset α) (B : Finset β) (energy : α → β → ℝ),
        (B.card : ℝ) ≤ 16 * (1 + Real.log X) →
        (∀ u ∈ J, ∀ j ∈ B, 0 ≤ energy u j) →
        (∀ u ∈ J, ∃ j ∈ B, (c / (1 + Real.log X))^2 ≤ energy u j) →
        (∀ j ∈ B, ∑ u ∈ J, energy u j ≤ D * X^q) →
        (J.card : ℝ) ≤ C * X^(1 / 2 : ℝ) := by
  obtain ⟨K, hK, hlog⟩ := logarithmic_power_absorption 3 (by decide)
    (1 / 2 - q) (by linarith)
  refine ⟨(16 * D / c^2) * K, by positivity, ?_⟩
  intro X hX J B energy hblocks hnonneg hdetect henergy
  have hX0 : 0 ≤ X := by linarith
  calc
    (J.card : ℝ) ≤ (16 * D / c^2) * (1 + Real.log X)^3 * X^q :=
      count_of_logarithmic_block_energy J B energy X c D q hX hc hD.le
        hblocks hnonneg hdetect henergy
    _ ≤ (16 * D / c^2) * (K * X^(1 / 2 - q)) * X^q := by
      gcongr
      exact hlog X hX
    _ = ((16 * D / c^2) * K) * X^(1 / 2 : ℝ) := by
      rw [mul_assoc (16 * D / c^2), mul_assoc K, ← Real.rpow_add (show 0 < X by linarith)]
      rw [show (1 / 2 : ℝ) - q + q = 1 / 2 by ring]
      ring

theorem dyadic_density_exponent_lt_half (ρ : ℝ) (hρ : ρ < 1 / 10) :
    11 * (2 - 2 * (249 / 250 : ℝ)) + ρ + 23 * (1 / 100) < 1 / 2 := by
  linarith

end
end ExceptionalCount

 def principalRows
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (K : KummerFrequencyFamily F ζ12 ι S U) (η : PrimitiveFrequencyCharacter F)
    (T : TwistedFrequencyFamily F ζ12 ι S U K η) (X : ℝ) : Set U.carrier :=
  {u | u ∈ frequencyDyad F S U X ∧ (T.denominator u).character.IsPrincipal}

 def zeroRows
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (K : KummerFrequencyFamily F ζ12 ι S U) (η : PrimitiveFrequencyCharacter F)
    (T : TwistedFrequencyFamily F ζ12 ι S U K η) (ρ X : ℝ) : Set U.carrier :=
  {u | u ∈ frequencyDyad F S U X ∧
    ¬ (T.denominator u).character.IsPrincipal ∧
    ∃ D : NonprincipalRayHeckeData F (T.denominator u).conductor
        (T.denominator u).character,
      ∃ s : ℂ, (249 / 250 : ℝ) ≤ s.re ∧
        |s.im| ≤ 4 * X ^ ρ ∧ D.L s = 0}

private theorem principalRows_count
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (η : PrimitiveFrequencyCharacter F) (T : TwistedFrequencyFamily F ζ12 ι S U K η)
    (X : ℝ) :
    (principalRows F ζ12 ι S U K η T X).Finite ∧
      (principalRows F ζ12 ι S U K η T X).ncard ≤ 1 := by
  have hs : (principalRows F ζ12 ι S U K η T X).Subsingleton := by
    intro u hu v hv
    exact twisted_frequency_at_most_one_principal F ζ12 hζ12 ι S hS hSix
      U K η T u v hu.2 hv.2
  have hf := hs.finite
  letI := hf.fintype
  exact ⟨hf, Set.ncard_le_one_iff_subsingleton.mpr hs⟩

private theorem exceptionalSet_of_zeroRows_bound
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F)
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (T : TwistedFrequencyFamily F ζ12 ι S U K η) (ρ X C : ℝ)
    (hX : 2 ≤ X) (hf : (frequencyDyad F S U X).Finite)
    (hbound : ((zeroRows F ζ12 ι S U K η T ρ X).ncard : ℝ) ≤
      C * X ^ ((1 / 2 : ℝ))) :
    ∃ E : Set U.carrier,
      E ⊆ frequencyDyad F S U X ∧ E.Finite ∧
      (E.ncard : ℝ) ≤ (C + 1) * X ^ ((1 / 2 : ℝ)) ∧
      (∀ u : U.carrier, u ∈ frequencyDyad F S U X →
        (T.denominator u).character.IsPrincipal → u ∈ E) ∧
      (∀ u : U.carrier, u ∈ frequencyDyad F S U X →
        ¬ (T.denominator u).character.IsPrincipal →
        (∃ D : NonprincipalRayHeckeData F (T.denominator u).conductor
            (T.denominator u).character,
          ∃ s : ℂ, (249 / 250 : ℝ) ≤ s.re ∧
            |s.im| ≤ 4 * X ^ ρ ∧ D.L s = 0) → u ∈ E) := by
  let P := principalRows F ζ12 ι S U K η T X
  let Z := zeroRows F ζ12 ι S U K η T ρ X
  obtain ⟨hPfin, hPcard⟩ := principalRows_count F ζ12 hζ12 ι S hS hSix U K η T X
  have hZsub : Z ⊆ frequencyDyad F S U X := fun _ hu => hu.1
  refine ⟨P ∪ Z, ?_, hPfin.union (hf.subset hZsub), ?_, ?_, ?_⟩
  · rintro u (hu | hu)
    · exact hu.1
    · exact hu.1
  · have hcard : ((P ∪ Z).ncard : ℝ) ≤ (P.ncard : ℝ) + (Z.ncard : ℝ) := by
      exact_mod_cast Set.ncard_union_le P Z
    have hPcard' : (P.ncard : ℝ) ≤ 1 := by exact_mod_cast hPcard
    have hpow : 1 ≤ X ^ ((1 / 2 : ℝ)) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    dsimp [Z] at hcard ⊢
    nlinarith
  · intro u hu hprincipal
    exact Or.inl ⟨hu, hprincipal⟩
  · intro u hu hnonprincipal hzero
    exact Or.inr ⟨hu, hnonprincipal, hzero⟩

theorem frequency_dyad_exceptional_count
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (η : PrimitiveFrequencyCharacter F) (hηS : conductorSupportedOn F S η) :
    ∃ (ρ X₀ C : ℝ), 0 < ρ ∧ ρ < 1 / 10 ∧ 2 ≤ X₀ ∧ 0 < C ∧
      ∀ (U : FrequencyRepresentatives F S)
        (K : KummerFrequencyFamily F ζ12 ι S U)
        (T : TwistedFrequencyFamily F ζ12 ι S U K η)
        (X : ℝ), X₀ ≤ X →
        ∃ E : Set U.carrier,
          E ⊆ frequencyDyad F S U X ∧ E.Finite ∧
          (E.ncard : ℝ) ≤ C * X ^ ((1 / 2 : ℝ)) ∧
          (∀ u : U.carrier, u ∈ frequencyDyad F S U X →
            (T.denominator u).character.IsPrincipal → u ∈ E) ∧
          (∀ u : U.carrier, u ∈ frequencyDyad F S U X →
            ¬ (T.denominator u).character.IsPrincipal →
            (∃ D : NonprincipalRayHeckeData F (T.denominator u).conductor
                (T.denominator u).character,
                ∃ s : ℂ, (249 / 250 : ℝ) ≤ s.re ∧
                  |s.im| ≤ 4 * X ^ ρ ∧ D.L s = 0) → u ∈ E) := by

  have hZeroDensity :
      ∃ (ρ X₀ C : ℝ), 0 < ρ ∧ ρ < 1 / 10 ∧ 2 ≤ X₀ ∧ 0 < C ∧
        ∀ (U : FrequencyRepresentatives F S)
          (K : KummerFrequencyFamily F ζ12 ι S U)
          (T : TwistedFrequencyFamily F ζ12 ι S U K η)
          (X : ℝ), X₀ ≤ X →
          ((zeroRows F ζ12 ι S U K η T ρ X).ncard : ℝ) ≤
            C * X ^ ((1 / 2 : ℝ)) := by
    obtain ⟨ρ, X₀, c, hρ, hρsmall, hX₀, hc, hdetect⟩ :=
      ExceptionalBlockEnergy.uniform_zero_block_detection F ζ12 hζ12 ι S hS hSix η hηS
    obtain ⟨D, hD, henergy⟩ :=
      ExceptionalBlockEnergy.uniform_row_block_energy_bound F ζ12 hζ12 ι S hS hSix η hηS
        (1 / 100) (by norm_num)
    let q : ℝ := 11 * (2 - 2 * (249 / 250 : ℝ)) + ρ + 23 * (1 / 100)
    obtain ⟨C, hC, hcount⟩ := ExceptionalCount.square_root_count_of_block_energy
      (α := Fˣ) (β := ℕ) c D q hc hD
      (ExceptionalCount.dyadic_density_exponent_lt_half ρ hρsmall)
    refine ⟨ρ, X₀, C, hρ, hρsmall, hX₀, hC, ?_⟩
    intro U K T X hX
    have hXtwo : 2 ≤ X := hX₀.trans hX
    obtain ⟨_, _, hfinite⟩ := frequency_dyad_row_count F ζ12 hζ12 S hS hSix
    have hZsub : zeroRows F ζ12 ι S U K η T ρ X ⊆ frequencyDyad F S U X :=
      fun _ hu => hu.1
    have hZfin := ((hfinite U X hXtwo).1).subset hZsub
    let J := hZfin.toFinset
    let J' : Finset Fˣ := J.map ⟨Subtype.val, Subtype.val_injective⟩
    let energy : Fˣ → ℕ → ℝ := fun u j =>
      if hu : u ∈ U.carrier then
        ExceptionalBlockEnergy.blockEnergy F (T.denominator ⟨u, hu⟩).character ρ X j
      else 0
    have heval (u : U.carrier) (j : ℕ) : energy u.val j =
        ExceptionalBlockEnergy.blockEnergy F (T.denominator u).character ρ X j := by
      simp [energy, u.property]
    have hblocks := (detector_sz_dyadic_cover X hXtwo).2.2.2.2.2.2
    have hnonneg : ∀ u ∈ J', ∀ j ∈ detector_sz_dyadicIndices X, 0 ≤ energy u j := by
      intro u hu j hj
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hu
      simp only [Function.Embedding.coeFn_mk] at hu ⊢
      rw [heval]
      have hNlo := ((detector_sz_dyadic_cover X hXtwo).2.2.2.2.2.1 j hj).1
      have hN : 2 ≤ (2 : ℝ)^j := by nlinarith [sq_nonneg (X - 2)]
      have hheight : 1 ≤ 4 * X^ρ := by
        have := Real.one_le_rpow (show 1 ≤ X by linarith) hρ.le
        linarith
      obtain ⟨t, ht, he, _⟩ := detectorHeightPrefixMaximum_attained F
        (ExceptionalBlockEnergy.blockCoefficients F X ((2 : ℝ)^j))
        (T.denominator v).character ((2 : ℝ)^j) (4 * X^ρ) hN hheight
      obtain ⟨y, hy, he', _⟩ := detectorPrefixMaximum_attained F
        (ExceptionalBlockEnergy.blockCoefficients F X ((2 : ℝ)^j))
        (T.denominator v).character ((2 : ℝ)^j) t hN
      dsimp [ExceptionalBlockEnergy.blockEnergy]
      rw [he, he']
      positivity
    have hdetected : ∀ u ∈ J', ∃ j ∈ detector_sz_dyadicIndices X,
        (c / (1 + Real.log X))^2 ≤ energy u j := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hu
      simp only [Function.Embedding.coeFn_mk] at hu ⊢
      have hvZ : v ∈ zeroRows F ζ12 ι S U K η T ρ X := by
        simpa [J] using hv
      simpa only [heval] using hdetect U K T X hX v hvZ.1 hvZ.2.1 hvZ.2.2
    have hbounded : ∀ j ∈ detector_sz_dyadicIndices X,
        ∑ u ∈ J', energy u j ≤ D * X^q := by
      intro j hj
      have hJsub : (↑J : Set U.carrier) ⊆ frequencyDyad F S U X := by
        intro u hu
        exact hZsub (by simpa [J] using hu)
      have he := henergy ρ hρ.le U K T X hXtwo J hJsub j hj
      simpa only [J', Finset.sum_map, Function.Embedding.coeFn_mk, heval] using he
    have h := hcount X hXtwo J' (detector_sz_dyadicIndices X) energy
      hblocks hnonneg hdetected hbounded
    simpa only [J', Finset.card_map, J, ← Set.ncard_eq_toFinset_card _ hZfin] using h
  obtain ⟨ρ, X₀, C, hρ, hρsmall, hX₀, hC, hcount⟩ := hZeroDensity
  obtain ⟨_, _, hfinite⟩ := frequency_dyad_row_count F ζ12 hζ12 S hS hSix
  refine ⟨ρ, X₀, C + 1, hρ, hρsmall, hX₀, by linarith, ?_⟩
  intro U K T X hX
  have hXtwo : 2 ≤ X := hX₀.trans hX
  exact exceptionalSet_of_zeroRows_bound F ζ12 hζ12 ι S hS hSix η U K T
    ρ X C hXtwo (hfinite U X hXtwo).1 (hcount U K T X hX)

end
end DedekindZetaZeroFree.Detector

end
