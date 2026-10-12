module

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.BlockEnergyCounts
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.ZeroFreeDiskReciprocalBounds
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.TwistedDeletedCoefficientInduction

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem freqOrbit_injective (R : PrincipalMellin.ActualRecipe S η) :
    Function.Injective (fun u : Frequency R =>
      ProbeOrbitNormSum.orbitMk R.A u.val) := by
  intro u v huv
  have h := Quotient.exact huv
  obtain ⟨γ, heq⟩ := MulAction.orbitRel_apply.mp h
  obtain ⟨δ, hδ⟩ := γ.property
  let I : R.A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  let r := R.probe.coefficients.generator I
  have hr := (R.probe.coefficients.generates I).1
  let m : ThetaReflectionData.Row R.A :=
    ⟨u.val.val * r ^ 6, mul_ne_zero u.val.property (pow_ne_zero _ hr)⟩
  obtain ⟨x, hx, hxuniq⟩ := R.probe.frequencies.factorization m
  have hg : R.probe.allowed.generator I = ThetaReflectionData.rowUnit R.A ⟨r, hr⟩ := by
    apply Units.ext
    exact R.probe.sameGenerator I
  have hu : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A m =
      ThetaReflectionData.rowUnit R.A u.val * R.probe.allowed.generator I ^ 6 *
        γ.val ^ 6 := by
    refine ⟨1, ?_⟩
    rw [hg]
    apply Units.ext
    simp [m, r, ThetaReflectionData.rowUnit]
  have hv : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A m =
      ThetaReflectionData.rowUnit R.A v.val * R.probe.allowed.generator I ^ 6 *
        γ.val ^ 6 := by
    refine ⟨δ, ?_⟩
    rw [hg]
    have huu := congrArg (fun x : ThetaReflectionData.Row R.A => (x.val : F)) heq
    have hδF := congrArg (fun x : R.A.U => (x.val : F)) hδ
    apply Units.ext
    simp only [m, ThetaReflectionData.rowUnit, Units.val_mk0, map_mul, map_pow]
    change (u.val.val : F) * (r : F) ^ 6 = (v.val.val : F) * (r : F) ^ 6 * (δ.val : F) ^ 6
    change ((R.A.unitEquiv γ.val : R.A.R) : F) * (v.val.val : F) = (u.val.val : F) at huu
    have hcoe : ((R.A.unitEquiv γ.val : R.A.R) : F) = (γ.val.val : F) := by
      simp [SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
    rw [hcoe, ← hδF] at huu
    change (δ.val : F) ^ 6 * (v.val.val : F) = (u.val.val : F) at huu
    rw [← huu]
    ring
  have he : (u, I) = (v, I) := (hxuniq _ hu).trans (hxuniq _ hv).symm
  exact congrArg Prod.fst he

private lemma freqOrbit_norm (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) :
    frequencyNorm R u =
      ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) := by
  unfold frequencyNorm FiniteTransform.exteriorNorm ProbeOrbitNormSum.orbitNorm
  rw [ProbeOrbitNormSum.orbitIdeal_mk]
  change (Nat.card (R.A.R ⧸ Ideal.span {u.val.val}) : ℝ) =
    R.A.exteriorNorm (ProbeOrbitNormSum.principalExterior R.A u.val)
  rw [(ProbeOrbitNormSum.principalExterior_generates R.A u.val).2, R.A.exteriorResidue_card]
  rfl

private lemma one_le_frequencyNorm (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) : 1 ≤ frequencyNorm R u := by
  rw [freqOrbit_norm R u]
  exact idealNorm_ge_one _
    (ProbeOrbitNormSum.orbitIdeal R.A (ProbeOrbitNormSum.orbitMk R.A u.val)).property.1

private lemma freq_count_linear (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency R | frequencyNorm R u ≤ X}.Finite ∧
      (Set.ncard {u : Frequency R | frequencyNorm R u ≤ X} : ℝ) ≤ K * X := by
  obtain ⟨C, hC0, hCcount⟩ := ProbeExteriorIdealCount.ideal_count_linear (F := F) R.A.cS
  refine ⟨(Nat.card R.A.UnitQuotient : ℝ) * C + 1, by positivity, ?_⟩
  intro X hX
  obtain ⟨hBfin, hBcard⟩ := hCcount X hX
  have hBfin' : {I : R.A.Exterior | R.A.exteriorNorm I ≤ X}.Finite := hBfin
  have hfiber : ∀ I : R.A.Exterior,
      {o : ProbeOrbitNormSum.Orbit R.A | ProbeOrbitNormSum.orbitIdeal R.A o = I}.Finite ∧
      Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
        ProbeOrbitNormSum.orbitIdeal R.A o = I} ≤ Nat.card R.A.UnitQuotient := by
    intro I
    refine ⟨ProbeOrbitNormSum.idealFiber_finite R.A I, ?_⟩
    rw [ProbeOrbitNormSum.idealFiber_card R.A R.classKilled I]
  obtain ⟨hprefin, hprecard⟩ := ProbeExteriorPrincipalIdealFibers.finite_preimage_card_bound
    (ProbeOrbitNormSum.orbitIdeal R.A) (Nat.card R.A.UnitQuotient) hfiber
    {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} hBfin'
  have ht : {o : ProbeOrbitNormSum.Orbit R.A |
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X}.Finite := hprefin
  have hprecard' : Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X} ≤
      Nat.card R.A.UnitQuotient * Set.ncard {I : R.A.Exterior |
        R.A.exteriorNorm I ≤ X} := hprecard
  have hpfin : ((fun u : Frequency R => ProbeOrbitNormSum.orbitMk R.A u.val) ⁻¹'
      {o : ProbeOrbitNormSum.Orbit R.A | ProbeOrbitNormSum.orbitNorm R.A o ≤ X}).Finite :=
    ht.preimage (fun a _ b _ hab => freqOrbit_injective R hab)
  have hfin : {u : Frequency R | frequencyNorm R u ≤ X}.Finite := by
    refine hpfin.subset ?_
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    show ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) ≤ X
    rw [← freqOrbit_norm R u]
    exact hu
  refine ⟨hfin, ?_⟩
  have hinj := Set.ncard_le_ncard_of_injOn
    (fun u : Frequency R => ProbeOrbitNormSum.orbitMk R.A u.val)
    (fun u hu => by
      show ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) ≤ X
      rw [← freqOrbit_norm R u]
      exact hu)
    (fun a _ b _ h => freqOrbit_injective R h) ht
  have hnat : Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X} =
      Set.ncard {o : ProbeOrbitNormSum.Orbit R.A |
        ProbeOrbitNormSum.orbitNorm R.A o ≤ X} := Nat.card_coe_set_eq _
  have hBcard' : (Set.ncard {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} : ℝ) ≤ C * X := by
    rw [← Nat.card_coe_set_eq]
    exact hBcard
  rw [hnat] at hprecard'
  calc
    (Set.ncard {u : Frequency R | frequencyNorm R u ≤ X} : ℝ)
        ≤ (Set.ncard {o : ProbeOrbitNormSum.Orbit R.A |
            ProbeOrbitNormSum.orbitNorm R.A o ≤ X} : ℝ) := by
          exact_mod_cast hinj
    _ ≤ (Nat.card R.A.UnitQuotient : ℝ) *
          (Set.ncard {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} : ℝ) := by
          exact_mod_cast hprecard'
    _ ≤ (Nat.card R.A.UnitQuotient : ℝ) * (C * X) :=
          mul_le_mul_of_nonneg_left hBcard' (Nat.cast_nonneg _)
    _ ≤ ((Nat.card R.A.UnitQuotient : ℝ) * C + 1) * X := by
          nlinarith [hC0, Nat.cast_nonneg (α := ℝ) (Nat.card R.A.UnitQuotient), hX]

theorem actual_complete_frequency_dyads
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (K : ℝ) (D : ℕ → Finset (Frequency R)),
      0 < K ∧
      (∀ j : ℕ, comparisonFrequencyDyad (frequencyNorm R) (principalFrequency R) K
        ((2 : ℝ) ^ j) (D j)) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R → ∃ j : ℕ, u ∈ D j) := by
  obtain ⟨K₀, hK₀, hcount⟩ := freq_count_linear R
  have hpow : ∀ j : ℕ, 1 ≤ (2 : ℝ) ^ (j + 1) := fun j => one_le_pow₀ (by norm_num)
  have hfin : ∀ j : ℕ, {u : Frequency R | frequencyNorm R u < (2 : ℝ) ^ (j + 1)}.Finite :=
    fun j => ((hcount _ (hpow j)).1).subset (fun _ hu => le_of_lt (Set.mem_setOf_eq.mp hu))
  let D : ℕ → Finset (Frequency R) := fun j =>
    (hfin j).toFinset.filter
      (fun u => u ≠ principalFrequency R ∧ (2 : ℝ) ^ j ≤ frequencyNorm R u)
  have hmem : ∀ (j : ℕ) (u : Frequency R), u ∈ D j ↔
      frequencyNorm R u < (2 : ℝ) ^ (j + 1) ∧ u ≠ principalFrequency R ∧
        (2 : ℝ) ^ j ≤ frequencyNorm R u := by
    intro j u
    simp only [D, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hDcard : ∀ j : ℕ, ((D j).card : ℝ) ≤ (2 * K₀) * (2 : ℝ) ^ j := by
    intro j
    have hpow_eq : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
    have hcard_le : (D j).card ≤ (hfin j).toFinset.card := Finset.card_filter_le _ _
    have hto : ((hfin j).toFinset.card : ℝ) =
        (Set.ncard {u : Frequency R | frequencyNorm R u < (2 : ℝ) ^ (j + 1)} : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ (hfin j)]
    have hsub : {u : Frequency R | frequencyNorm R u < (2 : ℝ) ^ (j + 1)} ⊆
        {u : Frequency R | frequencyNorm R u ≤ (2 : ℝ) ^ (j + 1)} :=
      fun _ hu => le_of_lt (Set.mem_setOf_eq.mp hu)
    have hle : (Set.ncard {u : Frequency R |
        frequencyNorm R u < (2 : ℝ) ^ (j + 1)} : ℝ) ≤ K₀ * (2 : ℝ) ^ (j + 1) :=
      (Nat.cast_le.mpr (Set.ncard_le_ncard hsub (hcount _ (hpow j)).1)).trans
        (hcount _ (hpow j)).2
    calc ((D j).card : ℝ) ≤ ((hfin j).toFinset.card : ℝ) := by exact_mod_cast hcard_le
      _ = (Set.ncard {u : Frequency R |
            frequencyNorm R u < (2 : ℝ) ^ (j + 1)} : ℝ) := hto
      _ ≤ K₀ * (2 : ℝ) ^ (j + 1) := hle
      _ = (2 * K₀) * (2 : ℝ) ^ j := by rw [hpow_eq]; ring
  refine ⟨2 * K₀, D, by positivity, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · intro u hu
      have hu' := (hmem j u).mp hu
      refine ⟨hu'.2.1, hu'.2.2, ?_⟩
      have hpow_eq : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
      rw [← hpow_eq]
      exact hu'.1
    · exact hDcard j
  · intro u hu
    have hq1 : 1 ≤ frequencyNorm R u := one_le_frequencyNorm R u
    have hex : ∃ n : ℕ, frequencyNorm R u < (2 : ℝ) ^ n :=
      ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually
        (Filter.eventually_gt_atTop (frequencyNorm R u))).exists
    let n := Nat.find hex
    have hn : frequencyNorm R u < (2 : ℝ) ^ n := Nat.find_spec hex
    have hnmin : ∀ m < n, ¬ frequencyNorm R u < (2 : ℝ) ^ m :=
      fun m hm => Nat.find_min hex hm
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hn
        simp only [pow_zero] at hn
        linarith
      · exact h
    have hle : (2 : ℝ) ^ (n - 1) ≤ frequencyNorm R u := by
      exact not_lt.mp (hnmin (n - 1) (Nat.sub_lt hnpos (by norm_num)))
    refine ⟨n - 1, (hmem (n - 1) u).mpr ⟨?_, hu, hle⟩⟩
    rw [Nat.sub_add_cancel hnpos]
    exact hn

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

theorem deleted_exterior_zero_iff_primitive
    (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (hSD : (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ D)
    (a : A.Exterior → ℂ)
    (ha : ∀ I : A.Exterior,
      a I = Detector.deletedPrimitiveIdealCoefficient F ν D I.val)
    (H : NonprincipalRayHeckeData F ν.conductor ν.character)
    (l : ℂ → ℂ) (hl : DifferentiableOn ℂ l {s : ℂ | 0 < s.re})
    (hseries : ∀ s : ℂ, 1 < s.re →
      l s = InitialSeparatedEuler.dirichletSeries a s)
    (s : ℂ) (hs : 0 < s.re) :
    l s = 0 ↔ H.L s = 0 := by
  classical
  have hmaskne : Detector.finiteEulerDeletionMask F D
      (fun v => ν.character v.asIdeal) s ≠ 0 := by
    letI := hD.fintype
    rw [Detector.finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact (Detector.finite_euler_local_factor_nonzero F s.re hs v.val
      (ν.character v.val.asIdeal) s
      (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero
        ν.character v.val.asIdeal) le_rfl).2.2
  have heq : l s = H.L s * Detector.finiteEulerDeletionMask F D
      (fun v => ν.character v.asIdeal) s := by
    let T : Set ℂ := {s : ℂ | 0 < s.re}
    have hT : IsOpen T := isOpen_lt continuous_const Complex.continuous_re
    have hLmero : MeromorphicOn H.L T := (H.L_holo.analyticOnNhd hT).meromorphicOn
    obtain ⟨hmaskdiff, -, hBs⟩ :=
      Detector.deleted_primitive_L_continuation F ν D hD T H.L hLmero H.series
    let g : ℂ → ℂ := fun z => H.L z *
      Detector.finiteEulerDeletionMask F D (fun v => ν.character v.asIdeal) z
    have hg : AnalyticOnNhd ℂ g T :=
      (H.L_holo.mul (hmaskdiff.differentiableOn.mono (Set.subset_univ T))).analyticOnNhd hT
    have hl' : AnalyticOnNhd ℂ l T := hl.analyticOnNhd hT
    have hpoint : ∀ z : ℂ, 1 < z.re → l z = g z := by
      intro z hz
      have hdir : InitialSeparatedEuler.dirichletSeries a z =
          ∑' I : Ideal (𝓞 F), Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-z) := by
        have hzero : ∀ I : Ideal (𝓞 F), ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) →
            Detector.deletedPrimitiveIdealCoefficient F ν D I *
              (Ideal.absNorm I : ℂ) ^ (-z) = 0 := by
          intro I hn
          have hc0 : Detector.deletedPrimitiveIdealCoefficient F ν D I = 0 := by
            by_cases hbot : I = ⊥
            · subst hbot
              simp only [Detector.deletedPrimitiveIdealCoefficient]
              by_cases hex : ∃ v ∈ D, (⊥ : Ideal (𝓞 F)) ≤ v.asIdeal
              · simp [hex]
              · simp only [hex, if_false]
                exact (ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
            · have hsup : I ⊔ A.cS ≠ ⊤ := fun h => hn ⟨hbot, h⟩
              have hex : ∃ v ∈ D, I ≤ v.asIdeal := by
                have hA : ¬ ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                    v ∈ A.Sf → I ⊔ v.asIdeal = ⊤ := by
                  intro hall
                  exact hsup ((SArithmeticData.exterior_iff A ⟨I, hbot⟩).mpr hall)
                push Not at hA
                obtain ⟨v, hvS, hvv⟩ := hA
                have heqv : v.asIdeal = I ⊔ v.asIdeal :=
                  v.isMaximal.eq_of_le hvv le_sup_right
                exact ⟨v, hSD (by simpa using hvS), le_sup_left.trans heqv.symm.le⟩
              simp only [Detector.deletedPrimitiveIdealCoefficient]
              simp [hex]
          rw [hc0, zero_mul]
        have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
            Detector.deletedPrimitiveIdealCoefficient F ν D I *
              (Ideal.absNorm I : ℂ) ^ (-z)) ⊆
            {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
          intro I hI
          by_contra hn
          exact hI (hzero I hn)
        rw [InitialSeparatedEuler.dirichletSeries]
        rw [← tsum_subtype_eq_of_support_subset hsupp]
        apply tsum_congr
        intro I
        simp only [ExteriorIdealEuler.summand]
        rw [ha I]
      rw [hseries z hz, hdir, (hBs z hz).tsum_eq]
    have hEqOn : Set.EqOn l g T :=
      hl'.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
        (z₀ := (2 : ℂ)) (by norm_num [T])
        (by
          filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
            (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with z hz
          exact hpoint z hz)
    have h := hEqOn (by simpa [T] using hs)
    simpa [g] using h
  rw [heq]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right hmaskne
  · intro h
    rw [h, zero_mul]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle

end

section
namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private lemma coprime_conductor_cofinite (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.asIdeal ⊔ m = ⊤ := by
  apply Filter.eventually_cofinite.mpr
  apply (Ideal.finite_factors hm).subset
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  apply Ideal.dvd_iff_le.mpr
  have hvmax : v.asIdeal.IsMaximal := v.isMaximal
  exact (hvmax.eq_of_le hv (show v.asIdeal ≤ v.asIdeal ⊔ m from le_sup_left)).symm ▸
    (show m ≤ v.asIdeal ⊔ m from le_sup_right)

theorem exact_coefficients_cofinite_denominator
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (ν : Frequency R → Detector.PrimitiveFrequencyCharacter F)
    (hfinite : ∀ u : Frequency R, (RawHeckeRows.rawDeletionSet (U u)).Finite)
    (hcoeff : ∀ (u : Frequency R) (I : R.A.Exterior),
      AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
        Detector.deletedPrimitiveIdealCoefficient F (ν u)
          (RawHeckeRows.rawDeletionSet (U u)) I.val)
    (W : Detector.FrequencyRepresentatives F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (e : Frequency R ≃ W.carrier)
    (he : ∀ u : Frequency R, (e u).val = ThetaReflectionData.rowUnit R.A u.val)
    (τ : Detector.PrimitiveFrequencyCharacter F)
    (hτ : ∀ I : R.A.Exterior, R.target I.val = τ.character I.val)
    (K : Detector.KummerFrequencyFamily F R.A.zeta12 R.σ
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) W)
    (T : Detector.TwistedFrequencyFamily F R.A.zeta12 R.σ
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) W K τ)
    (u : Frequency R) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (ν u).character v.asIdeal = (T.denominator (e u)).character v.asIdeal := by
  classical
  have hunit : (e u).val =
      Units.mk0 ((U u).u : F) (by exact_mod_cast (U u).generates.1) := by
    rw [he u]
    apply Units.ext
    change (u.val.val : F) = ((U u).u : F)
    rw [hU]
  have hK : Detector.IsKummerFrequencyCharacter F R.A.zeta12 R.σ
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (Units.mk0 ((U u).u : F) (by exact_mod_cast (U u).generates.1))
      (K.numerator (e u)) := by
    rw [← hunit]
    exact K.kummer (e u)
  obtain ⟨hχsupp, hχprime⟩ :=
    MinusArithmetic.source_kummer_raw_prime_values R.A R.σ (U u) (K.numerator (e u)) hK
  have hfin : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v ∉ RawHeckeRows.rawDeletionSet (U u) := by
    rw [Filter.eventually_cofinite]
    simpa using hfinite u
  have hcop : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.asIdeal ⊔ (τ.conductor * (K.numerator (e u)).conductor *
        (T.denominator (e u)).conductor) = ⊤ :=
    coprime_conductor_cofinite _
      (mul_ne_zero (mul_ne_zero τ.conductor_ne_zero (K.numerator (e u)).conductor_ne_zero)
        (T.denominator (e u)).conductor_ne_zero)
  filter_upwards [hfin, hcop] with v hvD hvc
  have hvSf : v ∉ (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :=
    fun h => hvD (Or.inl h)
  have hnotle : ¬ (U u).ideal.val ≤ v.asIdeal := fun h => hvD (Or.inr h)
  have hExterior : v.asIdeal ⊔ R.A.cS = ⊤ := by
    rw [R.A.exterior_iff ⟨v.asIdeal, v.ne_bot⟩]
    intro w hw
    exact v.isMaximal.coprime_of_ne w.isMaximal
      (fun h => hvSf ((HeightOneSpectrum.asIdeal_injective h).symm ▸ hw))
  let I : R.A.Exterior := LocalFiniteSums.primeIdeal ⟨v, hExterior⟩
  have hdel : Detector.deletedPrimitiveIdealCoefficient F (ν u)
      (RawHeckeRows.rawDeletionSet (U u)) I.val = (ν u).character I.val := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg]
    rintro ⟨w, hw, hvw⟩
    have he : v = w :=
      HeightOneSpectrum.asIdeal_injective (v.isMaximal.eq_of_le w.isPrime.ne_top hvw)
    exact hvD (he.symm ▸ hw)
  have hplus : AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
      (K.numerator (e u)).character I.val := by
    have h := hχprime ⟨v, hExterior⟩
    rw [if_neg hnotle] at h
    exact h
  have htwist := (T.induces (e u)) I.val v.ne_bot hvc
  calc (ν u).character v.asIdeal
      = (ν u).character I.val := rfl
    _ = Detector.deletedPrimitiveIdealCoefficient F (ν u)
          (RawHeckeRows.rawDeletionSet (U u)) I.val := hdel.symm
    _ = AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I :=
        (hcoeff u I).symm
    _ = R.target I.val * star (AllRowEuler.InitialSeparation.plusExteriorCoefficient
          R.σ (U u) I) := rfl
    _ = R.target I.val * star ((K.numerator (e u)).character I.val) := by rw [hplus]
    _ = τ.character I.val * star ((K.numerator (e u)).character I.val) := by rw [hτ I]
    _ = (T.denominator (e u)).character I.val := htwist.symm
    _ = (T.denominator (e u)).character v.asIdeal := rfl

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary

end

section
namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary
open scoped Classical

theorem filtered_card_le_finite_cover {α β : Type*} (e : α ↪ β)
    (C : Finset α) (P : α → Prop) (E : Set β) (hE : E.Finite)
    (hcover : ∀ u ∈ C, P u → e u ∈ E) :
    (C.filter P).card ≤ E.ncard := by
  have hs : ↑((C.filter P).map e) ⊆ E := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    exact hcover u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have hh := Set.ncard_le_ncard hs hE
  simpa only [Set.ncard_coe_finset, Finset.card_map] using hh

end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle.Dictionary

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

theorem deleted_exterior_continuation_eq_hecke_mask
    (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (hSD : (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ D)
    (a : A.Exterior → ℂ)
    (ha : ∀ I : A.Exterior, a I = Detector.deletedPrimitiveIdealCoefficient F ν D I.val)
    (H : NonprincipalRayHeckeData F ν.conductor ν.character)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | 0 < s.re})
    (hseries : ∀ s : ℂ, 1 < s.re → f s = InitialSeparatedEuler.dirichletSeries a s) :
    ∀ s : ℂ, 0 < s.re →
      f s = H.L s * Detector.finiteEulerDeletionMask F D
        (fun v => ν.character v.asIdeal) s := by
  classical
  let T : Set ℂ := {s : ℂ | 0 < s.re}
  have hT : IsOpen T := isOpen_lt continuous_const Complex.continuous_re
  have hLmero : MeromorphicOn H.L T := (H.L_holo.analyticOnNhd hT).meromorphicOn
  obtain ⟨hmaskdiff, -, hBs⟩ :=
    Detector.deleted_primitive_L_continuation F ν D hD T H.L hLmero H.series
  let g : ℂ → ℂ := fun s => H.L s *
    Detector.finiteEulerDeletionMask F D (fun v => ν.character v.asIdeal) s
  have hg : AnalyticOnNhd ℂ g T :=
    (H.L_holo.mul (hmaskdiff.differentiableOn.mono (Set.subset_univ T))).analyticOnNhd hT
  have hf' : AnalyticOnNhd ℂ f T := hf.analyticOnNhd hT
  have heq : ∀ s : ℂ, 1 < s.re → f s = g s := by
    intro s hs
    have hdir : InitialSeparatedEuler.dirichletSeries a s =
        ∑' I : Ideal (𝓞 F), Detector.deletedPrimitiveIdealCoefficient F ν D I *
          (Ideal.absNorm I : ℂ) ^ (-s) := by
      have hzero : ∀ I : Ideal (𝓞 F), ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) →
          Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-s) = 0 := by
        intro I hn
        have hc : Detector.deletedPrimitiveIdealCoefficient F ν D I = 0 := by
          by_cases hbot : I = ⊥
          · subst hbot
            simp only [Detector.deletedPrimitiveIdealCoefficient]
            by_cases hex : ∃ v ∈ D, (⊥ : Ideal (𝓞 F)) ≤ v.asIdeal
            · simp [hex]
            · simp only [hex, if_false]
              exact (ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
          · have hsup : I ⊔ A.cS ≠ ⊤ := fun h => hn ⟨hbot, h⟩
            have hex : ∃ v ∈ D, I ≤ v.asIdeal := by
              have hA : ¬ ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                  v ∈ A.Sf → I ⊔ v.asIdeal = ⊤ := by
                intro hall
                exact hsup ((SArithmeticData.exterior_iff A ⟨I, hbot⟩).mpr hall)
              push Not at hA
              obtain ⟨v, hvS, hvv⟩ := hA
              have heq : v.asIdeal = I ⊔ v.asIdeal :=
                v.isMaximal.eq_of_le hvv le_sup_right
              exact ⟨v, hSD (by simpa using hvS), le_sup_left.trans heq.symm.le⟩
            simp only [Detector.deletedPrimitiveIdealCoefficient]
            simp [hex]
        rw [hc, zero_mul]
      have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
          Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
          {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
        intro I hI
        by_contra hn
        exact hI (hzero I hn)
      rw [InitialSeparatedEuler.dirichletSeries]
      rw [← tsum_subtype_eq_of_support_subset hsupp]
      apply tsum_congr
      intro I
      simp only [ExteriorIdealEuler.summand]
      rw [ha I]
    rw [hseries s hs, hdir, (hBs s hs).tsum_eq]
  have hEqOn : Set.EqOn f g T :=
    hf'.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
      (z₀ := (2 : ℂ)) (by norm_num [T])
      (by
        filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
          (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
        exact heq s hs)
  intro s hs
  have h := hEqOn (by simpa [T] using hs)
  simpa [g] using h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

 def rawValuationIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : Ideal A.R where
  carrier := {r | v.valuation F (r : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact (ValuationClass.map_add_le_max _ _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (x.property v hv) zero_le).trans_lt (by simpa using hy)

private lemma raw_support_valuation {A : SArithmeticData F}
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) (h : U.ideal.val ≤ v.asIdeal) :
    v.valuation F (U.u : F) < 1 := by
  have hm : A.extendIdeal U.ideal ≤ rawValuationIdeal A v hv := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change v.valuation F (algebraMap (𝓞 F) F a) < 1
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr (h ha)
  apply hm
  rw [← U.generates.2]
  exact Ideal.mem_span_singleton_self _

theorem actual_raw_deletion_mask_linear_bound
    (R : PrincipalMellin.ActualRecipe S η) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
        U.u = u.val.val →
        ∀ (b : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℂ),
          (∀ v ∈ RawHeckeRows.rawDeletionSet U, ‖b v‖ ≤ 1) →
          ∀ s : ℂ, a ≤ s.re →
            ‖Detector.finiteEulerDeletionMask F (RawHeckeRows.rawDeletionSet U) b s‖ ≤
              C * frequencyNorm R u := by
  obtain ⟨C, hC, hbound⟩ := Detector.frequency_finite_euler_masks_subpower F
    (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) R.A.Sf.finite_toSet a 1 ha one_pos
  refine ⟨C, hC, ?_⟩
  intro u U hU b hb s hs
  have hsub : RawHeckeRows.rawDeletionSet U ⊆
      (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∪
        Detector.exteriorFrequencyPrimeSupport F
          (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) U.u := by
    intro v hv
    simp only [RawHeckeRows.rawDeletionSet, Set.mem_union, Set.mem_setOf_eq] at hv
    rcases hv with hvS | hvI
    · exact Or.inl hvS
    · by_cases hvS : v ∈ R.A.Sf
      · exact Or.inl hvS
      · exact Or.inr ⟨hvS, raw_support_valuation U v hvS hvI⟩
  have hb' := (hbound U.u U.generates.1).2.2 (RawHeckeRows.rawDeletionSet U) hsub
    b s hb hs
  rw [Real.rpow_one] at hb'
  calc ‖Detector.finiteEulerDeletionMask F (RawHeckeRows.rawDeletionSet U) b s‖
      ≤ C * (Detector.frequencyNorm F
          (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) U.u : ℝ) := hb'.2.1
    _ = C * frequencyNorm R u := by rw [hU]; rfl

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem primitive_denominator_rectangle_zero_count
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (ν : Frequency R → Detector.PrimitiveFrequencyCharacter F)
    (hfinite : ∀ u : Frequency R, (RawHeckeRows.rawDeletionSet (U u)).Finite)
    (hcoeff : ∀ (u : Frequency R) (I : R.A.Exterior),
      AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
        Detector.deletedPrimitiveIdealCoefficient F (ν u)
          (RawHeckeRows.rawDeletionSet (U u)) I.val)
    (hnp : ∀ u : Frequency R, u ≠ principalFrequency R →
      ¬ (ν u).character.IsPrincipal) :
    ∃ ρ B Uexc : ℝ, 0 < ρ ∧ ρ < 1 / 10 ∧ 0 < B ∧ 1 ≤ Uexc ∧
      ∀ (V : ℝ) (C : Finset (Frequency R)), Uexc ≤ V →
        (∀ u ∈ C, u ≠ principalFrequency R ∧
          V ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * V) →
        ((C.filter (fun u =>
          ∃ H : NonprincipalRayHeckeData F (ν u).conductor (ν u).character,
            ∃ s : ℂ, 249 / 250 ≤ s.re ∧ |s.im| ≤ 4 * V ^ ρ ∧ H.L s = 0)).card : ℝ) ≤
          B * V ^ (1 / 2 : ℝ) := by
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  letI : NumberField.IsTotallyComplex F := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) := by
    intro v hv
    by_contra h
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six R.A v h)
  obtain ⟨W, e, he, hSnorm⟩ := MinusArithmetic.actual_detector_frequency_representatives R
  have hnorm (u : Frequency R) : frequencyNorm R u =
      (Detector.frequencyNorm F _ (Detector.frequencySInteger F _ W (e u)) : ℝ) :=
    (hSnorm u).symm
  obtain ⟨τ, hτS, hτExterior, _⟩ := MinusArithmetic.target_primitive_inducer R
  have hτ (I : R.A.Exterior) : R.target I.val = τ.character I.val := (hτExterior I).symm
  obtain ⟨K⟩ := Detector.kummer_frequency_family_exists F R.A.zeta12 R.A.primitive_zeta12
    R.σ _ R.A.Sf.finite_toSet hSix W
  obtain ⟨T⟩ := Detector.twisted_frequency_family_exists F R.A.zeta12 R.A.primitive_zeta12
    R.σ _ R.A.Sf.finite_toSet hSix W K τ
  have hν : ∀ u : Frequency R, ν u = T.denominator (e u) := by
    intro u
    apply MinusArithmetic.primitive_inducers_eq_of_cofinite_prime_values
    exact Dictionary.exact_coefficients_cofinite_denominator R U hU ν hfinite hcoeff
      W e he τ hτ K T u
  obtain ⟨ρ, X₀, B, hρ, hρsmall, hX₀, hB, hcount⟩ :=
    Detector.frequency_dyad_exceptional_count F R.A.zeta12 R.A.primitive_zeta12
      R.σ _ R.A.Sf.finite_toSet hSix τ hτS
  refine ⟨ρ, B, X₀, hρ, hρsmall, hB, by linarith, ?_⟩
  intro V C hV hC
  obtain ⟨E, hEsub, hEfin, hEcount, _, hzero⟩ := hcount W K T V hV
  have hdyad : ∀ u ∈ C, e u ∈ Detector.frequencyDyad F _ W V := by
    intro u hu
    change V ≤ (Detector.frequencyNorm F _ (Detector.frequencySInteger F _ W (e u)) : ℝ) ∧
      (Detector.frequencyNorm F _ (Detector.frequencySInteger F _ W (e u)) : ℝ) < 2 * V
    rw [← hnorm]
    exact ⟨(hC u hu).2.1, (hC u hu).2.2⟩
  have hcard := Dictionary.filtered_card_le_finite_cover e.toEmbedding C
    (fun u => ∃ H : NonprincipalRayHeckeData F (ν u).conductor (ν u).character,
      ∃ s : ℂ, 249 / 250 ≤ s.re ∧ |s.im| ≤ 4 * V ^ ρ ∧ H.L s = 0)
    E hEfin (by
      intro u hu hz
      apply hzero (e u) (hdyad u hu)
      · rw [← hν u]
        exact hnp u (hC u hu).1
      · rw [← hν u]
        exact hz)
  exact (show ((C.filter (fun u =>
    ∃ H : NonprincipalRayHeckeData F (ν u).conductor (ν u).character,
      ∃ s : ℂ, 249 / 250 ≤ s.re ∧ |s.im| ≤ 4 * V ^ ρ ∧ H.L s = 0)).card : ℝ) ≤
      (E.ncard : ℝ) from by exact_mod_cast hcard).trans hEcount

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.DenominatorRectangle

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def actualDenominatorGood
    (R : PrincipalMellin.ActualRecipe S η)
    (minus : Frequency R → ℂ → ℂ) (ρ V : ℝ) (u : Frequency R) : Prop :=
  u ≠ principalFrequency R ∧
    ∀ ξ : ℂ, 249 / 250 ≤ ξ.re → |ξ.im| ≤ 4 * V ^ ρ → minus u ξ ≠ 0

theorem actual_denominator_rectangle_exceptional_count
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (minus : Frequency R → ℂ → ℂ)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s) :
    ∃ ρ B Uexc : ℝ, 0 < ρ ∧ ρ < 1 / 10 ∧ 0 < B ∧ 1 ≤ Uexc ∧
      ∀ (V : ℝ) (C : Finset (Frequency R)), Uexc ≤ V →
        (∀ u ∈ C, u ≠ principalFrequency R ∧
          V ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * V) →
        ((C.filter (fun u => ¬ actualDenominatorGood R minus ρ V u)).card : ℝ) ≤
          B * V ^ (1 / 2 : ℝ) := by
  obtain ⟨C₀, _, hC₀, _⟩ := RawHeckeRows.actual_context_and_raw_frequencies R
  obtain ⟨P, M, hfinite, hP, hM⟩ :=
    RawHeckeRows.actual_raw_masked_inducers R C₀ hC₀ U hU
  have hnp (u : Frequency R) (hu : u ≠ principalFrequency R) :
      ¬ (M u).character.IsPrincipal :=
    (RawHeckeRows.actual_raw_inducers_nonprincipal R u (U u) (hU u) hu
      (P u) (M u) (hP u) (hM u)).2
  obtain ⟨ρ, B, Uexc, hρ, hρsmall, hB, hUexc, hcount⟩ :=
    DenominatorRectangle.primitive_denominator_rectangle_zero_count
       R U hU M hfinite hM hnp
  refine ⟨ρ, B, Uexc, hρ, hρsmall, hB, hUexc, ?_⟩
  intro V C hV hC
  have hsub : C.filter (fun u => ¬ actualDenominatorGood R minus ρ V u) ⊆
      C.filter (fun u =>
        ∃ H : NonprincipalRayHeckeData F (M u).conductor (M u).character,
          ∃ s : ℂ, 249 / 250 ≤ s.re ∧ |s.im| ≤ 4 * V ^ ρ ∧ H.L s = 0) := by
    intro u hu
    obtain ⟨huC, hubad⟩ := Finset.mem_filter.mp hu
    have hunp := (hC u huC).1
    have hzero : ∃ s : ℂ, 249 / 250 ≤ s.re ∧
        |s.im| ≤ 4 * V ^ ρ ∧ minus u s = 0 := by
      by_contra h
      apply hubad
      refine ⟨hunp, ?_⟩
      intro s hsre hsim hs0
      exact h ⟨s, hsre, hsim, hs0⟩
    obtain ⟨s, hsre, hsim, hs0⟩ := hzero
    let H := nonprincipalRayHeckeData F
      (primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12)
      (M u).conductor (M u).conductor_ne_zero (M u).character
      (M u).primitive (hnp u hunp)
    have hH : H.L s = 0 :=
      (DenominatorRectangle.deleted_exterior_zero_iff_primitive R.A (M u)
        (RawHeckeRows.rawDeletionSet (U u)) (hfinite u)
        Set.subset_union_left
        (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u))
        (hM u) H (minus u) (hminus u hunp)
        (hminusSeries u) s (by linarith)).mp hs0
    exact Finset.mem_filter.mpr ⟨huC, H, s, hsre, hsim, hH⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount V C hV hC)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_denominator_reciprocal_of_nonprincipal_strip_growth
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (minus : Frequency R → ℂ → ℂ)
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (ρrect ρ : ℝ) (hρrect : 0 < ρrect) (hρ : 0 < ρ) (hρle : ρ ≤ ρrect)
    (C B A : ℝ)
    (hgrowth : ∀ (V : ℝ) (u : Frequency R), 2 ≤ V → u ≠ principalFrequency R →
      V ≤ frequencyNorm R u → frequencyNorm R u < 2 * V →
      ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
        ‖minus u s‖ ≤ C * V ^ B * (2 + |s.im|) ^ A) :
    ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
      ∀ (V : ℝ) (u : Frequency R), Udet ≤ V →
        actualDenominatorGood R minus ρrect V u →
        V ≤ frequencyNorm R u → frequencyNorm R u < 2 * V →
        ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * V ^ ρ →
          minus u ξ ≠ 0 ∧ ‖(minus u ξ)⁻¹‖ ≤ B * V ^ δ := by
  intro δ hδ
  let C₁ : ℝ := (3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-(1001 / 1000 : ℝ))
  obtain ⟨Cε, Uε, hCε, hUε, hmain⟩ :=
    detector_reciprocal_disk A B C C₁ ρrect 2 hρrect (by norm_num) δ hδ
  refine ⟨Cε, Uε, hCε, by linarith, ?_⟩
  intro V u hV hgood hVu hVu2 ξ hξre hξim
  have hV2 : 2 ≤ V := hUε.trans hV
  have hV1 : 1 ≤ V := by linarith
  have hu : u ≠ principalFrequency R := hgood.1
  have hpowle : V ^ ρ ≤ V ^ ρrect := Real.rpow_le_rpow_of_exponent_le hV1 hρle
  have hpowrect : 1 ≤ V ^ ρrect := Real.one_le_rpow hV1 hρrect.le
  have hξimrect : |ξ.im| ≤ 4 * V ^ ρrect := by
    have h2 : 2 * V ^ ρ ≤ 4 * V ^ ρrect := by linarith
    linarith [hξim, h2]
  have hξnon : minus u ξ ≠ 0 := hgood.2 ξ (by linarith) hξimrect
  refine ⟨hξnon, ?_⟩
  have ha := AllRowEuler.InitialSeparation.raw_minus_isCoefficient (σ := R.σ) (η := R.target) (U u)
  have hbound := hmain V (minus u)
    (HeckeLogProof.eulerLog (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u)))
    hV
    ((hminus u hu).mono (fun s hs => lt_trans (by norm_num : (0:ℝ) < 249 / 250) hs.1))
    (fun s hs hs' => hgood.2 s (le_of_lt hs) hs')
    (fun s hs1 hs2 => hgrowth V u hV2 hu hVu hVu2 s hs1 hs2)
    (HeckeLogProof.eulerLog_differentiableOn _ ha)
    (fun s hs => by
      rw [HeckeLogProof.exp_eulerLog _ ha s hs]
      exact (hminusSeries u s hs).symm)
    (fun s hs => by
      show ‖HeckeLogProof.eulerLog
        (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u)) s‖ ≤ C₁
      rw [show C₁ = (3 / 2 : ℝ) *
        ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-(1001 / 1000 : ℝ)) from rfl]
      exact HeckeLogProof.eulerLog_norm_le _ ha (1001 / 1000) (by norm_num) s hs)
    ξ hξre (by
      have h2 : 2 * V ^ ρ ≤ 2 * V ^ ρrect := by linarith
      linarith [hξim, h2])
  exact hbound

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_denominator_reciprocal_of_rectangle
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (minus : Frequency R → ℂ → ℂ)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (ρrect ρ : ℝ) (hρrect : 0 < ρrect) (hρrectSmall : ρrect < 1 / 10)
    (hρ : 0 < ρ) (hρle : ρ ≤ ρrect) :
    ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
      ∀ (V : ℝ) (u : Frequency R), Udet ≤ V →
        actualDenominatorGood R minus ρrect V u →
        V ≤ frequencyNorm R u → frequencyNorm R u < 2 * V →
        ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * V ^ ρ →
          minus u ξ ≠ 0 ∧ ‖(minus u ξ)⁻¹‖ ≤ B * V ^ δ := by
  obtain ⟨c, hc, hconductor⟩ := actual_raw_minus_inducer_conductor_bound R
  obtain ⟨Cctx, Uctx, hCctx, hUctx⟩ :=
    RawHeckeRows.actual_context_and_raw_frequencies R
  obtain ⟨P, M, hfinite, hP, hM⟩ :=
    RawHeckeRows.actual_raw_masked_inducers R Cctx hCctx U hU
  have htc : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨A, hA, hconvexity⟩ := detector_convexity_bridge F htc
    (2 * c) (by positivity)
  obtain ⟨Cp, hCp, hprimitive⟩ := hconvexity (1 / 2) (by norm_num)
  obtain ⟨Cm, hCm, hmask⟩ := actual_raw_deletion_mask_linear_bound R
    (3 / 1000) (by norm_num)
  apply actual_denominator_reciprocal_of_nonprincipal_strip_growth R U minus
    hminus hminusSeries ρrect ρ hρrect hρ hρle (2 * Cp * Cm) 2 A
  intro V u hV hu hVu hVu2 s hslo hshi
  have hnp : ¬ (M u).character.IsPrincipal :=
    (RawHeckeRows.actual_raw_inducers_nonprincipal R u (U u)
      (hU u) hu (P u) (M u) (hP u) (hM u)).2
  let H := nonprincipalRayHeckeData F htc (M u).conductor
    (M u).conductor_ne_zero (M u).character (M u).primitive hnp
  have hcond : (Ideal.absNorm (M u).conductor : ℝ) ≤ (2 * c) * V := by
    have hb := hconductor u (U u) (hU u) (M u) (hM u)
    have hscale := mul_le_mul_of_nonneg_left hVu2.le hc.le
    nlinarith
  have hp := (hprimitive V hV (M u).conductor (M u).conductor_ne_zero
    (M u).character (M u).primitive hcond s hslo hshi).1 hnp H
  have hm := hmask u (U u) (hU u) (fun v => (M u).character v.asIdeal)
    (fun v _ => RayUnitary.ray_character_norm_le_one F (M u).conductor
      (M u).conductor_ne_zero (M u).character v.asIdeal) s hslo
  have heq := deleted_exterior_continuation_eq_hecke_mask R.A (M u)
    (RawHeckeRows.rawDeletionSet (U u)) (hfinite u) Set.subset_union_left
    (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u))
    (hM u) H (minus u) (hminus u hu) (hminusSeries u) s
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 1000) hslo)
  calc
    ‖minus u s‖ = ‖H.L s‖ * ‖Detector.finiteEulerDeletionMask F
        (RawHeckeRows.rawDeletionSet (U u))
        (fun v => (M u).character v.asIdeal) s‖ := by rw [heq, norm_mul]
    _ ≤ (Cp * V ^ (1 / 2 + 1 / 2 : ℝ) * (2 + |s.im|) ^ A) *
        (Cm * frequencyNorm R u) :=
      mul_le_mul hp hm (norm_nonneg _) (by positivity)
    _ ≤ (Cp * V ^ (1 / 2 + 1 / 2 : ℝ) * (2 + |s.im|) ^ A) *
        (Cm * (2 * V)) := by
      gcongr
    _ = (2 * Cp * Cm) * V ^ (2 : ℝ) * (2 + |s.im|) ^ A := by
      norm_num [Real.rpow_two]
      ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_denominator_detector_dyads
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (minus : Frequency R → ℂ → ℂ)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (A_F : ℝ) (hA_F : 0 ≤ A_F) :
    ∃ (good : ℝ → Frequency R → Prop) (ρ K : ℝ) (D : ℕ → Finset (Frequency R)),
      (∀ (V : ℝ) (u : Frequency R), 1 ≤ V → good V u →
        DifferentiableOn ℂ (minus u) {ξ : ℂ | 0 < ξ.re}) ∧
      0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
        ∀ (V : ℝ) (u : Frequency R), Udet ≤ V → good V u →
          V ≤ frequencyNorm R u → frequencyNorm R u < 2 * V →
          ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * V ^ ρ →
            minus u ξ ≠ 0 ∧ ‖(minus u ξ)⁻¹‖ ≤ B * V ^ δ) ∧
      0 < K ∧
      (∀ j : ℕ, comparisonFrequencyDyad (frequencyNorm R) (principalFrequency R) K
        ((2 : ℝ) ^ j) (D j)) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R → ∃ j : ℕ, u ∈ D j) ∧
      (∃ B Uexc : ℝ, 0 < B ∧ 1 ≤ Uexc ∧ ∀ j : ℕ, Uexc ≤ (2 : ℝ) ^ j →
        (((D j).filter (fun u => ¬ good ((2 : ℝ) ^ j) u)).card : ℝ) ≤
          B * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ)) := by
  obtain ⟨K, D, hK, hD, hcover⟩ :=
    DetectorDyads.actual_complete_frequency_dyads R
  obtain ⟨ρrect, Bexc, Uexc, hρrect, hρrectSmall, hBexc, hUexc, hcount⟩ :=
    DetectorDyads.actual_denominator_rectangle_exceptional_count
       R U minus hU hminus hminusSeries
  let cap : ℝ := min (1 / 10) (1 / (A_F + 1))
  have hcap : 0 < cap := by
    apply lt_min
    · norm_num
    · exact div_pos zero_lt_one (by linarith)
  let ρ : ℝ := min ρrect cap / 2
  have hmin : 0 < min ρrect cap := lt_min hρrect hcap
  have hρ : 0 < ρ := div_pos hmin (by norm_num)
  have hρle : ρ ≤ ρrect := by
    dsimp [ρ]
    have := min_le_left ρrect cap
    linarith
  have hρsmall : ρ < cap := by
    dsimp [ρ]
    have := min_le_right ρrect cap
    linarith
  let good : ℝ → Frequency R → Prop :=
    DetectorDyads.actualDenominatorGood R minus ρrect
  have hrecip := DetectorDyads.actual_denominator_reciprocal_of_rectangle
     R U minus hU hminus hminusSeries ρrect ρ
      hρrect hρrectSmall hρ hρle
  refine ⟨good, ρ, K, D, ?_, hρ, hρsmall, hrecip, hK, hD, hcover, ?_⟩
  · intro V u hV hu
    exact hminus u hu.1
  · refine ⟨Bexc, Uexc, hBexc, hUexc, ?_⟩
    intro j hj
    exact hcount ((2 : ℝ) ^ j) (D j) hj (hD j).1

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
