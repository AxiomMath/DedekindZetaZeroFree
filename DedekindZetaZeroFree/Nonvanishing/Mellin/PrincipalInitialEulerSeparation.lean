module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.InitialFrequencyDecomposition
public import DedekindZetaZeroFree.Moments.Principal.EulerCorrectionsAndDoubleResidue
public import DedekindZetaZeroFree.Moments.Principal.FixedMellinWeightErrorEstimates

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
open scoped Classical NumberField Topology
open IsDedekindDomain Filter
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def correction (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (ξ w z : ℂ) : ℂ :=
  ∏' p : LocalFiniteSums.ExteriorPrime R.A, CorrectionFactors.localFactor C U p ξ w z

def regularization (R : PrincipalMellin.ActualRecipe S η) (s : ℂ) : ℂ :=
  R.continuation.R s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))

private theorem principal_coefficient_field_trace
    (R : PrincipalMellin.ActualRecipe S η) (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [R.probe.sameTrace, PrincipalProbeConstruction.Inputs.fieldTrace_phase]
  congr 1
  funext v
  exact R.normalization.sameFiniteTrace v

private theorem principal_arithmetic_binding (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    PrincipalProbeConstruction.ArithmeticBinding R.A R.σ R.target R.traceBad
      C R.probe.allowed R.probe.coefficients := by
  refine ⟨R.probe.sameComplement.trans (congrArg (fun D => D.B) hC),
    R.probe.sameGenerator, R.probe.exteriorCharacters, ?_, R.probe.gammaTwo_recipe,
    R.probe.sixthUnitCharacters, principal_coefficient_field_trace R, ?_⟩
  · intro m
    rw [R.probe.theta_principal, hC]
  · intro x
    rw [principal_coefficient_field_trace R,
      PrincipalProbeConstruction.Inputs.fieldTrace_phase]

private theorem principal_arithmetic_compatibility (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad C.correction := by
  exact PrincipalCorrection.probe_arithmetic_compatibility C R.probe hC
    (principal_arithmetic_binding R C hC)

private theorem finite_prime_delete_hasSum
    (F : Type) [Field F] [NumberField F]
    (W : Ideal (𝓞 F) → ℂ) (W0 : W ⊥ = 0)
    (Wmul : ∀ a b, W (a * b) = W a * W b)
    (L : ℂ) (hW : HasSum W L) (V : Finset (HeightOneSpectrum (𝓞 F))) :
    HasSum (fun I => if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I)
      (L * ∏ v ∈ V, (1 - W v.asIdeal)) := by
  induction V using Finset.induction_on with
  | empty => simpa using hW
  | @insert p V hp ih =>
    let G : Ideal (𝓞 F) → ℂ := fun I => if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I
    have G0 : G ⊥ = 0 := by simp [G, W0]
    have Gmul (I : Ideal (𝓞 F)) : G (I * p.asIdeal) = G I * W p.asIdeal := by
      have he : (∃ v ∈ V, I * p.asIdeal ≤ v.asIdeal) ↔ ∃ v ∈ V, I ≤ v.asIdeal := by
        constructor
        · rintro ⟨v, hv, h⟩
          have hprime := Ideal.prime_of_isPrime v.ne_bot v.isPrime
          have hd : v.asIdeal ∣ I * p.asIdeal := Ideal.dvd_iff_le.mpr h
          rcases hprime.dvd_or_dvd hd with hd | hd
          · exact ⟨v, hv, Ideal.dvd_iff_le.mp hd⟩
          · have heq : v = p := HeightOneSpectrum.ext ((Ideal.IsMaximal.eq_of_le p.isMaximal (Ideal.IsMaximal.ne_top v.isMaximal) (Ideal.dvd_iff_le.mp hd)).symm)
            exact (hp (heq ▸ hv)).elim
        · rintro ⟨v, hv, h⟩
          exact ⟨v, hv, (Ideal.mul_le_left).trans h⟩
      simp only [G, he]
      split_ifs <;> simp [Wmul]
    let H : Ideal (𝓞 F) → ℂ := fun I => if I ≤ p.asIdeal then G I else 0
    have hH : HasSum H ((L * ∏ v ∈ V, (1 - W v.asIdeal)) * W p.asIdeal) := by
      have hi : Function.Injective (fun I : Ideal (𝓞 F) => I * p.asIdeal) := mul_left_injective₀ p.ne_bot
      apply (hi.hasSum_iff ?_).mp
      · have heq : H ∘ (fun I : Ideal (𝓞 F) => I * p.asIdeal) = fun I => G I * W p.asIdeal := by
          funext I
          simp [H, Function.comp_def, Ideal.mul_le_right, Gmul]
        rw [heq]
        exact ih.mul_right _
      · intro I hI
        have hn : ¬ I ≤ p.asIdeal := by
          intro h
          obtain ⟨a, ha⟩ := Ideal.dvd_iff_le.mpr h
          exact hI ⟨a, by simpa [mul_comm] using ha.symm⟩
        simp [H, hn]
    have hh := ih.sub hH
    have heq : (fun I => (if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I) - H I) =
        (fun I => if ∃ v ∈ insert p V, I ≤ v.asIdeal then 0 else W I) := by
      funext I
      by_cases hI : I ≤ p.asIdeal <;> by_cases hV : ∃ v ∈ V, I ≤ v.asIdeal <;>
        simp [H, G, hI, hV, Finset.exists_mem_insert]
    rw [heq] at hh
    convert hh using 1
    rw [Finset.prod_insert hp]
    ring

private theorem norm_power (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s = comparisonRealPower q s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')]
  rw [← Complex.ofReal_log hq.le]
  unfold comparisonRealPower
  congr 1
  ring

private theorem L_eq_zeta (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (hs : 1 < s.re) : R.L s = InitialSeparatedEuler.zetaS R.A s := by
  let W : Ideal (𝓞 F) → ℂ := fun I => R.target I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hW0 : W ⊥ = 0 := by simp [W, (R.target.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  have hWmul (a b : Ideal (𝓞 F)) : W (a*b) = W a * W b := by
    dsimp [W]
    rw [R.target.map_mul', map_mul Ideal.absNorm, Nat.cast_mul]
    have hp : ((Ideal.absNorm a : ℂ) * (Ideal.absNorm b : ℂ)) ^ (-s) =
        (Ideal.absNorm a : ℂ) ^ (-s) * (Ideal.absNorm b : ℂ) ^ (-s) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm a) : (0 : ℝ) ≤ Ideal.absNorm a)
        (Nat.cast_nonneg (Ideal.absNorm b) : (0 : ℝ) ≤ Ideal.absNorm b) (-s)
    rw [hp]; ring
  have hdel := finite_prime_delete_hasSum F W hW0 hWmul _
    (R.continuation.series s hs) R.A.Sf
  let g : Ideal (𝓞 F) → ℂ := fun I => if ∃ v ∈ R.A.Sf, I ≤ v.asIdeal then 0 else W I
  have hg : Function.support g ⊆ {I | I ≠ ⊥ ∧ I ⊔ R.A.cS = ⊤} := by
    intro I hI
    have hi : I ≠ ⊥ := by intro h; subst I; simpa [g, W, hW0] using hI
    refine ⟨hi, ?_⟩
    apply (R.A.exterior_iff ⟨I, hi⟩).mpr
    intro v hv
    have hn : ¬ I ≤ v.asIdeal := by
      intro h
      exact hI (by simp [g, show ∃ v ∈ R.A.Sf, I ≤ v.asIdeal from ⟨v,hv,h⟩])
    by_contra ht
    have he := v.isMaximal.eq_of_le ht le_sup_right
    exact hn (by rw [he]; exact le_sup_left)
  have hext := (hasSum_subtype_iff_of_support_subset hg).mpr hdel
  have heq (I : R.A.Exterior) : g I.val = (Ideal.absNorm I.val : ℂ)^(-s) := by
    have hn : ¬ ∃ v ∈ R.A.Sf, I.val ≤ v.asIdeal := by
      rintro ⟨v,hv,h⟩
      have ht := (R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v hv
      have : I.val ⊔ v.asIdeal ≤ v.asIdeal := sup_le h le_rfl
      rw [ht] at this
      exact v.isMaximal.ne_top (top_unique this)
    rw [show g I.val = W I.val by simp [g,hn]]
    dsimp [W]
    rw [R.probe.principal I.val I.property.1 ?_, one_mul]
    by_contra h
    obtain ⟨p,hp,hle⟩ := Ideal.exists_le_maximal (I.val ⊔ R.A.modulus) h
    have hmod : R.A.modulus ≤ p := le_sup_right.trans hle
    have hp0 : p ≠ ⊥ := ne_bot_of_le_ne_bot R.A.modulus_ne_zero hmod
    let v : HeightOneSpectrum (𝓞 F) := ⟨p,hp.isPrime,hp0⟩
    have ht := (R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v
      (R.A.modulus_support v hmod)
    have : I.val ⊔ p ≤ p := sup_le (le_sup_left.trans hle) le_rfl
    rw [ht] at this
    exact hp.ne_top (top_unique this)
  have hres := hext.tsum_eq.symm
  simp only [Function.comp_def] at hres
  change _ = ∑' I : R.A.Exterior, g I.val at hres
  simp_rw [heq] at hres
  convert hres using 1
  · unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    dsimp [W, idealNorm]
    rw [← norm_power (Ideal.absNorm v.asIdeal : ℝ) (by
      exact_mod_cast (lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)))]
    simp only [Complex.ofReal_natCast]
  · rfl

private theorem exterior_coprime (R : PrincipalMellin.ActualRecipe S η) (I : R.A.Exterior) :
    I.val ⊔ R.A.modulus = ⊤ := by
  by_contra h
  obtain ⟨p,hp,hle⟩ := Ideal.exists_le_maximal (I.val ⊔ R.A.modulus) h
  have hmod : R.A.modulus ≤ p := le_sup_right.trans hle
  have hp0 : p ≠ ⊥ := ne_bot_of_le_ne_bot R.A.modulus_ne_zero hmod
  let v : HeightOneSpectrum (𝓞 F) := ⟨p,hp.isPrime,hp0⟩
  have ht := (R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v
    (R.A.modulus_support v hmod)
  have : I.val ⊔ p ≤ p := sup_le (le_sup_left.trans hle) le_rfl
  rw [ht] at this
  exact hp.ne_top (top_unique this)

private theorem plus_one (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1) (I : R.A.Exterior) :
    FrequencyCharacterMasks.plusExteriorCoefficient U I = 1 := by
  simp [FrequencyCharacterMasks.plusExteriorCoefficient, hU]

private theorem rows_eq (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1) (s : ℂ) :
    InitialSeparatedEuler.plusL U s = InitialSeparatedEuler.zetaS R.A s ∧
    InitialSeparatedEuler.minusL U s = InitialSeparatedEuler.zetaS R.A s := by
  constructor
  · unfold InitialSeparatedEuler.plusL InitialSeparatedEuler.dirichletSeries InitialSeparatedEuler.zetaS
    apply tsum_congr
    intro I
    rw [ExteriorIdealEuler.summand, plus_one R C U hU, one_mul]
  · unfold InitialSeparatedEuler.minusL InitialSeparatedEuler.dirichletSeries InitialSeparatedEuler.zetaS
    apply tsum_congr
    intro I
    rw [ExteriorIdealEuler.summand, FrequencyCharacterMasks.minusExteriorCoefficient,
      plus_one R C U hU, star_one, mul_one,
      R.probe.principal I.val I.property.1 (exterior_coprime R I), one_mul]

private theorem euler_open (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    separatedSeries R (principalFrequency R) ξ w z * R.L ξ =
      (R.L (6*z) * R.L w) * correction R C U ξ w z := by
  have h := (InitialSeparatedEuler.initial_separated_euler U R.probe.coefficients
    (principal_arithmetic_compatibility R C hC) ξ w z hξ hw hz).2
  rw [(rows_eq R C U hU ξ).2, (rows_eq R C U hU w).1] at h
  rw [← L_eq_zeta R ξ (by linarith), ← L_eq_zeta R w (by linarith),
    ← L_eq_zeta R (6*z) (by simp; linarith)] at h
  simpa only [separatedSeries, principalFrequency, NormalizedProbe.principalSeparatedMellinSeries,
    NormalizedProbe.separatedMellinSeries, hU, CorrectionFactors.H_u, correction] using h

private theorem majorant_antitone {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (i : NormalizedProbe.MellinSeriesIndex P) {a b c a' b' c' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    NormalizedProbe.separatedSeriesMajorant P i a' b' c' ≤ NormalizedProbe.separatedSeriesMajorant P i a b c := by
  have hn : ∀ I : A.Exterior, 1 ≤ A.exteriorNorm I := by
    intro I
    have hpos := A.exteriorNorm_pos I
    change 0 < (Ideal.absNorm I.val : ℝ) at hpos
    change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (show Ideal.absNorm I.val ≠ 0 by exact_mod_cast ne_of_gt hpos))
  letI := P.coefficients.finiteResidue i.1.val.val i.1.val.property
  have hu : (1 : ℝ) ≤ (FiniteTransform.exteriorNorm A.R.toSubring i.1.val.val : ℝ) := by
    simp only [FiniteTransform.exteriorNorm, Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty
      (FiniteTransform.Residue A.R.toSubring i.1.val.val))
  unfold NormalizedProbe.separatedSeriesMajorant
  apply mul_le_mul
  · apply mul_le_mul
    · apply mul_le_mul
      · apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
        · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
        · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
      · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
      · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
      · exact mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
          (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
    · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
    · exact Real.rpow_nonneg (A.exteriorNorm_pos _).le _
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
        (Real.rpow_nonneg (A.exteriorNorm_pos _).le _))
        (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
  · exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _))
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _))
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)

private theorem row_continuous (R : PrincipalMellin.ActualRecipe S η) :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => separatedSeries R (principalFrequency R) p.1 p.2.1 p.2.2)
      {p | 3 < p.1.re ∧ 3 < p.2.1.re ∧ 3/2 < p.2.2.re} := by
  let f := fun (i : CRTAbsoluteSeries.ExteriorIndex R.A) (p : ℂ × ℂ × ℂ) =>
    NormalizedProbe.weightedSeparatedSummand R.probe (principalFrequency R, i) p.1 p.2.1 p.2.2
  have hsum := (NormalizedProbe.separatedSeriesMajorant_summable R.probe 3 3 (3/2)
    (by norm_num) (by norm_num) (by norm_num)).comp_injective
      (show Function.Injective (fun i : CRTAbsoluteSeries.ExteriorIndex R.A => (principalFrequency R,i)) from
        fun _ _ h => congrArg Prod.snd h)
  have hc : ContinuousOn (fun p => ∑' i, f i p)
      {p : ℂ × ℂ × ℂ | 3 < p.1.re ∧ 3 < p.2.1.re ∧ 3/2 < p.2.2.re} := by
    refine continuousOn_tsum ?_ hsum ?_
    · intro i
      dsimp [f, NormalizedProbe.weightedSeparatedSummand, comparisonEulerPoissonSummand,
        comparisonRealPower]
      fun_prop
    · intro i p hp
      exact (NormalizedProbe.weightedSeparatedSummand_norm_le R.probe (principalFrequency R,i)
        p.1 p.2.1 p.2.2).trans (majorant_antitone R.probe _ hp.1.le hp.2.1.le hp.2.2.le)
  convert hc using 1
  funext p
  simp only [f, NormalizedProbe.weightedSeparatedSummand, principalFrequency,
    FiniteTransform.exteriorNorm, FiniteTransform.Residue, Ideal.span_singleton_one]
  haveI : Subsingleton (R.A.R.toSubring ⧸ (⊤ : Ideal R.A.R.toSubring)) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  simp [comparisonRealPower, separatedSeries, NormalizedProbe.principalSeparatedMellinSeries,
    NormalizedProbe.separatedMellinSeries, comparisonEulerPoissonSeries]

private theorem L_continuous (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (hs : 1 < s.re) : ContinuousAt R.L s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_compl_singleton)
  have hh : s ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    ⟨by linarith, by intro h; simp [h] at hs⟩
  have hc := (R.continuation.L_holo.differentiableAt (hopen.mem_nhds hh)).continuousAt
  unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
  apply hc.mul
  apply Continuous.continuousAt
  apply continuous_finsetProd
  intro v hv
  unfold comparisonRealPower
  fun_prop

theorem initial_line_euler
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (ξ w z : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries R (principalFrequency R) ξ w z =
      (R.L (6 * z) * R.L w / R.L ξ) * correction R C U ξ w z := by
  let p : ℂ × ℂ × ℂ := (ξ,w,z)
  let q : ℝ → ℂ × ℂ × ℂ := fun t => (ξ + (t : ℂ), w + (t : ℂ), z + (t : ℂ))
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hlim : Tendsto q (𝓝[>] 0) (𝓝 p) := by
    convert hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp [q,p]
  have hopen : IsOpen {p : ℂ × ℂ × ℂ | 3 < p.1.re ∧ 3 < p.2.1.re ∧ 3/2 < p.2.2.re} := by
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))))
  have hp : p ∈ {p : ℂ × ℂ × ℂ | 3 < p.1.re ∧ 3 < p.2.1.re ∧ 3/2 < p.2.2.re} := by
    dsimp [p]; rw [hξ,hw,hz]; norm_num
  have hc := (row_continuous R p hp).continuousAt (hopen.mem_nhds hp)
  have hl : ContinuousAt (fun p : ℂ × ℂ × ℂ => R.L p.1) p :=
    (L_continuous R ξ (by linarith)).comp continuous_fst.continuousAt
  have h6 : ContinuousAt (fun p : ℂ × ℂ × ℂ => R.L (6*p.2.2)) p :=
    (L_continuous R (6*z) (by norm_num [hz])).comp (f := fun p : ℂ × ℂ × ℂ => 6*p.2.2) (by fun_prop)
  have hwc : ContinuousAt (fun p : ℂ × ℂ × ℂ => R.L p.2.1) p :=
    (L_continuous R w (by linarith)).comp (by fun_prop)
  have hOmega : p ∈ CorrectionFactors.Omega := by
    apply Or.inl
    dsimp [p,CorrectionFactors.omegaFirst]
    rw [hξ,hw,hz]; norm_num
  have hh : ContinuousOn (fun x : ℂ × ℂ × ℂ => correction R C U x.1 x.2.1 x.2.2)
      CorrectionFactors.Omega := by
    exact continuousOn_iff_continuous_restrict.mpr (CorrectionFactors.continuous_H_u C U)
  have hhc := (hh p hOmega).continuousAt (CorrectionFactors.isOpen_Omega.mem_nhds hOmega)
  have heq : separatedSeries R (principalFrequency R) ξ w z * R.L ξ =
      (R.L (6*z) * R.L w) * correction R C U ξ w z := by
    apply tendsto_nhds_unique ((hc.mul hl).tendsto.comp hlim)
    apply (((h6.mul hwc).mul hhc).tendsto.comp hlim).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    exact (euler_open R C hC U hU _ _ _
      (by simp [q,hξ]; linarith) (by simp [q,hw]; linarith)
      (by simp [q,hz]; linarith)).symm
  have hne : R.L ξ ≠ 0 := by
    rw [L_eq_zeta R ξ (by linarith)]
    simpa only [ExteriorIdealEuler.summand, one_mul, InitialSeparatedEuler.zetaS] using
      (ExteriorIdealEuler.exterior_ideal_euler _
        (ExteriorIdealEuler.constant_one_isCoefficient R.A.cS) ξ (by linarith)).2.2.1
  apply (mul_right_cancel₀ hne)
  rw [heq]
  field_simp

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
