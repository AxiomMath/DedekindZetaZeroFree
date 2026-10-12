module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.InitialFrequencyDecomposition
public import DedekindZetaZeroFree.Moments.Principal.FixedMellinWeightErrorEstimates
public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
open MeasureTheory Filter
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private lemma principal_E_reflection (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (η : RayClassCharacter F m) (D : PrincipalRayHeckeData F m η) :
    ∀ s, D.E s = D.E (1-s) := by
  have he : ∀ s : ℂ, 0 < s.re → s ≠ 1 → D.E s = s*(s-1)*D.Λ s := by
    intro s hs hs1
    rw [D.E_eq s hs, D.regularized s hs hs1, D.completed s hs hs1]
    ring
  have hf : Differentiable ℂ (fun s : ℂ => D.E (1-s)) :=
    D.E_entire.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have eqn := (D.E_entire.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ (1/2 : ℂ))
  have hn : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ nhds (1/2 : ℂ) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    · norm_num
  have hh : D.E =ᶠ[nhds (1/2 : ℂ)] (fun s => D.E (1-s)) := by
    filter_upwards [hn] with s hs
    have hs0 : s ≠ 0 := by intro h; subst s; simp at hs
    have hs1 : s ≠ 1 := by intro h; subst s; simp at hs
    have ht : 0 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hs.2]
    have ht1 : 1-s ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    rw [he s hs.1 hs1, he (1-s) ht ht1, D.reflection s hs0 hs1]
    ring
  intro s
  exact eqn hh (Set.mem_univ s)

private lemma principal_prefactor (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (s : ℂ) :
    s * ((heckeConductorScale F m : ℂ) ^ (-s / 2) *
      (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
      ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1)) =
    heckeReciprocalCompletionFactor F m s := by
  have hr := one_le_nrComplexPlaces_of_totallyComplex F hF
  have hg : (Complex.Gammaℂ s)⁻¹ =
      s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s+1))⁻¹ := by
    simp only [Complex.Gammaℂ_def, mul_inv_rev]
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
    have hp : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hc : (2 * (Real.pi : ℂ)) ^ (-(s+1)) =
        (2 * (Real.pi : ℂ)) ^ (-s) * (2 * (Real.pi : ℂ))⁻¹ := by
      rw [show -(s+1) = -s + (-1 : ℂ) by ring, Complex.cpow_add _ _ hp]
      simp only [Complex.cpow_neg_one, mul_inv_rev]
    rw [hc]
    push_cast
    field_simp
  unfold heckeReciprocalCompletionFactor
  conv_rhs => rw [← Nat.sub_add_cancel hr, pow_succ]
  rw [hg]
  ring

private lemma completion_ratio_norm (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (δ : ℝ) (s : ℂ) (hs : s.re = -δ) :
    ‖heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)‖ =
      heckeConductorScale F m ^ ((1:ℝ)/2+δ) *
      ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ^
        NumberField.InfinitePlace.nrComplexPlaces F := by
  have hQ : 0 < heckeConductorScale F m := lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F m hm)
  have hc : (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) =
      (heckeConductorScale F m : ℂ) := by unfold heckeConductorScale; rw [Complex.ofReal_mul]; norm_cast
  unfold heckeReciprocalCompletionFactor heckeCompletionFactor
  rw [hc]
  simp only [norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  rw [show (-s/2).re = δ/2 by simp [hs],
    show ((1-s)/2).re = (1+δ)/2 by simp [hs]]
  rw [show (1:ℝ)/2+δ = δ/2 + (1+δ)/2 by ring, Real.rpow_add hQ, mul_pow]
  ring

private lemma principal_left_formula (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (η : RayClassCharacter F m) (D : PrincipalRayHeckeData F m η)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hs : s.re = -δ) :
    principalHeckeEntireRegularization F m η D s =
      (s-1) * (heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)) * D.L (1-s) := by
  have ht : 0 < (1-s).re := by simp [hs]; linarith
  have ht1 : 1-s ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp [hs] at hr
    linarith
  rw [principalHeckeEntireRegularization, principal_E_reflection F m η D s,
    D.E_eq (1-s) ht, D.regularized (1-s) ht ht1]
  have hp := principal_prefactor F hF m s
  linear_combination (s-1) * heckeCompletionFactor F m (1-s) * D.L (1-s) * hp

private lemma left_ratio_bound (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hb : ∀ s : ℂ, s.re = -δ → ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K*(2+|s.im|)^2)
    (s : ℂ) (hs : s.re = -δ) :
    ‖heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)‖ ≤
      ((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * K ^ NumberField.InfinitePlace.nrComplexPlaces F *
      (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ) * (2+|s.im|) ^ (2*NumberField.InfinitePlace.nrComplexPlaces F) := by
  rw [completion_ratio_norm F m hm δ s hs]
  have hA : 0 ≤ ((|NumberField.discr F| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (NumberField.discr F)
  rw [heckeConductorScale, Real.mul_rpow hA (Nat.cast_nonneg _)]
  have hx := pow_le_pow_left₀ (norm_nonneg _) (hb s hs) (NumberField.InfinitePlace.nrComplexPlaces F)
  calc
    _ ≤ (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ)) *
          (K*(2+|s.im|)^2)^NumberField.InfinitePlace.nrComplexPlaces F :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

private lemma principal_strip_bound (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m)
    (D : PrincipalRayHeckeData F m η) (δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : 1+δ ≤ s.re) (hs4 : s.re ≤ 4) :
    ‖principalHeckeEntireRegularization F m η D s‖ ≤ 4*idealAbsoluteSum F (1+δ)*(2+|s.im|) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; subst s; simp at hs; linarith
  rw [principalHeckeEntireRegularization_eq F hF m hm η D s hs0 hs1, norm_mul]
  have hb := heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) m hm η s hs (D.L s)
    (D.series s (by linarith))
  have hn : ‖s-1‖ ≤ 4*(2+|s.im|) := by
    calc
      _ ≤ |(s-1).re|+|(s-1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
        rw [abs_of_nonneg (by linarith : 0 ≤ s.re-1)]
        nlinarith [abs_nonneg s.im]
  calc
    _ ≤ (4*(2+|s.im|))*idealAbsoluteSum F (1+δ) :=
      mul_le_mul hn hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

private lemma principal_left_bound (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m) (D : PrincipalRayHeckeData F m η)
    (δ K : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1/10) (hK : 0 ≤ K)
    (hb : ∀ s : ℂ, s.re = -δ → ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K*(2+|s.im|)^2)
    (s : ℂ) (hs : s.re = -δ) :
    ‖principalHeckeEntireRegularization F m η D s‖ ≤
      (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * K ^ NumberField.InfinitePlace.nrComplexPlaces F *
      (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ) * idealAbsoluteSum F (1+δ)) * (2+|s.im|) ^ (2*NumberField.InfinitePlace.nrComplexPlaces F+1) := by
  rw [principal_left_formula F hF m η D δ hδ s hs, norm_mul, norm_mul]
  have hx := left_ratio_bound F m hm δ K hδ hK hb s hs
  have hd := heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) m hm η (1-s)
    (by simp [hs]) (D.L (1-s)) (D.series (1-s) (by simp [hs]; linarith))
  have hn : ‖s-1‖ ≤ 2+|s.im| := by
    calc
      _ ≤ |(s-1).re|+|(s-1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hs]
        rw [abs_of_nonpos (by linarith : -δ-1 ≤ 0)]
        linarith
  calc
    _ ≤ ((2+|s.im|)*(_))*idealAbsoluteSum F (1+δ) :=
      mul_le_mul (mul_le_mul hn hx (norm_nonneg _) (by positivity)) hd (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

private lemma regularization_bound (R : PrincipalMellin.ActualRecipe S η) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, (3 : ℝ)/1000 ≤ s.re → s.re ≤ 4 →
      ‖principalHeckeEntireRegularization F R.A.modulus R.target R.continuation s‖ ≤
        C * (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1) := by
  let m := R.A.modulus
  let D := R.continuation
  have hm : m ≠ ⊥ := R.A.modulus_ne_zero
  have hF := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  let k := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨K, hK, hb⟩ := gammaC_reflected_ratio_left_bound (1/10) (by norm_num) (by norm_num)
  let H := (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+1/10) *
    K ^ NumberField.InfinitePlace.nrComplexPlaces F * (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+1/10) *
    idealAbsoluteSum F (1+1/10))
  let C0 := max H (4 * idealAbsoluteSum F (1+1/10)) + 1
  have hsum : 0 ≤ idealAbsoluteSum F (1+1/10) := by
    unfold idealAbsoluteSum
    exact tsum_nonneg (fun I => by unfold idealAbsoluteWeight; split_ifs <;> positivity)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; linarith [le_max_left H (4 * idealAbsoluteSum F (1+1/10))]
  let Cp := max (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10)) + 1
  have hCp : 0 < Cp := by
    dsimp [Cp]
    have : 0 < 6 ^ k * C0 := by positivity
    linarith [le_max_left (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))]
  have hdiff := principalHeckeEntireRegularization_differentiable F hF m hm R.target D
  obtain ⟨M, B, hM, hB, hgr⟩ :=
    principalHeckeEntireRegularization_quadratic_strip_growth F hF m hm R.target D
      (-(1/10)) (1+1/10) (by norm_num)
  have hPL : ∀ t : ℂ, -(1/10) ≤ t.re ∧ t.re ≤ 1+1/10 →
      ‖principalHeckeEntireRegularization F m R.target D t‖ ≤ 6 ^ k * C0 * (2+|t.im|)^k := by
    apply norm_le_on_closed_strip_of_polynomial_boundary (1/10) (by norm_num) (by norm_num)
      k C0 hC0.le _ hdiff.diffContOnCl
    · exact ⟨M, B, hM, hB, fun t ht => hgr t ht.1.le ht.2.le⟩
    · intro t ht
      rcases ht with ht | ht
      · have hl := principal_left_bound F hF m hm R.target D (1/10) K
          (by norm_num) (by norm_num) hK.le hb t ht
        change ‖principalHeckeEntireRegularization F m R.target D t‖ ≤ H * (2+|t.im|)^k at hl
        exact hl.trans (mul_le_mul_of_nonneg_right
          (by dsimp [C0]; linarith [le_max_left H (4 * idealAbsoluteSum F (1+1/10))])
          (by positivity))
      · have hr := principal_strip_bound F hF m hm R.target D (1/10) (by norm_num) t
          (by rw [ht]) (by rw [ht]; norm_num)
        have hp : 2+|t.im| ≤ (2+|t.im|)^k := by
          simpa using pow_le_pow_right₀ (by linarith [abs_nonneg t.im] : 1 ≤ 2+|t.im|) hk
        exact hr.trans (mul_le_mul
          (by dsimp [C0]; linarith [le_max_right H (4 * idealAbsoluteSum F (1+1/10))])
          hp (by positivity) hC0.le)
  refine ⟨Cp, hCp, ?_⟩
  intro t hlo hhi
  by_cases ht : t.re ≤ 1+1/10
  · exact (hPL t ⟨by linarith, ht⟩).trans (mul_le_mul_of_nonneg_right
      (by dsimp [Cp]; linarith [le_max_left (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))])
      (by positivity))
  · have hr := principal_strip_bound F hF m hm R.target D (1/10) (by norm_num) t
      (by linarith) hhi
    have hp : 2+|t.im| ≤ (2+|t.im|)^k := by
      simpa using pow_le_pow_right₀ (by linarith [abs_nonneg t.im] : 1 ≤ 2+|t.im|) hk
    exact hr.trans (mul_le_mul
      (by dsimp [Cp]; linarith [le_max_right (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))])
      hp (by positivity) hCp.le)

private lemma weight_measurable (R : PrincipalMellin.ActualRecipe S η) : Measurable R.W.M := by
  let A := R.A
  letI : MeasurableSpace (SLocalProduct F A.Sf) := borel _
  letI : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩
  letI : MeasurableSpace (SLocalProduct F A.Sf)ˣ :=
    @Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)
  letI : BorelSpace (SLocalProduct F A.Sf)ˣ := by
    constructor
    change (borel (SLocalProduct F A.Sf)).comap Units.val = borel _
    rw [← borel_comap, ← (ProbeSheet.units_val_isEmbedding A).isInducing.eq_induced]
  letI := ProbeSheet.locallyCompact_G A
  letI := ProbeSheet.secondCountable_G A
  letI : LocallyCompactSpace (SLocalProduct F A.Sf)ˣ :=
    (ProbeSheet.localUnitsContinuous A).symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  letI : SecondCountableTopology (SLocalProduct F A.Sf)ˣ :=
    (ProbeSheet.localUnitsContinuous A).symm.toHomeomorph.secondCountableTopology
  letI := R.probe.multiplicativeHaar
  have hc := ProbeSheetFourierMellinBounds.raw_fourier_continuous A R.probe.finiteTrace
    R.probe.continuousTrace R.probe.additiveMeasure R.probe.additiveHaar
    R.probe.W0 R.probe.annular R.probe.compactSupport
  have hmod : Continuous (ProbeWeight.modulus F A.Sf) := by
    change Continuous (A.norm ∘ (ProbeSheet.localUnitsContinuous A).symm)
    exact (ProbeSheet.continuous_norm A).comp (ProbeSheet.localUnitsContinuous A).symm.continuous
  have hpos : ∀ y : (SLocalProduct F A.Sf)ˣ, 0 < ProbeWeight.modulus F A.Sf y := by
    intro y
    exact ProbeSheet.norm_pos A ((ProbeSheet.localUnitsContinuous A).symm y)
  have hi : Continuous (fun p : ℂ × (SLocalProduct F A.Sf)ˣ =>
      ProbeWeight.fourier F A.Sf R.probe.finiteTrace R.probe.additiveMeasure R.probe.W0 p.2.val *
      (ProbeWeight.modulus F A.Sf p.2 : ℂ) ^ p.1) := by
    apply ((hc.comp Units.continuous_val).comp continuous_snd).mul
    exact (Complex.continuous_ofReal.comp (hmod.comp continuous_snd)).cpow continuous_fst
      (fun p => Complex.ofReal_mem_slitPlane.mpr (hpos p.2))
  exact hi.measurable.stronglyMeasurable.integral_prod_right'.measurable

private lemma weight_decay (R : PrincipalMellin.ActualRecipe S η) :
    comparisonRapidStripDecay R.W.M PrincipalZShift.zLine comparisonZeta₁ := by
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar w
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, hM, hMd, hW, hWd, _⟩
  intro B hB
  obtain ⟨C, hC, hb⟩ := hMd PrincipalZShift.zLine comparisonZeta₁ B
    (by norm_num [PrincipalZShift.zLine])
    (by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta]) hB
  refine ⟨C + 1, by linarith, ?_⟩
  intro z hz
  have hh := hb z.re hz z.im
  rw [Complex.re_add_im] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith)
    (Real.rpow_nonneg (by positivity) _))

theorem error_mellin_measurable (R : PrincipalMellin.ActualRecipe S η) :
    Measurable R.W.M := weight_measurable R

theorem error_mellin_decay (R : PrincipalMellin.ActualRecipe S η) :
    comparisonRapidStripDecay R.W.M PrincipalZShift.zLine comparisonZeta₁ :=
  weight_decay R

theorem error_factor_inputs
    (R : PrincipalMellin.ActualRecipe S η) :
    Measurable R.W.M ∧
      comparisonRapidStripDecay R.W.M PrincipalZShift.zLine comparisonZeta₁ ∧
      (∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ,
        s.re ∈ ({(19 / 20 : ℝ), 6 * comparisonZeta₁,
          6 * PrincipalZShift.zLine} : Set ℝ) →
        ‖R.L s‖ ≤ B * (2 + |s.im|) ^ d) := by
  refine ⟨weight_measurable R, weight_decay R, ?_⟩
  obtain ⟨C, hC, hbound⟩ := regularization_bound R
  let k := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  refine ⟨2000000 * C * 2 ^ R.A.Sf.card, (k : ℝ), by positivity, by positivity, ?_⟩
  intro s hs
  have hlines : s.re = 19 / 20 ∨ s.re = 6 * comparisonZeta₁ ∨
      s.re = 6 * PrincipalZShift.zLine := by simpa only [Set.mem_insert_iff,
        Set.mem_singleton_iff] using hs
  have hlo : (3 : ℝ) / 1000 ≤ s.re := by
    rcases hlines with h | h | h <;>
      norm_num [h, comparisonZeta₁, comparisonDelta, PrincipalZShift.zLine]
  have hhi : s.re ≤ 4 := by
    rcases hlines with h | h | h <;>
      norm_num [h, comparisonZeta₁, comparisonDelta, PrincipalZShift.zLine]
  have hdist : (1 : ℝ) / 2000000 ≤ ‖s - 1‖ := by
    have hr := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at hr
    rcases hlines with h | h | h <;>
      norm_num [h, comparisonZeta₁, comparisonDelta, PrincipalZShift.zLine] at hr ⊢ <;>
      linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hdist
    norm_num at hdist
  have hF := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  have hb := hbound s hlo hhi
  rw [principalHeckeEntireRegularization_eq F hF R.A.modulus R.A.modulus_ne_zero
    R.target R.continuation s (by linarith) hs1, norm_mul] at hb
  have hfull : ‖R.continuation.L s‖ ≤ 2000000 * C * (2 + |s.im|) ^ k := by
    change ‖s - 1‖ * ‖R.continuation.L s‖ ≤ C * (2 + |s.im|) ^ k at hb
    nlinarith [norm_nonneg (R.continuation.L s)]
  have hlocal : ∀ v ∈ R.A.Sf,
      ‖1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 2 := by
    intro v hv
    have hq : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hp : ‖comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 1 := by
      rw [comparisonRealPower, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      apply Real.exp_le_one_iff.mpr
      have hlog := (Real.log_pos hq).le
      have hre : 0 ≤ s.re := by linarith
      nlinarith
    have hc := RayUnitary.ray_character_norm_le_one F R.A.modulus
      R.A.modulus_ne_zero R.target v.asIdeal
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖R.target v.asIdeal *
          comparisonRealPower (idealNorm v.asIdeal) (-s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
        rw [norm_one, norm_mul]
        have hm := mul_le_mul hc hp (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        linarith
      _ = 2 := by norm_num
  have hmask : ‖∏ v ∈ R.A.Sf,
      (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤
      (2 : ℝ) ^ R.A.Sf.card := by
    rw [norm_prod]
    simpa using Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) hlocal
  change ‖R.continuation.L s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤ _
  rw [norm_mul, Real.rpow_natCast]
  calc
    _ ≤ (2000000 * C * (2 + |s.im|) ^ k) * 2 ^ R.A.Sf.card :=
      mul_le_mul hfull hmask (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
