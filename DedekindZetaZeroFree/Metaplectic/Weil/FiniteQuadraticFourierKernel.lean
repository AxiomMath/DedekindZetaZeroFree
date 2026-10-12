module

public import DedekindZetaZeroFree.Metaplectic.Weil.Finite.OscillatoryIntegralStabilization
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.BallVolumesAndCovolumes

@[expose] public section

namespace DedekindZetaZeroFree.SArithmeticData

open NumberField IsDedekindDomain MeasureTheory Set Filter
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]

private theorem rationalPadicCharacter_locallyConstant (p : Nat.Primes) :
    IsLocallyConstant (rationalPadicCharacter p : ℚ_[p] → Circle) := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  have hopen : IsOpen (Set.range (fun z : ℤ_[p] => (z : ℚ_[p]))) :=
    PadicInt.isOpenEmbedding_coe.isOpen_range
  have hzero : (0 : ℚ_[p]) ∈ Set.range (fun z : ℤ_[p] => (z : ℚ_[p])) :=
    ⟨0, rfl⟩
  have h := ((continuous_id.sub continuous_const :
    Continuous (fun y : ℚ_[p] => y - x)).isOpen_preimage _ hopen).mem_nhds
      (show x - x ∈ Set.range (fun z : ℤ_[p] => (z : ℚ_[p])) by simpa using hzero)
  change ∀ᶠ y in nhds x, y - x ∈ Set.range (fun z : ℤ_[p] => (z : ℚ_[p])) at h
  filter_upwards [h] with y hy
  have heq := (rationalPadicCharacter_eq_one_iff p (y - x)).2 hy
  rw [AddChar.map_sub_eq_div] at heq
  exact div_eq_one.mp heq

private theorem localTraceCharacter_locallyConstant
    (v : HeightOneSpectrum (𝓞 F)) :
    IsLocallyConstant (ResidueTrace.localTraceCharacter v : v.adicCompletion F → Circle) := by
  letI : Fact (ResidueTrace.rationalPrimeBelow v).1.Prime :=
    ⟨(ResidueTrace.rationalPrimeBelow v).2⟩
  letI := (ResidueTrace.baseEmbedding v).toAlgebra
  letI := ResidueTrace.localTrace_finite v
  letI : ContinuousSMul ℚ_[ResidueTrace.rationalPrimeBelow v] (v.adicCompletion F) := by
    constructor
    change Continuous (fun x : ℚ_[ResidueTrace.rationalPrimeBelow v] × v.adicCompletion F =>
      ResidueTrace.baseEmbedding v x.1 * x.2)
    exact ((ResidueTrace.baseEmbedding_spec v).1.comp continuous_fst).mul continuous_snd
  exact (rationalPadicCharacter_locallyConstant (ResidueTrace.rationalPrimeBelow v)).comp_continuous
    (Algebra.trace ℚ_[ResidueTrace.rationalPrimeBelow v]
      (v.adicCompletion F)).continuous_of_finiteDimensional

 theorem localTraceCharacter_exists_ne_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : v.adicCompletion F, ResidueTrace.localTraceCharacter v x ≠ 1 := by
  letI := (ResidueTrace.baseEmbedding v).toAlgebra
  letI := ResidueTrace.localTrace_finite v
  obtain ⟨x, hx⟩ := Algebra.trace_surjective ℚ_[ResidueTrace.rationalPrimeBelow v]
    (v.adicCompletion F)
    (((ResidueTrace.rationalPrimeBelow v).1 : ℚ)⁻¹ : ℚ_[ResidueTrace.rationalPrimeBelow v])
  refine ⟨x, ?_⟩
  have h : ResidueTrace.localTraceCharacter v x =
      rationalPadicCharacter (ResidueTrace.rationalPrimeBelow v)
        (Algebra.trace ℚ_[ResidueTrace.rationalPrimeBelow v]
          (v.adicCompletion F) x) := rfl
  rw [h, hx]
  exact rationalPadicCharacter_inv_prime_ne_one _

private theorem finiteKernel_compact_support_periods {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    (φ : G → ℂ) (hlocal : IsLocallyConstant φ) (hsupport : HasCompactSupport φ) :
    ∃ U : AddSubgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ∀ x, φ (u + x) = φ x := by
  let U : AddSubgroup G :=
    { carrier := {u | ∀ x, φ (u + x) = φ x}
      zero_mem' := by simp
      add_mem' := by
        intro u v hu hv x
        rw [add_assoc, hu, hv]
      neg_mem' := by
        intro u hu x
        simpa using (hu (-u + x)).symm }
  have hn : IsOpen {p : G × G | φ (p.1 + p.2) = φ p.2} := by
    exact ((hlocal.comp_continuous (continuous_fst.add continuous_snd)).prodMk
      (hlocal.comp_continuous continuous_snd)) {q : ℂ × ℂ | q.1 = q.2}
  obtain ⟨V, W, hVo, hWo, h0V, hKW, hVW⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : G))) hsupport.isCompact hn
      (by intro p hp; change φ (p.1 + p.2) = φ p.2; rw [show p.1 = 0 from hp.1, zero_add])
  have h0 : (0 : G) ∈ V := h0V (by simp)
  have hN : V ∩ (fun u : G => -u) ⁻¹' V ∈ 𝓝 (0 : G) :=
    (hVo.inter (hVo.preimage continuous_neg)).mem_nhds (by simpa using And.intro h0 h0)
  have hNU : V ∩ (fun u : G => -u) ⁻¹' V ⊆ (U : Set G) := by
    intro u hu x
    by_cases hx : φ x = 0
    · by_cases hux : φ (u + x) = 0
      · rw [hx, hux]
      · have hK : u + x ∈ tsupport φ := subset_closure hux
        have heq := hVW (show (-u, u + x) ∈ V ×ˢ W from ⟨hu.2, hKW hK⟩)
        simpa using heq.symm
    · exact hVW (show (u, x) ∈ V ×ˢ W from ⟨hu.1, hKW (subset_closure hx)⟩)
  exact ⟨U, U.isOpen_of_mem_nhds (Filter.mem_of_superset hN hNU), fun _ hu => hu⟩

theorem finiteTraceFourier_bruhat (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f ∧ HasCompactSupport f) :
    IsLocallyConstant (A.finiteTraceFourier v f) ∧
      HasCompactSupport (A.finiteTraceFourier v f) := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  letI : (A.finiteTraceHaar v).IsAddLeftInvariant := by
    unfold finiteTraceHaar
    infer_instance
  have hχ := ResidueTrace.continuous_localTraceCharacter v
  have he := localTraceCharacter_locallyConstant v
  constructor
  · have ho : IsOpen {p : v.adicCompletion F × v.adicCompletion F |
        ResidueTrace.localTraceCharacter v (-p.1 * p.2) = 1} :=
      (he.comp_continuous (continuous_fst.neg.mul continuous_snd)) {1}
    obtain ⟨V, W, hVo, hWo, hKV, h0W, hVW⟩ :=
      generalized_tube_lemma hf.2.isCompact (isCompact_singleton (x := (0 : v.adicCompletion F))) ho
        (by intro p hp; simp only [Set.mem_setOf_eq, show p.2 = 0 from hp.2, mul_zero, AddChar.map_zero_eq_one])
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro y
    have hn : {z : v.adicCompletion F | z - y ∈ W} ∈ 𝓝 y :=
      (hWo.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simpa using h0W (by simp : (0 : v.adicCompletion F) ∈ ({0} : Set _)))
    filter_upwards [hn] with z hz
    unfold finiteTraceFourier
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : f x = 0
    · simp [hx]
    · have hp := hVW (show (x, z - y) ∈ V ×ˢ W from ⟨hKV (subset_tsupport f hx), hz⟩)
      change ResidueTrace.localTraceCharacter v (-x * (z - y)) = 1 at hp
      have hxy : -x * z = -x * y + -x * (z - y) := by ring
      rw [hxy, AddChar.map_add_eq_mul, hp, mul_one]
  · obtain ⟨U, hopen, hperiod⟩ := finiteKernel_compact_support_periods f hf.1 hf.2
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 U.zero_mem
    obtain ⟨t, ht⟩ := localTraceCharacter_exists_ne_one v
    have hc : IsClosed {y : v.adicCompletion F | ∀ u ∈ U,
        (ResidueTrace.localTraceCharacter v (-u * y) : ℂ) = 1} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun u => isClosed_iInter fun _ => ?_
      exact isClosed_eq ((continuous_subtype_val.comp hχ).comp
        (continuous_const.mul continuous_id)) continuous_const
    have hb : {y : v.adicCompletion F | ∀ u ∈ U,
        (ResidueTrace.localTraceCharacter v (-u * y) : ℂ) = 1} ⊆
        Metric.closedBall 0 (‖t‖ / ε) := by
      intro y hy
      simp only [Metric.mem_closedBall, dist_zero_right]
      by_contra! hlarge
      have hyv : y ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hlarge
        exact (not_lt_of_ge (div_nonneg (norm_nonneg _) hε.le)) hlarge
      have hsmall : ‖-t / y‖ < ε := by
        rw [norm_div, norm_neg]
        exact (div_lt_iff₀ (norm_pos_iff.mpr hyv)).mpr
          (by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlarge)
      have hu : -t / y ∈ U := hball (by simpa using hsmall)
      have hp := hy _ hu
      simp only [neg_div, neg_neg, div_mul_cancel₀ _ hyv] at hp
      exact ht (Circle.coe_injective (by simpa using hp))
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : v.adicCompletion F) (‖t‖ / ε)).of_isClosed_subset hc hb)
    intro y hy u hu
    by_contra hne
    have hi := integral_add_left_eq_self (μ := A.finiteTraceHaar v)
      (fun x : v.adicCompletion F => f x * (ResidueTrace.localTraceCharacter v (-x * y) : ℂ)) u
    have hphase (x : v.adicCompletion F) :
        f (u + x) * (ResidueTrace.localTraceCharacter v (-(u + x) * y) : ℂ) =
          (ResidueTrace.localTraceCharacter v (-u * y) : ℂ) *
            (f x * (ResidueTrace.localTraceCharacter v (-x * y) : ℂ)) := by
      rw [hperiod u hu x, neg_add, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    simp_rw [hphase] at hi
    rw [integral_const_mul] at hi
    change (ResidueTrace.localTraceCharacter v (-u * y) : ℂ) *
      A.finiteTraceFourier v f y = A.finiteTraceFourier v f y at hi
    exact hne ((mul_eq_right₀ hy).mp hi)

private lemma finiteKernel_traceHaar (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) :
    (A.finiteTraceHaar v).IsAddHaarMeasure := by
  let K := v.adicCompletion F
  let μ : Measure K := Measure.addHaar
  have hp : 0 < μ {x | ‖x‖ ≤ (1 : ℝ)} := by
    apply IsOpen.measure_pos
    · simpa [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero
    · exact ⟨0, by simp⟩
  have hf : μ {x | ‖x‖ ≤ (1 : ℝ)} ≠ ⊤ := by
    have hc : IsCompact {x : K | ‖x‖ ≤ (1 : ℝ)} := by
      simpa [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : K) (1 : ℝ)
    exact hc.measure_lt_top.ne
  apply Measure.IsAddHaarMeasure.smul μ
  · exact ENNReal.div_ne_zero.mpr ⟨by simpa using PoissonS.integerVolume_pos F v, hf⟩
  · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top hp.ne'

private lemma finiteKernel_cutoff_exhaust (v : HeightOneSpectrum (𝓞 F)) (K : Set (v.adicCompletion F))
    (hK : IsCompact K) : ∀ᶠ n : ℕ in atTop, K ⊆ exteriorQuadraticCutoff v n := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : v.adicCompletion F)
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hq).eventually_ge_atTop R] with n hn
  intro x hx
  exact (show ‖x‖ ≤ R from by simpa using hR hx).trans hn

private lemma finiteKernel_translate_ball {K : Type*} [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddLeftInvariant]
    (R : ℝ) (t : K) (ht : ‖t‖ ≤ R) (g : K → ℂ) :
    (∫ x in Metric.closedBall 0 R, g (x - t) ∂μ) = ∫ x in Metric.closedBall 0 R, g x ∂μ := by
  have hm (x : K) : x - t ∈ Metric.closedBall 0 R ↔ x ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hx
      have := (IsUltrametricDist.norm_add_le_max (x - t) t).trans (max_le hx ht)
      simpa using this
    · intro hx
      simpa only [sub_eq_add_neg] using (IsUltrametricDist.norm_add_le_max x (-t)).trans (max_le hx (by simpa using ht))
  have hi := integral_add_left_eq_self (μ := μ)
    ((Metric.closedBall 0 R).indicator g) (-t)
  have he (x : K) : (Metric.closedBall 0 R).indicator g (-t + x) =
      (Metric.closedBall 0 R).indicator (fun x => g (x - t)) x := by
    by_cases hx : x ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem (by simpa [sub_eq_add_neg, add_comm] using (hm x).mpr hx),
        Set.indicator_of_mem hx]
      congr 1; abel
    · rw [Set.indicator_of_notMem (by simpa [sub_eq_add_neg, add_comm] using mt (hm x).mp hx),
        Set.indicator_of_notMem hx]
  simp_rw [he] at hi
  simpa only [integral_indicator measurableSet_closedBall] using hi

theorem finiteQuadraticCutoff_linear_eventually (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (K : Set (v.adicCompletion F)) (hK : IsCompact K) :
    ∀ᶠ n : ℕ in atTop, ∀ b ∈ K,
      (∫ x in exteriorQuadraticCutoff v n,
        (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * x^2 - b*x) : ℂ)
          ∂A.finiteTraceHaar v) =
        A.finiteOscillatoryValue v a *
          (ResidueTrace.localTraceCharacter v (-b^2/(4*(a : v.adicCompletion F))) : ℂ) := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  letI : (A.finiteTraceHaar v).IsAddHaarMeasure := finiteKernel_traceHaar A v
  have ha : (a : v.adicCompletion F) ≠ 0 := a.ne_zero
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by exact_mod_cast (two_ne_zero : (2 : F) ≠ 0)
  have h4 : (4 : v.adicCompletion F) ≠ 0 := by exact_mod_cast (show (4 : F) ≠ 0 by norm_num)
  have hs := finiteKernel_cutoff_exhaust v ((fun b : v.adicCompletion F => b/(2*(a : v.adicCompletion F))) '' K)
    (hK.image (continuous_id.div_const _))
  filter_upwards [hs, A.finiteOscillatoryIntegral_eventually_eq_value v a] with n hn hv b hb
  have ht := hn (mem_image_of_mem _ hb)
  have he (x : v.adicCompletion F) : (a : v.adicCompletion F) * x^2 - b*x =
      (a : v.adicCompletion F) * (x-b/(2*(a : v.adicCompletion F)))^2 +
        (-b^2/(4*(a : v.adicCompletion F))) := by field_simp; ring
  simp_rw [he, AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [integral_mul_const]
  have hbball : exteriorQuadraticCutoff v n = Metric.closedBall 0 ((Ideal.absNorm v.asIdeal : ℝ)^n) := by
    ext x; simp [exteriorQuadraticCutoff, Metric.mem_closedBall, dist_zero_right]
  rw [hbball]
  have hi := finiteKernel_translate_ball (A.finiteTraceHaar v) _ (b/(2*(a : v.adicCompletion F))) ht
    (fun x => (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F)*x^2) : ℂ))
  rw [hi]
  unfold finiteOscillatoryIntegral at hv
  rw [hbball] at hv
  rw [hv]

private lemma finiteKernel_compact_fubini (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f ∧ HasCompactSupport f) (y : v.adicCompletion F) :
    A.finiteTraceFourier v (A.finiteQuadraticMultiplier v (a : v.adicCompletion F)
      (A.finiteTraceFourier v f)) y =
    A.finiteOscillatoryValue v a * ∫ z, f z *
      (ResidueTrace.localTraceCharacter v (-(y+z)^2/(4*(a : v.adicCompletion F))) : ℂ)
      ∂A.finiteTraceHaar v := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  letI : (A.finiteTraceHaar v).IsAddHaarMeasure := finiteKernel_traceHaar A v
  have hF := A.finiteTraceFourier_bruhat v f hf
  obtain ⟨n, hn, hs⟩ := ((finiteKernel_cutoff_exhaust v _ hF.2.isCompact).and
    (A.finiteQuadraticCutoff_linear_eventually v a ((fun z => y+z) '' tsupport f)
      (hf.2.isCompact.image (continuous_const.add continuous_id)))).exists
  let B := exteriorQuadraticCutoff v n
  have hB : IsCompact B := by
    simpa [B, exteriorQuadraticCutoff, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : v.adicCompletion F) ((Ideal.absNorm v.asIdeal : ℝ)^n)
  have hmB : MeasurableSet B := hB.measurableSet
  let μ := A.finiteTraceHaar v
  letI : IsFiniteMeasure (μ.restrict B) := ⟨by simpa using hB.measure_lt_top (μ := μ)⟩
  let g : v.adicCompletion F → v.adicCompletion F → ℂ := fun x z =>
    f z * (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F)*x^2 - (y+z)*x) : ℂ)
  have hg : Integrable (Function.uncurry g) ((μ.restrict B).prod μ) := by
    have hcont : Continuous (Function.uncurry g) := by
      exact (hf.1.continuous.comp continuous_snd).mul
        (continuous_subtype_val.comp ((ResidueTrace.continuous_localTraceCharacter v).comp
          ((continuous_const.mul (continuous_fst.pow 2)).sub
            ((continuous_const.add continuous_snd).mul continuous_fst))))
    have hfint : Integrable f μ := hf.1.continuous.integrable_of_hasCompactSupport hf.2
    have hi := (integrable_const (1 : ℂ) : Integrable (fun _ : v.adicCompletion F => (1 : ℂ)) (μ.restrict B)).mul_prod hfint
    have hir := hi.norm
    apply hir.mono' hcont.aestronglyMeasurable
    filter_upwards [] with p
    simp [g, Function.uncurry, norm_mul]
  have hswap := integral_integral_swap hg
  have hphase (x z : v.adicCompletion F) :
      g x z = (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F)*x^2) : ℂ) *
        (f z * (ResidueTrace.localTraceCharacter v (-z*x) : ℂ)) *
        (ResidueTrace.localTraceCharacter v (-x*y) : ℂ) := by
    have he : (a : v.adicCompletion F)*x^2 - (y+z)*x =
      (a : v.adicCompletion F)*x^2 + (-z*x) + (-x*y) := by ring
    simp only [g, he, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have hout : A.finiteTraceFourier v
      (A.finiteQuadraticMultiplier v (a : v.adicCompletion F) (A.finiteTraceFourier v f)) y =
      ∫ x in B, ∫ z, g x z ∂μ ∂μ := by
    unfold finiteTraceFourier finiteQuadraticMultiplier
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (fun x hx => ?_)]
    · apply integral_congr_ae
      filter_upwards [] with x
      simp_rw [hphase]
      rw [integral_mul_const, integral_const_mul]
    · have hz : A.finiteTraceFourier v f x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun hxS => hx (hn hxS)
      simp only [finiteTraceFourier] at hz
      simpa only [hz, mul_zero, zero_mul] using (show (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F)*x^2) : ℂ) *
        (∫ z, f z * (ResidueTrace.localTraceCharacter v (-z*x) : ℂ) ∂μ) *
        (ResidueTrace.localTraceCharacter v (-x*y) : ℂ) = 0 by rw [hz]; simp)
  rw [hout, hswap]
  have heq : (∫ z, ∫ x in B, g x z ∂μ ∂μ) = ∫ z, f z *
      (A.finiteOscillatoryValue v a *
        (ResidueTrace.localTraceCharacter v (-(y+z)^2/(4*(a : v.adicCompletion F))) : ℂ)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : f z = 0
    · simp [g, hz]
    · simp only [g, integral_const_mul]
      rw [hs (y+z) (mem_image_of_mem _ (subset_tsupport f hz))]
  rw [heq]
  simp_rw [mul_left_comm (f _) (A.finiteOscillatoryValue v a)]
  rw [integral_const_mul]

theorem finiteTraceFourier_quadratic_kernel (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f ∧ HasCompactSupport f)
    (y : v.adicCompletion F) :
    A.finiteTraceFourier v
        (A.finiteQuadraticMultiplier v (a : v.adicCompletion F)
          (A.finiteTraceFourier v f)) y =
      A.finiteGamma v a *
        (↑(Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖)⁻¹ : ℂ) *
        (ResidueTrace.localTraceCharacter v
          (-y ^ 2 / (4 * (a : v.adicCompletion F))) : ℂ) *
        A.finiteTraceFourier v
          (A.finiteQuadraticMultiplier v
            (-1 / (4 * (a : v.adicCompletion F))) f)
          (y / (2 * (a : v.adicCompletion F))) := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  rw [finiteKernel_compact_fubini A v a f hf y]
  have ha : (a : v.adicCompletion F) ≠ 0 := a.ne_zero
  have he (z : v.adicCompletion F) : -(y+z)^2/(4*(a : v.adicCompletion F)) =
      -y^2/(4*(a : v.adicCompletion F)) +
      (-1/(4*(a : v.adicCompletion F))) * z^2 + (-z)*(y/(2*(a : v.adicCompletion F))) := by
    field_simp; ring
  simp_rw [he, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hi : (∫ z, f z *
      (((ResidueTrace.localTraceCharacter v (-y^2/(4*(a : v.adicCompletion F))) : ℂ) *
        (ResidueTrace.localTraceCharacter v ((-1/(4*(a : v.adicCompletion F)))*z^2) : ℂ)) *
        (ResidueTrace.localTraceCharacter v ((-z)*(y/(2*(a : v.adicCompletion F)))) : ℂ)) ∂A.finiteTraceHaar v) =
      (ResidueTrace.localTraceCharacter v (-y^2/(4*(a : v.adicCompletion F))) : ℂ) *
        A.finiteTraceFourier v (A.finiteQuadraticMultiplier v (-1/(4*(a : v.adicCompletion F))) f)
          (y/(2*(a : v.adicCompletion F))) := by
    unfold finiteTraceFourier finiteQuadraticMultiplier
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [hi]
  simp only [finiteOscillatoryValue, div_eq_mul_inv, Complex.ofReal_inv]
  ring

theorem finiteTraceFourier_quadratic_operator (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f ∧ HasCompactSupport f) :
    A.finiteTraceFourier v
        (A.finiteQuadraticMultiplier v (a : v.adicCompletion F)
          (A.finiteTraceFourier v f)) =
      fun y => A.finiteGamma v a *
        (↑(Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖)⁻¹ : ℂ) *
        A.finiteQuadraticMultiplier v
          (-1 / (4 * (a : v.adicCompletion F)))
          (A.finiteDilation v (1 / (2 * (a : v.adicCompletion F)))
            (A.finiteTraceFourier v
              (A.finiteQuadraticMultiplier v
                (-1 / (4 * (a : v.adicCompletion F))) f))) y := by
  funext y
  simpa only [finiteQuadraticMultiplier, finiteDilation, div_eq_mul_inv,
    neg_mul, mul_neg, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    A.finiteTraceFourier_quadratic_kernel v a f hf y

end DedekindZetaZeroFree.SArithmeticData
