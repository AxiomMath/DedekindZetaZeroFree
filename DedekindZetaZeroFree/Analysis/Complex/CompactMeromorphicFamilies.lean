module

public import DedekindZetaZeroFree.Theta.Periods.MeromorphicContinuationAndResidues

@[expose] public section

noncomputable section
open scoped Topology
open Filter

namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

theorem compact_family_holomorphic {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → C(X, ℂ))
    (hc : ContinuousOn (fun p : ℂ × X => j p.1 p.2) (O ×ˢ Set.univ))
    (hd : ∀ x : X, DifferentiableOn ℂ (fun z => j z x) O) :
    DifferentiableOn ℂ j O := by
  have hj : ContinuousOn j O := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    let a : O × X → ℂ × X := fun p => (p.1.val,p.2)
    have ha : Continuous a := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact hc.comp_continuous ha (fun p => ⟨p.1.property, Set.mem_univ _⟩)
  intro s hs
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hs)
  let R := r/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall s R ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hrO
  have hcircle : CircleIntegrable j s R :=
    (hj.mono (Metric.sphere_subset_closedBall.trans hclosed)).circleIntegrable hR.le
  let g : ℂ → C(X,ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    circleIntegral (fun z => (z-w)⁻¹ • j z) s R
  have heq : Set.EqOn g j (Metric.ball s R) := by
    intro w hw
    ext x
    let L : C(X,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    have hw' : w ∉ Metric.sphere s |R| := by
      rw [abs_of_pos hR]
      intro hh
      exact (ne_of_lt (Metric.mem_ball.mp hw)) hh
    have hi := hcircle.sub_zpow_smul (-1) hw'
    have hL : L (circleIntegral (fun z => (z-w)⁻¹ • j z) s R) =
        circleIntegral (fun z => (z-w)⁻¹ • j z x) s R := by
      rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm (by simpa using hi.out)]
      simp only [map_smul]
      rfl
    change L ((2 * Real.pi * Complex.I : ℂ)⁻¹ • _) = _
    rw [map_smul, hL]
    exact (((hd x).mono hclosed).mono Metric.closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hg : DifferentiableAt ℂ g s := by
    change DifferentiableAt ℂ (fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      circleIntegral (fun z => (z-w)⁻¹ • j z) s R) s
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := s) hcircle (by
      simpa [abs_of_pos hR] using (ne_of_gt hR).symm)).const_smul
        (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  have he : g =ᶠ[𝓝 s] j :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds s hR) (fun w hw => heq hw)
  exact (hg.congr_of_eventuallyEq he.symm).differentiableWithinAt

theorem meromorphicOn_observation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] ℂ) (j : ℂ → E) (O : Set ℂ) (hj : MeromorphicOn j O) :
    MeromorphicOn (fun s => L (j s)) O := by
  intro z hz
  obtain ⟨n, hn⟩ := hj z hz
  refine ⟨n, ?_⟩
  have ha := (L.analyticAt _).comp hn
  simpa only [Function.comp_def, map_smul] using ha

theorem chamber_identity_germ {e f : ℂ → ℂ} {O : Set ℂ}
    (he : MeromorphicOn e O) (hf : MeromorphicOn f O)
    (hO : IsPreconnected O) (hch : {s : ℂ | (1 / 3 : ℝ) < s.re} ⊆ O)
    (hpin : ∀ s : ℂ, (1 / 3 : ℝ) < s.re → e s = f s)
    (z : ℂ) (hz : z ∈ O) : e =ᶠ[𝓝[≠] z] f := by
  have hopen : IsOpen {s : ℂ | (1 / 3 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {s : ℂ | (1 / 3 : ℝ) < s.re} := by norm_num
  have ht : meromorphicOrderAt (fun s => e s - f s) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds h1)] with s hs
    exact sub_eq_zero.mpr (hpin s hs)
  have ht' := (he.sub hf).meromorphicOrderAt_eq_top_of_isPreconnected hO (hch h1) hz ht
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp ht'] with s hs
  exact sub_eq_zero.mp hs

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem compact_meromorphic_germ_of_evaluation_germs
    {J K : ℂ → C(X, ℂ)} {z : ℂ}
    (hJ : MeromorphicAt J z) (hK : MeromorphicAt K z)
    (he : ∀ x, (fun s => J s x) =ᶠ[𝓝[≠] z] (fun s => K s x)) :
    J =ᶠ[𝓝[≠] z] K := by
  obtain ⟨n, hn⟩ := hJ.sub hK
  let A : ℂ → C(X, ℂ) := fun s => (s-z)^n • (J s - K s)
  have ha : AnalyticAt ℂ A z := hn
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp ha.eventually_analyticAt
  have hA : AnalyticOnNhd ℂ A (Metric.ball z r) := fun s hs => hb hs
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hzA : Set.EqOn A (fun _ => 0) (Metric.ball z r) := by
    intro s hs
    ext x
    have hx : AnalyticOnNhd ℂ (fun t => A t x) (Metric.ball z r) := by
      intro t ht
      exact ((ContinuousMap.evalCLM ℂ x).analyticAt _).comp (hA t ht)
    have hxe : (fun t => A t x) =ᶠ[𝓝[≠] z] (fun _ => 0) := by
      filter_upwards [he x] with t ht
      simp [A, ht]
    have hxe' : (fun t => A t x) =ᶠ[𝓝 z] (fun _ => 0) :=
      ((hx z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        continuousAt_const).mp hxe
    exact hx.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball z r).isPreconnected hz hxe' hs
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr),
    self_mem_nhdsWithin] with s hs hsz
  have hsne : s-z ≠ 0 := sub_ne_zero.mpr hsz
  have hzero : (s-z)^n • (J s-K s) = 0 := hzA hs
  have hdiff : J s-K s = 0 := (smul_eq_zero.mp hzero).resolve_left (pow_ne_zero n hsne)
  exact sub_eq_zero.mp hdiff

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

namespace DedekindZetaZeroFree.ResidueContinuity

theorem normalized_division_eq_chamber
    {Ω V : Set ℂ} (hΩ : IsPreconnected Ω) (hVΩ : V ⊆ Ω) (hV : IsOpen V)
    (q N A : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q Ω) (hq0 : q 0 = 1)
    (h0Ω : (0 : ℂ) ∈ Ω) (hN : MeromorphicOn N Ω) (hA : AnalyticOnNhd ℂ A V)
    (hpin : ∀ s ∈ V, N s = q s * A s) :
    Set.EqOn (toMeromorphicNFOn (fun s => N s / q s) Ω) A V := by
  have hqne : ∀ᶠ s in codiscreteWithin Ω, q s ≠ 0 := by
    rcases hq.eqOn_zero_or_eventually_ne_zero_of_preconnected hΩ with hz | hn
    · have h := hz h0Ω
      simp only [hq0, Pi.zero_apply] at h
      exact (one_ne_zero h).elim
    · exact hn
  have hm : MeromorphicOn (fun s => N s / q s) Ω := hN.div hq.meromorphicOn
  intro z hz
  have he : (fun s => N s / q s) =ᶠ[𝓝[≠] z] A := by
    have hn := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hqne z (hVΩ hz)
    filter_upwards [hn, nhdsWithin_le_nhds (hV.mem_nhds hz)] with s hs hv
    rw [hpin s hv, mul_div_cancel_left₀ _ (hs (hVΩ hv))]
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun s => N s / q s) Ω (hVΩ hz)
  have heNF := (hm.toMeromorphicNFOn_eq_self_on_nhdsNE (hVΩ hz)).trans he
  exact ((hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hA z hz).meromorphicNFAt).mp heNF).eq_of_nhds

end DedekindZetaZeroFree.ResidueContinuity

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualPeriodContinuation

variable {G₀ H J : Type*} [TopologicalSpace G₀] [AddCommGroup H] [Module ℂ H]
variable (D₀ : J → H →ₗ[ℂ] C(G₀, ℂ))

theorem powerSeries_compact_analytic (z₀ : ℂ) (ρ : ℝ) (a : ℕ → H) (f : ℂ → H)
    (ha : KPGlobalEisensteinData.SmoothPowerSeriesOn D₀ z₀ ρ a f)
    (i : KPGlobalEisensteinData.DifferentialCompact G₀ J) :
    AnalyticOnNhd ℂ (fun z => KPGlobalEisensteinData.derivativeRestriction D₀ i (f z))
      (Metric.ball z₀ ρ) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  apply TendstoLocallyUniformlyOn.differentiableOn
    (F := fun M : ℕ => fun z : ℂ => ∑ q ∈ Finset.range M,
      (z - z₀) ^ q • KPGlobalEisensteinData.derivativeRestriction D₀ i (a q))
    (φ := atTop) _ _ Metric.isOpen_ball
  · apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro z hz
    obtain ⟨r, hzr, hrρ⟩ := exists_between (Metric.mem_ball.mp hz)
    have hr : 0 < r := lt_of_le_of_lt dist_nonneg hzr
    refine ⟨Metric.closedBall z₀ r, ?_, ?_⟩
    · exact mem_of_superset (nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hzr))
        Metric.ball_subset_closedBall
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := ha i r hr.le hrρ ε hε
      filter_upwards [eventually_ge_atTop N] with M hM
      intro w hw
      have h := hN M hM w hw
      change ‖KPGlobalEisensteinData.derivativeRestriction D₀ i
        ((∑ q ∈ Finset.range M, (w - z₀) ^ q • a q) - f w)‖ < ε at h
      simpa only [map_sub, map_sum, map_smul, dist_eq_norm, norm_sub_rev] using h
  · exact Eventually.of_forall (fun M => by
      fun_prop)

theorem meromorphic_compact (f : ℂ → H) (O : Set ℂ)
    (hf : KPRankOneContinuation.SmoothMeromorphicOn D₀ f O)
    (i : KPGlobalEisensteinData.DifferentialCompact G₀ J) :
    MeromorphicOn (fun z => KPGlobalEisensteinData.derivativeRestriction D₀ i (f z)) O := by
  intro z₀ hz₀
  obtain ⟨ρ, m, a, cleared, hρ, hb, ha, hc⟩ := hf z₀ hz₀
  have han : AnalyticAt ℂ
      (fun z => KPGlobalEisensteinData.derivativeRestriction D₀ i (cleared z)) z₀ :=
    powerSeries_compact_analytic D₀ z₀ ρ a cleared ha i z₀ (Metric.mem_ball_self hρ)
  have hm : MeromorphicAt
      (fun z => ((z - z₀) ^ m)⁻¹ •
        KPGlobalEisensteinData.derivativeRestriction D₀ i (cleared z)) z₀ :=
    ((((MeromorphicAt.id z₀).sub (MeromorphicAt.const z₀ z₀)).pow m).inv).smul
      han.meromorphicAt
  apply hm.congr
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hρ),
    self_mem_nhdsWithin] with z hz hne
  have hn : z ≠ z₀ := hne
  rw [hc z hz hn, map_smul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero m (sub_ne_zero.mpr hn)), one_smul]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualPeriodContinuation

end
