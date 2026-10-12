module

public import DedekindZetaZeroFree.Eisenstein.Continuation.UpperPeriods.CompactInducingSources
public import DedekindZetaZeroFree.Theta.Periods.UpperPeriodLocalContinuation
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedCompactGerm

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation
open MomentSources ThetaExpansion.ChamberPeriods
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent renaming extension_of_compact_period → extension_of_compact_period
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming upper_fiber_eq → upper_fiber_eq
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming compact_additive_representatives → compact_additive_representatives

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem period_of_representative_source (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (g : Group R) {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (q : C(X, KPAdditiveQuotient F)) (hq : Function.Surjective q)
    (L : C(X, ℂ) →L[ℂ] ℂ)
    (hL : ∀ f : C(KPAdditiveQuotient F, ℂ), L (f.comp q) = ∫ y, f y ∂C.sources.dq)
    (Q : ℂ → ℂ) (J : ℂ → C(X, ℂ))
    (hQ : AnalyticOnNhd ℂ Q KPContinuation.spectralDomain) (hQ0 : Q 0 = 1)
    (hJ : MeromorphicOn J KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ x,
      J s x = Q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        C.sources.K (C.sources.flat v) s
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q x)) * g)) :
    ∃ I : ℂ → ℂ, MeromorphicOn I KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → I s = chamberPeriod C v s g) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) C.realization.radius, s ≠ 0 →
        clearedPeriod C v s g = s * I s := by
  letI : IsProbabilityMeasure C.sources.dq := ⟨C.sources.probability⟩
  let Ω := KPContinuation.spectralDomain
  let B := Metric.ball (0 : ℂ) C.realization.radius
  have h0 : (0 : ℂ) ∈ Ω := by norm_num [Ω, KPContinuation.spectralDomain]
  let K : ℂ → C(X, ℂ) := fun s =>
    (localMeromorphicIntegrand C.realization v s g).comp q
  have hK : MeromorphicOn K B := by
    intro z hz
    obtain ⟨n, hn⟩ := localMeromorphicIntegrand_meromorphic C.realization v g z hz
    refine ⟨n, ?_⟩
    exact ((ContinuousMap.compCLM ℂ ℂ q).analyticAt _).comp hn
  have hJK : J =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => Q s • K s) := by
    apply compact_meromorphic_germ_of_evaluation_germs (hJ 0 h0)
      ((hQ 0 h0).meromorphicAt.smul (hK 0 (Metric.mem_ball_self C.realization.radius_pos)))
    intro x
    let a := KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (q x)) * g
    have hjx : MeromorphicOn (fun s => J s x) Ω := by
      intro z hz
      obtain ⟨n, hn⟩ := hJ z hz
      refine ⟨n, ?_⟩
      simpa only [Function.comp_def, map_smul, ContinuousMap.evalCLM_apply] using
        ((ContinuousMap.evalCLM ℂ x).analyticAt _).comp hn
    have he := chamber_identity_germ hjx
      (hQ.meromorphicOn.mul (C.realization.meromorphic v a))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      (by
        intro s hs
        change J s x = Q s * C.realization.E v s a
        rw [hch s hs, C.realization.chamber v s hs]) 0 h0
    filter_upwards [he, nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0 : ℂ) C.realization.radius_pos), self_mem_nhdsWithin]
      with s hs hb hn
    change J s x = Q s * localMeromorphicIntegrand C.realization v s g (q x)
    rw [localMeromorphicIntegrand_apply C.realization v s hb hn]
    exact hs
  let A : ℂ → ℂ := fun s => L (J s) / Q s
  have hA : MeromorphicOn A Ω :=
    (meromorphicOn_observation L J Ω hJ).div hQ.meromorphicOn
  let I := toMeromorphicNFOn A Ω
  have hnear : A =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => CompactPeriod.localPeriod C.realization v s g) := by
    have hQne : ∀ᶠ s in 𝓝 (0 : ℂ), Q s ≠ 0 :=
      (hQ 0 h0).continuousAt.eventually_ne (by rw [hQ0]; exact one_ne_zero)
    filter_upwards [hJK, nhdsWithin_le_nhds hQne, nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0 : ℂ) C.realization.radius_pos)] with s hs hn hb
    dsimp [A]
    rw [hs, map_smul, smul_eq_mul, mul_div_cancel_left₀ _ hn, hL]
    change (∫ y, localMeromorphicIntegrand C.realization v s g y ∂C.sources.dq) = _
    simp only [localMeromorphicIntegrand, ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
    unfold CompactPeriod.localPeriod upper
    simp_rw [clearedIntegrand_apply C.realization v s hb g]
    rw [div_eq_mul_inv, mul_comm]
  refine ⟨I, (meromorphicNFOn_toMeromorphicNFOn _ _).meromorphicOn, ?_, ?_⟩
  · intro s hs
    apply ResidueContinuity.normalized_division_eq_chamber
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      (isOpen_lt continuous_const Complex.continuous_re)
      Q (fun t => L (J t)) (fun t => chamberPeriod C v t g)
      hQ hQ0 h0 (meromorphicOn_observation L J Ω hJ)
      (selected_chamber_period_analytic C v g) ?_ hs
    intro t ht
    let c : KPAdditiveQuotient F → ℂ := fun y => Q t *
      KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        C.sources.K (C.sources.flat v) t
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out y) * g)
    have hc : Continuous c := by
      apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
      exact (J t).continuous.congr (hch t ht)
    let f : C(KPAdditiveQuotient F, ℂ) := ⟨c, hc⟩
    have he : J t = f.comp q := by ext x; exact hch t ht x
    rw [he, hL]
    exact integral_const_mul _ _
  · intro s hs hn
    have hb : MeromorphicOn (fun t => CompactPeriod.localPeriod C.realization v t g) B :=
      CompactPeriod.localPeriod_meromorphic C.realization v g
    have ht0 : meromorphicOrderAt
        (fun t => A t - CompactPeriod.localPeriod C.realization v t g) 0 = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [hnear] with t ht
      exact sub_eq_zero.mpr ht
    have had : MeromorphicOn A B := fun t ht => hA t (C.realization.disc_domain ht)
    have hts := (had.sub hb).meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_ball (0 : ℂ) C.realization.radius).isPreconnected
      (Metric.mem_ball_self C.realization.radius_pos) hs ht0
    have hes : A =ᶠ[𝓝[≠] s] (fun t => CompactPeriod.localPeriod C.realization v t g) := by
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp hts] with t ht
      exact sub_eq_zero.mp ht
    have hba : AnalyticAt ℂ (fun t => CompactPeriod.localPeriod C.realization v t g) s :=
      (selected_cleared_period_analytic C v g s hs).div analyticAt_id hn
    have hid : I s = CompactPeriod.localPeriod C.realization v s g := by
      dsimp [I]
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hA (C.realization.disc_domain hs)]
      have he := (toMeromorphicNFAt_eventuallyEq_nhds_congr hes).eq_of_nhds
      rw [toMeromorphicNFAt_eq_self.mpr hba.meromorphicNFAt] at he
      exact he
    rw [hid]
    exact (CompactPeriod.localPeriod_clears C.realization v s hs hn g).2

theorem native_period_exists (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (g : Group R) :
    ∃ I : ℂ → ℂ, MeromorphicOn I KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → I s = chamberPeriod C v s g) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) C.realization.radius, s ≠ 0 →
        clearedPeriod C v s g = s * I s := by
  letI : IsProbabilityMeasure C.sources.dq := ⟨C.sources.probability⟩
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨X, hX, hqX⟩ := compact_additive_representatives F
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let q : C(X, KPAdditiveQuotient F) :=
    ⟨fun x => QuotientAddGroup.mk x.val,
      QuotientAddGroup.continuous_mk.comp continuous_subtype_val⟩
  have hq : Function.Surjective q := by
    intro y
    have hy : y ∈ (QuotientAddGroup.mk : KPAdeles F → KPAdditiveQuotient F) '' X := by
      rw [hqX]
      exact Set.mem_univ y
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, he⟩
  let j : C(X, Group R) :=
    ⟨fun x => KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x.val * g,
      ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
        F R.A.zeta12 R.A.primitive_zeta12).comp continuous_subtype_val).mul continuous_const⟩
  let D := j '' Set.univ
  have hD : IsCompact D := isCompact_univ.image j.continuous
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let jj : C(X, D) :=
    ⟨fun x => ⟨j x, ⟨x, Set.mem_univ x, rfl⟩⟩, j.continuous.subtype_mk _⟩
  obtain ⟨Q, A, hQ, hQ0, hA, hch⟩ := native_compact_source_exists
    F R.A.zeta12 R.A.primitive_zeta12 D hD C.sources.K C.sources.iwasawa (C.sources.flat v)
  let J : ℂ → C(X, ℂ) := fun s => (A s).comp jj
  have hJ : MeromorphicOn J KPContinuation.spectralDomain := by
    intro z hz
    obtain ⟨n, hn⟩ := hA z hz
    refine ⟨n, ?_⟩
    simpa only [Function.comp_def, map_smul, ContinuousMap.compCLM_apply] using
      ((ContinuousMap.compCLM ℂ ℂ jj).analyticAt _).comp hn
  obtain ⟨L, hL⟩ := extension_of_compact_period q hq C.sources.dq
  apply period_of_representative_source C v g q hq L hL Q J hQ hQ0 hJ
  intro s hs x
  change A s (jj x) = Q s * _
  rw [hch s hs (jj x)]
  congr 1
  exact (upper_fiber_eq F R.A.zeta12 R.A.primitive_zeta12
    (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      C.sources.K (C.sources.flat v) s)
    (KPLiteralExceptionalResidue.ResidueAutomorphy.eisenstein_rational
      F R.A.zeta12 R.A.primitive_zeta12 C.sources.K (C.sources.flat v) s hs) g x.val).symm

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

end
