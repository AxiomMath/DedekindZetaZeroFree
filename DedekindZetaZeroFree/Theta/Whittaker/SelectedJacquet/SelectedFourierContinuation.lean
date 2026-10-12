module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedFourierGerm
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberAnalyticity
public import DedekindZetaZeroFree.Eisenstein.Continuation.UpperPeriods.CompactInducingSources

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory Filter
open CompactPeriodAnalyticity.UpperPeriodContinuation
open DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation
  (exponential_integral_differentiable)
open KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit
open KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
local instance : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem selected_chamber_fourier_analytic (v : R.A.UnitQuotient) (g : Group R) :
    AnalyticOnNhd ℂ (fun s => fourier R Q.dq
      (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s) g)
      {s : ℂ | (1 / 3 : ℝ) < s.re} := by
  let arg : KPAdeles F → Group R := fun x =>
    KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g
  let p := fun x => KPLiteralChamber.iwasawaTriple F R.A.zeta12
    R.A.primitive_zeta12 Q.K Q.iwasawa (arg x)
  let l : KPAdeles F → ℝ := fun x => Real.log
    (((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 (p x).1 : NNReal) : ℝ))
  let c : KPAdeles F → ℂ := fun x =>
    (Q.flat v).val 0 ((p x).1.val * (p x).2.2.val) *
      star (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ)
  have hf (s : ℂ) (x : KPAdeles F) :
      (Q.flat v).val s (arg x) *
        star (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ) =
      Complex.exp (s * (l x : ℂ)) * c x := by
    rw [← KPLiteralChamber.compactExtension_eq_flat F R.A.zeta12
      R.A.primitive_zeta12 Q.K Q.iwasawa (Q.flat v) s (arg x)]
    exact mul_assoc _ _ _
  have hint (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) :
      Integrable (fun x => Complex.exp (s * (l x : ℂ)) * c x)
        (KPAdditiveHaar.adelicMeasure F) := by
    simpa only [← hf] using selected_open_cell_fourier_integrable R Q v s hs g
  have ha := (exponential_integral_differentiable
    (KPAdditiveHaar.adelicMeasure F) l c (1 / 3) hint).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  apply ha.congr (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  dsimp only
  rw [selected_chamber_fourier_unfolding R Q v s hs g]
  exact integral_congr_ae (Eventually.of_forall (fun x => (hf s x).symm))

theorem fourier_of_representative_source (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R)
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (q : C(X, KPAdditiveQuotient F)) (hq : Function.Surjective q)
    (L : C(X, ℂ) →L[ℂ] ℂ)
    (hL : ∀ f : C(KPAdditiveQuotient F, ℂ),
      L (f.comp q) = complexFourierExtraction Q.dq f)
    (b : ℂ → ℂ) (J : ℂ → C(X, ℂ))
    (hb : AnalyticOnNhd ℂ b KPContinuation.spectralDomain) (hb0 : b 0 = 1)
    (hJ : MeromorphicOn J KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ x,
      J s x = b s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        Q.K (Q.flat v) s
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q x)) * g)) :
    ∃ I : ℂ → ℂ, MeromorphicOn I KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → I s = fourier R Q.dq
        (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s) g) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) T.radius, s ≠ 0 →
        fourier R Q.dq (T.cleared v s) g = s * I s := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  let Ω := KPContinuation.spectralDomain
  let B := Metric.ball (0 : ℂ) T.radius
  have h0 : (0 : ℂ) ∈ Ω := by norm_num [Ω, KPContinuation.spectralDomain]
  let K : ℂ → C(X, ℂ) := fun s => (localMeromorphicIntegrand T v s g).comp q
  have hK : MeromorphicOn K B := by
    intro z hz
    obtain ⟨n, hn⟩ := localMeromorphicIntegrand_meromorphic T v g z hz
    exact ⟨n, ((ContinuousMap.compCLM ℂ ℂ q).analyticAt _).comp hn⟩
  have hJK : J =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => b s • K s) := by
    apply compact_meromorphic_germ_of_evaluation_germs (hJ 0 h0)
      ((hb 0 h0).meromorphicAt.smul (hK 0 (Metric.mem_ball_self T.radius_pos)))
    intro x
    let a := KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (q x)) * g
    have hjx : MeromorphicOn (fun s => J s x) Ω := by
      intro z hz
      obtain ⟨n, hn⟩ := hJ z hz
      refine ⟨n, ?_⟩
      simpa only [Function.comp_def, map_smul, ContinuousMap.evalCLM_apply] using
        ((ContinuousMap.evalCLM ℂ x).analyticAt _).comp hn
    have he := chamber_identity_germ hjx (hb.meromorphicOn.mul (T.meromorphic v a))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      (fun s hs => by
        change J s x = b s * T.E v s a
        rw [hch s hs, T.chamber v s hs]) 0 h0
    filter_upwards [he, nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos), self_mem_nhdsWithin] with s he hs hn
    change J s x = b s * localMeromorphicIntegrand T v s g (q x)
    rw [localMeromorphicIntegrand_apply T v s hs hn]
    exact he
  let a : ℂ → ℂ := fun s => L (J s) / b s
  have ha : MeromorphicOn a Ω := (meromorphicOn_observation L J Ω hJ).div hb.meromorphicOn
  let I := toMeromorphicNFOn a Ω
  let k : ℂ → ℂ := fun s => fourier R Q.dq (T.cleared v s) g / s
  have hk : MeromorphicOn k B :=
    (selected_fourier_cleared_analyticOnNhd T v g).meromorphicOn.div analyticOnNhd_id.meromorphicOn
  have hnear : a =ᶠ[𝓝[≠] (0 : ℂ)] k := by
    have hbne : ∀ᶠ s in 𝓝 (0 : ℂ), b s ≠ 0 :=
      (hb 0 h0).continuousAt.eventually_ne (by rw [hb0]; exact one_ne_zero)
    filter_upwards [hJK, nhdsWithin_le_nhds hbne, nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos)] with s he hn hs
    dsimp [a]
    rw [he, map_smul, smul_eq_mul, mul_div_cancel_left₀ _ hn, hL]
    change complexFourierExtraction Q.dq (s⁻¹ • clearedIntegrand T v s g) = _
    rw [map_smul, smul_eq_mul]
    unfold complexFourierExtraction k MomentSources.fourier
    simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
      clearedIntegrand_apply T v s hs]
    rw [div_eq_mul_inv, mul_comm]
  refine ⟨I, (meromorphicNFOn_toMeromorphicNFOn _ _).meromorphicOn, ?_, ?_⟩
  · apply ResidueContinuity.normalized_division_eq_chamber
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      (isOpen_lt continuous_const Complex.continuous_re) b (fun s => L (J s))
      (fun s => fourier R Q.dq
        (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s) g)
      hb hb0 h0 (meromorphicOn_observation L J Ω hJ)
      (selected_chamber_fourier_analytic v g)
    intro s hs
    let c : KPAdditiveQuotient F → ℂ := fun y => b s *
      KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        Q.K (Q.flat v) s
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out y) * g)
    have hc : Continuous c := by
      apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
      exact (J s).continuous.congr (hch s hs)
    let f : C(KPAdditiveQuotient F, ℂ) := ⟨c, hc⟩
    have he : J s = f.comp q := by ext x; exact hch s hs x
    rw [he, hL]
    change (∫ y, (b s * _) * _ ∂Q.dq) = _
    simp only [mul_assoc]
    exact integral_const_mul _ _
  · intro s hs hn
    have ht0 : meromorphicOrderAt (a-k) 0 = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [hnear] with t ht
      exact sub_eq_zero.mpr ht
    have had : MeromorphicOn a B := fun t ht => ha t (T.disc_domain ht)
    have hts := (had.sub hk).meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_ball (0 : ℂ) T.radius).isPreconnected
      (Metric.mem_ball_self T.radius_pos) hs ht0
    have hes : a =ᶠ[𝓝[≠] s] k := by
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp hts] with t ht
      exact sub_eq_zero.mp ht
    have hka : AnalyticAt ℂ k s :=
      (selected_fourier_cleared_analyticOnNhd T v g s hs).div analyticAt_id hn
    have hid : I s = k s := by
      dsimp [I]
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt ha (T.disc_domain hs)]
      have he := (toMeromorphicNFAt_eventuallyEq_nhds_congr hes).eq_of_nhds
      rw [toMeromorphicNFAt_eq_self.mpr hka.meromorphicNFAt] at he
      exact he
    rw [hid]
    exact (mul_div_cancel₀ _ hn).symm

end DedekindZetaZeroFree.SheetRescaling

end

section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory Filter
open CompactPeriodAnalyticity.UpperPeriodContinuation
open _root_.DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation renaming exponential_integral_differentiable → exponential_integral_differentiable
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming upper_fiber_eq → upper_fiber_eq
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming compact_additive_representatives → compact_additive_representatives
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent renaming extension_of_compact_period → extension_of_compact_period
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
local instance : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem selected_fourier_continuation_exists (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) :
    ∃ I : ℂ → ℂ, MeromorphicOn I KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → I s = fourier R Q.dq
        (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s) g) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) T.radius, s ≠ 0 →
        fourier R Q.dq (T.cleared v s) g = s * I s := by
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
  obtain ⟨b, A, hb, hb0, hA, hch⟩ := native_compact_source_exists
    F R.A.zeta12 R.A.primitive_zeta12 D hD Q.K Q.iwasawa (Q.flat v)
  let J : ℂ → C(X, ℂ) := fun s => (A s).comp jj
  have hJ : MeromorphicOn J KPContinuation.spectralDomain := by
    intro z hz
    obtain ⟨n, hn⟩ := hA z hz
    refine ⟨n, ?_⟩
    simpa only [Function.comp_def, map_smul, ContinuousMap.compCLM_apply] using
      ((ContinuousMap.compCLM ℂ ℂ jj).analyticAt _).comp hn
  obtain ⟨L, hL⟩ := extension_of_compact_period q hq Q.dq
  let weight : C(X, ℂ) := ⟨fun x => star (adelicTraceQuotientCharacter F (q x) : ℂ),
    (((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).comp q.continuous).star)⟩
  let Lχ : C(X, ℂ) →L[ℂ] ℂ := L.comp (ContinuousLinearMap.mul ℂ C(X, ℂ) weight)
  have hLχ (f : C(KPAdditiveQuotient F, ℂ)) :
      Lχ (f.comp q) = complexFourierExtraction Q.dq f := by
    let fχ : C(KPAdditiveQuotient F, ℂ) :=
      ⟨fun y => f y * star (adelicTraceQuotientCharacter F y : ℂ),
        f.continuous.mul ((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).star)⟩
    have he : weight * f.comp q = fχ.comp q := by
      ext x
      exact mul_comm _ _
    change L (weight * f.comp q) = _
    rw [he, hL]
    rfl
  apply fourier_of_representative_source T v g q hq Lχ hLχ b J hb hb0 hJ
  intro s hs x
  change A s (jj x) = b s * _
  rw [hch s hs (jj x)]
  congr 1
  exact (upper_fiber_eq F R.A.zeta12 R.A.primitive_zeta12
    (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s)
    (KPLiteralExceptionalResidue.ResidueAutomorphy.eisenstein_rational
      F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s hs) g x.val).symm

end DedekindZetaZeroFree.SheetRescaling

end
end
