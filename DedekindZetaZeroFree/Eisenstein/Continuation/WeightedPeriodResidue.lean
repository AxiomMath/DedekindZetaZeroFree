module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactPeriodNumerator
public import DedekindZetaZeroFree.Eisenstein.Residues.Automorphy.RationalAndGenuineCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming upper_fiber_eq → upper_fiber_eq
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming compact_additive_representatives → compact_additive_representatives
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent renaming extension_of_compact_period → extension_of_compact_period
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly renaming extension_evaluates_native_pullback → extension_evaluates_native_pullback
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
local notation "AF" => ownedLiteralResidueFamily (full_product_compact_iwasawa R)
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem core_period_continuation (x : V)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure) (g : G F ζ hζ) :
    ∃ (Q A B : ℂ → ℂ) (r : ℝ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      MeromorphicOn A KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → A s = Q s *
        ∫ q : KPAdditiveQuotient F, eisenstein F ζ hζ (fullProductCompact R)
          (coreFlatInsertion R P C x) s
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) r) ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → B s = s * A s) ∧
      B 0 = ∫ q : KPAdditiveQuotient F, coreResidue R P C x
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ := by
  letI : CompactSpace (KPAdditiveQuotient F) := (additiveAdeleQuotient_compactHausdorff F).1
  letI : T2Space (KPAdditiveQuotient F) := (additiveAdeleQuotient_compactHausdorff F).2
  letI : μ.IsAddHaarMeasure := hμ
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let f : Flat F ζ hζ (fullProductCompact R) := asLiteralFlat (coreFlatInsertion R P C x)
  obtain ⟨X, hX, hqX⟩ := compact_additive_representatives F
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let q : C(X, KPAdditiveQuotient F) :=
    ⟨fun y => QuotientAddGroup.mk y.val,
      QuotientAddGroup.continuous_mk.comp continuous_subtype_val⟩
  have hq : Function.Surjective q := by
    intro y
    have hy : y ∈ (QuotientAddGroup.mk : KPAdeles F → KPAdditiveQuotient F) '' X := by
      rw [hqX]; exact Set.mem_univ y
    obtain ⟨z, hz, he⟩ := hy
    exact ⟨⟨z, hz⟩, he⟩
  let j : C(X, G F ζ hζ) :=
    ⟨fun y => KPGlobalTorusFunctionData.N F ζ hζ y.val * g,
      ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ).comp
        continuous_subtype_val).mul continuous_const⟩
  let D := j '' Set.univ
  have hD : IsCompact D := isCompact_univ.image j.continuous
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let jj : C(X, D) := ⟨fun y => ⟨j y, ⟨y, Set.mem_univ y, rfl⟩⟩,
    j.continuous.subtype_mk _⟩
  obtain ⟨Q, J, T, r, hQ, hQ0, hJ, hch, hr, hb, hT, hclear⟩ :=
    SharedSource.literal_compact_numerator_exists D hD (fullProductCompact R)
      (full_product_compact_iwasawa R) f
  obtain ⟨L, hL⟩ := extension_of_compact_period q hq μ
  let LL : C(D, ℂ) →L[ℂ] ℂ := L.comp (ContinuousMap.compCLM ℂ ℂ jj)
  have hcenter (a : D) : T 0 a = (AF).cleared f 0 a := by
    obtain ⟨U, u, hU, hc, hUc, hu, hub, hE, hAc, han⟩ := (AF).germ.2 f
    have he : (fun z => J z a) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z => Q z * (AF).E f z a) := by
      apply _root_.DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ
        (_root_.DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.meromorphicOn_observation (ContinuousMap.evalCLM ℂ a) J _ hJ)
        (hQ.meromorphicOn.mul ((AF).normal f a).meromorphicOn)
        KPContinuation.spectralDomain_isConnected.isPreconnected
        KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 ?_
      · intro z hz
        change J z a = Q z * (AF).E f z a
        rw [hch z hz, (AF).germ.1 f z hz]
      · norm_num [KPContinuation.spectralDomain]
    have he' : (fun z => T z a) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z => Q z * (AF).cleared f z a) := by
      filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hu), self_mem_nhdsWithin]
        with z he hz hzu hz0
      rw [hclear z hz hz0, congrFun (hAc z hzu hz0) a]
      simp only [ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, he]
      ring
    have ha : AnalyticAt ℂ (fun z => T z a) 0 := by
      simpa only [Function.comp_def, ContinuousMap.evalCLM_apply] using
        ((ContinuousMap.evalCLM ℂ a).analyticAt _).comp (hT 0 (Metric.mem_ball_self hr))
    have hc : ContinuousAt (fun z => Q z * (AF).cleared f z a) 0 :=
      (hQ 0 (by norm_num [KPContinuation.spectralDomain])).continuousAt.mul
        (han a 0 (Metric.mem_ball_self hu)).continuousAt
    simpa only [hQ0, one_mul] using
      ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc).mp he').eq_of_nhds
  refine ⟨Q, fun s => LL (J s), fun s => LL (T s), r, hQ, hQ0,
    _root_.DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.meromorphicOn_observation LL J _ hJ, ?_, hr, hb,
    LL.comp_analyticOnNhd hT, ?_, ?_⟩
  · intro s hs
    rw [← integral_const_mul]
    apply extension_evaluates_native_pullback q hq μ L hL ((J s).comp jj)
    intro y
    rw [ContinuousMap.comp_apply, hch s hs]
    congr 1
    exact (upper_fiber_eq F ζ hζ (eisenstein F ζ hζ (fullProductCompact R) f s)
      (KPLiteralExceptionalResidue.ResidueAutomorphy.eisenstein_rational F ζ hζ (fullProductCompact R) f s hs)
      g y.val).symm
  · intro s hs hs0
    change LL (T s) = s * LL (J s)
    rw [hclear s hs hs0, map_smul, smul_eq_mul]
  · have hres : coreResidue R P C x = (AF).cleared f 0 := by
      change (AF).residue (literalZeroProfileEquiv (full_product_compact_iwasawa R)
        (coreFlatInsertion R P C x)) = _
      exact (AF).residue_flat _
    rw [hres]
    apply extension_evaluates_native_pullback q hq μ L hL ((T 0).comp jj)
    intro y
    rw [ContinuousMap.comp_apply, hcenter]
    exact (upper_fiber_eq F ζ hζ ((AF).cleared f 0)
      (KPLiteralExceptionalResidue.ResidueAutomorphy.residue_rational F ζ hζ (fullProductCompact R)
        (AF).E (AF).cleared (AF).germ f) g y.val).symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
