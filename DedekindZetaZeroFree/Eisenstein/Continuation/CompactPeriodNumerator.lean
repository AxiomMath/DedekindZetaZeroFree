module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactBanachNumerator
public import DedekindZetaZeroFree.Theta.Periods.NormalizedPeriodContinuity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming upper_fiber_eq → upper_fiber_eq
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit renaming compact_additive_representatives → compact_additive_representatives
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NormalizedPeriodContinuity renaming clearing_disk_rational → clearing_disk_rational
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

theorem core_compact_period_clearing (x : V)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure) (g : G F ζ hζ) :
    ∃ (r : ℝ) (B : ℂ → ℂ), 0 < r ∧
      Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) r) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r,
        Integrable (fun q : KPAdditiveQuotient F => (AF).cleared
          (coreFlatInsertion R P C x) s
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)) μ ∧
        B s = ∫ q : KPAdditiveQuotient F, (AF).cleared
          (coreFlatInsertion R P C x) s
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ := by
  letI : CompactSpace (KPAdditiveQuotient F) := (additiveAdeleQuotient_compactHausdorff F).1
  letI : T2Space (KPAdditiveQuotient F) := (additiveAdeleQuotient_compactHausdorff F).2
  letI : μ.IsAddHaarMeasure := hμ
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
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
  obtain ⟨t, N, ht, hb, hN, hpin⟩ := core_compact_clearing R P C x D hD
  obtain ⟨u, hu, hrat⟩ := clearing_disk_rational F ζ hζ (fullProductCompact R)
    (AF).E (AF).cleared (AF).germ (asLiteralFlat (coreFlatInsertion R P C x))
  obtain ⟨L, hL⟩ := extension_of_compact_period q hq μ
  let LL : C(D, ℂ) →L[ℂ] ℂ := L.comp (ContinuousMap.compCLM ℂ ℂ jj)
  let r := min t u
  refine ⟨r, fun s => LL (N s), lt_min ht hu,
    (Metric.ball_subset_ball (min_le_left _ _)).trans hb,
    (LL.comp_analyticOnNhd hN).mono (Metric.ball_subset_ball (min_le_left _ _)), ?_⟩
  intro s hs
  let c : KPAdditiveQuotient F → ℂ := fun z => (AF).cleared (coreFlatInsertion R P C x) s
    (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out z) * g)
  have he (y : X) : (N s).comp jj y = c (q y) := by
    rw [ContinuousMap.comp_apply, hpin s (Metric.ball_subset_ball (min_le_left _ _) hs)]
    exact (upper_fiber_eq F ζ hζ ((AF).cleared (coreFlatInsertion R P C x) s)
      (hrat s (Metric.ball_subset_ball (min_le_right _ _) hs)) g y.val).symm
  have hc : Continuous c :=
    (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
      (((N s).comp jj).continuous.congr he)
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, Measure.restrict_univ, c] using
      hc.continuousOn.integrableOn_compact' (μ := μ) isCompact_univ MeasurableSet.univ
  · exact extension_evaluates_native_pullback q hq μ L hL ((N s).comp jj) c he

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
