module

public import DedekindZetaZeroFree.Analysis.Complex.CompactMeromorphicFamilies
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.ChamberHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactScalarNumerators

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
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
set_option maxHeartbeats 1600000

theorem core_compact_clearing (x : V) (D : Set (G F ζ hζ)) (hD : IsCompact D) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ (r : ℝ) (N : ℂ → C(D, ℂ)), 0 < r ∧
      Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ N (Metric.ball (0 : ℂ) r) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, ∀ g : D,
        N s g = (AF).cleared (coreFlatInsertion R P C x) s g := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let f : Flat F ζ hζ (fullProductCompact R) := asLiteralFlat (coreFlatInsertion R P C x)
  obtain ⟨q, J, T, t, hq, hq0, hJ, hch, ht, htb, hT, hclear⟩ :=
    SharedSource.literal_compact_numerator_exists D hD (fullProductCompact R)
      (full_product_compact_iwasawa R) f
  obtain ⟨U, u, hU, hc, hUc, hu, hub, hE, hAc, han⟩ := (AF).germ.2 f
  have hqne : ∀ᶠ s in 𝓝 (0 : ℂ), q s ≠ 0 :=
    (hq 0 (by norm_num [KPContinuation.spectralDomain])).continuousAt.eventually_ne
      (by rw [hq0]; exact one_ne_zero)
  obtain ⟨v, hv, hvq⟩ := Metric.mem_nhds_iff.mp hqne
  let r := min t (min u v)
  have hr : 0 < r := lt_min ht (lt_min hu hv)
  let N : ℂ → C(D, ℂ) := fun s => (q s)⁻¹ • T s
  have hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans htb
  have hn : AnalyticOnNhd ℂ N (Metric.ball (0 : ℂ) r) := by
    intro s hs
    exact ((hq s (hb hs)).inv (hvq
      (Metric.ball_subset_ball ((min_le_right t _).trans (min_le_right u v)) hs))).smul
      (hT s (Metric.ball_subset_ball (min_le_left _ _) hs))
  refine ⟨r, N, hr, hb, hn, ?_⟩
  intro s hs g
  have hjg : MeromorphicOn (fun z => J z g) KPContinuation.spectralDomain :=
    _root_.DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.meromorphicOn_observation
      (ContinuousMap.evalCLM ℂ g) J _ hJ
  have he : (fun z => J z g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => q z * (AF).E f z g) := by
    apply _root_.DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ hjg
      (hq.meromorphicOn.mul ((AF).normal f g).meromorphicOn)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 ?_
    · intro z hz
      change J z g = q z * (AF).E f z g
      rw [hch z hz, (AF).germ.1 f z hz]
    · norm_num [KPContinuation.spectralDomain]
  have heg : (fun z => N z g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => (AF).cleared f z g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z he hz hzne
    have hzt := Metric.ball_subset_ball (min_le_left t _) hz
    have hzu := Metric.ball_subset_ball ((min_le_right t _).trans (min_le_left u v)) hz
    have hzv := Metric.ball_subset_ball ((min_le_right t _).trans (min_le_right u v)) hz
    dsimp only [N]
    rw [hclear z hzt hzne]
    simp only [ContinuousMap.smul_apply, smul_eq_mul, he]
    rw [congrFun (hAc z hzu hzne) g]
    change _ = z * (AF).E f z g
    calc
      _ = z * ((q z)⁻¹ * q z) * (AF).E f z g := by ring
      _ = _ := by rw [inv_mul_cancel₀ (hvq hzv), mul_one]
  have hng : AnalyticOnNhd ℂ (fun z => N z g) (Metric.ball (0 : ℂ) r) := by
    simpa only [Function.comp_def, ContinuousMap.evalCLM_apply] using
      ((ContinuousMap.evalCLM ℂ g).analyticOnNhd Set.univ).comp hn
        (fun _ _ => Set.mem_univ _)
  have hag : AnalyticOnNhd ℂ (fun z => (AF).cleared f z g) (Metric.ball (0 : ℂ) r) :=
    (han g).mono (Metric.ball_subset_ball ((min_le_right t _).trans (min_le_left u v)))
  have he0 := ((hng 0 (Metric.mem_ball_self hr)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hag 0 (Metric.mem_ball_self hr)).continuousAt).mp heg
  exact hng.eqOn_of_preconnected_of_eventuallyEq hag (convex_ball (0 : ℂ) r).isPreconnected
    (Metric.mem_ball_self hr) he0 hs

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
