module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.ChamberFrameRelations
public import DedekindZetaZeroFree.Eisenstein.Continuation.Scattering.MeromorphicNumerators

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem coreResidue_upper_slot_kernel (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ t.val) (g : Raw R.A)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (f : Plus R.A P C (Sum.inr q))
    (hf : scatteringSlotOutput R P C q μ hμ 0 g f = 0) :
    (∫ u : KPAdditiveQuotient F, coreResidue R P C (slotCore R P C t x q hq f)
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ g))
      ∂KPWildKernelUpperBound.quotientHaar F) = 0 := by
  let G := scalarQuotient F ζ hζ (amalgamation F ζ hζ g)
  obtain ⟨ι, hi, e, tests, d, c, hd, hd0, hc, hc0, hframe⟩ :=
    coreScattering_chamber_frame R P C N t x q hq g μ hμ
  letI : Fintype ι := hi
  obtain ⟨M, B, r, hM, hMch, hr, hrb, hB, hclear, hcenter⟩ :=
    core_scattering_continuation R P C (slotCore R P C t x q hq f) G
  have hex (i : ι) :=
    core_scattering_continuation R P C (slotCore R P C t x q hq (tests i)) G
  choose Mi Bi ri hMi hMich hri hrib hBi hcleari hcenteri using hex
  have h0 : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have hger : (fun z => d z * M z) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i, c f z i * Mi i z) := by
    apply CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ
      (hd.meromorphicOn.mul hM.meromorphicOn)
      (MeromorphicOn.fun_sum (fun i _ => (hc f i).meromorphicOn.mul (hMi i).meromorphicOn))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 h0
    intro z hz
    change d z * M z = ∑ i, c f z i * Mi i z
    rw [hMch z hz]
    simp_rw [hMich _ z hz]
    exact hframe z hz f
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i, Bi i z = z * Mi i z := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (hri i)),
      self_mem_nhdsWithin] with z hz hz0
    exact hcleari i z hz hz0
  have hnear : (fun z => d z * B z) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i, c f z i * Bi i z) := by
    filter_upwards [hger, hall,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr), self_mem_nhdsWithin]
      with z hger hall hz hz0
    rw [hclear z hz hz0]
    simp_rw [hall]
    calc
      d z * (z * M z) = z * (d z * M z) := by ring
      _ = z * (∑ i, c f z i * Mi i z) := by rw [hger]
      _ = ∑ i, c f z i * (z * Mi i z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hl : ContinuousAt (fun z => d z * B z) 0 :=
    (hd 0 h0).continuousAt.mul (hB 0 (Metric.mem_ball_self hr)).continuousAt
  have hh : ContinuousAt (fun z => ∑ i, c f z i * Bi i z) 0 := by
    apply AnalyticAt.continuousAt (𝕜 := ℂ)
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (hc f i 0 h0).mul (hBi i 0 (Metric.mem_ball_self (hri i)))
  have heq := ((hl.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hh).mp hnear).eq_of_nhds
  have hc0f : c f 0 = 0 := by rw [hc0, hf, map_zero]
  rw [hd0, one_mul] at heq
  have hB0 : B 0 = 0 := by simpa only [hc0f, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero] using heq
  exact hcenter.symm.trans hB0

theorem coreResidue_upper_finite_kernel (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ t.val)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (f : Plus R.A P C (Sum.inr q))
    (hf : KPRankOneShellRepair.actualCanonicalForwardMap F ζ hζ q
      (C.canonical q) (C.polarization q) μ hμ f = 0)
    (g : G F ζ hζ) :
    (∫ u : KPAdditiveQuotient F, coreResidue R P C (slotCore R P C t x q hq f)
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) * g)
      ∂KPWildKernelUpperBound.quotientHaar F) = 0 := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply coreResidue_upper_slot_kernel R P C N t x q hq g μ hμ f
      rw [scatteringSlotOutput_zero, hf]
      rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
