module

public import DedekindZetaZeroFree.Eisenstein.Continuation.WeightedPeriodResidue

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
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem coreFlatInsertion_entire (x : V) (g : G F ζ hζ) :
    AnalyticOnNhd ℂ (fun s => (coreFlatInsertion R P C x).val s g) Set.univ := by
  intro s hs
  change AnalyticAt ℂ (fun z => Complex.exp (z * (iwasawaLogHeight R g : ℂ)) *
    quotientCoreEvaluator R.A P C x g) s
  exact (analyticAt_id.mul analyticAt_const).cexp.mul analyticAt_const

theorem core_scattering_weighted_continuation (x : V) (g : G F ζ hζ) :
    let μ := KPWildKernelUpperBound.quotientHaar F
    ∃ (Q M B : ℂ → ℂ) (r : ℝ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      MeromorphicOn M KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → M s = Q s * coreScattering R P C x s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) r) ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → B s = s * M s) ∧
      B 0 = ∫ q : KPAdditiveQuotient F, coreResidue R P C x
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ := by
  let μ := KPWildKernelUpperBound.quotientHaar F
  obtain ⟨Q, A, T, r, hQ, hQ0, hA, hch, hr, hb, hT, hclear, hcenter⟩ :=
    core_period_continuation R P C x μ inferInstance g
  let f : ℂ → ℂ := fun s => (coreFlatInsertion R P C x).val s g
  have hf : AnalyticOnNhd ℂ f KPContinuation.spectralDomain :=
    (coreFlatInsertion_entire R P C x g).mono (Set.subset_univ _)
  have hmass : μ.real Set.univ = 1 := by simp [μ, Measure.real]
  refine ⟨Q, fun s => A s - Q s * f s, fun s => T s - s * (Q s * f s), r,
    hQ, hQ0, hA.sub (hQ.mul hf).meromorphicOn, ?_, hr, hb,
    hT.sub ((analyticOnNhd_id.mul (hQ.mul hf)).mono hb), ?_, ?_⟩
  · intro s hs
    change A s - Q s * f s = Q s * coreScattering R P C x s g
    rw [hch s hs, coreChamber_constantTerm R P C x μ inferInstance s hs g, hmass]
    simp only [Complex.ofReal_one, one_mul]
    dsimp only [f]
    ring
  · intro s hs hs0
    change T s - s * (Q s * f s) = s * (A s - Q s * f s)
    rw [hclear s hs hs0]
    ring
  · simpa only [zero_mul, sub_zero] using hcenter

theorem core_scattering_continuation (x : V) (g : G F ζ hζ) :
    let μ := KPWildKernelUpperBound.quotientHaar F
    ∃ (M B : ℂ → ℂ) (r : ℝ),
      MeromorphicNFOn M KPContinuation.spectralDomain ∧
      (∀ s, (1 / 3 : ℝ) < s.re → M s = coreScattering R P C x s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) r) ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → B s = s * M s) ∧
      B 0 = ∫ q : KPAdditiveQuotient F, coreResidue R P C x
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ := by
  obtain ⟨Q, A, T, t, hQ, hQ0, hA, hch, ht, htb, hT, hclear, hcenter⟩ :=
    core_scattering_weighted_continuation R P C x g
  have h0 : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have hQne : ∀ᶠ z in 𝓝 (0 : ℂ), Q z ≠ 0 :=
    (hQ 0 h0).continuousAt.eventually_ne (by rw [hQ0]; exact one_ne_zero)
  obtain ⟨u, hu, hQu⟩ := Metric.mem_nhds_iff.mp hQne
  let r := min t u
  have hr : 0 < r := lt_min ht hu
  have hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans htb
  let B : ℂ → ℂ := fun z => T z / Q z
  have hB : AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) r) := by
    intro z hz
    exact (hT z (Metric.ball_subset_ball (min_le_left _ _) hz)).div (hQ z (hb hz))
      (hQu (Metric.ball_subset_ball (min_le_right _ _) hz))
  let M := toMeromorphicNFOn (fun z => A z / Q z) KPContinuation.spectralDomain
  have hm : MeromorphicOn (fun z => A z / Q z) KPContinuation.spectralDomain :=
    hA.div hQ.meromorphicOn
  refine ⟨M, B, r, meromorphicNFOn_toMeromorphicNFOn _ _, ?_, hr, hb, hB, ?_, ?_⟩
  · intro z hz
    exact ResidueContinuity.normalized_division_eq_chamber
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      (isOpen_lt continuous_const Complex.continuous_re) Q A
      (fun s => coreScattering R P C x s g) hQ hQ0 h0 hA
      (coreScattering_analytic R P C x g) hch hz
  · intro z hz hz0
    let H : ℂ → ℂ := fun s => B s / s
    have hH : AnalyticAt ℂ H z := (hB z hz).div analyticAt_id hz0
    have he : (fun s => A s / Q s) =ᶠ[𝓝[≠] z] H := by
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hz),
        nhdsWithin_le_nhds (eventually_ne_nhds hz0)] with s hs hs0
      dsimp only [H, B]
      rw [hclear s (Metric.ball_subset_ball (min_le_left _ _) hs) hs0]
      field_simp
    have hMz : M z = H z := by
      dsimp only [M]
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (hb hz)]
      have hn := (toMeromorphicNFAt_eventuallyEq_nhds_congr he).eq_of_nhds
      rw [toMeromorphicNFAt_eq_self.mpr hH.meromorphicNFAt] at hn
      exact hn
    rw [hMz]
    dsimp only [H]
    exact (mul_div_cancel₀ (B z) hz0).symm
  · dsimp only [B]
    rw [hQ0, div_one]
    exact hcenter

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
