module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPContFlatArchDiagonalMultiplier

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "μ" => KPWildKernelUpperBound.quotientHaar F
theorem coreResidue_upper_arch_covariance
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    (u : InfinitePlace F → ℝ) (g : KPLiteralRaw.G F ζ hζ) :
    (∫ q : KPAdditiveQuotient F, coreResidue R P C x
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
        ((aInfinity F ζ hζ u).val * g)) ∂μ) =
    Complex.exp (((2 : ℂ)/3) * ((∑ w, u w : ℝ) : ℂ)) *
      (∫ q : KPAdditiveQuotient F, coreResidue R P C x
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ) := by
  obtain ⟨M₁,B₁,r₁,hM₁,hch₁,hr₁,hb₁,hB₁,hclear₁,hcenter₁⟩ :=
    core_scattering_continuation R P C x ((aInfinity F ζ hζ u).val * g)
  obtain ⟨M₀,B₀,r₀,hM₀,hch₀,hr₀,hb₀,hB₀,hclear₀,hcenter₀⟩ :=
    core_scattering_continuation R P C x g
  let e : ℂ → ℂ := fun s => Complex.exp (((2 : ℂ)/3-2*s) * ((∑ w, u w : ℝ) : ℂ))
  have he : AnalyticOnNhd ℂ e Set.univ := by
    intro s hs
    dsimp [e]
    fun_prop
  have hzero : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have heq := KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    hM₁.meromorphicOn ((he.mono (Set.subset_univ _)).meromorphicOn.mul hM₀.meromorphicOn)
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    KPContinuation.convergenceHalfPlane_subset_spectralDomain
    (show {s : ℂ | (1/3 : ℝ) < s.re}.Nonempty from ⟨1, by norm_num⟩)
    (show Set.EqOn M₁ (fun s => e s * M₀ s) {s : ℂ | (1/3 : ℝ) < s.re} from by
      intro s hs
      change M₁ s = e s * M₀ s
      rw [hch₁ s hs,hch₀ s hs]
      exact coreScattering_arch_covariance R P C x s u g) hzero
  have hev : B₁ =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => e s * B₀ s) := by
    filter_upwards [heq, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr₁),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr₀)] with s hs hn hs₁ hs₀
    change M₁ s = e s * M₀ s at hs
    have hn' : s ≠ 0 := by simpa using hn
    rw [hclear₁ s hs₁ hn',hclear₀ s hs₀ hn',hs]
    ring
  have hlim₁ := (hB₁ 0 (Metric.mem_ball_self hr₁)).continuousAt.tendsto
  have hlim₀ := ((he 0 (Set.mem_univ _)).continuousAt.mul
    (hB₀ 0 (Metric.mem_ball_self hr₀)).continuousAt).tendsto
  have hcenter : B₁ 0 = e 0 * B₀ 0 :=
    tendsto_nhds_unique ((hlim₁.mono_left nhdsWithin_le_nhds).congr' hev)
      (hlim₀.mono_left nhdsWithin_le_nhds)
  rw [hcenter₁,hcenter₀] at hcenter
  simpa only [e,mul_zero,sub_zero] using hcenter

theorem coreResidue_upper_mean_height
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    (t : ℝ) (b : InfinitePlace F → ℝ) (hb : ∑ w, b w = 0)
    (g : KPLiteralRaw.G F ζ hζ) :
    (∫ q : KPAdditiveQuotient F, coreResidue R P C x
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
        ((aInfinity F ζ hζ (fun w => t+b w)).val * g)) ∂μ) =
    Complex.exp (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * (2/3) * (t : ℂ)) *
      (∫ q : KPAdditiveQuotient F, coreResidue R P C x
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ) := by
  rw [coreResidue_upper_arch_covariance]
  congr 2
  rw [Finset.sum_add_distrib,hb,add_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [KPContFlatArchDiagonalMultiplier.complexDimension_eq_card F ζ hζ]
  push_cast
  ring

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
