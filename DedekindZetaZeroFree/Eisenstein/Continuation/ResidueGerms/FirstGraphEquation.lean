module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ResidueCenter.ClosedEigenEquation

@[expose] public section

noncomputable section
open Filter Topology MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

theorem closed_cleared_first_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : E →ₗ.[ℂ] E) (hD : D.IsClosed)
    (a : ℂ → ℂ) (v h w : ℂ → E) (c : ℂ)
    (da : ℂ) (dh dw : E)
    (ha : HasDerivAt a da c) (hh : HasDerivAt h dh c) (hw : HasDerivAt w dw c)
    (he : ∀ᶠ s in 𝓝[≠] c, ∃ hv : v s ∈ D.domain,
      D ⟨v s, hv⟩ - a s • v s = -(h s))
    (hclear : ∀ᶠ s in 𝓝[≠] c, w s = (s-c) • v s) :
    (dw, a c • dw + da • w c - h c) ∈ D.graph := by
  have h0 := closed_cleared_center_eigen D hD a v h w c
    ha.continuousAt hh.continuousAt hw.continuousAt he hclear
  let q : ℂ → E × E := fun s => (w s, a s • w s - (s-c) • h s)
  have hq0 : q c ∈ D.graph := by simpa [q] using h0
  have hq : ∀ᶠ s in 𝓝[≠] c, q s ∈ D.graph := by
    filter_upwards [he, hclear] with s hs hws
    obtain ⟨hv, heq⟩ := hs
    have hm := D.graph.smul_mem (s-c) (D.mem_graph ⟨v s, hv⟩)
    have hvEq : D ⟨v s, hv⟩ = -(h s) + a s • v s := sub_eq_iff_eq_add.mp heq
    simpa only [q, Prod.smul_mk, hws, hvEq, smul_add, smul_neg, smul_smul,
      mul_comm, sub_eq_add_neg, add_comm] using hm
  have hd : HasDerivAt q (dw, a c • dw + da • w c - h c) c := by
    have he := hw.prodMk ((ha.smul hw).sub (((hasDerivAt_id c).sub_const c).smul hh))
    simpa [q] using he
  apply hD.mem_of_tendsto hd.tendsto_slope
  filter_upwards [hq] with s hs
  exact D.graph.smul_mem (s-c)⁻¹ (D.graph.sub_mem hs hq0)

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

namespace DedekindZetaZeroFree.KPContActualHilbertSimpleGerms

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Hactual" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U
local notation "d" => (Module.finrank ℚ F / 2 : ℕ)
local notation "a" => KPContinuation.spectralCoordinate (d : ℤ)

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)

local notation "Bactual" => KPContActualSectorFriedrichsSynthesis.B_U
  F ζ hζ level R P H μG hμG hR realization
local notation "Δactual" => KPContActualSectorFriedrichsSynthesis.Δ_U
  F ζ hζ level R P H μG hμG hR realization

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem actual_simple_germs_first_graph
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (hf : DifferentiableOn ℂ f Ω) (c : ℂ) (hc : c ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ Ω ∧
      ∃ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball c r) ∧
        (∀ s ∈ Metric.ball c r, s ≠ c →
          w s = (s-c) • v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s) ∧
        (deriv w c, a c • deriv w c + deriv a c • w c - source.h c) ∈ (Δactual).graph := by
  have h := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U
    μG hμG hR realization ι hι hStage Ω hΩopen hΩ f hf buffer χ source
  obtain ⟨r, hr, hb, hi, w, hw, he, hp, hn⟩ := h.simple_germs c hc
  refine ⟨r, hr, hb, w, hw, he, ?_⟩
  have hD := (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ
    μG hμG level R hR P H realization).laplacian_closed
  have ha : HasDerivAt a (deriv a c) c :=
    (KPContinuation.spectralCoordinate_hasDerivAt (d : ℤ) c).differentiableAt.hasDerivAt
  have hh := (source.hilbert_holomorphic.differentiableAt (hΩopen.mem_nhds hc)).hasDerivAt
  have hwc := (hw.differentiableAt (Metric.ball_mem_nhds c hr)).hasDerivAt
  apply FourierContinuation.ResidualHilbertCenters.closed_cleared_first_graph Δactual hD a
    (v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source)
    source.h w c (deriv a c) (deriv source.h c) (deriv w c) ha hh hwc
  · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c hr), self_mem_nhdsWithin]
      with s hs hne
    have hn : s ∉ Sigma F ζ hζ C R P H U μG hμG hR realization Ω := by
      intro hp
      exact hne (hi ⟨hs,hp⟩)
    exact h.domain_equation s ⟨hb hs, hn⟩
  · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c hr), self_mem_nhdsWithin]
      with s hs hne
    exact he s hs hne
end DedekindZetaZeroFree.KPContActualHilbertSimpleGerms

end
