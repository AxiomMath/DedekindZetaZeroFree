module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ResidueGerms.FirstGraphEquation

@[expose] public section

noncomputable section
open Filter Topology MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
theorem first_graph_eigentest_pairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : E →ₗ.[ℂ] E) (hD : IsSelfAdjoint D)
    (lam : ℝ) (da : ℂ) (t w dw h : E)
    (ht : (t, (lam : ℂ) • t) ∈ D.graph)
    (hw : (dw, (lam : ℂ) • dw + da • w - h) ∈ D.graph) :
    inner ℂ t h = da * inner ℂ t w := by
  have hf := LinearPMap.adjoint_isFormalAdjoint hD.dense_domain
  rw [LinearPMap.isSelfAdjoint_def] at hD
  rw [hD] at hf
  obtain ⟨td, htt, hte⟩ := D.mem_graph_iff.mp ht
  obtain ⟨wd, hww, hwe⟩ := D.mem_graph_iff.mp hw
  have hp := hf td wd
  rw [htt, hte, hww, hwe] at hp
  simp only [inner_smul_left, inner_smul_right, inner_sub_right, inner_add_right,
    Complex.conj_ofReal] at hp
  linear_combination hp
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
theorem actual_simple_germs_zero_eigentest_pairing
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (hf : DifferentiableOn ℂ f Ω) (hc : (0 : ℂ) ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ Ω ∧
      ∃ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball 0 r) ∧
        (∀ s ∈ Metric.ball 0 r, s ≠ 0 →
          w s = s • v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s) ∧
        (∀ t : Hactual, (t, a 0 • t) ∈ (Δactual).graph →
          inner ℂ t (source.h 0) = deriv a 0 * inner ℂ t (w 0)) := by
  obtain ⟨r, hr, hb, w, hw, he, hg⟩ :=
    actual_simple_germs_first_graph F ζ hζ C R P H U μG hμG hR realization
      ι buffer Ω f χ source hι hStage hΩopen hΩ hf 0 hc
  refine ⟨r,hr,hb,w,hw,?_,?_⟩
  · simpa only [sub_zero] using he
  · intro t ht
    have hs := (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ
      μG hμG level R hR P H realization).laplacian_selfadjoint
    have ha : a 0 = ((8 * (d : ℝ) / 9 : ℝ) : ℂ) := by
      rw [KPContinuation.spectralCoordinate_zero]
      push_cast
      rfl
    rw [ha] at ht hg
    exact FourierContinuation.ResidualHilbertCenters.first_graph_eigentest_pairing
      Δactual hs (8 * (d : ℝ) / 9) (deriv a 0) t (w 0) (deriv w 0) (source.h 0) ht hg
end DedekindZetaZeroFree.KPContActualHilbertSimpleGerms

end
