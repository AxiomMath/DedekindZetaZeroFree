module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Spherical.HilbertResolventGerms
public import DedekindZetaZeroFree.Eisenstein.Continuation.PoleClearedSmoothResolvent

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualClearedNegativeGraph

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

local notation "Δactual" => KPContActualSectorFriedrichsSynthesis.Δ_U
  F ζ hζ level R P H μG hμG hR realization

local notation "Bactual" => KPContActualSectorFriedrichsSynthesis.B_U
  F ζ hζ level R P H μG hμG hR realization

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)

def GraphEquationOn (s₀ : ℂ) (w : ℂ → Hactual) (O : Set ℂ) : Prop :=
  (∀ s ∈ O, ∃ hs : w s ∈ (Δactual).domain,
    Δactual ⟨w s, hs⟩ = a s • w s - (s - s₀) • source.h s) ∧
  KPClearedResolvent.GraphHolomorphicOn Δactual w
    (fun s => a s • w s - (s - s₀) • source.h s) O

end DedekindZetaZeroFree.KPContActualClearedNegativeGraph

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cleared_negative_graph
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (_hΩopen : IsOpen Ω) (_hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (_hf : DifferentiableOn ℂ f Ω)
    {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (s₀ : ℂ) (_hs₀ : s₀ ∈ Ω) (r : ℝ) (_hr : 0 < r)
    (_hball : Metric.ball s₀ r ⊆ Ω)
    (_hisolates : Metric.ball s₀ r ∩
      KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω ⊆ {s₀})
    (w : ℂ → KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (_hw : DifferentiableOn ℂ w (Metric.ball s₀ r))
    (_hclears : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ →
      w s = (s - s₀) • KPContActualHilbertSimpleGerms.v
        F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s) :
    KPContActualClearedNegativeGraph.GraphEquationOn
      F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s₀ w
      (Metric.ball s₀ r) ∧
    (∀ r' : ℝ, 0 < r' → r' ≤ r →
      KPContActualClearedNegativeGraph.GraphEquationOn
        F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s₀ w
        (Metric.ball s₀ r')) := by
  have hcp := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hfin : Module.finrank ℚ F = 2 * NumberField.InfinitePlace.nrComplexPlaces F := by
    have h := hrank
    rw [hcp.1, zero_add] at h
    omega
  have hdeq : ((Module.finrank ℚ F / 2 : ℕ) : ℝ) = (Module.finrank ℚ F : ℝ) / 2 := by
    rw [← hcp.2.1, hfin]; push_cast; ring
  have hdeqZ : (((Module.finrank ℚ F / 2 : ℕ) : ℤ) : ℝ) =
      (Module.finrank ℚ F : ℝ) / 2 := by
    exact_mod_cast hdeq
  have hd : 0 < Module.finrank ℚ F / 2 :=
    KPContFlatArchDiagonalMultiplier.complexDimension_pos F ζ hζ
  have hdZ : 0 < ((Module.finrank ℚ F / 2 : ℕ) : ℤ) := by exact_mod_cast hd
  have hprops := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U μG hμG hR realization
    ι _hι _hStage Ω _hΩopen _hΩ f _hf buffer χ source
  have hspec := kp_cont_actual_sector_resolvent_specialization F ζ hζ μG hμG
    (KPContActualAllCuspSource.level F ζ hζ C R P H U) R hR P H realization
  have hcl : ((KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization)).IsClosed :=
    (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R hR P H
      realization).friedrichs.laplacian_closed
  have hcorr : ∀ s : ℂ, KPClearedResolvent.correction (Module.finrank ℚ F / 2) (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization)
      (fun s => -source.h s) s =
      KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization
        ι buffer Ω f χ source s := by
    intro s
    simp only [KPClearedResolvent.correction, KPContActualHilbertSimpleGerms.v, map_neg]
  have hw0 : s₀ ∉ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
      realization Ω → w s₀ = 0 := by
    intro hSig
    obtain ⟨r', hr', _hball', _, w', hw'diff, hw'clear, -, hw'zero⟩ :=
      hprops.simple_germs s₀ _hs₀
    have hw'0 : w' s₀ = 0 := hw'zero hSig
    have hmin : 0 < min r r' := lt_min _hr hr'
    have hcont : Filter.Tendsto (fun s => w s - w' s) (𝓝[≠] s₀) (𝓝 (w s₀ - w' s₀)) := by
      have hc : ContinuousAt (fun s => w s - w' s) s₀ :=
        ((_hw.continuousOn.continuousAt (Metric.ball_mem_nhds s₀ _hr)).sub
          (hw'diff.continuousOn.continuousAt (Metric.ball_mem_nhds s₀ hr')))
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun s => w s - w' s) =ᶠ[𝓝[≠] s₀] (fun _ => (0 : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)) := by
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds s₀ hmin] with s hsB hsne
      rw [_hclears s (Metric.ball_subset_ball (min_le_left _ _) hsB) hsne,
        hw'clear s (Metric.ball_subset_ball (min_le_right _ _) hsB) hsne]
      simp
    have hlim := tendsto_nhds_unique_of_eventuallyEq hcont tendsto_const_nhds hev
    rw [sub_eq_zero.mp hlim, hw'0]
  have aux : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      KPContActualClearedNegativeGraph.GraphEquationOn
        F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s₀ w
        (Metric.ball s₀ ρ) := by
    intro ρ hρ hρr
    have hρr' : Metric.ball s₀ ρ ⊆ Metric.ball s₀ r := Metric.ball_subset_ball hρr
    have hballρ : Metric.ball s₀ ρ ⊆ Ω := hρr'.trans _hball
    have hdisc : IsDiscrete (Metric.ball s₀ ρ ∩
        KPClearedResolvent.parameterPoleSet (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (Module.finrank ℚ F / 2)) := by
      apply Set.Subsingleton.isDiscrete
      intro x hx y hy
      have hxS : x ∈ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
          realization Ω := ⟨hballρ hx.1, hx.2⟩
      have hyS : y ∈ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
          realization Ω := ⟨hballρ hy.1, hy.2⟩
      have hx0 : x = s₀ := by simpa using _hisolates ⟨hρr' hx.1, hxS⟩
      have hy0 : y = s₀ := by simpa using _hisolates ⟨hρr' hy.1, hyS⟩
      rw [hx0, hy0]
    have hRρ : ∀ s ∈ Metric.ball s₀ ρ \
        KPClearedResolvent.parameterPoleSet (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (Module.finrank ℚ F / 2),
        KPResolventPencil.GenuineInverse (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s)
          (KPResolventPencil.shiftedResolvent (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s)) := by
      intro s hs
      rcases hs with ⟨hsball, hsS⟩
      have hsSpec : s ∈ KPContinuation.spectralDomain := _hΩ (hballρ hsball)
      have hzAvoid : KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s ∈
          (KPContinuation.thresholdRay ((Module.finrank ℚ F / 2 : ℕ) : ℤ))ᶜ :=
        KPContinuation.spectralCoordinate_avoids_thresholdRay
          ((Module.finrank ℚ F / 2 : ℕ) : ℤ) hdZ (Set.mem_image_of_mem _ hsSpec)
      have hzdom : KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s ∈ KPBelowThresholdResolvent.domain ((Module.finrank ℚ F : ℝ) / 2) := by
        rw [KPBelowThresholdResolvent.domain]
        rintro ⟨t, ht, htz⟩
        exact hzAvoid ⟨by rw [← htz]; simp,
          by rw [← htz, Complex.ofReal_re, hdeqZ]; exact ht⟩
      have hzpole : KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s ∉ KPBelowThresholdResolvent.poleSet (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization)
          ((Module.finrank ℚ F : ℝ) / 2) := fun hmem =>
        hsS (by
          show KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s ∈ KPBelowThresholdResolvent.poleSet (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (((Module.finrank ℚ F / 2 : ℕ)) : ℝ)
          rwa [hdeq])
      have hg := (hspec.genuine_inverse_off_poles (KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s) ⟨hzdom, hzpole⟩).1
      rwa [hspec.resolvent_exact (KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s)] at hg
    have hclearsρ : ∀ s ∈ Metric.ball s₀ ρ \
        KPClearedResolvent.parameterPoleSet (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (Module.finrank ℚ F / 2),
        w s = (fun s => s - s₀) s •
          KPClearedResolvent.correction (Module.finrank ℚ F / 2) (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization)
            (fun s => -source.h s) s := by
      intro s hs
      rcases hs with ⟨hsball, hsS⟩
      by_cases hss : s = s₀
      · subst hss
        have hSig : s ∉ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
            realization Ω := fun h => hsS (by
              show KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s ∈ KPBelowThresholdResolvent.poleSet (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) (((Module.finrank ℚ F / 2 : ℕ)) : ℝ)
              simpa only [hdeq] using h.2)
        rw [hw0 hSig]; simp
      · rw [_hclears s (hρr' hsball) hss, hcorr s]
    have hwρ : DifferentiableOn ℂ w (Metric.ball s₀ ρ) := _hw.mono hρr'
    have hhρ : DifferentiableOn ℂ (fun s => -source.h s) (Metric.ball s₀ ρ) :=
      (source.hilbert_holomorphic.mono hballρ).neg
    have hqρ : DifferentiableOn ℂ (fun s => s - s₀) (Metric.ball s₀ ρ) := by fun_prop
    have hqneρ : ∃ s ∈ Metric.ball s₀ ρ, (fun s => s - s₀) s ≠ 0 := by
      refine ⟨s₀ + (↑(ρ / 2) : ℂ), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · simp [hρ.ne']
    have key := kp_cont_local_cleared_resolvent (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization) hcl (Module.finrank ℚ F / 2) hd (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization)
      s₀ ρ hρ (hballρ.trans _hΩ) hdisc hRρ (fun s => -source.h s) w (fun s => s - s₀)
      hhρ hqρ hqneρ hwρ hclearsρ
    refine ⟨?_, ?_⟩
    · intro s hs
      obtain ⟨hsd, heq⟩ := key.1 s hs
      exact ⟨hsd, by rw [heq, smul_neg]; abel⟩
    · rw [show (fun s => KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s • w s - (s - s₀) • source.h s) =
          (fun s => KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s • w s + (s - s₀) • (-source.h s)) from by
        funext s; rw [smul_neg]; abel]
      exact key.2
  exact ⟨aux r _hr le_rfl, fun r' hr' hr'r => aux r' hr' hr'r⟩

end DedekindZetaZeroFree

end
