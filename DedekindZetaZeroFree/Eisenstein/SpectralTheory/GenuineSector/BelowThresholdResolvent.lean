module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.CompactRemainderEstimate
public import DedekindZetaZeroFree.Analysis.SpectralTheory.Resolvents.BelowThresholdMeromorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorResolventSpecialization

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "Hactual" => KPContSectorClosedLpSubspace.H F ζ hζ R U
local notation "B" => KPContActualSectorFriedrichsSynthesis.B_U
  F ζ hζ U R P H μG hμG hR realization
local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U
  F ζ hζ U R P H μG hμG hR realization
local notation "d" => (Module.finrank ℚ F : ℝ) / 2

def R_U (z : ℂ) : Hactual →L[ℂ] Hactual :=
  KPResolventPencil.shiftedResolvent B z

local notation "Ractual" => R_U F ζ hζ U R P H μG hμG hR realization

structure Properties : Prop where
  threshold_positive : 0 < d

  compact_remainder : ∀ ε : ℝ, 0 < ε →
    ∃ K : Hactual →L[ℂ] Hactual, IsCompactOperator K ∧
      ∀ u : Hactual, (d - ε) * ‖B u‖ ^ 2 ≤
        (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2

  resolvent_exact : ∀ z : ℂ, Ractual z = KPResolventPencil.shiftedResolvent B z
  norm_meromorphic : MeromorphicOn Ractual (KPBelowThresholdResolvent.domain d)
  full_inverse_region :
    KPResolventPencil.resolventSet Δ ∩ KPBelowThresholdResolvent.domain d =
      KPBelowThresholdResolvent.domain d \ KPBelowThresholdResolvent.poleSet Δ d
  base_inverse : KPResolventPencil.GenuineInverse Δ (-1) B
  base_value : Ractual (-1) = B
  bounded_positive : (B).IsPositive
  bounded_selfadjoint : IsSelfAdjoint B
  bounded_contraction : ‖B‖ ≤ 1
  norm_holomorphic_off_poles : AnalyticOnNhd ℂ Ractual
    (KPBelowThresholdResolvent.domain d \ KPBelowThresholdResolvent.poleSet Δ d)
  genuine_inverse_off_poles :
    ∀ z ∈ KPBelowThresholdResolvent.domain d \ KPBelowThresholdResolvent.poleSet Δ d,
      KPResolventPencil.GenuineInverse Δ z (Ractual z) ∧
      (∀ u : Hactual, Ractual z u ∈ (Δ).domain) ∧
      ∀ Q : Hactual →L[ℂ] Hactual, KPResolventPencil.GenuineInverse Δ z Q → Q = Ractual z

  poles_locally_finite : ∀ z ∈ KPBelowThresholdResolvent.domain d,
    ∃ r : ℝ, 0 < r ∧
      (KPBelowThresholdResolvent.poleSet Δ d ∩ Metric.closedBall z r).Finite

  exact_simple_poles : ∀ z ∈ KPBelowThresholdResolvent.domain d,
    z ∈ KPBelowThresholdResolvent.poleSet Δ d ↔
      meromorphicOrderAt Ractual z = ((-1 : ℤ) : WithTop ℤ)

  full_orthogonal_laurent :
    ∀ μ : ℝ, μ < d → KPBelowThreshold.eigenspace Δ μ ≠ ⊥ →
      0 ≤ μ ∧
      KPBelowThresholdResolvent.poleProjection B μ ≠ 0 ∧
      IsSelfAdjoint (KPBelowThresholdResolvent.poleProjection B μ) ∧
      KPBelowThresholdResolvent.poleProjection B μ *
        KPBelowThresholdResolvent.poleProjection B μ =
          KPBelowThresholdResolvent.poleProjection B μ ∧
      (KPBelowThresholdResolvent.poleProjection B μ).range =
        KPBelowThreshold.eigenspace Δ μ ∧
      FiniteDimensional ℂ (KPBelowThresholdResolvent.poleProjection B μ).range ∧
      (∀ u : Hactual, u ∈ KPBelowThreshold.eigenspace Δ μ →
        KPBelowThresholdResolvent.poleProjection B μ u = u) ∧
      Filter.Tendsto (fun z : ℂ => (z - (μ : ℂ)) • Ractual z)
        (𝓝[≠] (μ : ℂ)) (𝓝 (-KPBelowThresholdResolvent.poleProjection B μ)) ∧
      (¬ ∃ G : ℂ → (Hactual →L[ℂ] Hactual),
        ContinuousAt G (μ : ℂ) ∧ G =ᶠ[𝓝[≠] (μ : ℂ)] Ractual) ∧
      ∃ r : ℝ, 0 < r ∧
        Metric.ball (μ : ℂ) r ⊆ KPBelowThresholdResolvent.domain d ∧
        AnalyticOnNhd ℂ (KPIsolatedLaurent.holomorphicComplement B ((1 + μ)⁻¹))
          (Metric.ball (μ : ℂ) r) ∧
        ∀ z : ℂ, 0 < ‖z - (μ : ℂ)‖ → ‖z - (μ : ℂ)‖ < r →
          z ∈ KPResolventPencil.resolventSet Δ ∧
          Ractual z = ((μ : ℂ) - z)⁻¹ • KPBelowThresholdResolvent.poleProjection B μ +
            KPIsolatedLaurent.holomorphicComplement B ((1 + μ)⁻¹) z

end DedekindZetaZeroFree.KPContActualSectorResolventSpecialization

namespace DedekindZetaZeroFree

private theorem eigen_not_resolvent_aux
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (μ : ℝ)
    (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) :
    (μ : ℂ) ∉ KPResolventPencil.resolventSet Δ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
  obtain ⟨v, hv, rfl⟩ := (Submodule.mem_map).mp hx
  intro hres
  obtain ⟨R, hR⟩ := hres
  have h := hR.2.2 v
  have hz : Δ v - (μ : ℂ) • (v : H) = 0 := hv
  rw [hz, map_zero] at h
  exact hx0 h.symm

theorem kp_cont_actual_sector_resolvent_specialization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorResolventSpecialization.Properties
      F ζ hζ U R P H μG hμG hR realization := by
  classical
  have hd : (0 : ℝ) < (Module.finrank ℚ F : ℝ) / 2 := by
    have h1 : 0 < Module.finrank ℚ F := Module.finrank_pos
    positivity
  have hcoer : ∀ ε : ℝ, 0 < ε →
      ∃ K : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ]
          KPContSectorClosedLpSubspace.H F ζ hζ R U,
        IsCompactOperator K ∧
        ∀ u : KPContSectorClosedLpSubspace.H F ζ hζ R U,
          ((Module.finrank ℚ F : ℝ) / 2 - ε) *
              ‖KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
                realization u‖ ^ 2 ≤
            (inner ℂ
              (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
                realization u)
              (u - KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
                realization u)).re + ‖K u‖ ^ 2 :=
    kp_cont_actual_compact_remainder_estimate F ζ hζ μG hμG U R hR P H realization
  have hfr := (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H
    realization).friedrichs
  obtain ⟨hmem, hbaseval, hBpos, hBsa, hBnorm, hmero, hregion, hanalytic,
    hinvoff, hpoles, hlaurent⟩ :=
    kp_cont_below_threshold_resolvent
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
      hfr.laplacian_dense
      (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR realization)
      ((Module.finrank ℚ F : ℝ) / 2) hd hfr.laplacian_selfadjoint
      hfr.laplacian_nonnegative hfr.genuine_inverse hcoer
  obtain ⟨_, _, _, _, _, _, hreal, _, _, _, hwindow, _⟩ :=
    kp_cont_resolvent_spectrum_transfer
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
      hfr.laplacian_dense
      (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR realization)
      ((Module.finrank ℚ F : ℝ) / 2) hd hfr.laplacian_selfadjoint
      hfr.laplacian_nonnegative hfr.genuine_inverse hcoer
  refine ⟨hd, hcoer, (fun z => rfl), ?_, hregion, hfr.genuine_inverse, ?_,
    hBpos, hBsa, hBnorm, ?_, ?_, ?_, ?_, ?_⟩
  · exact hmero
  · exact hbaseval
  · exact hanalytic
  · intro z hz
    exact hinvoff z hz
  ·
    intro z hz
    by_cases hzim : z.im = 0
    ·
      have hzre : z.re < (Module.finrank ℚ F : ℝ) / 2 := by
        by_contra h
        exact hz ⟨z.re, not_lt.mp h, Complex.ext (by simp) (by simp [hzim])⟩
      set r : ℝ := ((Module.finrank ℚ F : ℝ) / 2 - z.re) / 2 with hrdef
      have hr : 0 < r := by rw [hrdef]; linarith
      have hbd : z.re + r < (Module.finrank ℚ F : ℝ) / 2 := by rw [hrdef]; linarith
      have hfin : (KPBelowThreshold.realSpectrum
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) ∩ Set.Icc (z.re - r) (z.re + r)).Finite :=
        hwindow (z.re - r) (z.re + r) hbd
      refine ⟨r, hr, Set.Finite.subset (hfin.image Complex.ofReal) ?_⟩
      intro w hw
      obtain ⟨hwP, hwB⟩ := hw
      obtain ⟨μ, hμd, heμ, rfl⟩ := hwP
      rw [Metric.mem_closedBall, dist_eq_norm] at hwB
      have hz_eq : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
      have habs : |μ - z.re| ≤ r := by
        rw [hz_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hwB
        exact hwB
      have hμmem : μ ∈ Set.Icc (z.re - r) (z.re + r) := by
        rw [Set.mem_Icc]
        exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
      have hμspec : μ ∈ KPBelowThreshold.realSpectrum
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) :=
        (hreal μ).mpr (eigen_not_resolvent_aux
          (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR
            realization) μ heμ)
      exact ⟨μ, ⟨hμspec, hμmem⟩, rfl⟩
    ·
      set r : ℝ := |z.im| / 2 with hrdef
      have hr : 0 < r := by rw [hrdef]; exact half_pos (abs_pos.mpr hzim)
      have hempty : KPBelowThresholdResolvent.poleSet
          (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR
            realization) ((Module.finrank ℚ F : ℝ) / 2) ∩ Metric.closedBall z r = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro w hw
        obtain ⟨hwP, hwB⟩ := hw
        obtain ⟨μ, -, -, rfl⟩ := hwP
        rw [Metric.mem_closedBall, dist_eq_norm] at hwB
        have h1 : |z.im| ≤ ‖(μ : ℂ) - z‖ := by
          have := RCLike.abs_im_le_norm ((μ : ℂ) - z)
          simpa using this
        have h2 : 2 * r = |z.im| := by rw [hrdef]; ring
        nlinarith [hwB, h1, h2, hr]
      refine ⟨r, hr, ?_⟩
      rw [hempty]
      exact Set.finite_empty
  · intro z hz
    exact hpoles z hz
  · intro μ hμd he
    obtain ⟨hμ0, hPne, hPsa, hPP, hPrange, hPfd, hTend, hNonrem, hDisk⟩ :=
      hlaurent μ hμd he
    have hfix : ∀ u : KPContSectorClosedLpSubspace.H F ζ hζ R U,
        u ∈ KPBelowThreshold.eigenspace
          (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR
            realization) μ →
        KPBelowThresholdResolvent.poleProjection
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) μ u = u := by
      intro u hu
      have hu' : u ∈ (KPBelowThresholdResolvent.poleProjection
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) μ).range := by
        rw [hPrange]; exact hu
      obtain ⟨v, hv⟩ := hu'
      rw [← hv]
      change (KPBelowThresholdResolvent.poleProjection
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) μ *
        KPBelowThresholdResolvent.poleProjection
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) μ) v =
        KPBelowThresholdResolvent.poleProjection
          (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR
            realization) μ v
      rw [hPP]
    exact ⟨hμ0, hPne, hPsa, hPP, hPrange, hPfd, hfix, hTend, hNonrem, hDisk⟩

end DedekindZetaZeroFree

end
