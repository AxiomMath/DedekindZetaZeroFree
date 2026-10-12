module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Resolvent.CutoffAndClearedGerms

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualClearedSmoothRepresentatives

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Hactual" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Represents" => KPContActualSmoothLineGluing.Represents F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)

local notation "vactual" => KPContActualHilbertSimpleGerms.v
  F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source
local notation "Σactual" => KPContActualHilbertSimpleGerms.Sigma
  F ζ hζ C R P H U μG hμG hR realization Ω

structure GermPromotion (V : ℂ → Smooth) (s₀ : ℂ) (r : ℝ) (w : ℂ → Hactual) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ r

  graph : KPContActualClearedNegativeGraph.GraphEquationOn
    F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s₀ w
    (Metric.ball s₀ radius)
  cleared : KPContActualCutoffPlusClearedGerm.ClearedNumerator
    F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source V s₀ radius w

  representative_data : KPContActualCutoffPlusClearedGerm.SmoothTaylorData
    F ζ hζ C R P H U (Metric.ball s₀ radius) cleared.W

structure Properties (V : ℂ → Smooth) : Prop where
  continuation : KPContActualCutoffPlusClearedGerm.Properties
    F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source V

  every_germ : ∀ s₀ ∈ Ω, ∀ r : ℝ, 0 < r → Metric.ball s₀ r ⊆ Ω →
    Metric.ball s₀ r ∩ Σactual ⊆ {s₀} →
    ∀ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball s₀ r) →
    (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • vactual s) →
    Nonempty (GermPromotion F ζ hζ C R P H U μG hμG hR realization
      ι buffer Ω f χ source V s₀ r w)

  overlaps : KPContActualSmoothLineGluing.Separation F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H

  same_class : ∀ (u : Hactual) (Z Z' : Smooth),
    Represents Z.val u → Represents Z'.val u → Z = Z'

end DedekindZetaZeroFree.KPContActualClearedSmoothRepresentatives

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cleared_smooth_representatives
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
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ) :
    ∃ V : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U,
      KPContActualClearedSmoothRepresentatives.Properties
        F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source V := by
  classical

  obtain ⟨V, hV⟩ := kp_cont_actual_cutoff_plus_cleared_germ F ζ hζ C R P H U μG hμG hR
    realization ι _hι _hStage Ω _hΩopen _hΩ f _hf buffer χ source
  refine ⟨V, ?_⟩
  refine ⟨hV, ?_, ?_, ?_⟩
  ·

    intro s₀ hs₀ r hr hball hisol w hw hclears
    obtain ⟨cn⟩ := hV.every_germ s₀ hs₀ r hr hball hisol w hw hclears
    obtain ⟨hg, _⟩ := kp_cont_actual_cleared_negative_graph F ζ hζ C R P H U μG hμG hR
      realization ι _hι _hStage Ω _hΩopen _hΩ f _hf buffer χ source s₀ hs₀ r hr hball
      hisol w hw hclears
    exact ⟨{ radius := r
             radius_pos := hr
             radius_le := le_rfl
             graph := hg
             cleared := cn
             representative_data :=
               kp_cont_actual_cleared_smooth_promotion F ζ hζ C R P H U realization
                 (Metric.ball s₀ r) Metric.isOpen_ball w cn.W cn.correction_holomorphy }⟩
  ·
    exact (kp_cont_actual_smooth_line_gluing F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H realization).separation
  ·
    intro u Z Z' hZ hZ'
    obtain ⟨hf, hfeq⟩ := hZ
    obtain ⟨hf', hf'eq⟩ := hZ'
    haveI : (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R (KPContActualAllCuspSource.level F ζ hζ C R P H U)).IsOpenPosMeasure :=
      realization.support.covered_open_positive
    have hae : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z.val).val
        =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R (KPContActualAllCuspSource.level F ζ hζ C R P H U)]
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z'.val).val :=
      (MeasureTheory.MemLp.toLp_eq_toLp_iff hf hf').mp (hfeq.trans hf'eq.symm)
    have hcont : Continuous
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z.val).val :=
      (KPContSectorLineL2Isometry.continuous_iff F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z.val).mp
        (fun i => (Z.2 i).continuous)
    have hcont' : Continuous
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z'.val).val :=
      (KPContSectorLineL2Isometry.continuous_iff F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z'.val).mp
        (fun i => (Z'.2 i).continuous)
    have hfun := MeasureTheory.Measure.eq_of_ae_eq hae hcont hcont'
    have hscalar : KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z.val =
        KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z'.val :=
      Subtype.ext hfun
    have hsymm : (KPContSectorScalarLineAlgebra.S F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm Z.val =
        (KPContSectorScalarLineAlgebra.S F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm Z'.val := by
      rw [← KPContSectorLineL2Isometry.scalarRepresentative_eq_symm F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z.val,
        ← KPContSectorLineL2Isometry.scalarRepresentative_eq_symm F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H Z'.val]
      exact hscalar
    refine Subtype.ext ?_
    have := congrArg (KPContSectorScalarLineAlgebra.S F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H) hsymm
    simpa using this

end DedekindZetaZeroFree

end
