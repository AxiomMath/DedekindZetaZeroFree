module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothHolomorphy.TaylorData

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

section CauchyHelpers
set_option maxHeartbeats 600000
open KPContLocalNorm KPContLocalHolomorphyUpgrade.CauchyAssembly

private theorem chartJetContinuous {n : ℕ} (A : LocalBall n)
    (Ω : Set ℂ) (h : ℂ → Space n → ℂ)
    (hh : KPCutoffSource.ChartSmoothHolomorphicOn A h Ω) : Raw.JetContinuousOn A h Ω := by
  intro z₀ hz₀ K hK hKA m ε hε
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j, hj, hspec⟩ := hh.2 K hK hKA m
  obtain ⟨δ, hδ, hd⟩ := hilbert_difference_small Ω j hj.continuousOn hz₀ hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz hdist α x
  have hb := hd z hz hdist
  have hp := (ContinuousMap.norm_coe_le_norm ((j z - j z₀) α) x).trans
    (norm_le_pi_norm (j z - j z₀) α)
  change ‖j z α x - j z₀ α x‖ ≤ _ at hp
  rw [hspec z hz α x, hspec z₀ hz₀ α x] at hp
  rw [coordinateDerivative, finite_coordinate_derivative_sub A (hh.1 z hz) (hh.1 z₀ hz₀)
    α.directions (hKA x.property), ← coordinateDerivative, ← coordinateDerivative]
  exact hp.trans_lt hb

private theorem scalarJetHolomorphic {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)
    (f : ℂ → Space n → ℂ) (hf : KPCutoffSource.ChartSmoothHolomorphicOn A f Ω)
    (m : ℕ) (α : MultiIndex n m) (x : Space n) (hx : x ∈ A.carrier) :
    DifferentiableOn ℂ (fun s => coordinateDerivative α (f s) x) Ω := by
  let K : Set (Space n) := {x}
  have hKA : K ⊆ A.carrier := Set.singleton_subset_iff.mpr hx
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_singleton : IsCompact K)
  obtain ⟨j, hj, hv⟩ := hf.2 K isCompact_singleton hKA m
  let L : CompactJets K m →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨x, rfl⟩ : K)).comp (ContinuousLinearMap.proj α)
  exact (L.differentiable.comp_differentiableOn hj).congr (fun s hs => (hv s hs α ⟨x, rfl⟩).symm)

 def scalarCauchy (f : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (j : ℕ) : ℂ :=
  (cauchyPowerSeries f c ρ j) (fun _ => 1)

private theorem scalarCauchySeries {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)
    (f : ℂ → Space n → ℂ) (hf : KPCutoffSource.ChartSmoothHolomorphicOn A f Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) :
    SmoothPowerSeriesOn A c ρ (fun j x => scalarCauchy (fun s => f s x) c ρ j) f := by
  let b := fun j x => scalarCauchy (fun s => f s x) c ρ j
  have hj := chartJetContinuous A Ω f hf
  have hb := fun j => ContourLift.coefficient_smooth_and_derivatives A Ω f hf.1 hj c ρ hρ hclosed j
  refine ⟨fun j => (hb j).1, fun s hs => hf.1 s (hclosed (Metric.ball_subset_closedBall hs)), ?_⟩
  intro K hK hKA m r hr hrρ ε hε
  have hhol : ∀ m (α : MultiIndex n m) x, x ∈ A.carrier →
      DifferentiableOn ℂ (fun s => coordinateDerivative α (f s) x) (Metric.ball c ρ) := by
    intro m α x hx
    exact (scalarJetHolomorphic A Ω f hf m α x hx).mono (Metric.ball_subset_closedBall.trans hclosed)
  obtain ⟨N, hN⟩ := ContourLift.scalar_jet_cauchy_uniform A Ω f hf.1 hj c ρ hρ hclosed hhol
    K hK hKA m r hr hrρ ε hε
  refine ⟨N, ?_⟩
  intro M hM z hz α x
  have hzΩ := hclosed ((Metric.closedBall_subset_closedBall hrρ.le) hz)
  rw [coordinate_derivative_taylor_remainder A b (fun j => (hb j).1) (f z) (hf.1 z hzΩ)
    (z - c) M α (hKA x.property)]
  have hd : ∀ j, coordinateDerivative α (b j) x = scalarCauchy
      (fun s => coordinateDerivative α (f s) x) c ρ j := fun j => (hb j).2 m α (hKA x.property)
  simp only [hd]
  exact hN M hM z hz α x

 theorem scalarCauchy_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (j : ℕ) :
    scalarCauchy (fun z => a * f z) c ρ j = a * scalarCauchy f c ρ j := by
  simp only [scalarCauchy, cauchyPowerSeries_apply, one_div, smul_eq_mul]
  have he : (fun z => (z - c)⁻¹ ^ j * ((z - c)⁻¹ * (a * f z))) =
      fun z => a * ((z - c)⁻¹ ^ j * ((z - c)⁻¹ * f z)) := by funext z; ring
  rw [he, circleIntegral.integral_const_mul]
  ring

open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open KPContActualChartRestrictionDensity KPContActualSmoothLineGluing
open NumberField IsDedekindDomain
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
  (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
  (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
  (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

private theorem coefficient_identity (w : Sections F ζ hζ U R P H)
    (A : ChartBall F ζ hζ U R P H) (hphase : A.phase = phaseClass F ζ hζ U 1)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    coefficient F ζ hζ U R P H w A p = (w A.component).val (coordinates F p) := by
  unfold coefficient
  rw [hphase, frameCoefficient_class, scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  simp

 def cauchySections (w : ℂ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (ρ : ℝ) (j : ℕ) : Sections F ζ hζ U R P H := by
  intro i
  refine ⟨fun x => scalarCauchy (fun s => ((w s).val i).val x) c ρ j, ?_, ?_⟩
  · intro x ε hε
    have he : (fun s => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * ((w s).val i).val x) =
        (fun s => ((w s).val i).val x) :=
      funext fun s => ((w s).val i).property.1 x ε hε
    exact (scalarCauchy_const_mul _ _ c ρ j).symm.trans (congrArg (fun f => scalarCauchy f c ρ j) he)
  · intro γ x
    have he : (fun s => ((w s).val i).val ((γ : KPCuspArithmetic.PGL2 F) • x)) =
        fun s => (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) *
          ((w s).val i).val x := funext fun s => ((w s).val i).property.2 γ x
    exact (congrArg (fun f => scalarCauchy f c ρ j) he).trans (scalarCauchy_const_mul _ _ c ρ j)

private theorem cauchySections_coordinate (w : ℂ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (ρ : ℝ) (j : ℕ) (A : ChartBall F ζ hζ U R P H)
    (hphase : A.phase = phaseClass F ζ hζ U 1) (p : Space (KPCuspLogShape.dimension F * 3)) :
    (cauchySections F ζ hζ U R P H w c ρ j A.component).val (coordinates F p) =
      scalarCauchy (fun s => coefficient F ζ hζ U R P H (w s).val A p) c ρ j := by
  apply congrArg (fun f => scalarCauchy f c ρ j)
  funext s
  exact (coefficient_identity F ζ hζ U R P H (w s).val A hphase p).symm

 theorem cauchySections_smooth (w : ℂ → smoothSections F ζ hζ U R P H)
    (Ω : Set ℂ)
    (hlocal : ∀ A : ChartBall F ζ hζ U R P H, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient F ζ hζ U R P H (w s).val A) Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) (j : ℕ) :
    IsSmoothSections F ζ hζ U R P H (cauchySections F ζ hζ U R P H w c ρ j) := by
  intro i
  have hsp : ContDiff ℝ (⊤ : ℕ∞) (fun p =>
      (cauchySections F ζ hζ U R P H w c ρ j i).val (coordinates F p)) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    let A := canonicalChartBall F ζ hζ U R P H i (coordinates F p) (phaseClass F ζ hζ U 1)
    have hp : p ∈ A.ball.carrier := by
      simpa only [Homeomorph.symm_apply_apply] using canonicalChartBall_mem F ζ hζ U R P H i
        (coordinates F p) (phaseClass F ζ hζ U 1)
    have hf := hlocal A
    have hb := (ContourLift.coefficient_smooth_and_derivatives A.ball Ω _ hf.1
      (chartJetContinuous A.ball Ω _ hf) c ρ hρ hclosed j).1
    have he : (fun q => (cauchySections F ζ hζ U R P H w c ρ j i).val (coordinates F q)) =
        (fun q => scalarCauchy (fun s => coefficient F ζ hζ U R P H (w s).val A q) c ρ j) := by
      funext q
      exact cauchySections_coordinate F ζ hζ U R P H w c ρ j A rfl q
    exact ((hb p hp).contDiffAt (Metric.isOpen_ball.mem_nhds hp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (congrFun he))
  have hc := hsp.comp (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff
    (KPCuspLogShape.dimension F))
  have he : ((fun p => (cauchySections F ζ hζ U R P H w c ρ j i).val (coordinates F p)) ∘
      (coordinates F).symm) = (cauchySections F ζ hζ U R P H w c ρ j i).val := by
    funext x
    exact congrArg (cauchySections F ζ hζ U R P H w c ρ j i).val ((coordinates F).apply_symm_apply x)
  change ContDiff ℝ (⊤ : ℕ∞) ((fun p => (cauchySections F ζ hζ U R P H w c ρ j i).val
    (coordinates F p)) ∘ (coordinates F).symm) at hc
  rwa [he] at hc

 def cauchySmoothSections (w : ℂ → smoothSections F ζ hζ U R P H) (Ω : Set ℂ)
    (hlocal : ∀ A : ChartBall F ζ hζ U R P H, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient F ζ hζ U R P H (w s).val A) Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) (j : ℕ) :
    smoothSections F ζ hζ U R P H :=
  ⟨cauchySections F ζ hζ U R P H w c ρ j,
    cauchySections_smooth F ζ hζ U R P H w Ω hlocal c ρ hρ hclosed j⟩

private theorem cauchySections_coefficient (w : ℂ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (ρ : ℝ) (j : ℕ) (A : ChartBall F ζ hζ U R P H)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    coefficient F ζ hζ U R P H (cauchySections F ζ hζ U R P H w c ρ j) A p =
      scalarCauchy (fun s => coefficient F ζ hζ U R P H (w s).val A p) c ρ j := by
  obtain ⟨ε, hε⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) A.phase
  change phaseClass F ζ hζ U ε = A.phase at hε
  have hcoef (v : Sections F ζ hζ U R P H) : coefficient F ζ hζ U R P H v A p =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (v A.component).val (coordinates F p) := by
    unfold coefficient
    rw [← hε, frameCoefficient_class, scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply, chi_coe]
  rw [hcoef]
  change _ * scalarCauchy (fun s => ((w s).val A.component).val (coordinates F p)) c ρ j = _
  rw [← scalarCauchy_const_mul]
  apply congrArg (fun f => scalarCauchy f c ρ j)
  funext s
  exact (hcoef (w s).val).symm

private theorem genuineCommonDisk (w : ℂ → smoothSections F ζ hζ U R P H) (Ω : Set ℂ)
    (hlocal : ∀ A : ChartBall F ζ hζ U R P H, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient F ζ hζ U R P H (w s).val A) Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) :
    ∃ b : ℕ → smoothSections F ζ hζ U R P H, ∀ A : ChartBall F ζ hζ U R P H,
      SmoothPowerSeriesOn A.ball c ρ (fun j => coefficient F ζ hζ U R P H (b j).val A)
        (fun s => coefficient F ζ hζ U R P H (w s).val A) := by
  refine ⟨cauchySmoothSections F ζ hζ U R P H w Ω hlocal c ρ hρ hclosed, ?_⟩
  intro A
  have he : (fun j => coefficient F ζ hζ U R P H
      (cauchySmoothSections F ζ hζ U R P H w Ω hlocal c ρ hρ hclosed j).val A) =
      fun j p => scalarCauchy (fun s => coefficient F ζ hζ U R P H (w s).val A p) c ρ j := by
    funext j p
    exact cauchySections_coefficient F ζ hζ U R P H w c ρ j A p
  rw [he]
  exact scalarCauchySeries A.ball Ω _ (hlocal A) c ρ hρ hclosed

end CauchyHelpers

theorem actual_cutoff_common_disk_coefficients
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ}
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (hΩ : IsOpen Ω) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hclosed : Metric.closedBall c ρ ⊆ Ω) :
    ∃ b : ℕ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U,
      ∀ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H,
      KPContLocalNorm.SmoothPowerSeriesOn A.ball c ρ
        (fun j => KPContActualSmoothLineGluing.coefficient F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (b j).val A)
        (fun s => KPContActualSmoothLineGluing.coefficient F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          (source.descent.cutoff s).val A) := by
  let V := KPContActualAllCuspSource.level F ζ hζ C R P H U
  have hlocal : ∀ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ V R P H,
      KPCutoffSource.ChartSmoothHolomorphicOn A.ball
        (fun s => KPContActualSmoothLineGluing.coefficient F ζ hζ V R P H
          (source.descent.cutoff s).val A) Ω := by
    intro A
    have hh := (source.local_holomorphy A.component A.center A.chart A.phase A.ball A.contained).1
    have hcoef (w : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U) :
        KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w A.component A.phase =
          KPContActualSmoothLineGluing.coefficient F ζ hζ V R P H w.val A := by
      unfold KPContActualAllCuspSource.chartCoefficient KPContActualSmoothLineGluing.coefficient
      have he : ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ V R P H).symm w).val =
          KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ V R P H w.val := by
        rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
        rfl
      rw [he]
    simpa only [hcoef] using hh
  exact genuineCommonDisk F ζ hζ V R P H source.descent.cutoff Ω hlocal c ρ hρ hclosed

end DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

end
