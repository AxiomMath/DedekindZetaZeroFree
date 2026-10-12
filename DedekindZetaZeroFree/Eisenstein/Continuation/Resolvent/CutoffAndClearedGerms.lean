module

public import DedekindZetaZeroFree.Eisenstein.Continuation.HolomorphicFamilies.SmoothTaylorData
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.GlobalTaylorCoefficients

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

open KPContLocalNorm KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Hactual" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Covered" => KPContActualAllCuspSource.Covered F ζ hζ C R P H U
local notation "Charts" => KPContActualSmoothLineGluing.ChartBall F ζ hζ level R P H
local notation "GroupCharts" => KPContActualSphericalRightFieldIdentification.GroupChart
  F ζ hζ level R P H
local notation "scalar" => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
local notation "coefficient" => KPContActualSmoothLineGluing.coefficient F ζ hζ level R P H
local notation "Represents" => KPContActualSmoothLineGluing.Represents F ζ hζ level R P H

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)

def E (domain poles : Set ℂ) (cutoff V : ℂ → Smooth) (s : ℂ) : Smooth :=
  if s ∈ domain \ poles then cutoff s + V s else 0

def numerator (cutoff : ℂ → Smooth) (s₀ : ℂ) (W : ℂ → Smooth) (s : ℂ) : Smooth :=
  (s - s₀) • cutoff s + W s

structure ClearedNumerator
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (V : ℂ → Smooth) (s₀ : ℂ) (r : ℝ)
    (w : ℂ → Hactual) where
  W : ℂ → Smooth
  represents : ∀ s ∈ Metric.ball s₀ r, Represents (W s).val (w s)
  unique : ∀ s ∈ Metric.ball s₀ r, ∀ Z : Smooth,
    Represents Z.val (w s) → Z = W s

  correction_holomorphy : KPContActualSmoothLineGluing.HolomorphicData
    F ζ hζ level R P H (Metric.ball s₀ r) w W
  numerator_data : SmoothTaylorData F ζ hζ C R P H U
    (Metric.ball s₀ r) ((numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W)
  punctured_sections : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ →
    (numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s = (s - s₀) • (E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s
  punctured_covered : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ →
    scalar ((numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s) = (s - s₀) • scalar ((E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s)
  punctured_charts : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ A : Charts,
    Set.EqOn (coefficient ((numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s).val A)
      ((s - s₀) • coefficient ((E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s).val A) A.ball.carrier
  punctured_group : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ →
    groupScalar F ζ hζ C R P H U ((numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s) =
      (s - s₀) • groupScalar F ζ hζ C R P H U ((E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s)
  correction_class : ∀ s ∈ Metric.ball s₀ r,
    Represents ((numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s - (s - s₀) • source.descent.cutoff s).val (w s)

  zero_extension : s₀ = 0 →
    (∀ s ∈ Metric.ball 0 r, s ≠ 0 → (numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s = s • (E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s) ∧
    (∀ s ∈ Metric.ball 0 r,
      (numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s - s • source.descent.cutoff s = W s ∧
      Represents ((numerator F ζ hζ C R P H U source.descent.cutoff) s₀ W s - s • source.descent.cutoff s).val (w s))

structure Properties
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (V : ℂ → Smooth) : Prop where
  correction_represents : ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω), Represents (V s).val ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source) s)
  correction_unique : ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω), ∀ Z : Smooth,
    Represents Z.val ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source) s) → Z = V s
  correction_holomorphy : KPContActualSmoothLineGluing.HolomorphicData
    F ζ hζ level R P H (Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω)) (KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source) V
  off_pole_class : ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω),
    Represents ((E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s - source.descent.cutoff s).val ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source) s)
  off_pole_unique : ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω), ∀ Z : Smooth,
    Represents (Z - source.descent.cutoff s).val ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source) s) → Z = (E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s
  totalization : ∀ s, s ∉ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) → (E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s = 0
  every_germ : ∀ s₀ ∈ Ω, ∀ r : ℝ, 0 < r → Metric.ball s₀ r ⊆ Ω →
    Metric.ball s₀ r ∩ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) ⊆ {s₀} →
    ∀ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball s₀ r) →
    (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • (KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source) s) →
    Nonempty (ClearedNumerator F ζ hζ C R P H U μG hμG hR ι Ω f χ
      realization buffer source V s₀ r w)
  cleared_germs : ∀ s₀ ∈ Ω,
    KPSphericalL2Formula.ClearedSmoothGerm
      (fun _ : Charts => KPCuspLogShape.dimension F * 3) (fun A => A.ball)
      (chartPullback F ζ hζ C R P H U)
      (KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ level)
      (fun s => scalar ((E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s)) Ω s₀
  cleared_at_zero : 0 ∈ Ω →
    KPSphericalL2Formula.ClearedSmoothGerm
      (fun _ : Charts => KPCuspLogShape.dimension F * 3) (fun A => A.ball)
      (chartPullback F ζ hζ C R P H U)
      (KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ level)
      (fun s => scalar ((E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) V s)) Ω 0

theorem same_class_unique
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (u : Hactual) (Z Z' : Smooth) (hZ : Represents Z.val u) (hZ' : Represents Z'.val u) :
    Z = Z' := by
  obtain ⟨hf, hfeq⟩ := hZ
  obtain ⟨hf', hf'eq⟩ := hZ'
  haveI : (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R level).IsOpenPosMeasure :=
    realization.support.covered_open_positive
  have hae : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val).val
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R level]
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z'.val).val :=
    (MeasureTheory.MemLp.toLp_eq_toLp_iff hf hf').mp (hfeq.trans hf'eq.symm)
  have hcont : Continuous
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val).val :=
    (KPContSectorLineL2Isometry.continuous_iff F ζ hζ level R P H Z.val).mp
      (fun i => (Z.2 i).continuous)
  have hcont' : Continuous
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z'.val).val :=
    (KPContSectorLineL2Isometry.continuous_iff F ζ hζ level R P H Z'.val).mp
      (fun i => (Z'.2 i).continuous)
  have hfun := MeasureTheory.Measure.eq_of_ae_eq hae hcont hcont'
  have hscalar : KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val =
      KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z'.val :=
    Subtype.ext hfun
  have hsymm : (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm Z.val =
      (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm Z'.val := by
    rw [← KPContSectorLineL2Isometry.scalarRepresentative_eq_symm F ζ hζ level R P H Z.val,
      ← KPContSectorLineL2Isometry.scalarRepresentative_eq_symm F ζ hζ level R P H Z'.val]
    exact hscalar
  refine Subtype.ext ?_
  have := congrArg (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H) hsymm
  simpa using this

 theorem represents_smul (u : Hactual) (Z : Smooth) (hZ : Represents Z.val u) (a : ℂ) :
    Represents (a • Z).val (a • u) := by
  obtain ⟨hf, he⟩ := hZ
  have hs : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H (a • Z).val).val =
      a • (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val).val := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm,
      KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    change ((KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm (a • Z.val)).val = _
    rw [map_smul]
    rfl
  refine ⟨hs ▸ hf.const_smul a, ?_⟩
  calc
    _ = (hf.const_smul a).toLp (a • (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val).val) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun hs))
    _ = a • hf.toLp _ := MemLp.toLp_const_smul a hf
    _ = _ := by rw [he]; rfl

theorem scalar_smul (a : ℂ) (Z : Smooth) :
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (a • Z) =
      a • KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U Z := by
  unfold KPContActualCutoffSmoothDescent.scalar
  rw [map_smul]
  rfl

theorem groupScalar_smul (a : ℂ) (Z : Smooth) :
    groupScalar F ζ hζ C R P H U (a • Z) =
      a • groupScalar F ζ hζ C R P H U Z := by
  unfold groupScalar
  rw [scalar_smul]
  rfl

theorem coefficient_smul (a : ℂ) (Z : Smooth)
    (A : KPContActualSmoothLineGluing.ChartBall F ζ hζ level R P H) :
    KPContActualSmoothLineGluing.coefficient F ζ hζ level R P H (a • Z).val A =
      a • KPContActualSmoothLineGluing.coefficient F ζ hζ level R P H Z.val A := by
  unfold KPContActualSmoothLineGluing.coefficient
  rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm,
    KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  change KPContActualChartRestrictionDensity.frameCoefficient F ζ hζ level R P H
      ((KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm (a • Z.val)) A.component A.phase = _
  rw [map_smul]
  funext p
  simp only [KPContActualChartRestrictionDensity.frameCoefficient, map_smul,
    LinearEquiv.apply_symm_apply]
  obtain ⟨ε, he⟩ := Quotient.exists_rep A.phase
  rw [← he]
  simp [KPContSectorSmoothFramesSupport.phaseCoefficient,
    KPContSectorSmoothFramesSupport.liftCoefficient,
    KPContSectorSmoothFramesSupport.liftFrame,
    KPContSectorSmoothFramesSupport.phaseTransport,
    KPContActualChartRestrictionDensity.frameCoefficient,
    KPContSectorLineL2Isometry.scalarRepresentative_eq_symm, smul_eq_mul]
  ring

 theorem numerator_sub_cutoff (cutoff W : ℂ → Smooth) (s₀ s : ℂ) :
    numerator F ζ hζ C R P H U cutoff s₀ W s - (s - s₀) • cutoff s = W s := by
  unfold numerator
  abel

 theorem numerator_at_center (cutoff W : ℂ → Smooth) (s₀ : ℂ) :
    numerator F ζ hζ C R P H U cutoff s₀ W s₀ = W s₀ := by
  simp [numerator]

 theorem off_pole_difference (domain poles : Set ℂ) (cutoff V : ℂ → Smooth)
    (s : ℂ) (hs : s ∈ domain \ poles) :
    E F ζ hζ C R P H U domain poles cutoff V s - cutoff s = V s := by
  simp only [E, if_pos hs]
  abel

 theorem off_pole_section_unique (domain poles : Set ℂ) (cutoff V : ℂ → Smooth)
    (s : ℂ) (hs : s ∈ domain \ poles) (u : Hactual)
    (hv : ∀ Z : Smooth, Represents Z.val u → Z = V s)
    (Z : Smooth) (hZ : Represents (Z - cutoff s).val u) :
    Z = E F ζ hζ C R P H U domain poles cutoff V s := by
  have he := hv (Z - cutoff s) hZ
  simp only [E, if_pos hs]
  rw [← he]
  abel

 theorem numerator_punctured_of_classes
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (domain poles : Set ℂ) (cutoff V W : ℂ → Smooth) (v w : ℂ → Hactual)
    (s₀ : ℂ) (r : ℝ)
    (hball : Metric.ball s₀ r ⊆ domain)
    (hisol : Metric.ball s₀ r ∩ poles ⊆ {s₀})
    (hV : ∀ s ∈ domain \ poles, Represents (V s).val (v s))
    (hW : ∀ s ∈ Metric.ball s₀ r, Represents (W s).val (w s))
    (hclears : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • v s)
    (s : ℂ) (hs : s ∈ Metric.ball s₀ r) (hne : s ≠ s₀) :
    numerator F ζ hζ C R P H U cutoff s₀ W s =
      (s - s₀) • E F ζ hζ C R P H U domain poles cutoff V s := by
  have hsp : s ∈ domain \ poles := ⟨hball hs, fun hp => hne (hisol ⟨hs, hp⟩)⟩
  have hrep := represents_smul F ζ hζ C R P H U (v s) (V s) (hV s hsp) (s - s₀)
  have hw : W s = (s - s₀) • V s :=
    same_class_unique F ζ hζ C R P H U realization (w s) (W s)
      ((s - s₀) • V s) (hW s hs) (by rw [hclears s hs hne]; exact hrep)
  simp only [numerator, E, if_pos hsp, smul_add]
  rw [hw]

 theorem chartPullback_eqOn_coefficient (Z : Smooth) (A : Charts) :
    Set.EqOn (chartPullback F ζ hζ C R P H U A (scalar Z))
      (coefficient Z.val A) A.ball.carrier := by
  intro p hp
  have hdom : p ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ level R P H
      A.component A.center A.chart := A.contained (Metric.ball_subset_closedBall hp)
  simp only [chartPullback, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hdom]
  have he : KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val =
      ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ level R P H).symm Z).val := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    rfl
  unfold KPContActualSmoothLineGluing.coefficient
  rw [KPContActualChartRestrictionDensity.covered_coefficient _ _ _ _ _ _ _ _ _ _ _ _ _ hdom, he]
  rfl

private theorem chart_holomorphic_congr {n : ℕ} (B : LocalBall n)
    {O : Set ℂ} {f g : ℂ → Space n → ℂ}
    (he : ∀ s ∈ O, Set.EqOn (f s) (g s) B.carrier)
    (hf : KPCutoffSource.ChartSmoothHolomorphicOn B f O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B g O := by
  have hd (l : List (Fin n)) {a b : Space n → ℂ} (hab : Set.EqOn a b B.carrier) :
      Set.EqOn (coordinateDerivativeList l a) (coordinateDerivativeList l b) B.carrier := by
    induction l with
    | nil => exact hab
    | cons i l ih =>
      intro x hx
      change fderiv ℝ (coordinateDerivativeList l a) x (EuclideanSpace.single i 1) =
        fderiv ℝ (coordinateDerivativeList l b) x (EuclideanSpace.single i 1)
      have heq := Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) ih
      rw [heq.fderiv_eq]
  refine ⟨fun s hs => (hf.1 s hs).congr (he s hs).symm, ?_⟩
  intro K hK hKB m
  obtain ⟨j,hj,hje⟩ := hf.2 K hK hKB m
  refine ⟨j,hj,?_⟩
  intro s hs α x
  rw [hje s hs α x]
  exact hd α.directions (he s hs) (hKB x.property)

 theorem taylorData_cleared_germ {O : Set ℂ} (Z E : ℂ → Smooth) (s₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball s₀ r ⊆ O)
    (hZ : SmoothTaylorData F ζ hζ C R P H U (Metric.ball s₀ r) Z)
    (he : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → Z s = (s - s₀) • E s) :
    KPSphericalL2Formula.ClearedSmoothGerm
      (fun _ : Charts => KPCuspLogShape.dimension F * 3) (fun A => A.ball)
      (chartPullback F ζ hζ C R P H U)
      (KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ level)
      (fun s => scalar (E s)) O s₀ := by
  refine ⟨r,hr,hball,fun s => scalar (Z s),?_,?_,?_⟩
  · intro s hs
    exact ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ level R P H).symm (Z s)).val.property
  · intro A
    exact chart_holomorphic_congr A.ball
      (fun s hs => (chartPullback_eqOn_coefficient F ζ hζ C R P H U (Z s) A).symm)
      (hZ.holomorphic A)
  · intro s hs hne
    change scalar (Z s) = (s - s₀) • scalar (E s)
    rw [he s hs hne, scalar_smul]

def clearedNumerator_of_promoted
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (V : ℂ → Smooth)
    (hV : ∀ s ∈ Ω \ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω,
      Represents (V s).val (KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s))
    (s₀ : ℂ) (r : ℝ) (hball : Metric.ball s₀ r ⊆ Ω)
    (hisol : Metric.ball s₀ r ∩ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω ⊆ {s₀})
    (w : ℂ → Hactual) (W : ℂ → Smooth)
    (hW : ∀ s ∈ Metric.ball s₀ r, Represents (W s).val (w s))
    (hhol : KPContActualSmoothLineGluing.HolomorphicData F ζ hζ level R P H (Metric.ball s₀ r) w W)
    (hdata : SmoothTaylorData F ζ hζ C R P H U (Metric.ball s₀ r)
      (numerator F ζ hζ C R P H U source.descent.cutoff s₀ W))
    (hclears : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) •
      KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s) :
    ClearedNumerator F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source V s₀ r w := by
  have he : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ →
      numerator F ζ hζ C R P H U source.descent.cutoff s₀ W s =
      (s - s₀) • E F ζ hζ C R P H U Ω
        (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω)
        source.descent.cutoff V s :=
    numerator_punctured_of_classes F ζ hζ C R P H U realization Ω _ _ V W _ w
      s₀ r hball hisol hV hW hclears
  refine ⟨W, hW, ?_, hhol, hdata, he, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs Z hZ
    exact same_class_unique F ζ hζ C R P H U realization (w s) Z (W s) hZ (hW s hs)
  · intro s hs hne
    rw [he s hs hne, scalar_smul]
  · intro s hs hne A
    rw [he s hs hne, coefficient_smul]
    exact fun _ _ => rfl
  · intro s hs hne
    rw [he s hs hne, groupScalar_smul]
  · intro s hs
    rw [numerator_sub_cutoff]
    exact hW s hs
  · intro hzero
    subst s₀
    constructor
    · intro s hs hne
      simpa using he s hs hne
    · intro s hs
      rw [show numerator F ζ hζ C R P H U source.descent.cutoff 0 W s - s • source.descent.cutoff s = W s by
        simpa using numerator_sub_cutoff F ζ hζ C R P H U source.descent.cutoff W 0 s]
      exact ⟨rfl, hW s hs⟩

theorem glue_promotions
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (O : Set ℂ) (hO : IsOpen O) (u : ℂ → Hactual)
    (hp : ∀ A : Charts, Nonempty (KPContActualLocalSolutionFamily.Promotion
      F ζ hζ level R P H A.component A.center A.chart A.phase A.ball A.contained O u)) :
    ∃ W : ℂ → Smooth,
      (∀ s ∈ O, Represents (W s).val (u s)) ∧
      (∀ s ∈ O, ∀ Z : Smooth, Represents Z.val (u s) → Z = W s) ∧
      KPContActualSmoothLineGluing.HolomorphicData F ζ hζ level R P H O u W := by
  let p := fun A : Charts => Classical.choice (hp A)
  let locals : KPContActualSmoothLineGluing.LocalRepresentatives F ζ hζ level R P H O u :=
    ⟨fun A => (p A).representative,
      fun A s hs => (p A).smooth s hs,
      fun A s hs => (p A).represents s hs⟩
  have hg := kp_cont_actual_smooth_line_gluing F ζ hζ level R P H realization
  obtain ⟨glued⟩ := hg.gluing O hO u locals
  refine ⟨glued.representative, glued.represents, ?_, ?_⟩
  · intro s hs Z hZ
    exact same_class_unique F ζ hζ C R P H U realization (u s) Z
      (glued.representative s) hZ (glued.represents s hs)
  · apply hg.promotion O hO u locals glued
    intro A
    exact ⟨p A, fun s hs _ _ => rfl⟩

 def sectionLocal (Z : Smooth) (A : Charts) :
    KPContActualSphericalRightFieldIdentification.LocalSection
      F ζ hζ level R P H A.component A.center A.chart := by
  refine ⟨ KPContSectorSmoothFramesSupport.liftCoefficient F ζ hζ level R P H Z.val A.component, ?_, ?_⟩
  ·
    exact (Z.property A.component).contDiffOn
  ·
    intro σ x hx
    exact (KPContSectorSmoothFramesSupport.liftCoefficient_transition F ζ hζ level R P H Z.val
      A.component σ.val x).1

 theorem sectionLocal_coefficient (Z : Smooth) (A : Charts) :
    KPContActualLocalSolutionFamily.localFrameCoefficient F ζ hζ level R P H
      (sectionLocal F ζ hζ C R P H U Z A) A.phase = KPContActualSmoothLineGluing.coefficient F ζ hζ level R P H Z.val A := by
  unfold KPContActualLocalSolutionFamily.localFrameCoefficient
    KPContActualSmoothLineGluing.coefficient KPContActualChartRestrictionDensity.frameCoefficient
  rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

theorem actual_off_pole_isOpen
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (h : KPContActualHilbertSimpleGerms.Properties F ζ hζ C R P H U μG hμG hR
      realization ι buffer Ω f χ source) :
    IsOpen (Ω \ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) := by
  apply Metric.isOpen_iff.mpr
  intro s hs
  obtain ⟨r,hr,hball,hisol,_⟩ := h.simple_germs s hs.1
  refine ⟨r,hr,?_⟩
  intro z hz
  refine ⟨hball hz,?_⟩
  intro hzp
  have he : z = s := hisol ⟨hz,hzp⟩
  exact hs.2 (he ▸ hzp)

 theorem cleared_germs_of_every_germ
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (V : ℂ → Smooth)
    (h : KPContActualHilbertSimpleGerms.Properties F ζ hζ C R P H U μG hμG hR
      realization ι buffer Ω f χ source)
    (hN : ∀ s₀ ∈ Ω, ∀ r : ℝ, 0 < r → Metric.ball s₀ r ⊆ Ω →
      Metric.ball s₀ r ∩ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω ⊆ {s₀} →
      ∀ w : ℂ → Hactual, DifferentiableOn ℂ w (Metric.ball s₀ r) →
      (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) •
        KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source s) →
      Nonempty (ClearedNumerator F ζ hζ C R P H U μG hμG hR ι Ω f χ
        realization buffer source V s₀ r w)) :
    ∀ s₀ ∈ Ω, KPSphericalL2Formula.ClearedSmoothGerm
      (fun _ : Charts => KPCuspLogShape.dimension F * 3) (fun A => A.ball)
      (chartPullback F ζ hζ C R P H U)
      (KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ level)
      (fun s => scalar (E F ζ hζ C R P H U Ω
        (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω)
        source.descent.cutoff V s)) Ω s₀ := by
  intro s₀ hs₀
  obtain ⟨r,hr,hball,hisol,w,hw,hclear,_⟩ := h.simple_germs s₀ hs₀
  obtain ⟨N⟩ := hN s₀ hs₀ r hr hball hisol w hw hclear
  exact taylorData_cleared_germ F ζ hζ C R P H U _ _ s₀ r hr hball
    N.numerator_data N.punctured_sections

local notation "a" => KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)

 theorem v_holomorphic_off_poles
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (hΩ : Ω ⊆ KPContinuation.spectralDomain) (hopen : IsOpen Ω) :
    DifferentiableOn ℂ
      (KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source)
      (Ω \ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) := by
  have hspec := kp_cont_actual_sector_resolvent_specialization F ζ hζ μG hμG level R hR P H realization
  haveI : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp H.totallyComplex
  have hfin : Module.finrank ℚ F = 2 * NumberField.InfinitePlace.nrComplexPlaces F :=
    NumberField.IsTotallyComplex.finrank F
  have hnat : (Module.finrank ℚ F / 2 : ℕ) = NumberField.InfinitePlace.nrComplexPlaces F := by
    rw [hfin]; omega
  have hdeq : ((Module.finrank ℚ F / 2 : ℕ) : ℝ) = (Module.finrank ℚ F : ℝ) / 2 := by
    rw [hnat, hfin]; push_cast; ring
  have hdZ : (0 : ℤ) < ((Module.finrank ℚ F / 2 : ℕ) : ℤ) := by
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    exact_mod_cast (show 0 < Module.finrank ℚ F / 2 by omega)
  have ha : AnalyticOnNhd ℂ a Set.univ := by
    unfold KPContinuation.spectralCoordinate
    fun_prop
  intro s hs
  have hz : a s ∈ KPBelowThresholdResolvent.domain ((Module.finrank ℚ F : ℝ) / 2) \
      KPBelowThresholdResolvent.poleSet
        (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H μG hμG hR realization)
        ((Module.finrank ℚ F : ℝ) / 2) := by
    refine ⟨?_, ?_⟩
    · have hh := KPContinuation.spectralCoordinate_avoids_thresholdRay _ hdZ
        (Set.mem_image_of_mem _ (hΩ hs.1))
      intro hp
      obtain ⟨μ, hμ, heq⟩ := hp
      apply hh
      change (a s).im = 0 ∧ (((Module.finrank ℚ F / 2 : ℕ) : ℤ) : ℝ) ≤ (a s).re
      rw [← heq]
      simp only [Int.cast_natCast, Complex.ofReal_im, Complex.ofReal_re, hdeq]
      exact ⟨trivial, hμ⟩
    · intro hp
      apply hs.2
      exact ⟨hs.1, by simpa only [hdeq] using hp⟩
  have hA := (hspec.norm_holomorphic_off_poles (a s) hz).comp (ha s (Set.mem_univ s))
  have hh := source.hilbert_holomorphic.analyticAt (hopen.mem_nhds hs.1)
  have hv := ((ContinuousLinearMap.analyticAt_bilinear
      (ContinuousLinearMap.id ℂ (Hactual →L[ℂ] Hactual))
      (KPContActualSectorResolventSpecialization.R_U F ζ hζ level R P H μG hμG hR realization (a s), source.h s)).comp₂ hA hh).neg
  have he : (fun z => -(KPContActualSectorResolventSpecialization.R_U F ζ hζ level R P H μG hμG hR realization (a z) (source.h z))) =
      KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source := by
    funext z
    rw [hspec.resolvent_exact]
    rfl
  rw [← he]
  exact hv.differentiableAt.differentiableWithinAt

private theorem chart_smul {n : ℕ} (B : LocalBall n) {O : Set ℂ}
    (q : ℂ → ℂ) (hq : DifferentiableOn ℂ q O) (g : ℂ → Space n → ℂ)
    (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B (fun s => q s • g s) O := by
  refine ⟨fun s hs => (hg.1 s hs).const_smul (q s), ?_⟩
  intro K hK hKB m
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,hje⟩ := hg.2 K hK hKB m
  refine ⟨fun s => q s • j s, hq.smul hj, ?_⟩
  intro s hs α x
  change q s * j s α x = _
  rw [hje s hs α x]
  exact (congrFun (KPContLocalHolomorphyUpgrade.CauchyAssembly.finite_coordinate_derivative_const_mul
    α.directions (q s) (g s)) x).symm

private theorem sobolev_smul {n : ℕ} (B : LocalBall n) {O : Set ℂ}
    (q : ℂ → ℂ) (hq : DifferentiableOn ℂ q O) (g : ℂ → Space n → ℂ)
    (hg : KPCutoffSource.ChartSobolevHolomorphicOn B g O) :
    KPCutoffSource.ChartSobolevHolomorphicOn B (fun s => q s • g s) O := by
  intro k
  obtain ⟨v,hv,hve⟩ := hg k
  refine ⟨fun s => q s • v s, hq.smul hv, ?_⟩
  intro s hs α
  have hd : coordinateDerivative α (q s • g s) = q s • coordinateDerivative α (g s) :=
    KPContLocalHolomorphyUpgrade.CauchyAssembly.finite_coordinate_derivative_const_mul α.directions (q s) (g s)
  refine ⟨hd ▸ (hve s hs α).1.const_smul (q s), ?_⟩
  rw [hd]
  filter_upwards [Lp.coeFn_smul (q s) (v s α), (hve s hs α).2] with x hx he
  exact hx.trans (congrArg (fun z : ℂ => q s • z) he)

 theorem source_class_restriction
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (A : Charts) (s : ℂ) (hs : s ∈ Ω) :
    (fun p => KPContActualChartRestrictionDensity.restriction F ζ hζ level R P H
      A.component A.center A.chart A.phase A.ball A.contained (source.h s) p) =ᵐ[volume.restrict A.ball.carrier]
      coefficient (source.descent.commutator s).val A := by
  obtain ⟨g,hg,he,hsec⟩ := source.line_representative s hs
  have hc : KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
      (source.descent.commutator s).val = g.val := by
    rw [← hsec, KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    simp
  unfold KPContActualSmoothLineGluing.coefficient
  rw [hc]
  exact KPContActualChartRestrictionDensity.restriction_representative F ζ hζ level R P H
    A.component A.center A.chart A.phase A.ball A.contained (source.h s) g he

 theorem source_holomorphic_coefficient
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (A : Charts) :
    KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient (source.descent.commutator s).val A) Ω ∧
    KPCutoffSource.ChartSobolevHolomorphicOn A.ball
      (fun s => coefficient (source.descent.commutator s).val A) Ω := by
  have hh := (source.local_holomorphy A.component A.center A.chart A.phase A.ball A.contained).2
  have hcoef (w : Smooth) : KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w A.component A.phase = coefficient w.val A := by
    unfold KPContActualAllCuspSource.chartCoefficient KPContActualSmoothLineGluing.coefficient
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    rfl
  simpa only [hcoef] using hh

 theorem source_solution_promotions
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (O : Set ℂ) (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (u : ℂ → Hactual) (hu : DifferentiableOn ℂ u O)
    (q : ℂ → ℂ) (hq : DifferentiableOn ℂ q O)
    (hdom : ∀ s ∈ O, u s ∈ (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H μG hμG hR realization).domain)
    (heq : ∀ s (hs : s ∈ O),
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H μG hμG hR realization) ⟨u s,hdom s hs⟩ - a s • u s = q s • source.h s) :
    ∀ A : Charts, Nonempty (KPContActualLocalSolutionFamily.Promotion
      F ζ hζ level R P H A.component A.center A.chart A.phase A.ball A.contained O u) := by
  intro A
  have ha : DifferentiableOn ℂ a O := by
    unfold KPContinuation.spectralCoordinate
    fun_prop
  let forcing := fun s => sectionLocal F ζ hζ C R P H U (q s • source.descent.commutator s) A
  have hf : (fun s => KPContActualLocalSolutionFamily.localFrameCoefficient F ζ hζ level R P H (forcing s) A.phase) =
      fun s => q s • coefficient (source.descent.commutator s).val A := by
    funext s
    rw [sectionLocal_coefficient, coefficient_smul]
  refine kp_cont_actual_local_solution_family F ζ hζ level R P H μG hμG hR realization
    A.component A.center A.chart A.phase A.ball A.contained O hO a ha u hu forcing
    ?_ ?_ hdom ?_
  · rw [hf]
    exact chart_smul A.ball q hq _ ⟨fun s hs => ((source_holomorphic_coefficient F ζ hζ C R P H U ι Ω f χ buffer source A).1.1 s (hOΩ hs)),
      fun K hK hKB m => by
        obtain ⟨j,hj,hje⟩ := (source_holomorphic_coefficient F ζ hζ C R P H U ι Ω f χ buffer source A).1.2 K hK hKB m
        exact ⟨j,hj.mono hOΩ,fun s hs => hje s (hOΩ hs)⟩⟩
  · intro B hBA
    let AB : Charts := ⟨A.component, A.center, A.chart, A.phase, B,
      hBA.trans (Metric.ball_subset_closedBall.trans A.contained)⟩
    have hh := (source_holomorphic_coefficient F ζ hζ C R P H U ι Ω f χ buffer source AB).2
    rw [hf]
    apply sobolev_smul B q hq
    intro k
    obtain ⟨v,hv,hve⟩ := hh k
    exact ⟨v,hv.mono hOΩ,fun s hs => hve s (hOΩ hs)⟩
  · intro s hs
    rw [congrFun hf s, heq s hs, map_smul]
    symm
    filter_upwards [Lp.coeFn_smul (q s) (KPContActualChartRestrictionDensity.restriction F ζ hζ level R P H
      A.component A.center A.chart A.phase A.ball A.contained (source.h s)),
      source_class_restriction F ζ hζ C R P H U ι Ω f χ buffer source A s (hOΩ hs)] with p hp he
    exact hp.trans (congrArg (fun z : ℂ => q s • z) he)

namespace ChartSeriesBridge
open KPContActualSphericalRightFieldIdentification KPContSectorSmoothFramesSupport
open KPContSectorQuotientRelationsComparison KPContSectorLineL2Isometry
open KPContActualCommonDiskRightHolomorphy KPContSectorScalarLineAlgebra
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 lemma tensor_lifted_smooth (D : GroupChart F ζ hζ U R P H)
    (w : smoothSections F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => lift F ζ hζ U R P H w.val (D.groupLift x)) D.T.carrier := by
  have he : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H w.val) = w.val :=
    (S F ζ hζ U R P H).apply_symm_apply w.val
  have hs := D.frame_smooth.mul
    ((w.property D.component).comp (baseCoordinates F).contDiff |>.contDiffOn |>.comp D.π_smooth
      (fun _ _ => Set.mem_univ _))
  apply hs.congr
  intro x hx
  simpa only [lift, he, KPContRightJets.scalarLift, Function.comp_apply] using D.global_scalar_pullback
    (scalarRepresentative F ζ hζ U R P H w.val) x hx

private lemma tensor_combination_smooth {m b : ℕ} (T : KPContLocalNorm.LocalBall m)
    (fields : Fin b → KPContLocalNorm.Space m → KPContLocalNorm.Space m)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T.carrier)
    (terms : List (ℂ × List (Fin b))) (f : KPContLocalNorm.Space m → ℂ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) f T.carrier) :
    ContDiffOn ℝ (⊤ : ℕ∞) (KPContRightJets.rightCombination fields terms f) T.carrier := by
  have hw (w : List (Fin b)) : ContDiffOn ℝ (⊤ : ℕ∞) (KPContRightJets.rightWord fields w f) T.carrier := by
    induction w with
    | nil => exact hs
    | cons i w ih => exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply (hf i)
  induction terms with
  | nil => exact contDiffOn_const
  | cons t ts ih => exact (contDiffOn_const.mul (hw t.2)).add ih

private lemma tensor_combination_identification (D : GroupChart F ζ hζ U R P H)
    (terms : Combination F) (w : smoothSections F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    rightCombination F ζ hζ terms (lift F ζ hζ U R P H w.val) (D.groupLift x) =
    KPContRightJets.rightCombination D.fields terms
      (fun y => lift F ζ hζ U R P H w.val (D.groupLift y)) x := by
  unfold rightCombination KPContRightJets.rightCombination
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [D.identification.right_iteration _ (tensor_lifted_smooth D w) t.2 x hx]

private lemma tensor_right_holomorphic
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (O : Set ℂ) (hO : IsOpen O)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (hdisks : ∀ c ρ, 0 < ρ → Metric.closedBall c ρ ⊆ O →
      ∃ b : ℕ → smoothSections F ζ hζ U R P H,
        CoherentSeries F ζ hζ U R P H W b c ρ)
    (D : GroupChart F ζ hζ U R P H) :
    KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
      (fun s x => lift F ζ hζ U R P H (W s).val (D.groupLift x)) O := by
  classical
  have hs := fun s => tensor_lifted_smooth D (W s)
  refine ⟨fun s _ => hs s, ?_⟩
  intro K hK hKT terms
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : ℂ → C(K, ℂ) := fun s =>
    ⟨fun x => KPContRightJets.rightCombination D.fields terms
      (fun y => lift F ζ hζ U R P H (W s).val (D.groupLift y)) x,
      ((tensor_combination_smooth D.T D.fields D.fields_smooth_actual terms _ (hs s)).continuousOn.mono hKT).restrict⟩
  refine ⟨j, ?_, fun _ _ _ => rfl⟩
  intro s₀ hs₀
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hs₀)
  obtain ⟨b, hb⟩ := hdisks s₀ ρ hρ hρO
  let C := D.groupLift '' K
  have hC : IsCompact C := hK.image_of_continuousOn (D.groupLift_continuous.mono hKT)
  have hp := kp_cont_actual_common_disk_right_holomorphy F ζ hζ U R P H
    realization O hO W b s₀ ρ hρ (Set.Subset.trans Metric.ball_subset_closedBall hρO) hb C hC terms
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨f, co, hf, _, hfd, _, _⟩ := hp.2.2
  let e : C(K, C) := ⟨fun x => ⟨D.groupLift x, ⟨x, x.property, rfl⟩⟩,
    ((D.groupLift_continuous.mono hKT).restrict).subtype_mk _⟩

  let L := ContinuousMap.compCLM ℂ ℂ e
  have heq : Set.EqOn j (fun s => L (f s)) (Metric.ball s₀ ρ) := by
    intro s hsball
    apply ContinuousMap.ext
    intro x
    change KPContRightJets.rightCombination D.fields terms
      (fun y => lift F ζ hζ U R P H (W s).val (D.groupLift y)) x = f s (e x)
    rw [hf s hsball (e x)]
    exact (tensor_combination_identification D terms (W s) x (hKT x.property)).symm
  have hd : DifferentiableOn ℂ (fun s => L (f s)) (Metric.ball s₀ ρ) :=
    L.differentiable.comp_differentiableOn hfd
  exact (hd.congr heq).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hρ)) |>.differentiableWithinAt

end ChartSeriesBridge

 theorem smoothTaylorData_of_chart_series
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (O : Set ℂ) (hO : IsOpen O) (W : ℂ → Smooth)
    (hhol : ∀ A : Charts, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient (W s).val A) O)
    (hdisk : ∀ c ρ, 0 < ρ → Metric.closedBall c ρ ⊆ O →
      ∃ b : ℕ → Smooth, ∀ A : Charts, SmoothPowerSeriesOn A.ball c ρ
        (fun j => coefficient (b j).val A) (fun s => coefficient (W s).val A)) :
    SmoothTaylorData F ζ hζ C R P H U O W := by
  refine ⟨hhol, ?_, ?_⟩
  · intro D
    have hs := ChartSeriesBridge.tensor_right_holomorphic realization O hO (fun _ => 0) W hdisk D
    exact hs
  · intro c ρ hρ hclosed
    obtain ⟨b,hb⟩ := hdisk c ρ hρ hclosed
    refine ⟨b,hb,?_⟩
    intro D K hK hKT terms r' hr' hr'ρ ε hε
    have hC := hK.image_of_continuousOn (D.groupLift_continuous.mono hKT)
    have hp := kp_cont_actual_common_disk_right_holomorphy F ζ hζ level R P H
      realization O hO W b c ρ hρ (Metric.ball_subset_closedBall.trans hclosed) hb
      (D.groupLift '' K) hC terms
    obtain ⟨N,hN⟩ := hp.2.1 r' hr' hr'ρ ε hε
    exact ⟨N,fun M hM s hs x hx => hN M hM s hs (D.groupLift x) ⟨x,hx,rfl⟩⟩

 theorem coefficient_add (Z Z' : Smooth) (A : Charts) :
    coefficient (Z + Z').val A = coefficient Z.val A + coefficient Z'.val A := by
  unfold KPContActualSmoothLineGluing.coefficient
  rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm,
    KPContSectorLineL2Isometry.scalarRepresentative_eq_symm,
    KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  change KPContActualChartRestrictionDensity.frameCoefficient F ζ hζ level R P H
    ((KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm (Z.val + Z'.val)) A.component A.phase = _
  rw [map_add]
  funext p
  obtain ⟨ε,he⟩ := Quotient.exists_rep A.phase
  rw [← he]
  simp [KPContActualChartRestrictionDensity.frameCoefficient,
    KPContSectorSmoothFramesSupport.phaseCoefficient, KPContSectorSmoothFramesSupport.liftCoefficient,
    KPContSectorSmoothFramesSupport.phaseTransport, KPContSectorSmoothFramesSupport.liftFrame, mul_add]

 theorem coefficient_sum {I : Type*} (t : Finset I) (Z : I → Smooth) (A : Charts) :
    coefficient (∑ i ∈ t, Z i).val A = ∑ i ∈ t, coefficient (Z i).val A := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have he := coefficient_smul F ζ hζ C R P H U 0 (0 : Smooth) A
    simpa using he
  | @insert i t hi ih => rw [Finset.sum_insert hi, coefficient_add, ih, Finset.sum_insert hi]

private theorem derivative_add {n : ℕ} (B : LocalBall n)
    {f g : Space n → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l (f + g))
      (coordinateDerivativeList l f + coordinateDerivativeList l g) B.carrier := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons i l ih =>
    intro x hx
    have he : coordinateDerivativeList l (f + g) =ᶠ[𝓝 x]
        coordinateDerivativeList l f + coordinateDerivativeList l g :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) ih
    change fderiv ℝ (coordinateDerivativeList l (f + g)) x (EuclideanSpace.single i 1) = _
    rw [he.fderiv_eq, fderiv_add]
    · rfl
    · exact ((KPContLocalHolomorphyUpgrade.CauchyAssembly.finite_coordinate_derivative_smooth B hf l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    · exact ((KPContLocalHolomorphyUpgrade.CauchyAssembly.finite_coordinate_derivative_smooth B hg l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)

private theorem chart_add {n : ℕ} (B : LocalBall n) {O : Set ℂ} {f g : ℂ → Space n → ℂ}
    (hf : KPCutoffSource.ChartSmoothHolomorphicOn B f O)
    (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B (fun s => f s + g s) O := by
  refine ⟨fun s hs => (hf.1 s hs).add (hg.1 s hs), ?_⟩
  intro K hK hKB m
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,hje⟩ := hf.2 K hK hKB m
  obtain ⟨k,hk,hke⟩ := hg.2 K hK hKB m
  refine ⟨fun s => j s + k s, hj.add hk, ?_⟩
  intro s hs α x
  change j s α x + k s α x = _
  rw [hje s hs α x, hke s hs α x]
  exact (derivative_add B (hf.1 s hs) (hg.1 s hs) α.directions (hKB x.property)).symm

private theorem series_add {n : ℕ} (B : LocalBall n) (c : ℂ) (ρ : ℝ)
    {b d : ℕ → Space n → ℂ} {f g : ℂ → Space n → ℂ}
    (hb : SmoothPowerSeriesOn B c ρ b f) (hd : SmoothPowerSeriesOn B c ρ d g) :
    SmoothPowerSeriesOn B c ρ (fun j => b j + d j) (fun s => f s + g s) := by
  refine ⟨fun j => (hb.1 j).add (hd.1 j), fun s hs => (hb.2.1 s hs).add (hd.2.1 s hs), ?_⟩
  intro K hK hKB m r hr hrρ ε hε
  obtain ⟨N,hN⟩ := hb.2.2 K hK hKB m r hr hrρ (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := hd.2.2 K hK hKB m r hr hrρ (ε/2) (by positivity)
  refine ⟨max N M,?_⟩
  intro L hL s hs α x
  have hsb : s ∈ Metric.ball c ρ := Metric.closedBall_subset_ball hrρ hs
  have he : (fun y => (∑ j ∈ Finset.range L, (s-c)^j * (b j + d j) y) - (f s + g s) y) =
      (fun y => (∑ j ∈ Finset.range L, (s-c)^j * b j y) - f s y) +
      (fun y => (∑ j ∈ Finset.range L, (s-c)^j * d j y) - g s y) := by
    funext y
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  rw [he]
  have hc1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (∑ j ∈ Finset.range L, (s-c)^j * b j y) - f s y) B.carrier :=
    (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hb.1 j)).sub (hb.2.1 s hsb)
  have hc2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (∑ j ∈ Finset.range L, (s-c)^j * d j y) - g s y) B.carrier :=
    (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hd.1 j)).sub (hd.2.1 s hsb)
  simp only [coordinateDerivative]
  rw [derivative_add B hc1 hc2 α.directions (hKB x.property)]
  exact (norm_add_le _ _).trans_lt (by
    have h1 := hN L (le_trans (le_max_left _ _) hL) s hs α x
    have h2 := hM L (le_trans (le_max_right _ _) hL) s hs α x
    simp only [coordinateDerivative] at h1 h2
    linarith)

set_option maxHeartbeats 1000000 in
 theorem numerator_smoothTaylorData
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (hΩ : IsOpen Ω) (O : Set ℂ) (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (s₀ : ℂ) (W : ℂ → Smooth) (hW : SmoothTaylorData F ζ hζ C R P H U O W) :
    SmoothTaylorData F ζ hζ C R P H U O
      (numerator F ζ hζ C R P H U source.descent.cutoff s₀ W) := by
  have hC : ∀ A : Charts, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient (source.descent.cutoff s).val A) Ω := by
    intro A
    have hh := (source.local_holomorphy A.component A.center A.chart A.phase A.ball A.contained).1
    have hcoef (w : Smooth) : KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w A.component A.phase = coefficient w.val A := by
      unfold KPContActualAllCuspSource.chartCoefficient KPContActualSmoothLineGluing.coefficient
      rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      rfl
    simpa only [hcoef] using hh
  have hformula : ∀ s A, coefficient (numerator F ζ hζ C R P H U source.descent.cutoff s₀ W s).val A =
      (s-s₀) • coefficient (source.descent.cutoff s).val A + coefficient (W s).val A := by
    intro s A
    rw [numerator, coefficient_add, coefficient_smul]
  apply smoothTaylorData_of_chart_series F ζ hζ C R P H U realization O hO
  · intro A
    simp only [hformula]
    apply chart_add A.ball _ (hW.holomorphic A)
    apply chart_smul A.ball (fun s => s-s₀) (by fun_prop)
    exact ⟨fun s hs => (hC A).1 s (hOΩ hs), fun K hK hKB m => by
      obtain ⟨j,hj,hje⟩ := (hC A).2 K hK hKB m
      exact ⟨j,hj.mono hOΩ,fun s hs => hje s (hOΩ hs)⟩⟩
  · intro c ρ hρ hclosed
    obtain ⟨b,hb⟩ := actual_cutoff_common_disk_coefficients F ζ hζ C R P H U ι Ω f χ buffer source
      hΩ c ρ hρ (hclosed.trans hOΩ)
    obtain ⟨d,hd,_⟩ := hW.disks c ρ hρ hclosed
    let Rρ : NNReal := ⟨ρ, hρ.le⟩
    let q := fun s : ℂ => s-s₀
    have hq : DifferentiableOn ℂ q (Metric.closedBall c (Rρ : ℝ)) := by dsimp [q]; fun_prop
    let p := cauchyPowerSeries q c (Rρ : ℝ)
    have hp : HasFPowerSeriesOnBall q p c Rρ := hq.hasFPowerSeriesOnBall hρ
    let e : ℕ → Smooth := fun j =>
      (∑ z ∈ Finset.HasAntidiagonal.antidiagonal j, p.coeff z.1 • b z.2) + d j
    refine ⟨e,?_⟩
    intro A
    have hbq := KPContLocalHolomorphyUpgrade.CauchyAssembly.smooth_series_scalar_product A.ball c ρ Rρ
      le_rfl q p hp _ _ (hb A)
    have hsum := series_add A.ball c ρ hbq (hd A)
    have he : ∀ j, coefficient (e j).val A =
      (fun y => ∑ z ∈ Finset.HasAntidiagonal.antidiagonal j, p.coeff z.1 * coefficient (b z.2).val A y) + coefficient (d j).val A := by
      intro j
      simp only [e, coefficient_add, coefficient_sum, coefficient_smul]
      funext y
      simp
    simpa only [he, hformula, q, Pi.smul_def, smul_eq_mul] using hsum

end DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

namespace DedekindZetaZeroFree

set_option maxHeartbeats 1500000 in

theorem kp_cont_actual_cutoff_plus_cleared_germ
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
      KPContActualCutoffPlusClearedGerm.Properties
        F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source V := by
  classical
  open KPContActualCutoffPlusClearedGerm in
    let level := KPContActualAllCuspSource.level F ζ hζ C R P H U
    let v := KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source
    let poles := KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω
    let O := Ω \ poles
    let Δ := KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ level R P H μG hμG hR realization
    let a := KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)
    have hg := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U μG hμG hR realization
      ι _hι _hStage Ω _hΩopen _hΩ f _hf buffer χ source
    have hO : IsOpen O := actual_off_pole_isOpen F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source hg
    have hv := v_holomorphic_off_poles F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source _hΩ _hΩopen
    let hdom : ∀ s ∈ O, v s ∈ Δ.domain := fun s hs => (hg.domain_equation s hs).choose
    have heq : ∀ s (hs : s ∈ O), Δ ⟨v s,hdom s hs⟩ - a s • v s = (-1 : ℂ) • source.h s := by
      intro s hs
      rw [_root_.neg_one_smul ℂ (source.h s)]
      simpa only [hdom, Δ, a, v, level, Int.natCast_div] using (hg.domain_equation s hs).choose_spec
    have hprom := source_solution_promotions F ζ hζ C R P H U μG hμG hR ι Ω f χ
      realization buffer source O hO (fun _ hs => hs.1) v hv (fun _ => -1)
      (differentiableOn_const (-1 : ℂ)) hdom heq
    obtain ⟨V,hrep,hunique,hhol⟩ := glue_promotions F ζ hζ C R P H U realization O hO v hprom
    have hN : ∀ s₀ ∈ Ω, ∀ r : ℝ, 0 < r → Metric.ball s₀ r ⊆ Ω →
        Metric.ball s₀ r ∩ poles ⊆ {s₀} →
        ∀ w : ℂ → KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
          DifferentiableOn ℂ w (Metric.ball s₀ r) →
          (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s-s₀) • v s) →
          Nonempty (ClearedNumerator F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source V s₀ r w) := by
      intro s₀ hs₀ r hr hball hisol w hw hclear
      obtain ⟨hgraph,_⟩ := kp_cont_actual_cleared_negative_graph F ζ hζ C R P H U μG hμG hR
        realization ι _hι _hStage Ω _hΩopen _hΩ f _hf buffer χ source s₀ hs₀ r hr hball hisol w hw hclear
      let wdom : ∀ s ∈ Metric.ball s₀ r, w s ∈ Δ.domain := fun s hs => (hgraph.1 s hs).choose
      have weq : ∀ s (hs : s ∈ Metric.ball s₀ r), Δ ⟨w s,wdom s hs⟩ - a s • w s =
          (-(s-s₀)) • source.h s := by
        intro s hs
        rw [(hgraph.1 s hs).choose_spec]
        change a s • w s - (s - s₀) • source.h s - a s • w s = _
        rw [_root_.neg_smul (s - s₀) (source.h s)]
        abel
      have wp := source_solution_promotions F ζ hζ C R P H U μG hμG hR ι Ω f χ
        realization buffer source (Metric.ball s₀ r) Metric.isOpen_ball hball w hw
        (fun s => -(s-s₀)) (by fun_prop) wdom weq
      obtain ⟨W,hW,hWuniq,hWhol⟩ := glue_promotions F ζ hζ C R P H U realization (Metric.ball s₀ r) Metric.isOpen_ball w wp
      have hWd := kp_cont_actual_cleared_smooth_promotion F ζ hζ C R P H U realization
        (Metric.ball s₀ r) Metric.isOpen_ball w W hWhol
      have hNd := numerator_smoothTaylorData F ζ hζ C R P H U ι Ω f χ realization buffer source
        _hΩopen (Metric.ball s₀ r) Metric.isOpen_ball hball s₀ W hWd
      exact ⟨clearedNumerator_of_promoted F ζ hζ C R P H U μG hμG hR ι Ω f χ
        realization buffer source V hrep s₀ r hball hisol w W hW hWhol hNd hclear⟩
    have hcleared := cleared_germs_of_every_germ F ζ hζ C R P H U μG hμG hR ι Ω f χ
      realization buffer source V hg hN
    refine ⟨V, hrep, hunique, hhol, ?_, ?_, ?_, hN, hcleared, hcleared 0⟩
    · intro s hs
      rw [off_pole_difference F ζ hζ C R P H U Ω poles source.descent.cutoff V s hs]
      exact hrep s hs
    · intro s hs Z hZ
      exact off_pole_section_unique F ζ hζ C R P H U Ω poles source.descent.cutoff V s hs (v s)
        (hunique s hs) Z hZ
    · intro s hs
      exact if_neg hs

end DedekindZetaZeroFree

end
