module

public import DedekindZetaZeroFree.Adeles.Quotients.LineSections.ChartRestrictionDensity
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.CommutatorSobolevHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.DistributionEquation

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section
open scoped Classical NumberField ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualAllCuspSource

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev level := KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U
abbrev Base := KPContActualCutoffSmoothDescent.Base F ζ hζ C R P H U
abbrev Covered := KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U
abbrev Cusps := KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U
abbrev SmoothSections := KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U

abbrev Sector := KPContSectorClosedLpSubspace.H F ζ hζ R (level F ζ hζ C R P H U)

abbrev measure := KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
  (level F ζ hζ C R P H U)

abbrev Tests := KPCuspCutoffGraph.scalarTests F ζ hζ H.totallyComplex
  (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))

def testSection (φ : Tests F ζ hζ C R P H U) : SmoothSections F ζ hζ C R P H U :=
  ⟨φ.val, φ.property.1⟩

def testScalar (φ : Tests F ζ hζ C R P H U) : Covered F ζ hζ C R P H U → ℂ :=
  KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
    (testSection F ζ hζ C R P H U φ)

def testLaplacian (φ : Tests F ζ hζ C R P H U) : Covered F ζ hζ C R P H U → ℂ :=
  ((KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H).symm
    (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
      ⟨φ.val, φ.property.1⟩)).val

def chartCoefficient (w : SmoothSections F ζ hζ C R P H U)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ (level F ζ hζ C R P H U)) :
    KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3) → ℂ :=
  KPContActualChartRestrictionDensity.frameCoefficient F ζ hζ
    (level F ζ hζ C R P H U) R P H
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U)
      R P H).symm w).val i m

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)

abbrev K := KPContActualCollarBuffer.collars F ζ hζ
  (level F ζ hζ C R P H U) R P H B.τ T

structure Source (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) where
  descent : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι B Ω f χ
  compact_collars : IsCompact (K F ζ hζ C R P H U B)

  support : ∀ s ∈ Ω, tsupport
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U)
      R P H (descent.commutator s).val) ⊆ K F ζ hζ C R P H U B

  local_equation : ∀ s ∈ Ω,
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (z : KPFiniteCuspAtlas.SymmetricSpace F),
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      ((descent.cutoff s).val i).val z -
        KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
          ((descent.cutoff s).val i).val z = ((descent.commutator s).val i).val z

  test_metric : ∀ (φ : Tests F ζ hζ C R P H U) i z,
    (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
      ⟨φ.val, φ.property.1⟩ i).val z =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        (φ.val i).val z
  h : ℂ → Sector F ζ hζ C R P H U
  hilbert_holomorphic : DifferentiableOn ℂ h Ω
  source_memLp : ∀ s ∈ Ω, MemLp
    (KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.commutator s))
    2 (measure F ζ hζ C R P H U)
  source_ae : ∀ s ∈ Ω,
    ((h s : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R (level F ζ hζ C R P H U)) :
      Covered F ζ hζ C R P H U → ℂ) =ᵐ[measure F ζ hζ C R P H U]
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.commutator s)

  line_representative : ∀ s ∈ Ω,
    ∃ g : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ
        (level F ζ hζ C R P H U) R,
      g.val.val = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
        (descent.commutator s) ∧
      KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ (level F ζ hζ C R P H U)
        R P H g = h s ∧
      KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H g.val =
        (descent.commutator s).val
  restrictions : KPContActualChartRestrictionDensity.RestrictionFamily F ζ hζ
    (level F ζ hζ C R P H U) R P H

  local_holomorphy :
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (x : KPFiniteCuspAtlas.SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ
        (level F ζ hζ C R P H U) R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ (level F ζ hζ C R P H U))
      (A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3)),
    KPContLocalCubeEmbedding.closedCarrier A ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
        (level F ζ hζ C R P H U) R P H i x O →
    KPCutoffSource.ChartSmoothHolomorphicOn A
      (fun s => chartCoefficient F ζ hζ C R P H U (descent.cutoff s) i m) Ω ∧
    KPCutoffSource.ChartSmoothHolomorphicOn A
      (fun s => chartCoefficient F ζ hζ C R P H U (descent.commutator s) i m) Ω ∧
    KPCutoffSource.ChartSobolevHolomorphicOn A
      (fun s => chartCoefficient F ζ hζ C R P H U (descent.commutator s) i m) Ω

  restriction_ae :
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (x : KPFiniteCuspAtlas.SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ
        (level F ζ hζ C R P H U) R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ (level F ζ hζ C R P H U))
      (A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3))
      (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆
        KPContActualChartRestrictionDensity.chartDomain F ζ hζ
          (level F ζ hζ C R P H U) R P H i x O),
    ∀ s ∈ Ω, (fun p => restrictions.restriction i x O m A hA (h s) p) =ᵐ[volume.restrict A.carrier]
      chartCoefficient F ζ hζ C R P H U (descent.commutator s) i m

  distribution : ∀ s ∈ Ω, ∀ φ : Tests F ζ hζ C R P H U,
    let c := KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.cutoff s)
    let hs := KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.commutator s)
    Integrable (fun x => c x * star (testLaplacian F ζ hζ C R P H U φ x))
      (measure F ζ hζ C R P H U) ∧
    Integrable (fun x => c x * star (testScalar F ζ hζ C R P H U φ x))
      (measure F ζ hζ C R P H U) ∧
    Integrable (fun x => hs x * star (testScalar F ζ hζ C R P H U φ x))
      (measure F ζ hζ C R P H U) ∧
    (∫ x, c x * star (testLaplacian F ζ hζ C R P H U φ x) ∂measure F ζ hζ C R P H U) -
      KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
        (∫ x, c x * star (testScalar F ζ hζ C R P H U φ x) ∂measure F ζ hζ C R P H U) =
      ∫ x, hs x * star (testScalar F ζ hζ C R P H U φ x) ∂measure F ζ hζ C R P H U

  pairing_holomorphy : ∀ φ : Tests F ζ hζ C R P H U,
    DifferentiableOn ℂ (fun s => ∫ x,
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.cutoff s) x *
        star (testLaplacian F ζ hζ C R P H U φ x) ∂measure F ζ hζ C R P H U) Ω ∧
    DifferentiableOn ℂ (fun s => ∫ x,
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.cutoff s) x *
        star (testScalar F ζ hζ C R P H U φ x) ∂measure F ζ hζ C R P H U) Ω ∧
    DifferentiableOn ℂ (fun s => ∫ x,
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.commutator s) x *
        star (testScalar F ζ hζ C R P H U φ x) ∂measure F ζ hζ C R P H U) Ω

end DedekindZetaZeroFree.KPContActualAllCuspSource

namespace DedekindZetaZeroFree

private theorem allCusp_coordinate_reindex {n m : ℕ} (h : n = m)
    (p : KPContLocalNorm.Space (m * 3)) :
    (fun i : Fin m => CotangentLogCoframe.A n
      (WithLp.toLp 2 (fun ik : Fin n × Fin 3 =>
        (cast (congrArg (fun k => KPContLocalNorm.Space (k * 3)) h.symm) p)
          (finProdFinEquiv ik))) ((finCongr h).symm i)) =
      (fun i : Fin m => ((⟨p (finProdFinEquiv (i, 0)), p (finProdFinEquiv (i, 1))⟩ : ℂ),
        p (finProdFinEquiv (i, 2)))) := by
  subst m
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [CotangentLogCoframe.A, finCongr]
  · simp [CotangentLogCoframe.A, finCongr]

private theorem allCusp_chart_transport {n m : ℕ} (h : n = m)
    (A : KPContLocalNorm.LocalBall m) (g v : ℂ → KPContLocalNorm.Space m → ℂ)
    (g' v' : ℂ → KPContLocalNorm.Space n → ℂ) (Ω : Set ℂ)
    (hg : ∀ s x, g' s (cast (congrArg KPContLocalNorm.Space h.symm) x) = g s x)
    (hv : ∀ s x, v' s (cast (congrArg KPContLocalNorm.Space h.symm) x) = v s x)
    (H : KPCutoffSource.ChartSmoothHolomorphicOn
        (cast (congrArg KPContLocalNorm.LocalBall h.symm) A) g' Ω ∧
      KPCutoffSource.ChartSmoothHolomorphicOn
        (cast (congrArg KPContLocalNorm.LocalBall h.symm) A) v' Ω ∧
      KPCutoffSource.ChartSobolevHolomorphicOn
        (cast (congrArg KPContLocalNorm.LocalBall h.symm) A) v' Ω) :
    KPCutoffSource.ChartSmoothHolomorphicOn A g Ω ∧
      KPCutoffSource.ChartSmoothHolomorphicOn A v Ω ∧
      KPCutoffSource.ChartSobolevHolomorphicOn A v Ω := by
  subst m
  have hgg : g' = g := funext (fun s => funext (hg s))
  have hvv : v' = v := funext (fun s => funext (hv s))
  simpa [hgg, hvv] using H

private theorem allCusp_closedBall_transport {n m : ℕ} (h : n = m)
    (A : KPContLocalNorm.LocalBall m) (V : Set (KPContLocalNorm.Space m))
    (V' : Set (KPContLocalNorm.Space n))
    (hV : ∀ x, cast (congrArg KPContLocalNorm.Space h.symm) x ∈ V' ↔ x ∈ V)
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ V) :
    Metric.closedBall
      (cast (congrArg KPContLocalNorm.LocalBall h.symm) A).center
      (cast (congrArg KPContLocalNorm.LocalBall h.symm) A).radius ⊆ V' := by
  subst m
  intro x hx
  exact (hV x).mpr (hA hx)

private theorem allCusp_sectionFields_injective
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (v w : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (h : ∀ (a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H))
      (x : KPContCotangentOverlapRationalBranches.omega a),
      KPContActualSectorSmoothTestModules.sectionFields v a x =
        KPContActualSectorSmoothTestModules.sectionFields w a x) : v = w := by
  classical
  obtain ⟨A⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  funext i
  apply Subtype.ext
  funext z
  let p := (H.atlas U).components ⟨i, KPCuspSiegel.projection F
    (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) z⟩
  have hp : p ∈ ⋃ n, (A.chart n).baseDomain := by rw [A.covers]; trivial
  obtain ⟨n, y, hy⟩ := Set.mem_iUnion.mp hp
  have he : (H.atlas U).components
      ⟨(A.chart n).component, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H (A.chart n).component) y.val⟩ =
      (H.atlas U).components ⟨i, KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) z⟩ := by
    simpa only [KPContActualCotangentCountableShrinking.ShrunkChart.toBase, p,
      (H.atlas U).components_formula] using hy
  have he' := (H.atlas U).components.injective he
  have hi : (A.chart n).component = i := congrArg Sigma.fst he'
  let a := A.chart n
  let x : KPContCotangentOverlapRationalBranches.omega a :=
    KPContActualCotangentPieceHilbertSum.coordinates a y
  have hx := h a x
  have hl : KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x.val = y.val := by
    funext k
    simp [x, KPContActualCotangentPieceHilbertSum.coordinates,
      KPContCotangentActualOverlap.labeledA, KPContCotangentActualOverlap.labeledAInv]
  have hvw : (v a.component).val y.val = (w a.component).val y.val := by
    simpa [KPContActualSectorSmoothTestModules.sectionFields,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualOverlap.ChartKind.representative, hl] using hx
  have hq : KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i)
      y.val = KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) z := by
    have heq : HEq (KPCuspSiegel.projection F
        (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H (A.chart n).component) y.val)
        (KPCuspSiegel.projection F
          (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) z) :=
      (Sigma.mk.inj he').2
    subst i
    exact eq_of_heq heq
  obtain ⟨γ, hγ⟩ := Quotient.exact hq
  have hvw' : (v i).val y.val = (w i).val y.val := by
    change (v (A.chart n).component).val y.val = (w (A.chart n).component).val y.val at hvw
    rw [hi] at hvw
    exact hvw
  change (γ : KPCuspArithmetic.PGL2 F) • z = y.val at hγ
  rw [← hγ, (v i).property.2 γ, (w i).property.2 γ] at hvw'
  exact mul_left_cancel₀ (Units.ne_zero _) hvw'

theorem kp_cont_actual_all_cusp_source
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f Ω)
    (T : ℝ) (hT : (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).threshold < T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) :
    ∃ B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T,
      Nonempty (KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ) := by
  obtain ⟨B⟩ := kp_cont_actual_collar_buffer F ζ hζ
    (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H _hR T hT
  obtain ⟨D⟩ := kp_cont_actual_cutoff_smooth_descent F ζ hζ C R P H U _hR B ι hι
    _hStage Ω hΩ f hf χ
  have hloc := kp_cont_actual_cutoff_local_commutator F ζ hζ C R P H U _hR B ι hι
    _hStage Ω hΩ f hf χ D
  obtain ⟨HH⟩ := kp_cont_actual_commutator_hilbert_holomorphy F ζ hζ C R P H U _hR B ι hι
    _hStage Ω hΩopen hΩ f hf χ D
  obtain ⟨RF⟩ := (kp_cont_actual_chart_restriction_density F ζ hζ
    (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H _hR).2
  have hdist := kp_cont_actual_cutoff_distribution_equation F ζ hζ C R P H U _hR B ι hι
    _hStage Ω hΩ hΩopen f hf χ D
  let h : ℂ → KPContActualAllCuspSource.Sector F ζ hζ C R P H U := fun s => HH.J_L (HH.g s)
  refine ⟨B, ⟨{ descent := D,
                 compact_collars := B.compact_collars,
                 support := D.support,
                 local_equation := ?_,
                 test_metric := ?_,
                 h := h,
                 hilbert_holomorphic := HH.hilbert_holomorphic,
                 source_memLp := ?_,
                 source_ae := ?_,
                 line_representative := ?_,
                 restrictions := RF,
                 local_holomorphy := ?_,
                 restriction_ae := ?_,
                 distribution := ?_,
                 pairing_holomorphy := ?_ }⟩⟩
  · intro s hs i z
    have hh := congrArg (fun w : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U =>
      (w.val i).val z) (hloc.equation s hs)
    change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        ((D.cutoff s).val i).val z -
      KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
        ((D.cutoff s).val i).val z = ((D.commutator s).val i).val z at hh
    exact hh
  · intro φ
    have heq : KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
        (KPContActualAllCuspSource.level F ζ hζ C R P H U)
        (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U))
        ⟨φ.val, φ.property.1⟩ =
        (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U
          (KPContActualAllCuspSource.testSection F ζ hζ C R P H U φ)).val := by
      apply allCusp_sectionFields_injective
      intro a x
      rw [KPContActualPartitionPairing.canonical_laplacian_chart,
        KPContActualCutoffLocalCommutator.localLaplacian_chart]
      rfl
    intro i z
    exact congrArg (fun w => (w i).val z) heq
  · intro s hs
    exact (MeasureTheory.Lp.memLp (HH.J_L (HH.g s) :
      KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R
        (KPContActualAllCuspSource.level F ζ hζ C R P H U))).ae_eq (HH.inclusion s hs)
  · intro s hs
    exact HH.inclusion s hs
  · intro s hs
    obtain ⟨b, hb1, hb2, hb3, _hb4⟩ := HH.representative s hs
    refine ⟨b, hb1, ?_, hb3⟩
    show KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b = HH.J_L (HH.g s)
    have hto := KPContSectorLineL2Isometry.sectorLineIsometry_toSector F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b
    have hsym := congrArg (KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm hto
    simp only [LinearIsometryEquiv.symm_apply_apply] at hsym
    rw [show KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b =
      KPContSectorLineL2Isometry.toSector F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
        (KPContSectorLineL2Isometry.borelS F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b) from rfl, hsym, ← hb2]
    simp
  · intro i x O m A hA
    obtain ⟨ε, rfl⟩ := Quotient.mk_surjective m
    let q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i :=
      { kind := .orbifold x O
        places := KPContCotangentActualOverlap.placeEquiv F ζ hζ
        splitting := fun _ => ε
        splitting_locallyConstant := IsLocallyConstant.const ε }
    let hd : KPContCotangentActualOverlap.d F = KPCuspLogShape.dimension F :=
      (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm
    let hn : KPContActualCutoffChartJetHolomorphy.dimension F = KPCuspLogShape.dimension F * 3 :=
      congrArg (fun n => n * 3) hd
    let A' : KPContLocalNorm.LocalBall (KPContActualCutoffChartJetHolomorphy.dimension F) :=
      cast (congrArg KPContLocalNorm.LocalBall hn.symm) A
    have hcoord (p : KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :
        KPContCotangentActualOverlap.labeledA q.places
          (KPContActualCutoffChartJetHolomorphy.coordinates F
            (cast (congrArg KPContLocalNorm.Space hn.symm) p)) =
          KPContActualChartRestrictionDensity.coordinates F p := by
      exact allCusp_coordinate_reindex hd p
    have hdom (p : KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :
        cast (congrArg KPContLocalNorm.Space hn.symm) p ∈
          KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q ↔
        p ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H i x O := by
      change KPContCotangentActualOverlap.labeledA q.places
        (KPContActualCutoffChartJetHolomorphy.coordinates F _) ∈ O.neighborhood ↔ _
      rw [hcoord]
      rfl
    have hA' : Metric.closedBall A'.center A'.radius ⊆
        KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q :=
      allCusp_closedBall_transport hn A _ _ hdom hA
    have hj := kp_cont_actual_cutoff_chart_jet_holomorphy F ζ hζ C R P H U _hR B ι hι
      _hStage Ω hΩ hΩopen f hf χ D i q A' hA'
    have hsob := kp_cont_actual_commutator_chart_sobolev_holomorphy F ζ hζ C R P H U _hR B
      ι hι _hStage Ω hΩ hΩopen f hf χ D i q A' hA'
    have hframe (w : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
        (p : KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :
        KPContActualCutoffChartJetHolomorphy.framePullback F ζ hζ C R P H U q w
          (cast (congrArg KPContLocalNorm.Space hn.symm) p) =
          KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w i
            (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ
              (KPContActualAllCuspSource.level F ζ hζ C R P H U) ε) p := by
      unfold KPContActualAllCuspSource.chartCoefficient
      rw [KPContActualChartRestrictionDensity.frameCoefficient_class]
      have hS : KPContSectorScalarLineAlgebra.S F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm w).val = w.val := by
        rw [← KPContSectorSmoothFramesSupport.smoothS_apply]
        simp
      rw [hS]
      simp only [KPContActualCutoffChartJetHolomorphy.framePullback,
        KPContCotangentActualOverlap.LiftedChart.coefficient, q,
        KPContCotangentActualOverlap.ChartKind.representative, one_smul]
      rw [hcoord]
      rfl
    apply allCusp_chart_transport hn A _ _
      (KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U ι B Ω f χ D q false)
      (KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U ι B Ω f χ D q true) Ω
    · intro s p
      exact hframe (D.cutoff s) p
    · intro s p
      exact hframe (D.commutator s) p
    · exact ⟨hj.on_ball false, hj.on_ball true, hsob⟩
  · intro i x O m A hA s hs
    obtain ⟨b, _hb1, hb2, hb3, _hb4⟩ := HH.representative s hs
    have hb : KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b = h s := by
      show KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b = HH.J_L (HH.g s)
      have hto := KPContSectorLineL2Isometry.sectorLineIsometry_toSector F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b
      have hsym := congrArg (KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm hto
      simp only [LinearIsometryEquiv.symm_apply_apply] at hsym
      rw [show KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b =
        KPContSectorLineL2Isometry.toSector F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          (KPContSectorLineL2Isometry.borelS F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b) from rfl, hsym, ← hb2]
      simp
    obtain ⟨_hmem, hae⟩ := RF.representative i x O m A hA (h s) b hb
    filter_upwards [hae] with p hp
    rw [hp]
    have hS : KPContSectorScalarLineAlgebra.S F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H b.val =
        KPContSectorScalarLineAlgebra.S F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm
              (D.commutator s)).val := by
      rw [show KPContSectorScalarLineAlgebra.S F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
            ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
              (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm
                (D.commutator s)).val = (D.commutator s).val from by
        rw [← KPContSectorSmoothFramesSupport.smoothS_apply F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm
              (D.commutator s))]
        simp]
      exact hb3
    unfold KPContActualAllCuspSource.chartCoefficient
    simp only [KPContActualChartRestrictionDensity.frameCoefficient]
    rw [hS]
  · intro s hs φ
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hdist.pairings.cutoff_laplacian_tests φ).covered_integrable s hs
    · exact (hdist.pairings.cutoff_tests φ).covered_integrable s hs
    · exact (hdist.pairings.commutator_tests φ).covered_integrable s hs
    · exact hdist.covered_equation s hs φ
  · intro φ
    refine ⟨?_, ?_, ?_⟩
    · exact (hdist.pairings.cutoff_laplacian_tests φ).covered_holomorphic
    · exact (hdist.pairings.cutoff_tests φ).covered_holomorphic
    · exact (hdist.pairings.commutator_tests φ).covered_holomorphic

end DedekindZetaZeroFree

end
