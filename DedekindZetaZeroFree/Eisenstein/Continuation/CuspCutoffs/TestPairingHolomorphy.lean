module

public import DedekindZetaZeroFree.Adeles.Quotients.SmoothPartitions.LocalTestMultipliers
public import DedekindZetaZeroFree.Adeles.Quotients.HermitianPairings.LaplacianChartTransport
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.ChartJetHolomorphy
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffTestPairingHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

section CompactIntegralMaps

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

 def compactIntegral : C(X, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

private lemma compactIntegral_apply (g : C(X, ℂ)) :
    compactIntegral μ g = ∫ x, g x ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ g) = _
  rw [← L1.integral_eq']
  rw [L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ g)

private lemma compactIntegral_holomorphic {Ω : Set ℂ} {j : ℂ → C(X, ℂ)}
    (hj : DifferentiableOn ℂ j Ω) :
    DifferentiableOn ℂ (fun s => ∫ x, j s x ∂μ) Ω := by
  have h := (compactIntegral μ).differentiable.comp_differentiableOn hj
  simpa only [Function.comp_def, compactIntegral_apply] using h

private lemma compactHermitianIntegral_holomorphic {Ω : Set ℂ} {j : ℂ → C(X, ℂ)}
    (hj : DifferentiableOn ℂ j Ω) (ψ : C(X, ℂ)) :
    DifferentiableOn ℂ (fun s => ∫ x, j s x * star (ψ x) ∂μ) Ω := by
  have hmul : DifferentiableOn ℂ (fun s => j s * star ψ) Ω := hj.mul_const (star ψ)
  simpa using compactIntegral_holomorphic μ hmul

private lemma compact_pullback_hermitian {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsFiniteMeasure ν] (q : A → X) (hq : Measurable q)
    {Ω : Set ℂ} {j : ℂ → C(X, ℂ)} (hj : DifferentiableOn ℂ j Ω) (ψ : C(X, ℂ)) :
    (∀ s, Integrable (fun y => j s (q y) * star (ψ (q y))) ν) ∧
      DifferentiableOn ℂ (fun s => ∫ y, j s (q y) * star (ψ (q y)) ∂ν) Ω := by
  have hi (s : ℂ) : Integrable (fun x => j s x * star (ψ x)) (Measure.map q ν) :=
    memLp_one_iff_integrable.mp ((j s * star ψ).memLp (Measure.map q ν) ℂ)
  have he (s : ℂ) : (∫ y, j s (q y) * star (ψ (q y)) ∂ν) =
      ∫ x, j s x * star (ψ x) ∂Measure.map q ν := by
    exact (integral_map hq.aemeasurable (hi s).aestronglyMeasurable).symm
  refine ⟨fun s => (hi s).comp_measurable hq, ?_⟩
  exact (compactHermitianIntegral_holomorphic (Measure.map q ν) hj ψ).congr (fun s _ => he s)

end CompactIntegralMaps

section ActualCharts
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {C : KPGlobalTorusInducingPlan.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {U : KPMsRationalCompactCrossPairing.Level F ζ hζ}
variable (a : ShrunkChart F ζ hζ (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)

private lemma chart_measure_finite : IsFiniteMeasure a.liftedMeasure := by
  let V := KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U
  let ν := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P V
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts F ζ hζ R P V
  let proj : KPCuspGenuineMonodromy.SymmetricSpace F → KPFiniteCuspAtlas.rawXU F ζ hζ V :=
    fun z => (H.atlas V).components ⟨a.component, Quotient.mk _ z⟩
  have hc : Continuous proj :=
    (H.atlas V).components.continuous.comp (continuous_sigmaMk.comp continuous_quot_mk)
  have hK := a.closure_compact.image hc
  have hsub : a.baseDomain ⊆ proj '' closure a.domain := by
    rintro x ⟨y, rfl⟩
    refine ⟨y.val, subset_closure y.property, ?_⟩
    change (H.atlas V).components ⟨a.component, Quotient.mk _ y.val⟩ = _
    rw [(H.atlas V).components_formula]
    rfl
  letI : IsFiniteMeasure (ν.restrict a.baseDomain) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top⟩
  have hp := every_shrunkChart_properties F ζ hζ V R P H a
  letI : IsFiniteMeasure (Measure.map a.toBase a.liftedMeasure) := by
    rw [hp.exact_pushforward]
    exact inferInstance
  exact Measure.isFiniteMeasure_of_map hp.measurable.aemeasurable

open KPContLocalNorm KPContActualCutoffChartJetHolomorphy

 def flattenEquiv : Space (dimension F) ≃ₗᵢ[ℝ] M F :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv.symm

private lemma flattenEquiv_apply (x : Space (dimension F)) :
    flattenEquiv (F := F) x = KPContActualCutoffChartJetHolomorphy.coordinates F x := by
  ext i
  simp [flattenEquiv, LinearIsometryEquiv.piLpCongrLeft, KPContActualCutoffChartJetHolomorphy.coordinates]

 def flatCoord (y : KPCuspGenuineMonodromy.SymmetricSpace F) : Space (dimension F) :=
  (flattenEquiv (F := F)).symm (labeledAInv (placeEquiv F ζ hζ) y)

private lemma flatCoord_continuous : Continuous (flatCoord (F := F) (ζ := ζ) (hζ := hζ)) := by
  apply (flattenEquiv (F := F)).symm.continuous.comp
  exact (CotangentLogCoframe.A (d F)).symm.continuous.comp (continuous_pi fun k => continuous_apply _)

private lemma coordinates_flatCoord (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    KPContActualCutoffChartJetHolomorphy.coordinates F (flatCoord (ζ := ζ) (hζ := hζ) y) =
      labeledAInv (placeEquiv F ζ hζ) y := by
  rw [← flattenEquiv_apply]
  exact (flattenEquiv (F := F)).apply_symm_apply _

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)
variable (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)

private lemma chart_continuous_family (hΩ : IsOpen Ω)
    (hΩspectral : Ω ⊆ KPContinuation.spectralDomain) (hf : DifferentiableOn ℂ f Ω)
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι) (b : Bool) :
    let L := flatCoord (F := F) (ζ := ζ) (hζ := hζ) '' closure a.domain
    letI : CompactSpace L := isCompact_iff_compactSpace.mp
      (a.closure_compact.image flatCoord_continuous)
    ∃ j : ℂ → C(L, ℂ), DifferentiableOn ℂ j Ω ∧
      ∀ s ∈ Ω, ∀ x : L, j s x =
        KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U ι buffer Ω f χ D
          (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a) b s x := by
  let L := flatCoord (F := F) (ζ := ζ) (hζ := hζ) '' closure a.domain
  have hL : IsCompact L := a.closure_compact.image flatCoord_continuous
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hLD : L ⊆ chartDomain F ζ hζ C R P H U
      (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a) := by
    rintro x ⟨y, hy, rfl⟩
    change KPContActualCutoffChartJetHolomorphy.coordinates F (flatCoord (ζ := ζ) (hζ := hζ) y) ∈
      (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).omega
    rw [coordinates_flatCoord]
    change labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) ∈ a.larger.neighborhood
    have he : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
      funext k; simp [labeledA, labeledAInv]
    rw [he]
    exact a.closure_subset hy
  obtain ⟨j, hj, he⟩ := compact_jets_holomorphic F ζ hζ C R P H U ι buffer Ω f χ
    hΩ hΩspectral hf hι hStage D (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a) b L hL hLD 0
  let α : MultiIndex (dimension F) 0 := ⟨fun _ => 0, by simp⟩
  have hp := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : MultiIndex (dimension F) 0 => C(L, ℂ)) α).differentiable.comp_differentiableOn hj
  refine ⟨fun s => j s α, hp, ?_⟩
  intro s hs x
  have hn : α.directions = [] := by
    dsimp [α, MultiIndex.directions]
    induction List.finRange (dimension F) with
    | nil => rfl
    | cons i is ih => simpa using ih
  simpa [coordinateDerivative, hn, coordinateDerivativeList] using he s hs α x

open KPContActualCutoffSmoothDescent KPContActualSectorSmoothTestModules

private theorem pairing_smooth_laplacian {d : ℕ} (g : HyperbolicChart.Space d → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.laplacian d g) := by
  have hd (f : HyperbolicChart.Space d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (k : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.coordinateDerivative d i k f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  unfold HyperbolicChart.laplacian
  apply ContDiff.sum
  intro i hi
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space d => (Real.exp (2 * q (i, 2)) : ℂ)) := by
    have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space d => Real.exp (2 * q (i,2))) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp hreal
  exact ((hd _ (hd g hg i 2) i 2).neg.add (contDiff_const.mul (hd g hg i 2))).sub
    (he.mul ((hd _ (hd g hg i 0) i 0).add (hd _ (hd g hg i 1) i 1)))
private theorem pairing_continuous_laplacian_section (ψ : Tests F ζ hζ C R P H U) :
    ∀ i, Continuous (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
      ⟨ψ.val, ψ.property.1⟩ i).val := by
  intro i
  have hi := ψ.property.1 i
  have hg : ContDiff ℝ (⊤ : ℕ∞) ((ψ.val i).val ∘ KPCuspCutoffGraph.toArch F) :=
    hi.comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)
  change Continuous (HyperbolicChart.laplacian _ _ ∘ KPCuspCutoffGraph.fromArch F)
  exact (pairing_smooth_laplacian _ hg).continuous.comp (by
    change Continuous (CotangentLogCoframe.A (KPCuspLogShape.dimension F)).symm
    exact (CotangentLogCoframe.A _).symm.continuous)

private lemma chart_hermitian_holomorphic (hΩ : IsOpen Ω)
    (hΩspectral : Ω ⊆ KPContinuation.spectralDomain) (hf : DifferentiableOn ℂ f Ω)
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι) (b : Bool)
    (t : KPContSectorSmoothFramesSupport.Sections F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    (ht : ∀ i, Continuous (t i).val) :
    DifferentiableOn ℂ (fun s => ∫ y,
      KPContActualSectorSmoothTestModules.sectionFields
        (if b then (D.commutator s).val else (D.cutoff s).val) a
        (KPContActualCotangentPieceHilbertSum.coordinates a y) *
      star (KPContActualSectorSmoothTestModules.sectionFields t a
        (KPContActualCotangentPieceHilbertSum.coordinates a y)) ∂a.liftedMeasure) Ω := by
  let L := flatCoord (F := F) (ζ := ζ) (hζ := hζ) '' closure a.domain
  have hL : IsCompact L := a.closure_compact.image flatCoord_continuous
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  letI : IsFiniteMeasure a.liftedMeasure := chart_measure_finite a
  obtain ⟨j, hj, he⟩ := chart_continuous_family a ι buffer Ω f χ D hΩ hΩspectral hf hι hStage b
  let q : a.domain → L := fun y => ⟨flatCoord (ζ := ζ) (hζ := hζ) y.val,
    ⟨y.val, subset_closure y.property, rfl⟩⟩
  have hq : Continuous q := (flatCoord_continuous.comp continuous_subtype_val).subtype_mk _
  have hA : Continuous (labeledA (placeEquiv F ζ hζ)) := by
    unfold labeledA
    exact continuous_pi fun k => (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  let ψ : C(L, ℂ) := ⟨fun x => (t a.component).val
    (labeledA (placeEquiv F ζ hζ) (KPContActualCutoffChartJetHolomorphy.coordinates F x.val)),
    (ht a.component).comp (hA.comp ((coordinates_contDiff F).continuous.comp continuous_subtype_val))⟩
  have hh := (compact_pullback_hermitian (X := L)
    a.liftedMeasure q hq.measurable hj ψ).2
  apply hh.congr
  intro s hs
  apply integral_congr_ae
  filter_upwards [] with y
  have hjq := he s hs (q y)
  have hqcoord : KPContActualCutoffChartJetHolomorphy.coordinates F (q y).val =
    (KPContActualCotangentPieceHilbertSum.coordinates a y).val := coordinates_flatCoord y.val
  have hψ : ψ (q y) = KPContActualSectorSmoothTestModules.sectionFields t a
      (KPContActualCotangentPieceHilbertSum.coordinates a y) := by
    change (t a.component).val (labeledA _ (KPContActualCutoffChartJetHolomorphy.coordinates F (q y).val)) = _
    rw [hqcoord]
    simp [KPContActualSectorSmoothTestModules.sectionFields,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart, LiftedChart.coefficient,
      ChartKind.representative]
  rw [hψ, hjq]
  unfold KPContActualCutoffChartJetHolomorphy.pullback framePullback
  rw [hqcoord]
  cases b <;> rfl

private theorem pairing_testLaplacian_sum {n : ℕ} (ψ : Fin n → Tests F ζ hζ C R P H U) :
    testLaplacian F ζ hζ C R P H U (∑ i, ψ i) =
      fun x => ∑ i, testLaplacian F ζ hζ C R P H U (ψ i) x := by
  unfold testLaplacian
  simp only [← KPCuspCutoffGraph.divergence_differential_local]
  simp only [map_sum, Submodule.coe_sum]
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply]

private theorem pairing_testScalar_sum {n : ℕ} (ψ : Fin n → Tests F ζ hζ C R P H U) :
    testScalar F ζ hζ C R P H U (∑ i, ψ i) =
      fun x => ∑ i, testScalar F ζ hζ C R P H U (ψ i) x := by
  have he (φ : Tests F ζ hζ C R P H U) : testScalar F ζ hζ C R P H U φ =
      ((KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H).symm φ.val).val := rfl
  simp only [he, Submodule.coe_sum, map_sum]
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply]

end ActualCharts

structure PairingConclusions (Ω : Set ℂ)
    (w : ℂ → KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U)
    (ψ : KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ) : Prop where
  covered_integrable : ∀ s ∈ Ω, Integrable (coveredPair F ζ hζ C R P H U (w s) ψ)
    (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U))
  quotient_integrable : ∀ s ∈ Ω,
    Integrable (quotientPair F ζ hζ C R P H U (w s) ψ) R.quotientHaar
  integral_identification : ∀ s ∈ Ω,
    (∫ x, quotientPair F ζ hζ C R P H U (w s) ψ x ∂ R.quotientHaar) =
      ∫ x, coveredPair F ζ hζ C R P H U (w s) ψ x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)
  covered_holomorphic : DifferentiableOn ℂ
    (fun s => ∫ x, coveredPair F ζ hζ C R P H U (w s) ψ x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)) Ω
  quotient_holomorphic : DifferentiableOn ℂ
    (fun s => ∫ x, quotientPair F ζ hζ C R P H U (w s) ψ x ∂ R.quotientHaar) Ω

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)

structure Conclusions
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ) : Prop where
  cutoff_tests : ∀ ψ : Tests F ζ hζ C R P H U,
    PairingConclusions F ζ hζ C R P H U Ω D.cutoff (testScalar F ζ hζ C R P H U ψ)
  cutoff_laplacian_tests : ∀ φ : Tests F ζ hζ C R P H U,
    PairingConclusions F ζ hζ C R P H U Ω D.cutoff (testLaplacian F ζ hζ C R P H U φ)
  commutator_tests : ∀ ψ : Tests F ζ hζ C R P H U,
    PairingConclusions F ζ hζ C R P H U Ω D.commutator (testScalar F ζ hζ C R P H U ψ)

end DedekindZetaZeroFree.KPContActualCutoffTestPairingHolomorphy

namespace DedekindZetaZeroFree

open KPContActualCutoffSmoothDescent KPContActualCutoffTestPairingHolomorphy
open KPContActualSectorFiniteSupportPartition

private lemma pairing_conclusions_of_covered
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (level F ζ hζ C R P H U) R P H)
    (Ω : Set ℂ) (w : ℂ → SmoothSections F ζ hζ C R P H U)
    (ψ : Covered F ζ hζ C R P H U → ℂ)
    (hint : ∀ s ∈ Ω, Integrable (coveredPair F ζ hζ C R P H U (w s) ψ)
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)))
    (hhol : DifferentiableOn ℂ
      (fun s => ∫ x, coveredPair F ζ hζ C R P H U (w s) ψ x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (level F ζ hζ C R P H U)) Ω) :
    PairingConclusions F ζ hζ C R P H U Ω w ψ := by
  have hf : AEMeasurable (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
      (level F ζ hζ C R P H U)) R.quotientHaar :=
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ
      (level F ζ hζ C R P H U)).aemeasurable
  have hcov : ∀ s ∈ Ω, Integrable (coveredPair F ζ hζ C R P H U (w s) ψ)
      (Measure.map (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
        (level F ζ hζ C R P H U)) R.quotientHaar) := by
    intro s hs
    exact hint s hs
  have hqint : ∀ s ∈ Ω, Integrable (quotientPair F ζ hζ C R P H U (w s) ψ)
      R.quotientHaar := by
    intro s hs
    exact (integrable_map_measure (hcov s hs).aestronglyMeasurable hf).1 (hcov s hs)
  have hid : ∀ s ∈ Ω,
      (∫ x, quotientPair F ζ hζ C R P H U (w s) ψ x ∂ R.quotientHaar) =
        ∫ x, coveredPair F ζ hζ C R P H U (w s) ψ x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
            (level F ζ hζ C R P H U) := by
    intro s hs
    have hmap := integral_map (μ := R.quotientHaar)
      (φ := KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
        (level F ζ hζ C R P H U)) hf (hcov s hs).aestronglyMeasurable
    rw [← hR.covered_pushforward] at hmap
    exact hmap.symm
  exact ⟨hint, hqint, hid, hhol, hhol.congr (fun s hs => hid s hs)⟩

private lemma covered_pairing_holomorphy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (Ω : Set ℂ) (hopen : IsOpen Ω) (f : ℂ → S)
    (hΩspectral : Ω ⊆ KPContinuation.spectralDomain) (hf : DifferentiableOn ℂ f Ω)
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (D : Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (w : ℂ → SmoothSections F ζ hζ C R P H U) (ψ : Covered F ζ hζ C R P H U → ℂ)
    (hw : w = D.cutoff ∨ w = D.commutator)
    (hψ : (∃ ψ₀ : Tests F ζ hζ C R P H U, ψ = testScalar F ζ hζ C R P H U ψ₀) ∨
      (∃ ψ₀ : Tests F ζ hζ C R P H U, ψ = testLaplacian F ζ hζ C R P H U ψ₀)) :
    (∀ s ∈ Ω, Integrable (coveredPair F ζ hζ C R P H U (w s) ψ)
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U))) ∧
    DifferentiableOn ℂ
      (fun s => ∫ x, coveredPair F ζ hζ C R P H U (w s) ψ x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (level F ζ hζ C R P H U)) Ω := by
    obtain ⟨b, rfl⟩ : ∃ b : Bool, w = fun s => if b then D.commutator s else D.cutoff s := by
      rcases hw with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    obtain ⟨φ, l, rfl⟩ : ∃ φ : Tests F ζ hζ C R P H U, ∃ l : Bool,
        ψ = if l then testLaplacian F ζ hζ C R P H U φ else testScalar F ζ hζ C R P H U φ := by
      rcases hψ with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
      · exact ⟨φ, false, rfl⟩
      · exact ⟨φ, true, rfl⟩
    obtain ⟨K, hK, hφK⟩ := φ.property.2
    obtain ⟨n, a, _, _, ⟨Q⟩⟩ := kp_cont_actual_sector_finite_support_partition
      F ζ hζ (level F ζ hζ C R P H U) R P H K Set.univ hK isOpen_univ (Set.subset_univ K)
    have ht := fun i => KPContActualPartitionLocalTest.localize_test a Q φ i
    choose τ σ hτ hσ hc hi using ht
    have hrec : φ = ∑ i, τ i := by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      funext z
      simp only [Finset.sum_apply, Submodule.coe_sum]
      simp only [hτ, ← Finset.sum_mul]
      by_cases hz : KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
          (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z ∈ K
      · have hh := Q.partition _ (Q.contains_compact hz)
        have hh' : (∑ i, (Q.multiplier i (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
            (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z) : ℂ)) = 1 := by
          exact_mod_cast hh
        rw [hh', one_mul]
      · rw [hφK j z hz, mul_zero]
    have hsupport (i : Fin n) : ∃ B : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U)),
        IsCompact B ∧ B ⊆ (a i).baseDomain ∧ ∀ j z,
          KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
            (H.atlas (level F ζ hζ C R P H U)) j z ∉ B → ((τ i).val j).val z = 0 := by
      refine ⟨tsupport (Q.multiplier i), Q.compact_support i, fun x hx => (Q.support_subset i hx).1, ?_⟩
      intro j z hz
      rw [hτ i j z, image_eq_zero_of_notMem_tsupport hz]
      simp
    let p (φ : Tests F ζ hζ C R P H U) :=
      if l then testLaplacian F ζ hζ C R P H U φ else testScalar F ζ hζ C R P H U φ
    let v (s : ℂ) := if b then D.commutator s else D.cutoff s
    let t (i : Fin n) : KPContSectorSmoothFramesSupport.Sections F ζ hζ
        (level F ζ hζ C R P H U) R P H :=
      if l then KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
        (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) ⟨(τ i).val, (τ i).property.1⟩
      else (τ i).val
    have hp (i : Fin n) (s : ℂ) := KPContActualPartitionPairing.single_chart_pairing
      (τ i) (a i) (hsupport i) (v s)
    have hint (i : Fin n) (s : ℂ) : Integrable (coveredPair F ζ hζ C R P H U (v s) (p (τ i)))
        (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)) := by
      cases l
      · exact (hp i s).1
      · exact (hp i s).2.1
    have heq (i : Fin n) (s : ℂ) :
        (∫ x, coveredPair F ζ hζ C R P H U (v s) (p (τ i)) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)) =
        ∫ y, KPContActualSectorSmoothTestModules.sectionFields (v s).val (a i)
          (KPContActualCotangentPieceHilbertSum.coordinates (a i) y) *
          star (KPContActualSectorSmoothTestModules.sectionFields (t i) (a i)
            (KPContActualCotangentPieceHilbertSum.coordinates (a i) y)) ∂(a i).liftedMeasure := by
      cases l
      · exact (hp i s).2.2.1
      · refine (hp i s).2.2.2.trans ?_
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [t]
        rw [KPContActualPartitionPairing.canonical_laplacian_chart]
    have hhol (i : Fin n) : DifferentiableOn ℂ
        (fun s => ∫ x, coveredPair F ζ hζ C R P H U (v s) (p (τ i)) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)) Ω := by
      have ht : ∀ j, Continuous (t i j).val := by
        cases l
        · exact fun j => ((τ i).property.1 j).continuous
        · exact pairing_continuous_laplacian_section (τ i)
      have hh := chart_hermitian_holomorphic (a i) ι buffer Ω f χ D hopen hΩspectral hf hι hStage b (t i) ht
      apply hh.congr
      intro s hs
      cases b <;> simpa only [v, Bool.false_eq_true, if_false, if_true] using heq i s
    have hsum : p φ = fun x => ∑ i, p (τ i) x := by
      rw [hrec]
      cases l
      · exact pairing_testScalar_sum τ
      · exact pairing_testLaplacian_sum τ
    have hpair (s : ℂ) : coveredPair F ζ hζ C R P H U (v s) (p φ) =
        fun x => ∑ i, coveredPair F ζ hζ C R P H U (v s) (p (τ i)) x := by
      rw [hsum]
      funext x
      simp [coveredPair, map_sum, Finset.mul_sum]
    constructor
    · intro s hs
      change Integrable (coveredPair F ζ hζ C R P H U (v s) (p φ)) _
      rw [hpair]
      exact integrable_finset_sum _ (fun i _ => hint i s)
    · change DifferentiableOn ℂ
        (fun s => ∫ x, coveredPair F ζ hζ C R P H U (v s) (p φ) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R (level F ζ hζ C R P H U)) Ω
      apply (DifferentiableOn.fun_sum (fun i _ => hhol i)).congr
      intro s hs
      rw [hpair, integral_finset_sum _ (fun i _ => hint i s)]

theorem kp_cont_actual_cutoff_test_pairing_holomorphy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (_hΩ : Ω ⊆ KPContinuation.spectralDomain) (_hopen : IsOpen Ω)
    (f : ℂ → S) (_hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T) :
    ∀ D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ,
      KPContActualCutoffTestPairingHolomorphy.Conclusions F ζ hζ C R P H U
        ι buffer Ω f χ D := by
  intro D
  have key : ∀ (w : ℂ → KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U)
      (ψ : KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U → ℂ),
      (w = D.cutoff ∨ w = D.commutator) →
      ((∃ ψ₀ : KPContActualCutoffTestPairingHolomorphy.Tests F ζ hζ C R P H U,
          ψ = KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U ψ₀) ∨
        (∃ ψ₀ : KPContActualCutoffTestPairingHolomorphy.Tests F ζ hζ C R P H U,
          ψ = KPContActualCutoffTestPairingHolomorphy.testLaplacian F ζ hζ C R P H U ψ₀)) →
      KPContActualCutoffTestPairingHolomorphy.PairingConclusions F ζ hζ C R P H U Ω w ψ := by
    intro w ψ hw hψ
    obtain ⟨hint, hhol⟩ := covered_pairing_holomorphy F ζ hζ C R P H U ι buffer Ω _hopen f _hΩ _hf _hι _hStage χ
      D w ψ hw hψ
    exact pairing_conclusions_of_covered F ζ hζ C R P H U _hR Ω w ψ hint hhol
  refine ⟨?_, ?_, ?_⟩
  · intro ψ
    exact key D.cutoff
      (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U ψ)
      (Or.inl rfl) (Or.inl ⟨ψ, rfl⟩)
  · intro φ
    exact key D.cutoff
      (KPContActualCutoffTestPairingHolomorphy.testLaplacian F ζ hζ C R P H U φ)
      (Or.inl rfl) (Or.inr ⟨φ, rfl⟩)
  · intro ψ
    exact key D.commutator
      (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U ψ)
      (Or.inr rfl) (Or.inl ⟨ψ, rfl⟩)

end DedekindZetaZeroFree

end
