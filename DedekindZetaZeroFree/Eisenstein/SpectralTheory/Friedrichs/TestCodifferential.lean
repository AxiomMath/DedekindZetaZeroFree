module

public import DedekindZetaZeroFree.Adeles.Quotients.LineSections.ChartRestrictionDensity
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.TestL2Embeddings
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.LogarithmicCoordinates
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContFriedrichsChartTestDifferential

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

 def flatCLM : Space (KPCuspLogShape.dimension F * 3) →L[ℝ] KPArch.Space (KPCuspLogShape.dimension F) :=
  LinearMap.toContinuousLinearMap {
    toFun := coordinates F
    map_add' := by intro p q; funext i; apply Prod.ext <;> simp [coordinates, KPArchRealCoordinates.coordinates]; rfl
    map_smul' := by
      intro c p
      funext i
      apply Prod.ext <;> simp [coordinates, KPArchRealCoordinates.coordinates, Complex.real_smul]
      apply Complex.ext <;> simp }
private theorem flat_vector (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    flatCLM F (EuclideanSpace.single (finProdFinEquiv (i,k)) 1) =
      KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k := by
  funext j
  by_cases hj : j = i
  · subst j
    fin_cases k <;> simp [flatCLM, coordinates, KPArchRealCoordinates.coordinates,
      KPContFlatCuspCasimirSpecialization.coordinateDirection, Complex.ext_iff]
  · fin_cases k <;> simp [flatCLM, coordinates, KPArchRealCoordinates.coordinates,
      KPContFlatCuspCasimirSpecialization.coordinateDirection, hj, Complex.ext_iff]
private theorem flat_first (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : Differentiable ℝ f) (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    fderiv ℝ (f ∘ coordinates F) p (EuclideanSpace.single (finProdFinEquiv (i,k)) 1) =
      fderiv ℝ f (coordinates F p)
        (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k) := by
  have hh := ((hf _).hasFDerivAt.comp p (flatCLM F).hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ flatCLM F) p _ = _
  rw [hh, ContinuousLinearMap.comp_apply, flat_vector]
  rfl
private theorem diagonal_sum (p : Space (KPCuspLogShape.dimension F * 3))
    (i : Fin (KPCuspLogShape.dimension F * 3)) (v : Fin (KPCuspLogShape.dimension F * 3) → ℂ) :
    (∑ j, ((Matrix.diagonal (fun j =>
      let ik := finProdFinEquiv.symm j
      if ik.2 = 2 then 1 else Real.exp (2 * (coordinates F p ik.1).2)) :
      Matrix (Fin (KPCuspLogShape.dimension F * 3)) (Fin (KPCuspLogShape.dimension F * 3)) ℝ) i j : ℂ) * v j) =
      (KPContFlatCuspCasimirSpecialization.inverseMetricWeight (KPCuspLogShape.dimension F)
        (coordinates F p) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 : ℂ) * v i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
    congr 2
    unfold KPContFlatCuspCasimirSpecialization.inverseMetricWeight KPArch.height
    by_cases h : (finProdFinEquiv.symm i).2 = 2
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      rw [← Real.exp_nat_mul]
      norm_num
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne' _ hj]
    simp
  · intro h; exact (h (Finset.mem_univ i)).elim
private theorem divergence_flat {A : LocalBall (KPCuspLogShape.dimension F * 3)}
    {cρ Cρ κ Λ : ℝ} (D : KPContLocalEnergy.Coefficients A cρ Cρ κ Λ)
    (hρ : D.density = density F)
    (hg : D.matrix = fun p => Matrix.diagonal (fun j =>
      let ik := finProdFinEquiv.symm j
      if ik.2 = 2 then 1 else Real.exp (2 * (coordinates F p ik.1).2)))
    (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    KPContLocalEnergy.divergenceOperator D (fun q => f (coordinates F q)) p =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f (coordinates F p) := by
  change KPContLocalEnergy.divergenceOperator D (fun q => f (coordinates F q)) p =
    KPContFlatCuspCasimirSpecialization.Δloc _ f _
  unfold KPContLocalEnergy.divergenceOperator KPContFlatCuspCasimirSpecialization.Δloc
  rw [hρ]
  have hmatrix : ∀ y i, (∑ j, (D.matrix y i j : ℂ) * coordinateDerivativeList [j] (fun q => f (coordinates F q)) y) =
      (KPContFlatCuspCasimirSpecialization.inverseMetricWeight (KPCuspLogShape.dimension F)
        (coordinates F y) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 : ℂ) *
          coordinateDerivativeList [i] (fun q => f (coordinates F q)) y := by
    intro y i
    simp only [hg]
    exact diagonal_sum F y i _
  simp_rw [hmatrix]
  simp only [coordinateDerivativeList]
  rw [show density F p = KPArch.volumeDensity (KPCuspLogShape.dimension F) (coordinates F p) from rfl]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  simp_rw [show ∀ q i k, fderiv ℝ (fun q => f (coordinates F q)) q
      (EuclideanSpace.single (finProdFinEquiv (i,k)) 1) =
      fderiv ℝ f (coordinates F q)
        (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k)
      from fun q i k => flat_first F f (hf.differentiable (by simp)) i k q]
  simp only [smul_eq_mul, neg_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hm : (fun q => (density F q : ℂ) *
      (KPContFlatCuspCasimirSpecialization.inverseMetricWeight (KPCuspLogShape.dimension F)
        (coordinates F q) i k : ℂ) *
        fderiv ℝ f (coordinates F q) (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k)) =
      (fun y => ((KPArch.volumeDensity (KPCuspLogShape.dimension F) y *
        KPContFlatCuspCasimirSpecialization.inverseMetricWeight (KPCuspLogShape.dimension F) y i k : ℝ) : ℂ) *
        fderiv ℝ f y (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k)) ∘ coordinates F := by
    funext q; simp [density, coordinates, KPArchRealCoordinates.density, Function.comp_def, Complex.ofReal_mul, mul_assoc]
  rw [show (fun q => (density F q : ℂ) *
      ((KPContFlatCuspCasimirSpecialization.inverseMetricWeight (KPCuspLogShape.dimension F)
        (coordinates F q) i k : ℂ) *
        fderiv ℝ f (coordinates F q) (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k))) =
      (fun q => (density F q : ℂ) *
      (KPContFlatCuspCasimirSpecialization.inverseMetricWeight (KPCuspLogShape.dimension F)
        (coordinates F q) i k : ℂ) *
        fderiv ℝ f (coordinates F q) (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k)) by funext q; ring, hm]
  have hdf : Differentiable ℝ (fun y => fderiv ℝ f y
      (KPContFlatCuspCasimirSpecialization.coordinateDirection (KPCuspLogShape.dimension F) i k)) :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  exact flat_first F _ (by
    unfold KPContFlatCuspCasimirSpecialization.inverseMetricWeight KPArch.volumeDensity KPArch.height
    simp only [← Real.exp_neg]
    split_ifs <;> fun_prop) i k p

section ActualHelpers
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
private theorem restriction_iota
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    ∀ᵐ p ∂volume.restrict A.carrier,
      restriction F ζ hζ U R P H i x O m A hA (KPContActualSectorTestEmbeddings.iota f) p =
        (liftFrame F ζ hζ U (coordinates F p)
          (phaseCoefficient F ζ hζ U R P H
            (KPContActualSectorSmoothTestModules.scalarSections f) i m (coordinates F p)) : ℂ) := by
  let fB : BorelL2Scalars F ζ hζ U R :=
    ⟨KPContActualSectorSmoothTestModules.scalarCovered f,
      (KPContSectorLineL2Isometry.borel_iff F ζ hζ U R P H _).mp
        (fun i => ((Classical.choose_spec
          (KPContActualSectorSmoothTestModules.scalar_gluing f)).1.1 i).continuous.measurable),
      KPContActualSectorTestEmbeddings.scalar_memLp f⟩
  have hf : scalarEmbedding F ζ hζ U R P H fB = KPContActualSectorTestEmbeddings.iota f := by
    apply Subtype.ext
    exact scalarEmbedding_coe F ζ hζ U R P H fB
  have ha := restriction_representative F ζ hζ U R P H i x O m A hA _ fB hf
  have hS : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H fB.val =
      KPContActualSectorSmoothTestModules.scalarSections f := by
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H
        (KPContActualSectorSmoothTestModules.scalarSections f)) = _
    rw [scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  change _ =ᵐ[_] (fun p => (liftFrame F ζ hζ U (coordinates F p)
    (phaseCoefficient F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H fB.val)
      i m (coordinates F p)) : ℂ)) at ha
  filter_upwards [ha] with p hp
  rw [hS] at hp
  exact hp

private theorem coefficient_eq (s : Sections F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  simp [sectionFields, LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]
private theorem fields_sections (f : S_U F ζ hζ U R P H) :
    sectionFields (scalarSections f) = f.val :=
  (Classical.choose_spec (scalar_gluing f)).1.2.2
private theorem shrink_exists (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
    ∃ C : ShrunkChart F ζ hζ U R P H, C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (orbifoldChart_exists F ζ hζ U R P H i p)
  letI : Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) p) :=
    chart_stabilizer_finite F ζ hζ U R P H i p O
  letI := Fintype.ofFinite (MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  obtain ⟨W,hWo,hpW,hWsub,hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer (Component F ζ hζ U R P H i) p,
    (fun x : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i,p,O,V,hopen,hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub,?_⟩,rfl,rfl,hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h*g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x,?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h*g⁻¹)

private theorem section_laplacian
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (i : Fin (H.atlas U).componentCount) (y : SymmetricSpace F) :
    (scalarSections (δ_U (D_U f)) i).val y =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        (scalarSections f i).val y := by
  obtain ⟨a, ha, _, hy⟩ := shrink_exists F ζ hζ U R P H i y
  let q := labeledAInv (placeEquiv F ζ hζ) y
  have hq : labeledA (placeEquiv F ζ hζ) q = y := by
    funext k; simp [q, labeledA, labeledAInv]
  have hqy : q ∈ omega a := by change labeledA (placeEquiv F ζ hζ) q ∈ a.domain; rw [hq]; exact hy
  have hcoef (g : S_U F ζ hζ U R P H) : g.val a ⟨q,hqy⟩ = (scalarSections g i).val y := by
    rw [← fields_sections F ζ hζ U R P H g, coefficient_eq, hq, ha]
  rw [← hcoef (δ_U (D_U f))]
  rw [(kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization).laplacian_chart]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (scalarSections f i).val :=
    (Classical.choose_spec (scalar_gluing f)).1.1 i
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F)
    (KPCuspLogShape.dimension F) (placeEquiv F ζ hζ) (scalarSections f i).val hs q
  change KPContActualSphericalFlatStage.localLaplacian _ (scalarSections f i).val
    (labeledA (placeEquiv F ζ hζ) q) =
    HyperbolicChart.laplacian _ (fun z => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) z)) q at hb
  rw [hq] at hb
  rw [hb]
  apply KPCuspCutoffGraphApproximation.laplacian_congr_nhds
  have hopen : IsOpen (omega a) := by
    apply a.domain_open.preimage
    unfold labeledA
    fun_prop
  filter_upwards [hopen.mem_nhds hqy] with z hz
  simp only [liftExtension, dite_eq_left hz]
  rw [← fields_sections F ζ hζ U R P H f, coefficient_eq, ha]

end ActualHelpers

theorem differential_on_tests
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    {cρ Cρ κ Λ : ℝ} (D : KPContLocalEnergy.Coefficients A cρ Cρ κ Λ)
    (hρ : D.density = density F)
    (hg : D.matrix = fun p => Matrix.diagonal (fun j =>
      let ik := finProdFinEquiv.symm j
      if ik.2 = 2 then 1 else Real.exp (2 * (coordinates F p ik.1).2)))
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    ∀ᵐ p ∂volume.restrict A.carrier,
      restriction F ζ hζ U R P H i x O m A hA
        (KPContActualSectorTestEmbeddings.iota
          (KPContActualSectorTestDifferentialDescent.δ_U
            (KPContActualSectorTestDifferentialDescent.D_U f))) p =
      KPContLocalEnergy.divergenceOperator D
        (fun q => (liftFrame F ζ hζ U (coordinates F q)
          (phaseCoefficient F ζ hζ U R P H
            (KPContActualSectorSmoothTestModules.scalarSections f) i m
              (coordinates F q)) : ℂ)) p := by
  obtain ⟨ε, hε⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change phaseClass F ζ hζ U ε = m at hε
  subst m
  let c : ℂ := (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)
  have hframe (g : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) (q : Space (KPCuspLogShape.dimension F * 3)) :
      (liftFrame F ζ hζ U (coordinates F q)
        (phaseCoefficient F ζ hζ U R P H (KPContActualSectorSmoothTestModules.scalarSections g) i (phaseClass F ζ hζ U ε) (coordinates F q)) : ℂ) =
      (KPContActualSectorSmoothTestModules.scalarSections (c • g) i).val (coordinates F q) := by
    rw [show (liftFrame F ζ hζ U (coordinates F q)) = LinearIsometryEquiv.refl ℂ _ from rfl]
    change (phaseCoefficient F ζ hζ U R P H (KPContActualSectorSmoothTestModules.scalarSections g) i (phaseClass F ζ hζ U ε) (coordinates F q) : ℂ) = _
    rw [phaseCoefficient_class, map_smul]
    rfl
  have hfun : (fun q => (liftFrame F ζ hζ U (coordinates F q)
        (phaseCoefficient F ζ hζ U R P H (KPContActualSectorSmoothTestModules.scalarSections f) i (phaseClass F ζ hζ U ε) (coordinates F q)) : ℂ)) =
      (fun q => (KPContActualSectorSmoothTestModules.scalarSections (c • f) i).val (coordinates F q)) := funext (hframe f)
  rw [hfun]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (KPContActualSectorSmoothTestModules.scalarSections (c • f) i).val :=
    (Classical.choose_spec (KPContActualSectorSmoothTestModules.scalar_gluing (c • f))).1.1 i
  filter_upwards [restriction_iota F ζ hζ U R P H i x O (phaseClass F ζ hζ U ε) A hA (KPContActualSectorTestDifferentialDescent.δ_U (KPContActualSectorTestDifferentialDescent.D_U f))] with p hp
  rw [hp, hframe, divergence_flat F D hρ hg _ hs]
  have heq := section_laplacian F ζ hζ U R P H μG hμG hR realization (c • f) i (coordinates F p)
  rw [map_smul, map_smul] at heq
  exact heq

end DedekindZetaZeroFree.KPContFriedrichsChartTestDifferential

end
