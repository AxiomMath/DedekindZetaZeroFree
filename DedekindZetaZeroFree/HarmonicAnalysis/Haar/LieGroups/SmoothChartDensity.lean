module

public import DedekindZetaZeroFree.MeasureTheory.FiniteProductDensity.PiWithDensity
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLProductExponentialCharts

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame
open MeasureTheory Raw
open scoped NumberField Classical ENNReal NNReal Manifold ContDiff Matrix.Norms.Operator

private theorem map_density_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (ν : Measure X) (w : X → ℝ≥0∞) :
    Measure.map e (ν.withDensity w) =
      (Measure.map e ν).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext
  intro s hs
  rw [e.measurableEmbedding.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs,
    e.measurableEmbedding.lintegral_map]
  simp only [e.symm_apply_apply]

private theorem product_chart_density {ι : Type*} [Fintype ι]
    (ν : Measure PGLComplex.Group) [ν.IsHaarMeasure] [SigmaFinite ν]
    (g : ι → PGLComplex.Group) (c : ℝ)
    (hc : Measure.map PGLComplex.affineChart.symm (ν.restrict PGLComplex.affineTarget) =
      (volume.withDensity (fun x => ENNReal.ofReal (c / ‖PGLComplex.delta x‖ ^ 4))).restrict
        PGLComplex.affineSource) :
    Measure.map (OpenPartialHomeomorph.pi (fun i => PGLComplex.translatedAffineChart (g i)))
      ((Measure.pi (fun _ : ι => ν)).restrict
        (OpenPartialHomeomorph.pi (fun i => PGLComplex.translatedAffineChart (g i))).source) =
      (volume.withDensity (fun x : ι → PGLComplex.Coordinates =>
        ∏ i, ENNReal.ofReal (c / ‖PGLComplex.delta (x i)‖ ^ 4))).restrict
          (Set.univ.pi (fun _ : ι => PGLComplex.affineSource)) := by
  let e := fun i => PGLComplex.translatedAffineChart (g i)
  have he (i : ι) : Measure.map (e i) (ν.restrict (e i).source) =
      (volume.withDensity (fun x => ENNReal.ofReal (c / ‖PGLComplex.delta x‖ ^ 4))).restrict
        PGLComplex.affineSource :=
    PGLExponential.translated_chart_haar_density ν (g i) c hc
  haveI (i : ι) : SigmaFinite (Measure.map (e i) (ν.restrict (e i).source)) := by
    rw [he i]; infer_instance
  change Measure.map (OpenPartialHomeomorph.pi e)
    ((Measure.pi (fun _ : ι => ν)).restrict (Set.univ.pi (fun i => (e i).source))) = _
  rw [Measure.restrict_pi_pi]
  change Measure.map (fun x i => e i (x i)) (Measure.pi (fun i => ν.restrict (e i).source)) = _
  rw [Measure.pi_map_pi (fun i => (e i).continuousOn.aemeasurable (e i).open_source.measurableSet)]
  simp_rw [he]
  rw [← Measure.restrict_pi_pi, FiniteProductDensity.Measure.pi_withDensity_ofReal]
  · rfl
  · intro i
    exact (measurable_const.div
      (PGLComplex.contDiff_delta.continuous.measurable.norm.pow_const 4)).aemeasurable

set_option backward.isDefEq.respectTransparency false in

theorem raw_affine_haar_density (F : Type) [Field F] [NumberField F]
    (μ : Measure (ArchGroup F)) (hμ : μ.IsHaarMeasure) (g : ArchGroup F) :
    ∃ ρ : Coordinates F → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) ρ (rawAffineChart F g).source ∧
      (∀ x ∈ (rawAffineChart F g).source, 0 < ρ x) ∧
      Measure.map (rawAffineChart F g).symm
        (μ.restrict (rawAffineChart F g).target) =
        (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict
          (rawAffineChart F g).source := by
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
    change LocallyCompactSpace (Fin 2 → Fin 2 → ℂ); infer_instance
  letI : LocallyCompactSpace PGLComplex.Group := by
    change LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ); infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology PGLComplex.Group := by
    change SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
    infer_instance
  letI : IsTopologicalGroup (ArchGroup F) := by
    change IsTopologicalGroup (NumberField.InfinitePlace F → PGLComplex.Group)
    infer_instance
  have hm : Raw.instMeasurableSpaceArchGroup F =
      @MeasurableSpace.pi (NumberField.InfinitePlace F) (fun _ => PGLComplex.Group)
        (fun _ => PGLComplex.instMeasurableSpaceGroup) :=
    (@BorelSpace.measurable_eq (ArchGroup F) _ MeasurableSpace.pi Pi.borelSpace).symm
  revert μ
  rw [hm]
  intro μ hμ
  letI : MeasurableSpace (ArchGroup F) := MeasurableSpace.pi
  letI := hμ
  let ν₀ : Measure PGLComplex.Group := Measure.haar
  obtain ⟨c, hcpos, hc⟩ := PGLComplex.affine_haar_density ν₀
  let ν : Measure (ArchGroup F) := Measure.pi (fun _ : NumberField.InfinitePlace F => ν₀)
  haveI : ν.IsHaarMeasure := by dsimp [ν]; infer_instance
  let a : ℝ≥0 := Measure.haarScalarFactor μ ν
  have ha : 0 < (a : ℝ) := NNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν)
  have hμν : μ = a • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  let R : Coordinates F ≃L[ℝ] (NumberField.InfinitePlace F → PGLComplex.Coordinates) :=
    (coordinateReindex F).trans (PGLComplex.productCoordinatesFlatten _).symm
  let E := OpenPartialHomeomorph.pi (fun w => PGLComplex.translatedAffineChart (g w))
  have hchart : rawAffineChart F g =
      R.toHomeomorph.toOpenPartialHomeomorph.trans E.symm := by
    simp [rawAffineChart, R, E, PGLComplex.productAffineChart, PGLComplex.translatedAffineChart,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ContinuousLinearEquiv.toHomeomorph_symm]
    have hr : ((coordinateReindex F).trans
        (PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).symm).toHomeomorph =
        (coordinateReindex F).toHomeomorph.trans
          (PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).toHomeomorph.symm := rfl
    rw [hr, Homeomorph.trans_toOpenPartialHomeomorph, OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph]
  let S : Set (NumberField.InfinitePlace F → PGLComplex.Coordinates) :=
    Set.univ.pi (fun _ => PGLComplex.affineSource)
  have htarget : E.target = S := by
    simp [E, S, PGLComplex.translatedAffineChart_target]
  have hsource : (rawAffineChart F g).source = R ⁻¹' S := by
    rw [hchart]
    simp [OpenPartialHomeomorph.trans_source, htarget]
  let w : (NumberField.InfinitePlace F → PGLComplex.Coordinates) → ℝ :=
    fun x => ∏ i, c / ‖PGLComplex.delta (x i)‖ ^ 4
  have hprod : Measure.map E (ν.restrict E.source) =
      (volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict S := by
    rw [product_chart_density ν₀ g c hc]
    congr 2
    funext x
    dsimp [w]
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    exact div_nonneg hcpos.le (pow_nonneg (norm_nonneg _) _)
  let κ : Measure (Coordinates F) := Measure.map R.symm (volume : Measure (NumberField.InfinitePlace F → PGLComplex.Coordinates))
  haveI : κ.IsAddHaarMeasure := R.symm.isAddHaarMeasure_map _
  let b : ℝ≥0 := Measure.addHaarScalarFactor κ volume
  have hb : 0 < (b : ℝ) := NNReal.coe_pos.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure κ volume)
  have hκ : κ = b • volume := Measure.isAddLeftInvariant_eq_smul κ volume
  refine ⟨fun x => (a : ℝ) * (b : ℝ) * w (R x), ?_, ?_, ?_⟩
  · apply ContDiffOn.mul contDiffOn_const
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∏ i, c / ‖PGLComplex.delta (R x i)‖ ^ 4)
      (rawAffineChart F g).source
    apply contDiffOn_prod
    intro i _
    have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => PGLComplex.delta (R x i))
        (rawAffineChart F g).source :=
      (PGLComplex.contDiff_delta.comp ((contDiff_apply ℝ PGLComplex.Coordinates i).comp R.contDiff)).contDiffOn
    have hz : ∀ x ∈ (rawAffineChart F g).source, PGLComplex.delta (R x i) ≠ 0 := by
      intro x hx
      rw [hsource] at hx
      exact hx i (Set.mem_univ i)
    exact contDiffOn_const.div ((hd.norm ℂ hz).pow 4)
      (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr (hz x hx)))
  · intro x hx
    apply mul_pos (mul_pos ha hb)
    apply Finset.prod_pos
    intro i _
    apply div_pos hcpos
    apply pow_pos
    apply norm_pos_iff.mpr
    rw [hsource] at hx
    exact hx i (Set.mem_univ i)
  · rw [hμν, Measure.restrict_smul, Measure.map_smul]
    · rw [hchart, PGLExponential.coordinate_pullback_trans]
      simp only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
        Homeomorph.toOpenPartialHomeomorph_target, Measure.restrict_univ]
      rw [hprod, ← hchart]
      change a • Measure.map R.symm
        ((volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict S) = _
      have hs : R.symm ⁻¹' (rawAffineChart F g).source = S := by
        rw [hsource]
        ext y
        simp
      rw [← hs, ← Measure.restrict_map R.symm.continuous.measurable
        (rawAffineChart F g).open_source.measurableSet]
      have hd := map_density_equiv R.symm.toHomeomorph.toMeasurableEquiv volume
        (fun x => ENNReal.ofReal (w x))
      change Measure.map R.symm (volume.withDensity (fun x => ENNReal.ofReal (w x))) =
        κ.withDensity (fun x => ENNReal.ofReal (w (R x))) at hd
      rw [hd]
      change a • (κ.withDensity (fun x => ENNReal.ofReal (w (R x)))).restrict
        (rawAffineChart F g).source = _
      rw [hκ]
      change (a : ℝ≥0∞) • (((b : ℝ≥0∞) • volume).withDensity
        (fun x => ENNReal.ofReal (w (R x)))).restrict (rawAffineChart F g).source = _
      rw [withDensity_smul_measure, Measure.restrict_smul, ← smul_assoc]
      rw [← Measure.restrict_smul]
      congr 1
      change (((a * b : ℝ≥0) : ℝ≥0∞) • volume.withDensity
        (fun x => ENNReal.ofReal (w (R x)))) = _
      rw [← withDensity_smul' (r := ((a * b : ℝ≥0) : ℝ≥0∞)) _ ENNReal.coe_ne_top]
      congr 1
      funext x
      simp [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul hb.le, mul_assoc]
    · exact (rawAffineChart F g).continuousOn_symm.aemeasurable
        (rawAffineChart F g).open_target.measurableSet

end DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame
open MeasureTheory Topology Raw
open scoped NumberField Classical ENNReal Manifold ContDiff Matrix.Norms.Operator

private theorem smooth_det_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)}
    {F : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ))}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (F x).det) U := by
  have hm (i j : ι) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
        (F x).toLinearMap i j) U := by
    simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr]
    exact (contDiff_apply ℝ ℝ i).contDiffOn.comp (hF.clm_apply contDiffOn_const)
      (fun _ _ => Set.mem_univ _)
  have hd (x : ι → ℝ) : (F x).det =
      ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ •
        ∏ i, LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
          (F x).toLinearMap (σ i) i := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Pi.basisFun ℝ ι), Matrix.det_apply]
  simp_rw [hd]
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.const_smul
  exact contDiffOn_prod (fun i _ => hm (σ i) i)

private theorem diffeo_det_ne_zero_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : DifferentiableOn ℝ e e.source)
    (hei : DifferentiableOn ℝ e.symm e.target) {x : ι → ℝ} (hx : x ∈ e.source) :
    (fderiv ℝ e x).det ≠ 0 := by
  have hd := ((he x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt
  have hi := ((hei (e x) (e.map_source hx)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))).hasFDerivAt
  have hinv : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := e.eventually_left_inverse hx
  have hcomp := (hi.comp x hd).congr_of_eventuallyEq hinv.symm
  have hlin := hcomp.fderiv
  rw [fderiv_id] at hlin
  have hdet := congrArg (fun A : (ι → ℝ) →L[ℝ] (ι → ℝ) => A.det) hlin
  change (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)).det =
    ((fderiv ℝ e.symm (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap).det at hdet
  rw [LinearMap.det_id, LinearMap.det_comp] at hdet
  intro hz
  change (fderiv ℝ e x).toLinearMap.det = 0 at hz
  rw [hz, mul_zero] at hdet
  exact one_ne_zero hdet

private theorem smooth_positive_coordinate_change_density_pi {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ν : Measure (ι → ℝ)) [ν.IsAddHaarMeasure]
    (e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ))
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hei : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (w : (ι → ℝ) → ℝ)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w e.target)
    (hwpos : ∀ x ∈ e.target, 0 < w x) :
    let ρ := fun x => |(fderiv ℝ e x).det| * w (e x)
    ContDiffOn ℝ (⊤ : ℕ∞) ρ e.source ∧
      (∀ x ∈ e.source, 0 < ρ x) ∧
      Measure.map e.symm ((ν.withDensity (fun x => ENNReal.ofReal (w x))).restrict e.target) =
        (ν.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict e.source := by
  dsimp only
  have hd := he.differentiableOn (by simp)
  have hdi := hei.differentiableOn (by simp)
  have hdet : ∀ x ∈ e.source, (fderiv ℝ e x).det ≠ 0 :=
    fun _ hx => diffeo_det_ne_zero_pi e hd hdi hx
  refine ⟨?_, ?_, ?_⟩
  · exact ((smooth_det_pi (he.fderiv_of_isOpen e.open_source (by simp))).abs
      (fun x hx => hdet x hx)).mul (hw.comp he e.mapsTo)
  · intro x hx
    exact mul_pos (abs_pos.mpr (hdet x hx)) (hwpos (e x) (e.map_source hx))
  · rw [PGLExponential.coordinate_change_density ν e hd]
    congr 2
    funext x
    exact (ENNReal.ofReal_mul (abs_nonneg _)).symm

private theorem glue_smooth_positive_density_pi {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X] [BorelSpace X]
    [HereditarilyLindelofSpace X] [SigmaFinite (volume : Measure X)]
    [Measure.IsOpenPosMeasure (volume : Measure X)]
    (μ : Measure X) (S : Set X)
    (U : S → Set X) (hU : ∀ x, IsOpen (U x))
    (hxU : ∀ x : S, (x : X) ∈ U x)
    (hUS : ∀ x, U x ⊆ S)
    (w : S → X → ℝ)
    (hw : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (w x) (U x))
    (hpos : ∀ x y, y ∈ U x → 0 < w x y)
    (hμ : ∀ x, μ.restrict (U x) =
      (volume.withDensity (fun y => ENNReal.ofReal (w x y))).restrict (U x)) :
    ∃ ρ : X → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) ρ S ∧ (∀ y ∈ S, 0 < ρ y) ∧
      μ.restrict S = (volume.withDensity (fun y => ENNReal.ofReal (ρ y))).restrict S := by
  classical
  have heq (x z : S) : Set.EqOn (w x) (w z) (U x ∩ U z) := by
    have hx := congrArg (fun ν : Measure X => ν.restrict (U z)) (hμ x)
    have hz := congrArg (fun ν : Measure X => ν.restrict (U x)) (hμ z)
    simp only [Measure.restrict_restrict (hU _).measurableSet] at hx hz
    rw [Set.inter_comm (U z) (U x)] at hx
    have hh : (volume.withDensity (fun y => ENNReal.ofReal (w x y))).restrict (U x ∩ U z) =
        (volume.withDensity (fun y => ENNReal.ofReal (w z y))).restrict (U x ∩ U z) :=
      hx.symm.trans hz
    rw [restrict_withDensity (hU x |>.inter (hU z)).measurableSet,
      restrict_withDensity (hU x |>.inter (hU z)).measurableSet] at hh
    have hc1 : ContinuousOn (w x) (U x ∩ U z) := (hw x).continuousOn.mono Set.inter_subset_left
    have hc2 : ContinuousOn (w z) (U x ∩ U z) := (hw z).continuousOn.mono Set.inter_subset_right
    have hae := (withDensity_eq_iff_of_sigmaFinite
      ((ENNReal.continuous_ofReal.comp_continuousOn hc1).aemeasurable
        ((hU x).inter (hU z)).measurableSet)
      ((ENNReal.continuous_ofReal.comp_continuousOn hc2).aemeasurable
        ((hU x).inter (hU z)).measurableSet)).mp hh
    have he := Measure.eqOn_open_of_ae_eq hae ((hU x).inter (hU z))
      (ENNReal.continuous_ofReal.comp_continuousOn hc1)
      (ENNReal.continuous_ofReal.comp_continuousOn hc2)
    intro y hy
    exact (ENNReal.ofReal_eq_ofReal_iff (hpos x y hy.1).le (hpos z y hy.2).le).mp (he hy)
  let ρ : X → ℝ := fun y => if hy : y ∈ S then w ⟨y, hy⟩ y else 0
  have hρ (x : S) : Set.EqOn ρ (w x) (U x) := by
    intro y hy
    have hyS := hUS x hy
    dsimp [ρ]
    rw [dif_pos hyS]
    exact heq ⟨y, hyS⟩ x ⟨hxU ⟨y, hyS⟩, hy⟩
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro y hy
    let x : S := ⟨y, hy⟩
    have hh : ρ =ᶠ[𝓝 y] w x := Filter.eventuallyEq_of_mem ((hU x).mem_nhds (hxU x)) (hρ x)
    exact ((hw x y (hxU x)).contDiffAt ((hU x).mem_nhds (hxU x))).congr_of_eventuallyEq hh
      |>.contDiffWithinAt
  · intro y hy
    simpa only [ρ, dif_pos hy] using hpos ⟨y, hy⟩ y (hxU ⟨y, hy⟩)
  · have hcov : S ⊆ ⋃ x, U x := by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩
    obtain ⟨t, htc, ht⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U hU hcov
    have hunion : (⋃ x ∈ t, U x) = S := Set.Subset.antisymm
      (by simp only [Set.iUnion_subset_iff]; intro x _; exact hUS x) ht
    rw [← hunion]
    apply Measure.restrict_biUnion_congr htc |>.mpr
    intro x hx
    rw [hμ x]
    rw [restrict_withDensity (hU x).measurableSet,
      restrict_withDensity (hU x).measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (hU x).measurableSet] with y hy
    exact congrArg ENNReal.ofReal (hρ x hy).symm

theorem raw_smooth_chart_haar_density (F : Type) [Field F] [NumberField F]
    {C : ChartedSpace (Coordinates F) (ArchGroup F)}
    [LieGroup (𝓘(ℝ, Coordinates F)) (⊤ : ℕ∞) (ArchGroup F)]
    (hC : ∀ g, chartAt (Coordinates F) g = (rawAffineChart F g).symm)
    (μ : Measure (ArchGroup F)) (hμ : μ.IsHaarMeasure)
    (E : OpenPartialHomeomorph (Coordinates F) (ArchGroup F))
    (hE : ContMDiffOn (𝓘(ℝ, Coordinates F)) (𝓘(ℝ, Coordinates F))
      (⊤ : ℕ∞) E E.source)
    (hEi : ContMDiffOn (𝓘(ℝ, Coordinates F)) (𝓘(ℝ, Coordinates F))
      (⊤ : ℕ∞) E.symm E.target) :
    ∃ ρ : Coordinates F → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) ρ E.source ∧
      (∀ x ∈ E.source, 0 < ρ x) ∧
      Measure.map E.symm (μ.restrict E.target) =
        (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict E.source := by
  haveI : BorelSpace (ArchGroup F) := ⟨rfl⟩
  let T (g : ArchGroup F) := chartAt (Coordinates F) g
  let Fx (x : E.source) := E.trans (T (E x))
  have hT (g : ArchGroup F) : (T g).target = (rawAffineChart F g).source := by
    dsimp [T]
    rw [hC, OpenPartialHomeomorph.symm_target]
  have hF (x : E.source) : ContDiffOn ℝ (⊤ : ℕ∞) (Fx x) (Fx x).source := by
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_chart (I := 𝓘(ℝ, Coordinates F)) (x := E x)).comp
      (hE.mono (by rw [OpenPartialHomeomorph.trans_source]; exact Set.inter_subset_left))
      (by intro y hy; exact hy.2)
  have hFi (x : E.source) : ContDiffOn ℝ (⊤ : ℕ∞) (Fx x).symm (Fx x).target := by
    apply ContMDiffOn.contDiffOn
    exact hEi.comp
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Coordinates F)) (x := E x)).mono
        (by rw [OpenPartialHomeomorph.trans_target]; exact Set.inter_subset_left))
      (by intro y hy; exact hy.2)
  have htarget (x : E.source) : (Fx x).target ⊆ (rawAffineChart F (E x)).source := by
    rw [← hT (E x)]
    exact Set.inter_subset_left
  have htargetT (x : E.source) : (Fx x).target ⊆ (T (E x)).target := by
    rw [hT (E x)]
    exact htarget x
  let w (x : E.source) : Coordinates F → ℝ :=
    Classical.choose (raw_affine_haar_density F μ hμ (E x))
  have hw_spec (x : E.source) :
      ContDiffOn ℝ (⊤ : ℕ∞) (w x) (rawAffineChart F (E x)).source ∧
      (∀ y ∈ (rawAffineChart F (E x)).source, 0 < w x y) ∧
      Measure.map (rawAffineChart F (E x)).symm
        (μ.restrict (rawAffineChart F (E x)).target) =
        (volume.withDensity (fun y => ENNReal.ofReal (w x y))).restrict
          (rawAffineChart F (E x)).source :=
    Classical.choose_spec (raw_affine_haar_density F μ hμ (E x))
  have hsmooth (x : E.source) := smooth_positive_coordinate_change_density_pi volume
    (Fx x) (hF x) (hFi x) (w x) ((hw_spec x).1.mono (htarget x))
    (fun y hy => (hw_spec x).2.1 y (htarget x hy))
  let ρ (x : E.source) : Coordinates F → ℝ :=
    fun y => |(fderiv ℝ (Fx x) y).det| * w x (Fx x y)
  have hloc (x : E.source) :
      (Measure.map E.symm (μ.restrict E.target)).restrict (Fx x).source =
      (volume.withDensity (fun y => ENNReal.ofReal (ρ x y))).restrict (Fx x).source := by
    have hover := PGLExponential.coordinate_overlap_pullback E (T (E x)).symm μ
    simp only [OpenPartialHomeomorph.symm_symm] at hover
    rw [← hover]
    have ht : Measure.map (T (E x)) (μ.restrict (T (E x)).source) =
        (volume.withDensity (fun y => ENNReal.ofReal (w x y))).restrict
          (T (E x)).target := by
      dsimp only [T]
      rw [hC, OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target]
      exact (hw_spec x).2.2
    change Measure.map (Fx x).symm
      ((Measure.map (T (E x)) (μ.restrict (T (E x)).source)).restrict (Fx x).target) = _
    rw [ht, Measure.restrict_restrict_of_subset (htargetT x)]
    exact (hsmooth x).2.2
  obtain ⟨r, hr, hp, hm⟩ := glue_smooth_positive_density_pi
    (Measure.map E.symm (μ.restrict E.target)) E.source (fun x => (Fx x).source)
    (fun x => (Fx x).open_source)
    (fun x => ⟨x.property, mem_chart_source (Coordinates F) (E x)⟩)
    (fun x => Set.inter_subset_left) ρ
    (fun x => (hsmooth x).1) (fun x => (hsmooth x).2.1) hloc
  exact ⟨r, hr, hp, (PGLExponential.coordinate_pullback_support E μ).symm.trans hm⟩

end DedekindZetaZeroFree.LocalQuotientCharts.ExponentialHaarFrame

end

end
