module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.CoordinateNullEquivalence

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorBallRestriction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContSectorLineL2Isometry
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualSectorCoordinateNullEquivalence

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

namespace ActualScalarTransport

variable (a : ActualChart (U := U) (H := H))

def emb (y : a.domain) := fromActual (ζ := ζ) (hζ := hζ) y.val

 def actualEquiv : EuclideanSpace ℝ (Fin (3 * d F)) ≃ᵐ
    KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := toActual (ζ := ζ) (hζ := hζ)
  invFun := fromActual (ζ := ζ) (hζ := hζ)
  left_inv x := by
    unfold fromActual toActual
    have hh : ∀ y : M F, labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) y) = y := by
      intro y; apply PiLp.ext; intro k; simp [labeledAInv, labeledA]
    rw [hh, LinearIsometryEquiv.apply_symm_apply]
  right_inv y := by
    simp only [toActual, fromActual, LinearIsometryEquiv.symm_apply_apply]
    funext k
    simp [labeledA, labeledAInv]
  measurable_toFun := by
    change Measurable (toActual (ζ := ζ) (hζ := hζ))
    apply Continuous.measurable
    unfold toActual labeledA
    fun_prop
  measurable_invFun := by
    change Measurable (fromActual (ζ := ζ) (hζ := hζ))
    apply Continuous.measurable
    unfold fromActual labeledAInv
    fun_prop

theorem emb_meas : MeasurableEmbedding (emb a) :=
  (actualEquiv (ζ := ζ) (hζ := hζ)).symm.measurableEmbedding.comp
    (MeasurableEmbedding.subtype_coe a.domain_open.measurableSet)

theorem emb_mem (y : a.domain) :
    labeledAInv (placeEquiv F ζ hζ) y.val ∈ omega a := by
  change labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) ∈ a.domain
  rw [show labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val from by
    funext k; simp [labeledA, labeledAInv]]
  exact y.property

theorem scalar_pull (s : BorelL2Sections F ζ hζ U R P H) (y : a.domain) :
    scalar s a (emb a y) = (a.coefficient s.val y : ℂ) := by
  simp only [scalar, emb, fromActual, LinearIsometryEquiv.symm_apply_apply,
    KPContActualSectorTestDifferentialDescent.liftExtension, dif_pos (emb_mem a y),
    sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContActualCotangentCountableShrinking.ShrunkChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
    ChartKind.representative, one_smul, map_one, Units.val_one, one_mul,
    KPContSectorSmoothFramesSupport.liftCoefficient]
  rw [show labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val from by
    funext k; simp [labeledA, labeledAInv]]

theorem coefficient_norm
    (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H) (y : a.domain) :
    KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s (a.toBase y)
      = ‖(a.coefficient s y : ℂ)‖ := by
  change KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H s
    (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (KPCuspSiegel.projection F _ y.val)) = _
  rw [← (H.atlas U).components_formula]
  exact KPContSectorSmoothFramesSupport.sectionNorm_component
    F ζ hζ U R P H s a.component y.val

theorem coefficient_lintegral_le (s : BorelL2Sections F ζ hζ U R P H) :
    ∫⁻ y, squaredNorm F ζ hζ U R P H s.val (a.toBase y) ∂a.liftedMeasure ≤
      normIntegral F ζ hζ U R P H s.val := by
  have ha := KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H a
  calc
    (∫⁻ y, squaredNorm F ζ hζ U R P H s.val (a.toBase y) ∂a.liftedMeasure) =
        ∫⁻ b, squaredNorm F ζ hζ U R P H s.val b ∂Measure.map a.toBase a.liftedMeasure :=
      (lintegral_map' (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1).aemeasurable
        ha.measurable.aemeasurable).symm
    _ = ∫⁻ b in a.baseDomain, squaredNorm F ζ hζ U R P H s.val b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
      rw [ha.exact_pushforward]
    _ ≤ normIntegral F ζ hζ U R P H s.val := setLIntegral_le_lintegral _ _

theorem coefficient_memLp (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (fun y : a.domain => (a.coefficient s.val y : ℂ)) 2 a.liftedMeasure := by
  have hmeas : Measurable (fun y : a.domain => (a.coefficient s.val y : ℂ)) :=
    (s.property.1 a.component).comp measurable_subtype_coe
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have he (y : a.domain) : ‖(‖(a.coefficient s.val y : ℂ)‖ ^ 2 : ℝ)‖ₑ =
      squaredNorm F ζ hζ U R P H s.val (a.toBase y) := by
    rw [Real.enorm_eq_ofReal (sq_nonneg _), squaredNorm, coefficient_norm]
  simp only [he]
  exact lt_of_le_of_lt (coefficient_lintegral_le a s) s.property.2

end ActualScalarTransport

theorem scalar_memLp (a : ActualChart (U := U) (H := H))
    (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (fun x => scalar s a x) 2 (measure a) := by
  let c : a.domain → ℂ := fun y => (a.coefficient s.val y : ℂ)
  have hc : MemLp c 2 a.liftedMeasure := ActualScalarTransport.coefficient_memLp a s
  have hmap : Measure.map (ActualScalarTransport.emb a) a.liftedMeasure = measure a := by
    rw [show ActualScalarTransport.emb a =
      (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) from rfl]
    exact lifted_measure_transport (a := a)
  have hg : MemLp (Function.extend (ActualScalarTransport.emb a) c 0) 2 (measure a) := by
    have hm := (ActualScalarTransport.emb_meas a).memLp_map_measure_iff.mpr
      (show MemLp (Function.extend (ActualScalarTransport.emb a) c 0 ∘ ActualScalarTransport.emb a) 2
          a.liftedMeasure from by
        rw [Function.extend_comp (ActualScalarTransport.emb_meas a).injective]
        exact hc)
    rwa [hmap] at hm
  refine MemLp.ae_eq ?_ hg
  have hpt : ∀ y : a.domain,
      Function.extend (ActualScalarTransport.emb a) c 0 (ActualScalarTransport.emb a y)
        = scalar s a (ActualScalarTransport.emb a y) := by
    intro y
    have h1 : Function.extend (ActualScalarTransport.emb a) c 0 (ActualScalarTransport.emb a y) = c y :=
      congrFun (Function.extend_comp (ActualScalarTransport.emb_meas a).injective c 0) y
    rw [h1, show c y = (a.coefficient s.val y : ℂ) from rfl]
    exact (ActualScalarTransport.scalar_pull a s y).symm
  have h : ∀ᵐ x ∂Measure.map (ActualScalarTransport.emb a) a.liftedMeasure,
      Function.extend (ActualScalarTransport.emb a) c 0 x = scalar s a x :=
    (MeasurableEmbedding.ae_map_iff (ActualScalarTransport.emb_meas a)
      (μ := a.liftedMeasure)
      (p := fun x => Function.extend (ActualScalarTransport.emb a) c 0 x = scalar s a x)).mpr
      (Filter.Eventually.of_forall hpt)
  rwa [hmap] at h

private theorem scalarToLp_norm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ).toReal := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow]
  congr 1
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal))
    (by norm_num) hf.aestronglyMeasurable
  norm_num at h
  rw [h]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

private theorem scalarPull (a : ActualChart (U := U) (H := H))
    (s : BorelL2Sections F ζ hζ U R P H) (y : a.domain) :
    scalar s a (fromActual (ζ := ζ) (hζ := hζ) y.val) = (s.val a.component).val y.val := by
  have he : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z
    funext k
    simp [labeledA, labeledAInv]
  have hy : labeledAInv (placeEquiv F ζ hζ) y.val ∈ omega a := by
    change labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) ∈ a.domain
    rw [he]
    exact y.property
  simp [scalar, fromActual, KPContActualSectorTestDifferentialDescent.liftExtension,
    sectionFields, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
    LiftedChart.coefficient, ChartKind.representative, hy, he]

private theorem scalarPull_norm (a : ActualChart (U := U) (H := H))
    (s : BorelL2Sections F ζ hζ U R P H) (y : a.domain) :
    ENNReal.ofReal (‖scalar s a (fromActual (ζ := ζ) (hζ := hζ) y.val)‖^2) =
      squaredNorm F ζ hζ U R P H s.val (a.toBase y) := by
  rw [scalarPull]
  unfold squaredNorm
  congr 2
  have hb : a.toBase y = (H.atlas U).components ⟨a.component, Quotient.mk _ y.val⟩ := by
    rw [KPContActualCotangentCountableShrinking.ShrunkChart.toBase]
    simp only [KPFiniteCuspAtlas.componentMap, (H.atlas U).components_formula]
    rfl
  rw [hb, KPContSectorSmoothFramesSupport.sectionNorm_component]

theorem scalar_norm_bound (a : ActualChart (U := U) (H := H)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : BorelL2Sections F ζ hζ U R P H,
      ‖(scalar_memLp a s).toLp (fun x => scalar s a x)‖ ≤
        C * ‖mk F ζ hζ U R P H s‖ := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro s
  have hP := KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H a
  have hi : (∫⁻ x, ENNReal.ofReal (‖scalar s a x‖^2) ∂measure a) ≤
      normIntegral F ζ hζ U R P H s.val := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (‖scalar s a x‖^2)) (measure a) :=
      ((scalar_memLp a s).aestronglyMeasurable.norm.aemeasurable.pow_const 2).ennreal_ofReal
    have he : Measurable (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) := by
      apply Continuous.measurable
      unfold fromActual labeledAInv
      exact (baseReindex (F := F)).continuous.comp
        ((CotangentLogCoframe.A (d F)).symm.continuous.comp
          (continuous_pi fun k => (continuous_apply _).comp continuous_subtype_val))
    rw [show measure a = Measure.map (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val)
      a.liftedMeasure from (lifted_measure_transport (a := a)).symm] at hm ⊢
    rw [lintegral_map' hm he.aemeasurable]
    simp only [scalarPull_norm]
    rw [← lintegral_map' (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1).aemeasurable
      hP.measurable.aemeasurable, hP.exact_pushforward]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hs : ‖(scalar_memLp a s).toLp (scalar s a)‖^2 ≤ ‖mk F ζ hζ U R P H s‖^2 := by
    rw [scalarToLp_norm_sq, norm_sq]
    exact ENNReal.toReal_mono s.property.2.ne hi
  simp only [one_mul]
  nlinarith [norm_nonneg ((scalar_memLp a s).toLp (scalar s a)), norm_nonneg (mk F ζ hζ U R P H s)]

theorem scalar_ae_of_mk_eq_measure (a : ActualChart (U := U) (H := H))
    (s t : BorelL2Sections F ζ hζ U R P H)
    (hst : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t) :
    scalar s a =ᵐ[measure a] scalar t a := by
  let r := s - t
  have hm : mk F ζ hζ U R P H r = 0 := by
    change mk F ζ hζ U R P H (s-t) = 0
    have hh := (mk F ζ hζ U R P H).map_sub s t
    exact hh.trans (by rw [hst, sub_self])
  obtain ⟨C, _, hb⟩ := scalar_norm_bound a
  have hn : ‖(scalar_memLp a r).toLp (scalar r a)‖ = 0 := by
    have h := hb r
    rw [hm, norm_zero, mul_zero] at h
    exact le_antisymm h (norm_nonneg _)
  have hz : (scalar_memLp a r).toLp (scalar r a) = 0 := norm_eq_zero.mp hn
  have ha : scalar r a =ᵐ[measure a] 0 := by
    have h := (scalar_memLp a r).coeFn_toLp
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 (measure a))
  filter_upwards [ha] with x hx
  have he : scalar r a x = scalar s a x - scalar t a x := by
    simp [r, scalar, KPContActualSectorTestDifferentialDescent.liftExtension,
      sectionFields, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      LiftedChart.coefficient, map_sub]
    split_ifs <;> simp
  exact sub_eq_zero.mp (he.symm.trans hx)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in

theorem scalarProducer_exists (a : ActualChart (U := U) (H := H)) :
    ∃ Φ : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] Lp ℂ 2 (measure a),
      ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
        (s : BorelL2Sections F ζ hζ U R P H),
        sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
          Φ u =ᵐ[measure a] scalar s a := by
  let W := BorelL2Sections F ζ hζ U R P H
  letI : HasQuotient W (Submodule ℂ W) :=
    @Submodule.hasQuotient ℂ W inferInstance inferInstance inferInstance
  letI : NormedAddCommGroup (L2Line F ζ hζ U R P H) :=
    instNormedAddCommGroupL2Line F ζ hζ U R P H
  letI : NormedSpace ℂ (L2Line F ζ hζ U R P H) :=
    instNormedSpaceL2Line F ζ hζ U R P H
  letI : TopologicalSpace (L2Line F ζ hζ U R P H) :=
    (instNormedAddCommGroupL2Line F ζ hζ U R P H).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let N : Submodule ℂ W := nullSections F ζ hζ U R P H
  let L : W →ₗ[ℂ] Lp ℂ 2 (measure a) := {
    toFun := fun s => (scalar_memLp a s).toLp (scalar s a)
    map_add' := by
      intro s t
      apply Lp.ext
      filter_upwards [(scalar_memLp a (s+t)).coeFn_toLp,
        (scalar_memLp a s).coeFn_toLp, (scalar_memLp a t).coeFn_toLp,
        Lp.coeFn_add ((scalar_memLp a s).toLp _) ((scalar_memLp a t).toLp _)] with x h1 h2 h3 h4
      rw [h1, h4]
      simp only [Pi.add_apply, h2, h3]
      simp [scalar, KPContActualSectorTestDifferentialDescent.liftExtension,
        sectionFields, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
        KPContSectorSmoothFramesSupport.liftCoefficient, LiftedChart.coefficient, map_add]
      split_ifs <;> simp
    map_smul' := by
      intro c s
      apply Lp.ext
      filter_upwards [(scalar_memLp a (c • s)).coeFn_toLp,
        (scalar_memLp a s).coeFn_toLp,
        Lp.coeFn_smul c ((scalar_memLp a s).toLp _)] with x h1 h2 h3
      simp only [RingHom.id_apply]
      rw [h1, h3]
      simp only [Pi.smul_apply, h2]
      simp [scalar, KPContActualSectorTestDifferentialDescent.liftExtension,
        sectionFields, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
        KPContSectorSmoothFramesSupport.liftCoefficient, LiftedChart.coefficient, map_smul] }
  have hNL : N ≤ LinearMap.ker L := by
    intro s hs
    have hm : mk F ζ hζ U R P H s = mk F ζ hζ U R P H 0 := by
      apply (mk_eq_mk_iff F ζ hζ U R P H s 0).mpr
      change squaredNorm F ζ hζ U R P H s.val =ᵐ[_] 0 at hs
      simpa only [Submodule.coe_zero, sub_zero] using hs
    change L s = 0
    apply Lp.ext
    have hz : scalar (0 : W) a = 0 := by
      funext x
      simp [scalar, KPContActualSectorTestDifferentialDescent.liftExtension,
        sectionFields, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
        KPContSectorSmoothFramesSupport.liftCoefficient, LiftedChart.coefficient]
    filter_upwards [(scalar_memLp a s).coeFn_toLp,
      scalar_ae_of_mk_eq_measure a s 0 hm, Lp.coeFn_zero ℂ 2 (measure a)] with x h1 h2 h3
    exact h1.trans (h2.trans (by simpa [hz] using h3.symm))
  let QL : L2Line F ζ hζ U R P H →ₗ[ℂ] Lp ℂ 2 (measure a) :=
    @Submodule.liftQ ℂ W inferInstance inferInstance inferInstance N
      ℂ (Lp ℂ 2 (measure a)) inferInstance inferInstance inferInstance (RingHom.id ℂ) L hNL
  obtain ⟨C, hC, hb⟩ := scalar_norm_bound a
  have hbound : ∀ v, ‖QL v‖ ≤ C * ‖v‖ := by
    intro v
    obtain ⟨s, rfl⟩ := @Submodule.mkQ_surjective ℂ W inferInstance inferInstance inferInstance N v
    exact hb s
  let QC := QL.mkContinuous C hbound
  refine ⟨QC.comp (sectorLineIsometry F ζ hζ U R P H).toContinuousLinearEquiv.toContinuousLinearMap, ?_⟩
  intro u s hs
  change QC (sectorLineIsometry F ζ hζ U R P H u) =ᵐ[measure a] scalar s a
  rw [hs]
  exact (scalar_memLp a s).coeFn_toLp

end DedekindZetaZeroFree.KPContActualSectorBallRestriction

end
