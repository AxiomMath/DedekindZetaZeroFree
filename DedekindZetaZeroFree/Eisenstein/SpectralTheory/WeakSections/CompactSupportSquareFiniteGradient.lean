module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.GradientSupportLocality

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse.Energy
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContActualCotangentMeasurableFamilies KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualSectorTestDifferentialDescent KPContActualCotangentChartRestriction KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 def first (n : ℕ) (j : Fin n) : MultiIndex n 1 :=
  ⟨fun i => if i = j then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
    simp only [apply_ite (Fin.val)]
    simp⟩

private theorem local_coordinate_integrable
    (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (hweak : WeakChartData s W)
    (a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : InteriorBall a B) (j : Fin (3 * d F)) :
    Integrable (fun x => ‖covariantCoordinate W a x j‖ ^ 2) (volume.restrict B.carrier) := by
  obtain ⟨h, hz, hd⟩ := hweak a B hB 1
  have hder := hd (first (3*d F) j) j (by simp [first])
  simp only [map_one, Units.val_one, one_mul] at hder
  have hLp : MemLp (fun x => covariantCoordinate W a x j) 2 (volume.restrict B.carrier) :=
    MemLp.ae_eq hder (Lp.memLp (h.derivatives (first (3*d F) j)))
  exact memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable |>.mp hLp
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse.Energy
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse.Energy
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContActualSectorFormWeakLocalization KPContActualCotangentMeasurableFamilies
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualSectorTestDifferentialDescent KPContActualCotangentChartRestriction KPContCotangentActualGenuineTwistIsotropy
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem coframe_decode_bound (W : Family (U := U) (H := H))
    (a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H))
    (x : Space (3*d F)) (C : ℝ) (hC : 1 ≤ C)
    (hb : ∀ i : Fin (d F), Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)) ≤ C) :
    ‖KPContActualSectorTestDifferentialDescent.liftExtension a (coefficient W a)
        ((baseReindex (F:=F)).symm x)‖ ^ 2 ≤
      C * ∑ j, ‖covariantCoordinate W a x j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  conv_rhs => rw [← Equiv.sum_comp (coefficientIndex (F:=F)), Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Fin.sum_univ_three, covariantCoordinate, Equiv.symm_apply_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  let p := (baseReindex (F:=F)).symm x
  let v := KPContActualSectorTestDifferentialDescent.liftExtension a (coefficient W a) p
  change ‖v (i,0)‖^2 + ‖v (i,1)‖^2 + ‖v (i,2)‖^2 ≤
    C * ((Real.exp (-p (i,2)))^2 * ‖v (i,1)‖^2 +
      (Real.exp (-p (i,2)))^2 * ‖v (i,2)‖^2 + ‖v (i,0)‖^2)
  have he : Real.exp (-p (i,2)) ^ 2 = (Real.exp (2*p (i,2)))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  have hprod : 1 ≤ C * (Real.exp (2*p (i,2)))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    simpa using hb i
  nlinarith [mul_le_mul_of_nonneg_right hprod (sq_nonneg ‖v (i,1)‖),
    mul_le_mul_of_nonneg_right hprod (sq_nonneg ‖v (i,2)‖),
    mul_le_mul_of_nonneg_right hC (sq_nonneg ‖v (i,0)‖)]
private theorem local_norm_integrable
    (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) (hweak : WeakChartData s W)
    (a : KPContActualSectorSmoothTestModules.ActualChart (U := U) (H := H))
    (B : LocalBall (3*d F)) (hB : InteriorBall a B) :
    Integrable (fun x => ‖liftExtension a (coefficient W a)
      ((baseReindex (F:=F)).symm x)‖ ^ 2) (volume.restrict B.carrier) := by
  have hm : Measurable (fun x => liftExtension a (coefficient W a)
      ((baseReindex (F:=F)).symm x)) := by
    have hg : Measurable (liftExtension a (coefficient W a)) := by
      unfold liftExtension
      exact Measurable.dite (W.property.1 a) measurable_const (KPContActualGlobalGreen.isOpen_omega_actual a).measurableSet
    exact hg.comp (baseReindex (F:=F)).symm.continuous.measurable
  have hcont : Continuous (fun x : Space (3*d F) =>
      ∑ i : Fin (d F), Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2))) := by
    fun_prop
  obtain ⟨C, hb⟩ := hB.1.exists_bound_of_continuousOn hcont.continuousOn
  let D := max 1 C
  have hD : 1 ≤ D := le_max_left _ _
  have hbound (x) (hx : x ∈ B.carrier) (i : Fin (d F)) :
      Real.exp (2 * ((baseReindex (F:=F)).symm x) (i,2)) ≤ D := by
    have hs := Finset.single_le_sum (fun j _ => le_of_lt (Real.exp_pos
      (2 * ((baseReindex (F:=F)).symm x) (j,2)))) (Finset.mem_univ i)
    have hc := hb x (subset_closure hx)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ => le_of_lt (Real.exp_pos _)))] at hc
    exact hs.trans (hc.trans (le_max_right _ _))
  have hi : Integrable (fun x => D * ∑ j, ‖covariantCoordinate W a x j‖ ^ 2)
      (volume.restrict B.carrier) :=
    (integrable_finsetSum _ (fun j _ => local_coordinate_integrable s W hweak a B hB j)).const_mul D
  apply hi.mono' ((hm.norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact coframe_decode_bound W a x D hD (hbound x hx)

private theorem ball_around
    (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) :
    ∃ B : LocalBall (3*d F), InteriorBall a B ∧ x ∈ B.carrier := by
  have hd : 0 < d F := by
    have hp := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
    rw [show d F = Module.finrank ℚ F / 2 from rfl, ← hp.2.1]
    exact hp.2.2
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp ((KPContActualGlobalGreen.isOpen_omega_actual a).preimage (baseReindex (F:=F)).symm.continuous) x hx
  let B : LocalBall (3*d F) := ⟨by omega, x, r/2, by linarith⟩
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · change IsCompact (closure (Metric.ball x (r/2)))
    rw [closure_ball x (by linarith : r/2 ≠ 0)]
    exact isCompact_closedBall _ _
  · change closure (Metric.ball x (r/2)) ⊆ coordinateDomain a
    rw [closure_ball x (by linarith : r/2 ≠ 0)]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hb
  · exact Metric.mem_ball_self B.radius_pos

open KPContActualCotangentCountableShrinking KPContSectorSmoothFramesSupport
open KPCuspGenuineMonodromy KPContSectorPhaseComponentCharts
private theorem chart_around (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
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

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse.Energy
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse.Energy
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContActualSectorFormWeakLocalization KPContActualCotangentMeasurableFamilies
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualSectorTestDifferentialDescent KPContActualCotangentChartRestriction
open KPContActualCotangentCountableShrinking KPContSectorSmoothFramesSupport
open KPCuspGenuineMonodromy KPContSectorPhaseComponentCharts
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem subchart_ball (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (ha : a.center ∈ a.domain) (B : LocalBall (3*d F))
    (hB : fromActual (ζ:=ζ) (hζ:=hζ) a.center ∈ B.carrier) :
    ∃ c : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H),
      c.component = a.component ∧ c.center = a.center ∧ c.center ∈ c.domain ∧
      c.domain ⊆ a.domain ∧ chart c ⊆ B.carrier := by
  letI : Finite a.Isotropy := (every_shrunkChart_properties F ζ hζ U R P H a).finite_isotropy
  letI := Fintype.ofFinite a.Isotropy
  let W := a.domain ∩ (fromActual (ζ:=ζ) (hζ:=hζ)) ⁻¹' B.carrier
  have hc : Continuous (fromActual (ζ:=ζ) (hζ:=hζ)) := by
    unfold fromActual labeledAInv
    fun_prop
  have hWo : IsOpen W := a.domain_open.inter (B.toOpens.isOpen.preimage hc)
  let V := ⋂ g : a.Isotropy,
    (fun x : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hVW : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : a.Isotropy)
  have hp : a.center ∈ V := by
    apply Set.mem_iInter.mpr
    intro g
    change g.val • a.center ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact ⟨ha, hB⟩
  let c : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H) :=
    ⟨a.component,a.center,a.larger,V,hVo,
      a.closure_compact.of_isClosed_subset isClosed_closure (closure_mono (fun x hx => (hVW hx).1)),
      (closure_mono (fun x hx => (hVW hx).1)).trans a.closure_subset, by
        intro g
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          apply Set.mem_iInter.mpr
          intro h
          simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h*g)
        · intro hx
          refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x,?_, smul_inv_smul _ _⟩
          apply Set.mem_iInter.mpr
          intro h
          simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
            using Set.mem_iInter.mp hx (h*g⁻¹)⟩
  refine ⟨c,rfl,rfl,hp,fun x hx => (hVW hx).1, ?_⟩
  intro x hx
  have hh := (hVW hx).2
  change fromActual (ζ:=ζ) (hζ:=hζ) (toActual (ζ:=ζ) (hζ:=hζ) x) ∈ B.carrier at hh
  have he : fromActual (ζ:=ζ) (hζ:=hζ) (toActual (ζ:=ζ) (hζ:=hζ) x) = x := by
    unfold fromActual toActual
    have hi : ∀ z : M F, labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) z) = z := by
      intro z
      apply PiLp.ext
      intro k
      simp [labeledAInv,labeledA]
    rw [hi,LinearIsometryEquiv.apply_symm_apply]
  rwa [he] at hh
private theorem weight_continuous (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H)) :
    Continuous (weight a) := by
  unfold weight KPArch.volumeDensity KPArch.height toActual labeledA
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro i _
  apply Continuous.pow
  apply Continuous.inv₀
  · fun_prop
  · intro x
    exact Real.exp_ne_zero _

private theorem subchart_integrable
    (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H)
    (W : Family (U:=U) (H:=H)) (hweak : WeakChartData s W)
    (a c : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (B : LocalBall (3*d F)) (hB : InteriorBall a B)
    (hca : c.component = a.component) (hsub : c.domain ⊆ a.domain)
    (hcB : chart c ⊆ B.carrier) :
    IntegrableOn (fun x => (normSquare W x : ℝ)) c.baseDomain
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  let g := fun x => ‖liftExtension a (coefficient W a) ((baseReindex (F:=F)).symm x)‖ ^ 2
  obtain ⟨D, hb⟩ := hB.1.exists_bound_of_continuousOn (weight_continuous c).continuousOn
  have hgi : Integrable (fun x => weight c x * g x) (volume.restrict B.carrier) :=
    (local_norm_integrable s W hweak a B hB).bdd_mul
      (weight_continuous c).aestronglyMeasurable (by
        filter_upwards [ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hx
        exact hb x (subset_closure hx))
  have hgc : Integrable g (KPContActualSectorChartEquivariantInputs.measure c) := by
    unfold KPContActualSectorChartEquivariantInputs.measure KPChartL2.weightedMeasure
    apply (integrable_withDensity_iff ((weight_continuous c).measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).mpr
    have hi := hgi.mono_measure (Measure.restrict_mono hcB le_rfl)
    apply hi.congr
    filter_upwards [ae_restrict_mem (scalarData c).open_chart.measurableSet] with x hx
    rw [ENNReal.toReal_ofReal (show 0 ≤ weight c x from le_of_lt ((scalarData c).positive_weight x hx)), mul_comm]
  let emb := fun y : c.domain => fromActual (ζ:=ζ) (hζ:=hζ) y.val
  have hme : Measure.map emb c.liftedMeasure = KPContActualSectorChartEquivariantInputs.measure c := lifted_measure_transport (a:=c)
  have hcomp : Integrable (fun y : c.domain => g (emb y)) c.liftedMeasure := by
    change Integrable (g ∘ emb) c.liftedMeasure
    apply (integrable_map_measure (f:=emb) (g:=g) ?_ ?_).mp
    · exact hme.symm ▸ hgc
    · exact hme.symm ▸ hgc.aestronglyMeasurable
    · apply Continuous.aemeasurable
      exact (by
        have hc : Continuous (fromActual (ζ:=ζ) (hζ:=hζ)) := by
          unfold fromActual labeledAInv
          fun_prop
        exact hc.comp continuous_subtype_val)
  have hnorm : (fun y : c.domain => g (emb y)) = (fun y => (normSquare W (c.toBase y) : ℝ)) := by
    funext y
    let p := labeledAInv (placeEquiv F ζ hζ) y.val
    have hi : labeledA (placeEquiv F ζ hζ) p = y.val := by
      funext k
      simp [p,labeledA,labeledAInv]
    have hp : p ∈ omega a := by
      change labeledA (placeEquiv F ζ hζ) p ∈ a.domain
      rw [hi]
      exact hsub y.property
    have hbx : (baseReindex (F:=F)).symm (emb y) = p :=
      (baseReindex (F:=F)).symm_apply_apply p
    change ‖liftExtension a (coefficient W a) ((baseReindex (F:=F)).symm (emb y))‖^2 = _
    rw [hbx, liftExtension, dif_pos hp]
    have hq : q a p = c.toBase y := by
      change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
        (KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ) p)) = _
      rw [hi]
      simp only [ShrunkChart.toBase, KPContSectorPhaseComponentCharts.Component]
      rw [hca]
    rw [← hq,normSquare_chart W a ⟨p,hp⟩]
    simp
  rw [hnorm] at hcomp
  rw [IntegrableOn, ← (every_shrunkChart_properties F ζ hζ U R P H c).exact_pushforward]
  apply (integrable_map_measure ((measurable_normSquare W).coe_nnreal_real.aestronglyMeasurable)
    (every_shrunkChart_properties F ζ hζ U R P H c).measurable.aemeasurable).mpr
  exact hcomp

private theorem to_from (y : SymmetricSpace F) :
    toActual (ζ:=ζ) (hζ:=hζ) (fromActual (ζ:=ζ) (hζ:=hζ) y) = y := by
  unfold fromActual toActual
  rw [LinearIsometryEquiv.symm_apply_apply]
  funext k
  simp [labeledA,labeledAInv]

theorem weakChartData_normSquare_locallyIntegrable
    (s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H)
    (W : Family (U:=U) (H:=H)) (hweak : WeakChartData s W) :
    LocallyIntegrable (fun x => (normSquare W x : ℝ))
      (KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
  intro x
  obtain ⟨⟨i,w⟩,rfl⟩ := (H.atlas U).components.surjective x
  obtain ⟨p,rfl⟩ := Quotient.exists_rep w
  obtain ⟨a,hai,hap,ha⟩ := chart_around (H:=H) i p
  have hac : a.center ∈ a.domain := hap.symm ▸ ha
  have hx : fromActual (ζ:=ζ) (hζ:=hζ) a.center ∈ coordinateDomain a := by
    change labeledA (placeEquiv F ζ hζ) ((baseReindex (F:=F)).symm
      (fromActual (ζ:=ζ) (hζ:=hζ) a.center)) ∈ a.domain
    change toActual (ζ:=ζ) (hζ:=hζ) (fromActual (ζ:=ζ) (hζ:=hζ) a.center) ∈ a.domain
    rw [to_from]
    exact hac
  obtain ⟨B,hB,hmem⟩ := ball_around a _ hx
  obtain ⟨c,hci,hcp,hcm,hsub,hcB⟩ := subchart_ball a hac B hmem
  have hi := subchart_integrable s W hweak a c B hB hci hsub hcB
  have hc := every_shrunkChart_properties F ζ hζ U R P H c
  refine ⟨c.baseDomain, hc.base_open.mem_nhds ?_,hi⟩
  refine ⟨⟨c.center,hcm⟩, ?_⟩
  simp only [ShrunkChart.toBase, KPCuspSiegel.projection, KPContSectorPhaseComponentCharts.Component,
    (H.atlas U).components_formula]
  rw [hci,hai,hcp,hap]

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse.Energy

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry
open KPContActualCotangentMeasurableFamilies
open KPContActualSectorFormWeakLocalization

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem weakChartData_squareFinite_of_zero_off (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U:=U) (H:=H))
    (hweak : WeakChartData s W) (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (hz : ∀ᵐ x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P, x ∉ K → normSquare W x = 0) :
    squareFinite W := by
  have hlocal := Energy.weakChartData_normSquare_locallyIntegrable s W hweak
  have hi := (hlocal.locallyIntegrableOn K).integrableOn_isCompact hK
  have hInt := hi.integrable_of_ae_notMem_eq_zero (by
    filter_upwards [hz] with x hx hnot
    simp [hx hnot])
  have hf := hInt.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at hf
  simpa only [squareFinite, KPContActualSectorCotangentL2.muU, baseMeasure, Real.norm_of_nonneg (NNReal.coe_nonneg _)] using hf

theorem actualWeakH1Loc_compactSupport_squareFinite
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (hsupp : SupportedAE (H := H) u K) (hweak : ActualWeakH1Loc (H := H) u) :
    ∃ (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H)),
      sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s ∧
      WeakChartData s r.val := by
  obtain ⟨s, W, hs, hW⟩ := hweak
  obtain ⟨t, ht, hsupport⟩ := hsupp
  have hst : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t := hs.symm.trans ht
  have hWt : WeakChartData t W := by
    intro a B hB ε
    obtain ⟨h, hzero, hder⟩ := hW a B hB ε
    refine ⟨h, hzero.trans ?_, hder⟩
    have he := KPContActualSectorCoordinateNullEquivalence.scalar_ae_of_mk_eq
      s t hst a B hB
    filter_upwards [he] with x hx
    exact congrArg (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * z) hx
  have hz := weakChartData_zero_off_closed t W hWt K hK.isClosed hsupport
  exact ⟨t, ⟨W, weakChartData_squareFinite_of_zero_off t W hWt K hK hz⟩, ht, hWt⟩

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end
