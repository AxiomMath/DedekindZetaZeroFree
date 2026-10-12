module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.NormalBallMeasure
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.SphericalChartModulus

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal Pointwise
open MeasureTheory Topology Set

namespace DedekindZetaZeroFree.KPFixedHaarNormalBallMaps

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualFixedHaarCoreLocalizers KPContSectorSmoothFramesSupport
  KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

 abbrev instTopologicalSpaceL2LineLocal : TopologicalSpace (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceL2LineLocal

 abbrev instAddCommMonoidL2LineLocal : AddCommMonoid (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidL2LineLocal

 abbrev instTopologicalSpaceHULocal : TopologicalSpace (H_U F ζ hζ U R) :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHULocal

 abbrev instTopologicalSpaceHKLocal (K : Set (X_U F ζ hζ U)) :
    TopologicalSpace (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHKLocal

 abbrev instAddCommMonoidHKLocal (K : Set (X_U F ζ hζ U)) :
    AddCommMonoid (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidHKLocal

variable {G X : Type*} [Group G] [Countable G] [MulAction G X]
  [MeasurableSpace X] [MeasurableConstSMul G X]
private theorem countable_equivariant_extension (S : Set X) (hS : MeasurableSet S) (T : Subgroup G)
    (χ : G →* ℂˣ) (V : Submodule ℂ ℂ) (b : X → ℂ) (hb : Measurable b)
    (hbV : ∀ x ∈ S, b x ∈ V)
    (hsep : ∀ g : G, ∀ x ∈ S, g • x ∈ S → g ∈ T)
    (heq : ∀ g : T, ∀ x ∈ S, b (g.val • x) = (χ g.val : ℂ) * b x) :
    ∃ p : X → ℂ, Measurable p ∧ (∀ x, p x ∈ V) ∧
      (∀ g : G, ∀ x, p (g • x) = (χ g : ℂ) * p x) ∧
      (∀ x ∈ S, p x = b x) ∧
      (∀ x, (∀ g : G, g • x ∉ S) → p x = 0) := by
  let A : G → Set X := fun g => (fun x => g⁻¹ • x) ⁻¹' S
  have hA : ∀ g, MeasurableSet (A g) := fun g => hS.preimage (measurable_const_smul _)
  let v : G → X → ℂ := fun g x => (χ g : ℂ) * b (g⁻¹ • x)
  have hv : ∀ g, Measurable (v g) := fun g => measurable_const.mul (hb.comp (measurable_const_smul _))
  have hcompat : Pairwise fun g h => EqOn (v g) (v h) (A g ∩ A h) := by
    intro g h _ x hx
    have hxg : g⁻¹ • x ∈ S := hx.1
    have hxh : h⁻¹ • x ∈ S := hx.2
    have hm : h⁻¹ * g ∈ T := hsep _ _ hxg (by simpa only [mul_smul, smul_inv_smul] using hxh)
    have hc := heq ⟨h⁻¹ * g, hm⟩ (g⁻¹ • x) hx.1
    change b ((h⁻¹ * g) • (g⁻¹ • x)) = (χ (h⁻¹ * g) : ℂ) * b (g⁻¹ • x) at hc
    simp only [mul_smul, smul_inv_smul] at hc
    change (χ g : ℂ) * b (g⁻¹ • x) = (χ h : ℂ) * b (h⁻¹ • x)
    rw [hc]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨q, hq, hqv⟩ := exists_measurable_piecewise A hA v hv hcompat
  let W := ⋃ g, A g
  have hW : MeasurableSet W := MeasurableSet.iUnion hA
  let p := W.indicator q
  have hp (g : G) (x : X) (hx : x ∈ A g) : p x = v g x := by
    rw [show p x = q x by exact indicator_of_mem (mem_iUnion.mpr ⟨g,hx⟩) _]
    exact hqv g hx
  have hWinv (g : G) (x : X) : g • x ∈ W ↔ x ∈ W := by
    simp only [W, mem_iUnion, A, mem_preimage]
    constructor
    · rintro ⟨h,hh⟩
      refine ⟨g⁻¹ * h, ?_⟩
      simpa only [mul_inv_rev, inv_inv, mul_smul] using hh
    · rintro ⟨h,hh⟩
      refine ⟨g * h, ?_⟩
      simpa only [mul_inv_rev, mul_smul, inv_smul_smul] using hh
  refine ⟨p, hq.indicator hW, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ W
    · obtain ⟨g,hg⟩ := mem_iUnion.mp hx
      rw [hp g x hg]
      exact V.smul_mem (χ g : ℂ) (hbV _ hg)
    · rw [show p x = 0 from indicator_of_notMem hx _]
      exact V.zero_mem
  · intro g x
    by_cases hx : x ∈ W
    · obtain ⟨h,hh⟩ := mem_iUnion.mp hx
      have hgh : g • x ∈ A (g * h) := by
        simpa only [A, mem_preimage, mul_inv_rev, mul_smul, inv_smul_smul] using hh
      rw [hp h x hh, hp (g * h) (g • x) hgh]
      simp only [v, map_mul, Units.val_mul, mul_inv_rev, mul_smul, inv_smul_smul]
      ring
    · rw [show p x = 0 from indicator_of_notMem hx _,
        show p (g • x) = 0 from indicator_of_notMem (fun h => hx ((hWinv g x).mp h)) _]
      simp
  · intro x hx
    have h1 : x ∈ A 1 := by simpa [A] using hx
    rw [hp 1 x h1]
    simp [v]
  · intro x hx
    have hw : x ∉ W := by
      intro h
      obtain ⟨g, hg⟩ := mem_iUnion.mp h
      exact hx g⁻¹ hg
    exact indicator_of_notMem hw _

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

private theorem normal_coefficient_extension
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (b : KPCoreChartLocalizers.E C.n → ℂ) (hb : Measurable b)
    (hbV : ∀ x, b x ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (heq : ∀ g : C.G F ζ hζ H.totallyComplex U, ∀ x ∈ Metric.ball 0 C.radius,
      b (C.orthogonal g x) = (C.rho F ζ hζ H.totallyComplex U g : ℂ) * b x) :
    ∃ t : KPCuspGenuineMonodromy.sections F ζ hζ U
        ((H.atlas U).representative C.component) ((H.atlas U).line C.component).rho,
      Measurable t.val ∧ (∀ x ∈ Metric.ball 0 C.radius, t.val (C.coordinates x) = b x) ∧
      (∀ x, (∀ g : KPCuspGenuineMonodromy.Component F ζ hζ U
        ((H.atlas U).representative C.component),
        g.val • x ∉ C.coordinates '' Metric.ball 0 C.radius) → t.val x = 0) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative C.component)
  letI : MeasurableConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measurable⟩
  let B := Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius
  let S := C.coordinates '' B
  have hB : B ⊆ C.extendedDomain := subset_closure.trans C.closed_ball_in_extension
  have hS : IsOpen S := by
    have hi := C.coordinates_ball_open_map F ζ hζ H.totallyComplex U _ isOpen_univ
    convert hi using 1
    ext z
    simp only [S, image_univ, Set.range, mem_image]
    exact ⟨fun ⟨x,hx,h⟩ => ⟨⟨x,hx⟩,h⟩, fun ⟨x,h⟩ => ⟨x.val,x.property,h⟩⟩
  obtain ⟨inv, hinv, hleft⟩ := C.smooth_inverse
  have hc : Continuous (fun z : S => inv z.val) :=
    continuousOn_iff_continuous_restrict.mp (hinv.continuousOn.mono (Set.image_mono hB))
  let β : KPFiniteCuspAtlas.SymmetricSpace F → ℂ := fun z =>
    if hz : z ∈ S then b (inv z) else 0
  have hβ : Measurable β := by
    exact (hb.comp hc.measurable).dite measurable_const hS.measurableSet
  have hβV : ∀ z ∈ S, β z ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
    intro z hz
    simp only [β, dif_pos hz]
    exact hbV _
  have hβcoord (x) (hx : x ∈ B) : β (C.coordinates x) = b x := by
    have hs : C.coordinates x ∈ S := ⟨x,hx,rfl⟩
    simp only [β, dif_pos hs, hleft x (hB hx)]
  have hsep : ∀ g : Γ, ∀ z ∈ S, g • z ∈ S → g ∈ MulAction.stabilizer Γ C.center := by
    intro g z hz hgz
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨y,hy,hyz⟩ := hgz
    exact C.separated g x y (hB hx) (hB hy) hyz.symm
  have hβeq : ∀ g : MulAction.stabilizer Γ C.center, ∀ z ∈ S,
      β (g.val • z) = (KPCuspGenuineMonodromy.chi F ζ hζ
        (((H.atlas U).line C.component).rho g.val) : ℂ) * β z := by
    intro g z hz
    obtain ⟨x,hx,rfl⟩ := hz
    have hgx : C.orthogonal g x ∈ B := (C.orthogonal_mem_ball F ζ hζ H.totallyComplex U g x).mpr hx
    change β (g.val.val • C.coordinates x) = _
    rw [← C.equivariance g x (hB hx), hβcoord _ hgx, hβcoord _ hx]
    exact heq g x hx
  obtain ⟨p,hp,hpV,hpeq,hpb,hpzero⟩ := countable_equivariant_extension S hS.measurableSet
    (MulAction.stabilizer Γ C.center)
    ((KPCuspGenuineMonodromy.chi F ζ hζ).comp ((H.atlas U).line C.component).rho)
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) β hβ hβV hsep hβeq
  refine ⟨⟨p, hpV, hpeq⟩, hp, ?_, hpzero⟩
  intro x hx
  exact (hpb _ ⟨x,hx,rfl⟩).trans (hβcoord x hx)

private theorem projected_average_measurable
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    Measurable (fun x =>
      ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
        (C.average F ζ hζ H.totallyComplex U f x) : ℂ)) := by
  apply measurable_subtype_coe.comp
  apply (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto.measurable.comp
  unfold KPCoreChartLocalizers.Chart.average
  apply Measurable.indicator _ Metric.isOpen_ball.measurableSet
  exact measurable_const.mul (Finset.measurable_sum _ (fun g _ =>
    measurable_const.mul ((Lp.stronglyMeasurable f).measurable.comp (C.orthogonal g).continuous.measurable)))

private theorem projected_average_equivariant
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)))
    (g : C.G F ζ hζ H.totallyComplex U) (x : KPCoreChartLocalizers.E C.n) :
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U f (C.orthogonal g x)) : ℂ) =
      (C.rho F ζ hζ H.totallyComplex U g : ℂ) *
        ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
          (C.average F ζ hζ H.totallyComplex U f x) : ℂ) := by
  rw [C.average_equivariant F ζ hζ H.totallyComplex U]
  change ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      ((C.rho F ζ hζ H.totallyComplex U g : ℂ) • _) : ℂ) = _
  rw [map_smul]
  rfl

 def singleComponent
    (i : Fin (H.atlas U).componentCount)
    (t : KPCuspGenuineMonodromy.sections F ζ hζ U
      ((H.atlas U).representative i) ((H.atlas U).line i).rho) :
    KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H :=
  fun j => if h : i = j then h ▸ t else 0

private theorem singleComponent_apply
    (i : Fin (H.atlas U).componentCount)
    (t : KPCuspGenuineMonodromy.sections F ζ hζ U
      ((H.atlas U).representative i) ((H.atlas U).line i).rho) :
    singleComponent F ζ hζ U R P H i t i = t := by
  simp [singleComponent]

private theorem singleComponent_measurable
    (i : Fin (H.atlas U).componentCount)
    (t : KPCuspGenuineMonodromy.sections F ζ hζ U
      ((H.atlas U).representative i) ((H.atlas U).line i).rho)
    (ht : Measurable t.val) :
    ∀ j, Measurable ((singleComponent F ζ hζ U R P H i t) j).val := by
  intro j
  by_cases h : i = j
  · subst j
    simpa [singleComponent] using ht
  · simpa [singleComponent, h] using (measurable_zero : Measurable (0 : KPFiniteCuspAtlas.SymmetricSpace F → ℂ))

private theorem singleComponent_zero_off_chart
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (t : KPCuspGenuineMonodromy.sections F ζ hζ U
      ((H.atlas U).representative C.component) ((H.atlas U).line C.component).rho)
    (ht : ∀ x, (∀ g : KPCuspGenuineMonodromy.Component F ζ hζ U
      ((H.atlas U).representative C.component),
      g.val • x ∉ C.coordinates '' Metric.ball 0 C.radius) → t.val x = 0) :
    ∀ b, b ∉ C.O F ζ hζ H.totallyComplex U →
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H
        (singleComponent F ζ hζ U R P H C.component t) b = 0 := by
  intro b
  rw [show b = (H.atlas U).components ((H.atlas U).components.symm b) from
    ((H.atlas U).components.apply_symm_apply b).symm]
  obtain ⟨i,q⟩ := (H.atlas U).components.symm b
  refine Quotient.inductionOn q (fun x => ?_)
  intro hb
  rw [KPContSectorLineL2Isometry.squaredNorm,
    KPContSectorSmoothFramesSupport.sectionNorm_component]
  by_cases hi : C.component = i
  · subst i
    rw [singleComponent_apply]
    have hz : t.val x = 0 := ht x (by
      intro g hg
      apply hb
      obtain ⟨y,hy,he⟩ := hg
      refine ⟨y,hy,?_⟩
      rw [KPCoreChartLocalizers.Chart.toBase, ← (H.atlas U).components_formula]
      apply congrArg (fun q => (H.atlas U).components ⟨C.component,q⟩)
      apply Quotient.sound
      exact ⟨g, he.symm⟩)
    simp [hz]
  · simp [singleComponent, hi]

private theorem lp_norm_squared {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : Lp ℂ 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) = ENNReal.ofReal (‖f‖ ^ 2) := by
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
  change (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) = ‖f‖ₑ ^ (2 : ℝ)
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := fun x => f x) (show (0 : ℝ) < 2 by norm_num)]
  have he := eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (Lp.aestronglyMeasurable f)
  simp only [ENNReal.toReal_ofNat] at he
  rw [← he, ← Lp.enorm_def]

private theorem projected_average_integral_le
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    (∫⁻ x in Metric.ball 0 C.radius, ENNReal.ofReal
      (‖((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
        (C.average F ζ hζ H.totallyComplex U f x) : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal (‖f‖ ^ 2) := by
  let B := Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius
  have hsub : B ⊆ KPCoreChartLocalizers.cube C.n C.a :=
    subset_closure.trans (C.closed_ball_in_cube.trans interior_subset)
  have hf := (Lp.memLp f).mono_measure (Measure.restrict_mono hsub le_rfl)
  let r : Lp ℂ 2 (volume.restrict B) := hf.toLp f
  have hr : (r : KPCoreChartLocalizers.E C.n → ℂ) =ᵐ[volume.restrict B] f := hf.coeFn_toLp
  let q := C.averageLp F ζ hζ H.totallyComplex U r
  have hq : (q : KPCoreChartLocalizers.E C.n → ℂ) =ᵐ[volume.restrict B]
      C.average F ζ hζ H.totallyComplex U f :=
    (C.averageLp_formula F ζ hζ H.totallyComplex U r).trans
      (C.average_congr_ae F ζ hζ H.totallyComplex U hr)
  calc
    _ ≤ ∫⁻ x in B, ENNReal.ofReal (‖C.average F ζ hζ H.totallyComplex U f x‖ ^ 2) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).norm_orthogonalProjectionOnto_apply_le _
    _ = ENNReal.ofReal (‖q‖ ^ 2) := by
      rw [← lp_norm_squared (volume.restrict B) q]
      apply lintegral_congr_ae
      filter_upwards [hq] with x hx
      rw [hx]
    _ ≤ ENNReal.ofReal (‖r‖ ^ 2) := ENNReal.ofReal_le_ofReal
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (C.norm_averageLp_le F ζ hζ H.totallyComplex U r))
    _ ≤ ENNReal.ofReal (‖f‖ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hr]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))

private theorem actual_integral_bound
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)))
    (t : KPCuspGenuineMonodromy.sections F ζ hζ U
      ((H.atlas U).representative C.component) ((H.atlas U).line C.component).rho)
    (htm : Measurable t.val)
    (htb : ∀ x ∈ Metric.ball 0 C.radius, t.val (C.coordinates x) =
      ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
        (C.average F ζ hζ H.totallyComplex U f x) : ℂ))
    (ht0 : ∀ b, b ∉ C.O F ζ hζ H.totallyComplex U →
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H
        (singleComponent F ζ hζ U R P H C.component t) b = 0) :
    KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H
      (singleComponent F ζ hζ U R P H C.component t) ≤
      (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ *
        ((H.disintegration U).componentWeight C.component * ENNReal.ofReal C.upper) * ENNReal.ofReal (‖f‖ ^ 2) := by
  let B := Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius
  let c := (H.disintegration U).componentWeight C.component
  let d : KPCoreChartLocalizers.E C.n → ℝ≥0∞ := fun x => ENNReal.ofReal (c.toReal * C.weight x)
  let ν := (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ • (volume.restrict B).withDensity d
  let N := KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H
    (singleComponent F ζ hζ U R P H C.component t)
  have hNm : Measurable N := KPContSectorLineL2Isometry.squaredNorm_measurable F ζ hζ U R P H _
    (singleComponent_measurable F ζ hζ U R P H _ t htm)
  have hsupport : Function.support N ⊆ C.O F ζ hζ H.totallyComplex U := by
    intro b hb
    by_contra h
    exact hb (ht0 b h)
  have hbase : AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) (volume.restrict B) :=
    (continuousOn_iff_continuous_restrict.mpr
      (C.toBase_ball_continuous F ζ hζ H.totallyComplex U)).aemeasurable Metric.isOpen_ball.measurableSet
  have hνac : ν ≪ volume.restrict B :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hd : d ≤ᵐ[volume.restrict B] fun _ => c * ENNReal.ofReal C.upper := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    dsimp [d]
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ne_of_lt ((H.disintegration U).finite_componentWeight C.component))]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (C.finite_bounds x (subset_closure hx)).2) c
  have hnule : ν ≤ ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ * (c * ENNReal.ofReal C.upper)) • volume.restrict B := by
    calc ν ≤ (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        ((c * ENNReal.ofReal C.upper) • volume.restrict B) := by
          intro s
          simp only [Measure.smul_apply, smul_eq_mul]
          exact mul_le_mul_right (((withDensity_mono hd).trans_eq (withDensity_const _)) s) _
      _ = _ := by rw [smul_smul]
  have hNcoord : ∀ x ∈ B, N (C.toBase F ζ hζ H.totallyComplex U x) =
      ENNReal.ofReal (‖((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
        (C.average F ζ hζ H.totallyComplex U f x) : ℂ)‖ ^ 2) := by
    intro x hx
    dsimp [N]
    rw [KPContSectorLineL2Isometry.squaredNorm, KPCoreChartLocalizers.Chart.toBase,
      ← (H.atlas U).components_formula]
    change ENNReal.ofReal (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H _
      ((H.atlas U).components ⟨C.component, Quotient.mk _ (C.coordinates x)⟩) ^ 2) = _
    rw [KPContSectorSmoothFramesSupport.sectionNorm_component, singleComponent_apply, htb x hx]
    rfl
  calc
    _ = ∫⁻ b in C.O F ζ hζ H.totallyComplex U, N b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U :=
      (setLIntegral_eq_of_support_subset hsupport).symm
    _ = ∫⁻ x, N (C.toBase F ζ hζ H.totallyComplex U x) ∂ν := by
      rw [← KPFixedHaarLocalizersBodies.actual_chart_measure F ζ hζ U R P H C]
      exact lintegral_map' hNm.aemeasurable (hbase.mono_ac hνac)
    _ ≤ ∫⁻ x, N (C.toBase F ζ hζ H.totallyComplex U x)
        ∂(((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ * (c * ENNReal.ofReal C.upper)) • volume.restrict B) := lintegral_mono' hnule le_rfl
    _ = ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ * (c * ENNReal.ofReal C.upper)) *
        ∫⁻ x in B, ENNReal.ofReal (‖((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
          (C.average F ζ hζ H.totallyComplex U f x) : ℂ)‖ ^ 2) := by
      rw [lintegral_smul_measure]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact hNcoord x hx
    _ ≤ _ := mul_le_mul_right (projected_average_integral_le F ζ hζ U R P H C f) _

 theorem averaged_section_descent
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    ∃ t : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H,
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
        (t.val C.component).val (C.coordinates x) =
          ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
            (C.average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
      (∀ b, b ∉ C.O F ζ hζ H.totallyComplex U →
        KPContSectorLineL2Isometry.squaredNorm F ζ hζ U R P H t.val b = 0) ∧
      KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H t.val ≤
        (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ *
          ((H.disintegration U).componentWeight C.component * ENNReal.ofReal C.upper) * ENNReal.ofReal (‖f‖ ^ 2) := by
  let b := fun x =>
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U f x) : ℂ)
  have hb : Measurable b := projected_average_measurable F ζ hζ U R P H C f
  have hbV : ∀ x, b x ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := fun x =>
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto _).property
  have heq : ∀ g : C.G F ζ hζ H.totallyComplex U, ∀ x ∈ Metric.ball 0 C.radius,
      b (C.orthogonal g x) = (C.rho F ζ hζ H.totallyComplex U g : ℂ) * b x :=
    fun g x _ => projected_average_equivariant F ζ hζ U R P H C f g x
  obtain ⟨t,htm,htb,ht0⟩ := normal_coefficient_extension F ζ hζ U R P H C b hb hbV heq
  let s := singleComponent F ζ hζ U R P H C.component t
  have hsm : ∀ i, Measurable (s i).val := singleComponent_measurable F ζ hζ U R P H _ t htm
  have hs0 := singleComponent_zero_off_chart F ζ hζ U R P H C t ht0
  have hbound := actual_integral_bound F ζ hζ U R P H C f t htm htb hs0
  have hsfin : KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H s < ⊤ := by
    refine lt_of_le_of_lt hbound ?_
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by simp only [ENNReal.inv_lt_top, Nat.cast_pos]; exact Fintype.card_pos)
        (ENNReal.mul_lt_top ((H.disintegration U).finite_componentWeight C.component)
          ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
  refine ⟨⟨s,hsm,hsfin⟩, ?_, hs0, hbound⟩
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  change (singleComponent F ζ hζ U R P H C.component t C.component).val (C.coordinates x) = b x
  rw [singleComponent_apply]
  exact htb x hx

private theorem sectionNorm_nonneg (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) : 0 ≤ sectionNorm F ζ hζ U R P H s b := by
  dsimp [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  exact norm_nonneg _

private theorem norm_difference_le (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (s - t) b ≤
      sectionNorm F ζ hζ U R P H s b + sectionNorm F ζ hζ U R P H t b := by
  dsimp [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  exact norm_sub_le _ _

private theorem squaredNorm_zero_iff (s : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    squaredNorm F ζ hζ U R P H s b = 0 ↔ sectionNorm F ζ hζ U R P H s b = 0 := by
  rw [squaredNorm, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    nlinarith [sectionNorm_nonneg F ζ hζ U R P H s b]
  · intro h
    simp [h]

private theorem zero_difference (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U)
    (hs : squaredNorm F ζ hζ U R P H s b = 0)
    (ht : squaredNorm F ζ hζ U R P H t b = 0) :
    squaredNorm F ζ hζ U R P H (s - t) b = 0 := by
  apply (squaredNorm_zero_iff F ζ hζ U R P H _ b).mpr
  have h := norm_difference_le F ζ hζ U R P H s t b
  rw [(squaredNorm_zero_iff F ζ hζ U R P H s b).mp hs,
    (squaredNorm_zero_iff F ζ hζ U R P H t b).mp ht, zero_add] at h
  exact le_antisymm h (sectionNorm_nonneg F ζ hζ U R P H _ b)

private theorem zero_sum (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U)
    (hs : squaredNorm F ζ hζ U R P H s b = 0)
    (ht : squaredNorm F ζ hζ U R P H t b = 0) :
    squaredNorm F ζ hζ U R P H (s + t) b = 0 := by
  apply (squaredNorm_zero_iff F ζ hζ U R P H _ b).mpr
  have h : sectionNorm F ζ hζ U R P H (s + t) b ≤
      sectionNorm F ζ hζ U R P H s b + sectionNorm F ζ hζ U R P H t b := by
    dsimp [sectionNorm]
    refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
    exact norm_add_le _ _
  rw [(squaredNorm_zero_iff F ζ hζ U R P H s b).mp hs,
    (squaredNorm_zero_iff F ζ hζ U R P H t b).mp ht, zero_add] at h
  exact le_antisymm h (sectionNorm_nonneg F ζ hζ U R P H _ b)

private theorem zero_smul (z : ℂ) (s : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U)
    (hs : squaredNorm F ζ hζ U R P H s b = 0) :
    squaredNorm F ζ hζ U R P H (z • s) b = 0 := by
  apply (squaredNorm_zero_iff F ζ hζ U R P H _ b).mpr
  have h : sectionNorm F ζ hζ U R P H (z • s) b = ‖z‖ * sectionNorm F ζ hζ U R P H s b := by
    dsimp [sectionNorm]
    refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
    exact norm_mul _ _
  rw [h, (squaredNorm_zero_iff F ζ hζ U R P H s b).mp hs, mul_zero]

set_option maxHeartbeats 1200000 in
private theorem class_eq_of_ball (K : Set (X_U F ζ hζ U))
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U))
    (s t : BorelL2Sections F ζ hζ U R P H)
    (heq : ∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
      (s.val C.component).val (C.coordinates x) = (t.val C.component).val (C.coordinates x))
    (hs : ∀ b, b ∉ C.O F ζ hζ H.totallyComplex U → squaredNorm F ζ hζ U R P H s.val b = 0)
    (ht : ∀ b, b ∉ C.O F ζ hζ H.totallyComplex U → squaredNorm F ζ hζ U R P H t.val b = 0) :
    mkK F ζ hζ U R P H K s = mkK F ζ hζ U R P H K t := by
  apply (mkK_eq_iff F ζ hζ U R P H K s t).mpr
  apply Filter.Eventually.filter_mono (ae_restrict_le)
  let ν := ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x)))
  let N := squaredNorm F ζ hζ U R P H (s.val - t.val)
  have hν : ν ≪ volume.restrict (Metric.ball 0 C.radius) :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hcoord : ∀ᵐ x ∂ν, N (C.toBase F ζ hζ H.totallyComplex U x) = 0 := by
    filter_upwards [hν.ae_le heq] with x hx
    dsimp [N]
    rw [squaredNorm, KPCoreChartLocalizers.Chart.toBase, ← (H.atlas U).components_formula, KPCuspSiegel.projection,
      sectionNorm_component]
    change ENNReal.ofReal (‖(s.val C.component).val (C.coordinates x) -
      (t.val C.component).val (C.coordinates x)‖ ^ 2) = 0
    simp [hx]
  have hm : Measurable N := squaredNorm_measurable F ζ hζ U R P H _
    (s - t).property.1
  have hb : AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) ν :=
    ((continuousOn_iff_continuous_restrict.mpr
      (C.toBase_ball_continuous F ζ hζ H.totallyComplex U)).aemeasurable
      Metric.isOpen_ball.measurableSet).mono_ac hν
  have hon : ∀ᵐ b ∂(muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U), N b = 0 := by
    rw [← hchart]
    have hmeas : MeasurableSet {b | N b = 0} := hm (measurableSet_singleton 0)
    exact (ae_map_iff hb hmeas).mpr hcoord
  have hO : MeasurableSet (C.O F ζ hζ H.totallyComplex U) :=
    (C.open_image F ζ hζ H.totallyComplex U).measurableSet
  rw [ae_restrict_iff' hO] at hon
  filter_upwards [hon] with b hb
  by_cases h : b ∈ C.O F ζ hζ H.totallyComplex U
  · exact hb h
  · exact zero_difference F ζ hζ U R P H s.val t.val b (hs b h) (ht b h)

 def descended (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    BorelL2Sections F ζ hζ U R P H := Classical.choose (averaged_section_descent F ζ hζ U R P H C f)

private theorem descended_ball (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
      ((descended F ζ hζ U R P H C f).val C.component).val (C.coordinates x) =
        ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
          (C.average F ζ hζ H.totallyComplex U f x) : ℂ) :=
  (Classical.choose_spec (averaged_section_descent F ζ hζ U R P H C f)).1

private theorem descended_zero (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    ∀ b, b ∉ C.O F ζ hζ H.totallyComplex U →
      squaredNorm F ζ hζ U R P H (descended F ζ hζ U R P H C f).val b = 0 :=
  (Classical.choose_spec (averaged_section_descent F ζ hζ U R P H C f)).2.1

private theorem projection_add (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f g : KPCoreChartLocalizers.E C.n → ℂ) (x : KPCoreChartLocalizers.E C.n) :
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U (f + g) x) : ℂ) =
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U f x) : ℂ) +
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U g x) : ℂ) := by
  have ha : C.average F ζ hζ H.totallyComplex U (f + g) x =
      C.average F ζ hζ H.totallyComplex U f x + C.average F ζ hζ H.totallyComplex U g x := by
    by_cases hx : x ∈ Metric.ball 0 C.radius
    · simp only [KPCoreChartLocalizers.Chart.average, indicator_of_mem hx, Pi.add_apply,
        mul_add, Finset.sum_add_distrib]
    · simp [C.average_zero_outside F ζ hζ H.totallyComplex U _ hx]
  rw [ha, map_add]
  rfl

private theorem projection_smul (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (z : ℂ) (f : KPCoreChartLocalizers.E C.n → ℂ) (x : KPCoreChartLocalizers.E C.n) :
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U (z • f) x) : ℂ) =
    z * ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U f x) : ℂ) := by
  have ha : C.average F ζ hζ H.totallyComplex U (z • f) x =
      z • C.average F ζ hζ H.totallyComplex U f x := by
    by_cases hx : x ∈ Metric.ball 0 C.radius
    · simp only [KPCoreChartLocalizers.Chart.average, indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
      have he : (∑ g : C.G F ζ hζ H.totallyComplex U,
          ((C.rho F ζ hζ H.totallyComplex U g)⁻¹ : ℂˣ) * (z * f (C.orthogonal g x))) =
          z * ∑ g : C.G F ζ hζ H.totallyComplex U,
          ((C.rho F ζ hζ H.totallyComplex U g)⁻¹ : ℂˣ) * f (C.orthogonal g x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        ring
      rw [he]
      ring
    · simp [C.average_zero_outside F ζ hζ H.totallyComplex U _ hx]
  rw [ha, map_smul]
  rfl

private theorem projection_congr (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f g : KPCoreChartLocalizers.E C.n → ℂ)
    (h : f =ᵐ[volume.restrict (KPCoreChartLocalizers.cube C.n C.a)] g) :
    (fun x => ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U f x) : ℂ)) =ᵐ[volume.restrict (Metric.ball 0 C.radius)]
    (fun x => ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U g x) : ℂ)) := by
  have hsub : Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius ⊆ KPCoreChartLocalizers.cube C.n C.a :=
    subset_closure.trans (C.closed_ball_in_cube.trans interior_subset)
  have ha := C.average_congr_ae F ζ hζ H.totallyComplex U
    (h.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl)))
  filter_upwards [ha] with x hx
  rw [hx]

set_option maxHeartbeats 1200000 in
private theorem descended_norm (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (f : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a))) :
    ‖mkK F ζ hζ U R P H K (descended F ζ hζ U R P H C f)‖ ≤
      Real.sqrt (((H.disintegration U).componentWeight C.component).toReal * C.upper /
        (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ)) * ‖f‖ := by
  let c := ((H.disintegration U).componentWeight C.component).toReal * C.upper /
    (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ)
  have hu : 0 ≤ C.upper := le_trans C.positive_lower.le
    (le_trans (C.finite_bounds 0 (subset_closure (by simpa using C.positive_radius))).1
      (C.finite_bounds 0 (subset_closure (by simpa using C.positive_radius))).2)
  have hc : 0 ≤ c := div_nonneg (mul_nonneg ENNReal.toReal_nonneg hu) (Nat.cast_nonneg _)
  have hb : normIntegral F ζ hζ U R P H (descended F ζ hζ U R P H C f).val ≤
      (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ *
      ((H.disintegration U).componentWeight C.component * ENNReal.ofReal C.upper) * ENNReal.ofReal (‖f‖ ^ 2) :=
    (Classical.choose_spec (averaged_section_descent F ζ hζ U R P H C f)).2.2
  have hconst : (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ *
      ((H.disintegration U).componentWeight C.component * ENNReal.ofReal C.upper) * ENNReal.ofReal (‖f‖ ^ 2) =
      ENNReal.ofReal (c * ‖f‖ ^ 2) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ne_of_lt ((H.disintegration U).finite_componentWeight C.component)),
      ENNReal.ofReal_natCast, div_eq_mul_inv]
    ring
  rw [hconst] at hb
  have hs : ‖mkK F ζ hζ U R P H K (descended F ζ hζ U R P H C f)‖ ^ 2 ≤ c * ‖f‖ ^ 2 := by
    rw [norm_mkK_sq F ζ hζ U R P H K]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc (sq_nonneg _))
      ((lintegral_mono' Measure.restrict_le_self le_rfl).trans hb)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hc]
  exact hs

set_option maxHeartbeats 1200000 in

theorem averagedZeroExtension_exists
    (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)
    (C : KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U))
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
        ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
          (volume.restrict (Metric.ball 0 C.radius)).withDensity
            (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U)) :
    ∃ Rmap : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) →L[ℂ]
        H_K F ζ hζ U R P H K,
      ‖Rmap‖ ≤ Real.sqrt (((H.disintegration U).componentWeight C.component).toReal *
        C.upper / (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ)) ∧
      ∀ f, ∃ t : BorelL2Sections F ζ hζ U R P H,
        Rmap f = mkK F ζ hζ U R P H K t ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
          C.toBase F ζ hζ H.totallyComplex U x ∈ K →
          (t.val C.component).val (C.coordinates x) =
            ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
              (C.average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
        (∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
          b ∉ C.O F ζ hζ H.totallyComplex U → squaredNorm F ζ hζ U R P H t.val b = 0) := by
  let L : Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube C.n C.a)) →ₗ[ℂ] H_K F ζ hζ U R P H K := {
    toFun := fun f => mkK F ζ hζ U R P H K (descended F ζ hζ U R P H C f)
    map_add' := by
      intro f g
      rw [← map_add]
      apply class_eq_of_ball F ζ hζ U R P H K C hchart
      · have ha := projection_congr F ζ hζ U R P H C _ _ (Lp.coeFn_add f g)
        filter_upwards [descended_ball F ζ hζ U R P H C (f+g),
          descended_ball F ζ hζ U R P H C f, descended_ball F ζ hζ U R P H C g, ha] with x hx hf hg ha
        change _ = ((descended F ζ hζ U R P H C f).val C.component).val (C.coordinates x) +
          ((descended F ζ hζ U R P H C g).val C.component).val (C.coordinates x)
        rw [hx, ha, projection_add, hf, hg]
      · exact descended_zero F ζ hζ U R P H C (f+g)
      · intro b hb
        exact zero_sum F ζ hζ U R P H _ _ b
          (descended_zero F ζ hζ U R P H C f b hb)
          (descended_zero F ζ hζ U R P H C g b hb)
    map_smul' := by
      intro z f
      rw [← map_smul]
      apply class_eq_of_ball F ζ hζ U R P H K C hchart
      · have ha := projection_congr F ζ hζ U R P H C _ _ (Lp.coeFn_smul z f)
        filter_upwards [descended_ball F ζ hζ U R P H C (z • f),
          descended_ball F ζ hζ U R P H C f, ha] with x hx hf ha
        change _ = z * ((descended F ζ hζ U R P H C f).val C.component).val (C.coordinates x)
        rw [hx, ha, projection_smul, hf]
      · exact descended_zero F ζ hζ U R P H C (z • f)
      · intro b hb
        exact zero_smul F ζ hζ U R P H z _ b (descended_zero F ζ hζ U R P H C f b hb) }
  let c := Real.sqrt (((H.disintegration U).componentWeight C.component).toReal * C.upper /
        (Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ))
  let Lc := L.mkContinuous c (descended_norm F ζ hζ U R P H K hK C)
  refine ⟨Lc, ?_, ?_⟩
  · apply LinearMap.mkContinuous_norm_le
    exact Real.sqrt_nonneg _
  · intro f
    refine ⟨descended F ζ hζ U R P H C f, rfl, ?_, ?_⟩
    · filter_upwards [descended_ball F ζ hζ U R P H C f] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (descended_zero F ζ hζ U R P H C f)

end DedekindZetaZeroFree.KPFixedHaarNormalBallMaps

end
