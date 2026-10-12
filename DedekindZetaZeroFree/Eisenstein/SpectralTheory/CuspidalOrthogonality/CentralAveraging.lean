module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspidalOrthogonality.CommutatorFibers

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport
open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
local instance : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

theorem integral_central_average (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Integrable g (coveredMeasure F ζ hζ R U)) :
    (∫ v, (3 : ℂ)⁻¹ * ∑ ε : rootsOfUnity 3 F, g (z F ζ hζ U ε v)
      ∂coveredMeasure F ζ hζ R U) = ∫ v, g v ∂coveredMeasure F ζ hζ R U := by
  have hmp (ε : rootsOfUnity 3 F) :=
    KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε
  have hi (ε : rootsOfUnity 3 F) : Integrable (fun v => g (z F ζ hζ U ε v))
      (coveredMeasure F ζ hζ R U) :=
    (hmp ε).integrable_comp_of_integrable hg
  rw [integral_const_mul, integral_finset_sum _ (fun ε _ => hi ε)]
  have he (ε : rootsOfUnity 3 F) :
      (∫ v, g (z F ζ hζ U ε v) ∂coveredMeasure F ζ hζ R U) =
        ∫ v, g v ∂coveredMeasure F ζ hζ R U :=
    (hmp ε).integral_comp (z F ζ hζ U ε).measurableEmbedding g
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    KPContSectorFiniteOrbitIntegral.card_cubic_center F ζ hζ, nsmul_eq_mul]
  norm_num
  ring

def centralComplexAverage (g : CoveredSpherical F ζ hζ U → ℂ) :
    CoveredSpherical F ζ hζ U → ℂ :=
  fun v => (3 : ℂ)⁻¹ * ∑ ε : rootsOfUnity 3 F, g (z F ζ hζ U ε v)

 theorem centralComplexAverage_invariant (g : CoveredSpherical F ζ hζ U → ℂ)
    (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U) :
    centralComplexAverage F ζ hζ U g (z F ζ hζ U ε v) =
      centralComplexAverage F ζ hζ U g v := by
  unfold centralComplexAverage
  congr 1
  calc
    _ = ∑ δ : rootsOfUnity 3 F, g (z F ζ hζ U (δ * ε) v) := by
      apply Finset.sum_congr rfl
      intro δ _
      congr 1
      exact (mul_smul δ ε v).symm
    _ = _ := Equiv.sum_comp (Equiv.mulRight ε) (fun δ => g (z F ζ hζ U δ v))

 theorem centralComplexAverage_measurable (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Measurable g) : Measurable (centralComplexAverage F ζ hζ U g) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro ε _
  exact hg.comp (z F ζ hζ U ε).continuous.measurable

 theorem centralComplexAverage_integrable (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Integrable g (coveredMeasure F ζ hζ R U)) :
    Integrable (centralComplexAverage F ζ hζ U g) (coveredMeasure F ζ hζ R U) := by
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro ε _
  exact (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).integrable_comp_of_integrable hg

private theorem complex_measurable_iff_comp_q
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ) :
    Measurable a ↔ Measurable (a ∘ q F ζ hζ U) := by
  have hmap := Continuous.map_borel_eq
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U)
  change @Measurable _ _ (borel (KPFiniteCuspAtlas.rawXU F ζ hζ U)) _ a ↔
    @Measurable _ _ (borel (CoveredSpherical F ζ hζ U)) _ (a ∘ q F ζ hζ U)
  rw [measurable_iff_le_map, measurable_iff_le_map, ← hmap, MeasurableSpace.map_comp]

 theorem exists_complex_borel_descent (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Measurable g) :
    ∃ a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ,
      Measurable a ∧ ∀ v, a (q F ζ hζ U v) = centralComplexAverage F ζ hζ U g v := by
  have hm := centralComplexAverage_measurable F ζ hζ U g hg
  have hfiber : ∀ v w, q F ζ hζ U v = q F ζ hζ U w →
      centralComplexAverage F ζ hζ U g v = centralComplexAverage F ζ hζ U g w := by
    intro v w hvw
    obtain ⟨ε, rfl⟩ :=
      (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U v w).mp hvw
    exact (centralComplexAverage_invariant F ζ hζ U g ε v).symm
  obtain ⟨b, hb⟩ :=
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U).hasRightInverse
  refine ⟨fun x => centralComplexAverage F ζ hζ U g (b x), ?_, ?_⟩
  · rw [complex_measurable_iff_comp_q F ζ hζ U]
    have he : (fun x => centralComplexAverage F ζ hζ U g (b x)) ∘ q F ζ hζ U =
        centralComplexAverage F ζ hζ U g := by
      funext v
      exact hfiber _ _ (hb _)
    rw [he]
    exact hm
  · intro v
    exact hfiber _ _ (hb _)

 theorem integral_complex_borel_descent
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Integrable g (coveredMeasure F ζ hζ R U))
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ) (ha : Measurable a)
    (he : ∀ v, a (q F ζ hζ U v) = centralComplexAverage F ζ hζ U g v) :
    (∫ v, g v ∂coveredMeasure F ζ hζ R U) =
      ∫ b, a b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  rw [← map_q_coveredMeasure F ζ hζ R P U,
    integral_map (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable.aemeasurable ha.aestronglyMeasurable]
  simp_rw [he]
  exact (integral_central_average F ζ hζ R U g hg).symm

 theorem complex_borel_descent_integrable
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Integrable g (coveredMeasure F ζ hζ R U))
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ) (ha : Measurable a)
    (he : ∀ v, a (q F ζ hζ U v) = centralComplexAverage F ζ hζ U g v) :
    Integrable a (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) := by
  rw [← map_q_coveredMeasure F ζ hζ R P U]
  apply (integrable_map_measure ha.aestronglyMeasurable
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable.aemeasurable).mpr
  simp_rw [Function.comp_def, he]
  exact centralComplexAverage_integrable F ζ hζ R U g hg

 theorem complex_borel_descent_zero_off
    (g : CoveredSpherical F ζ hζ U → ℂ)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ)
    (he : ∀ v, a (q F ζ hζ U v) = centralComplexAverage F ζ hζ U g v)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : ∀ v, q F ζ hζ U v ∉ E → g v = 0) :
    ∀ b, b ∉ E → a b = 0 := by
  intro b hb
  obtain ⟨v,rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U b
  rw [he]
  unfold centralComplexAverage
  have hz (ε : rootsOfUnity 3 F) : g (z F ζ hζ U ε v) = 0 := by
    apply hE
    simpa only [q_z] using hb
  simp_rw [hz]
  simp
end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport
open KPMsFixedHaarDisintegration
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : SphericalTransport F ζ hζ)
variable (H : AllLevels F ζ hζ R P)
variable (U : Level F ζ hζ)
local notation "A" => H.atlas U
local notation "D" => H.disintegration U

def cuspKernel : Kernel (Omega A) (CrossSection A) where
  toFun := (H.disintegration U).unipotent
  measurable' := Measure.measurable_of_measurable_coe _ (H.disintegration U).measurable_kernel

instance : IsMarkovKernel (cuspKernel F ζ hζ R P H U) where
  isProbabilityMeasure ω := (H.disintegration U).probability_unipotent ω

def cuspRadial (Y : ℝ) : Measure (Set.Ioi Y) :=
  Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure

 theorem sigmaFinite_comap {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (f : X → Z) (hf : MeasurableEmbedding f) (ν : Measure Z) [SigmaFinite ν] :
    SigmaFinite (ν.comap f) := by
  apply Measure.sigmaFinite_of_countable (Set.countable_range (fun n : ℕ => f ⁻¹' spanningSets ν n))
  · rintro _ ⟨n, rfl⟩
    rw [hf.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top ν n)
  · simp only [Set.sUnion_range, ← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

instance (Y : ℝ) : SFinite (cuspRadial Y) := by
  unfold cuspRadial
  letI : SigmaFinite radialMeasure := by unfold radialMeasure; infer_instance
  letI := sigmaFinite_comap (Subtype.val : Set.Ioi Y → ℝ)
    (MeasurableEmbedding.subtype_coe isOpen_Ioi.measurableSet) radialMeasure
  infer_instance

def cuspJoint (Y : ℝ) : Measure (((Set.Ioi Y) × Omega A) × CrossSection A) :=
  ((H.disintegration U).beta Set.univ) • ((cuspRadial Y).prod (probability A (H.disintegration U).beta) ⊗ₘ
    (cuspKernel F ζ hζ R P H U).comap (fun p : Set.Ioi Y × Omega A => p.2) measurable_snd)

def cuspJointChart (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    ((Set.Ioi Y × Omega A) × CrossSection A) → Spherical F ζ hζ U :=
  fun p => (H.disintegration U).chart Y hY (p.2,p.1.1)

theorem cuspJointChart_measurable (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    Measurable (cuspJointChart F ζ hζ R P H U Y hY) := by
  exact ((H.disintegration U).measurable_chart Y hY).comp (measurable_snd.prodMk (measurable_fst.fst))

 theorem map_cuspJoint (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    Measure.map (cuspJointChart F ζ hζ R P H U Y hY)
      (cuspJoint F ζ hζ R P H U Y) =
      (sphericalMeasure F ζ hζ R P U).restrict (cuspEnds A Y) := by
  letI := (H.disintegration U).probability_mass
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (cuspJointChart_measurable F ζ hζ R P H U Y hY) hE]
  rw [← lintegral_indicator_one hE]
  change _ = ∫⁻ x in cuspEnds A Y, E.indicator (fun _ => 1) x ∂sphericalMeasure F ζ hζ R P U
  rw [(H.disintegration U).cusp_integral Y hY (E.indicator (fun _ => 1)) (measurable_const.indicator hE)]
  unfold cuspJoint
  rw [Measure.smul_apply, Measure.compProd_apply]
  rw [lintegral_prod]
  · congr 1
    apply lintegral_congr
    intro r
    apply lintegral_congr
    intro ω
    rw [Kernel.comap_apply]
    change (H.disintegration U).unipotent ω
      ((fun x : CrossSection A => (H.disintegration U).chart Y hY (x,r)) ⁻¹' E) = _
    have hxE : MeasurableSet ((fun x : CrossSection A => (H.disintegration U).chart Y hY (x,r)) ⁻¹' E) :=
      hE.preimage ((H.disintegration U).measurable_chart Y hY |>.comp (measurable_id.prodMk (measurable_const (a := r))))
    rw [← lintegral_indicator_one hxE]
    apply lintegral_congr
    intro x
    by_cases hx : (H.disintegration U).chart Y hY (x,r) ∈ E <;> simp [hx]
  · exact (Kernel.measurable_kernel_prodMk_left
      (hE.preimage (cuspJointChart_measurable F ζ hζ R P H U Y hY))).aemeasurable
  · exact hE.preimage (cuspJointChart_measurable F ζ hζ R P H U Y hY)

 theorem integral_cuspJoint (Y : ℝ)
    (f : ((Set.Ioi Y × Omega A) × CrossSection A) → ℂ)
    (hf : Integrable f (cuspJoint F ζ hζ R P H U Y)) :
    (∫ p, f p ∂cuspJoint F ζ hζ R P H U Y) =
      ((H.disintegration U).beta Set.univ).toReal *
        ∫ r, ∫ ω, ∫ x, f ((r,ω),x) ∂(H.disintegration U).unipotent ω
          ∂probability A (H.disintegration U).beta ∂cuspRadial Y := by
  letI := (H.disintegration U).probability_mass
  have hc0 := (H.disintegration U).positive_beta
  have hct : (H.disintegration U).beta Set.univ ≠ ⊤ := by
    letI := (H.disintegration U).finite_beta
    exact measure_ne_top _ _
  have hi : Integrable f ((cuspRadial Y).prod (probability A (H.disintegration U).beta) ⊗ₘ
      (cuspKernel F ζ hζ R P H U).comap (fun p : Set.Ioi Y × Omega A => p.2) measurable_snd) :=
    (integrable_smul_measure hc0 hct).mp hf
  unfold cuspJoint
  rw [integral_smul_measure, Measure.integral_compProd hi]
  simp_rw [Kernel.comap_apply]
  have hiter : Integrable (fun a : Set.Ioi Y × Omega A =>
      ∫ x, f (a,x) ∂(cuspKernel F ζ hζ R P H U) a.2)
      ((cuspRadial Y).prod (probability A (H.disintegration U).beta)) := by
    simpa [Kernel.prodMkLeft_apply, Kernel.comap_apply] using hi.integral_compProd
  rw [integral_prod _ hiter]
  rfl

 theorem integral_cusp_disintegration (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (g : Spherical F ζ hζ U → ℂ)
    (hg : Integrable g ((sphericalMeasure F ζ hζ R P U).restrict (cuspEnds A Y))) :
    (∫ b in cuspEnds A Y, g b ∂sphericalMeasure F ζ hζ R P U) =
      ((H.disintegration U).beta Set.univ).toReal *
        ∫ r : Set.Ioi Y, ∫ ω, ∫ x, g ((H.disintegration U).chart Y hY (x,r))
          ∂(H.disintegration U).unipotent ω ∂probability A (H.disintegration U).beta ∂cuspRadial Y := by
  have hp : MeasurePreserving (cuspJointChart F ζ hζ R P H U Y hY)
      (cuspJoint F ζ hζ R P H U Y)
      ((sphericalMeasure F ζ hζ R P U).restrict (cuspEnds A Y)) :=
    ⟨cuspJointChart_measurable F ζ hζ R P H U Y hY, map_cuspJoint F ζ hζ R P H U Y hY⟩
  have hi := hp.integrable_comp_of_integrable hg
  rw [← hp.map_eq]
  rw [integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hg.aestronglyMeasurable)]
  exact integral_cuspJoint F ζ hζ R P H U Y _ hi

 theorem integral_cusp_eq_zero_of_kernel (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (g : Spherical F ζ hζ U → ℂ)
    (hg : Integrable g ((sphericalMeasure F ζ hζ R P U).restrict (cuspEnds A Y)))
    (hzero : ∀ r : Set.Ioi Y, ∀ ω,
      (∫ x, g ((H.disintegration U).chart Y hY (x,r)) ∂(H.disintegration U).unipotent ω) = 0) :
    (∫ b in cuspEnds A Y, g b ∂sphericalMeasure F ζ hζ R P U) = 0 := by
  rw [integral_cusp_disintegration F ζ hζ R P H U Y hY g hg]
  simp_rw [hzero]
  simp
end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport
open KPMsFixedHaarDisintegration KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : SphericalTransport F ζ hζ) (H : AllLevels F ζ hζ R P) (U : Level F ζ hζ)
 theorem covered_integral_eq_zero_of_cusp_kernel (Y : ℝ)
    (hY : AdmissibleCutoff (H.atlas U) Y)
    (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Integrable g (coveredMeasure F ζ hζ R U))
    (hgm : Measurable g)
    (hsupp : ∀ v, q F ζ hζ U v ∉ cuspEnds (H.atlas U) Y → g v = 0)
    (hzero : ∀ a : Spherical F ζ hζ U → ℂ, Measurable a →
      (∀ v, a (q F ζ hζ U v) = centralComplexAverage F ζ hζ U g v) →
      ∀ r : Set.Ioi Y, ∀ ω,
        (∫ x, a ((H.disintegration U).chart Y hY (x,r)) ∂(H.disintegration U).unipotent ω) = 0) :
    (∫ v, g v ∂coveredMeasure F ζ hζ R U) = 0 := by
  obtain ⟨a,ha,he⟩ := exists_complex_borel_descent F ζ hζ U g hgm
  rw [integral_complex_borel_descent F ζ hζ R U P g hg a ha he]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (complex_borel_descent_zero_off F ζ hζ U g a he _ hsupp)]
  exact integral_cusp_eq_zero_of_kernel F ζ hζ R P H U Y hY a
    ((complex_borel_descent_integrable F ζ hζ R U P g hg a ha he).restrict) (hzero a ha he)
end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
open MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport
variable (F : Type) [Field F] [NumberField F]
variable (K L : AddSubgroup F) (hKL : K ≤ L)

def horizontalTorusMap : KPCuspCharts.Torus F K →+ KPCuspCharts.Torus F L :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id _) (by
    intro x hx
    obtain ⟨r,hr,he⟩ := AddSubgroup.mem_map.mp hx
    exact AddSubgroup.mem_map.mpr ⟨r,hKL hr,he⟩)

 theorem horizontalTorusMap_continuous : Continuous (horizontalTorusMap F K L hKL) := by
  apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk

 theorem horizontalTorusMap_surjective : Function.Surjective (horizontalTorusMap F K L hKL) := by
  apply QuotientAddGroup.map_surjective_of_surjective
  exact QuotientAddGroup.mk_surjective

 theorem horizontalTorusMap_probabilityHaar
    [BorelSpace (KPCuspCharts.Torus F K)] [BorelSpace (KPCuspCharts.Torus F L)]
    [LocallyCompactSpace (KPCuspCharts.Torus F L)]
    (μ : Measure (KPCuspCharts.Torus F K)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (ν : Measure (KPCuspCharts.Torus F L)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    Measure.map (horizontalTorusMap F K L hKL) μ = ν := by
  have hc := horizontalTorusMap_continuous F K L hKL
  letI : (Measure.map (horizontalTorusMap F K L hKL) μ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure μ _ hc
      (horizontalTorusMap_surjective F K L hKL)
  letI : IsProbabilityMeasure (Measure.map (horizontalTorusMap F K L hKL) μ) :=
    (Measure.isProbabilityMeasure_map_iff hc.measurable.aemeasurable).mpr inferInstance
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

 theorem horizontalTorus_integral_eq_zero
    [BorelSpace (KPCuspCharts.Torus F K)] [BorelSpace (KPCuspCharts.Torus F L)]
    [LocallyCompactSpace (KPCuspCharts.Torus F L)]
    (μ : Measure (KPCuspCharts.Torus F K)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (ν : Measure (KPCuspCharts.Torus F L)) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (g : KPCuspCharts.Torus F L → ℂ) (hg : Measurable g)
    (hzero : (∫ q, g (horizontalTorusMap F K L hKL q) ∂μ) = 0) :
    (∫ q, g q ∂ν) = 0 := by
  rw [← horizontalTorusMap_probabilityHaar F K L hKL μ ν,
    integral_map (horizontalTorusMap_continuous F K L hKL).measurable.aemeasurable hg.aestronglyMeasurable]
  exact hzero
end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge
open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContActualCutoffSmoothDescent
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "V" => level F ζ hζ C R P H U
local notation "A" => H.atlas V
local notation "D" => H.disintegration V
local notation "CS" => KPMsFixedHaarDisintegration.CrossSection A
local notation "X" => Covered F ζ hζ C R P H U
local instance : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

theorem scalar_continuous (u : SmoothSections F ζ hζ C R P H U) :
    Continuous (scalar F ζ hζ C R P H U u) := by
  exact (KPContSectorLineL2Isometry.continuous_iff F ζ hζ V R P H u.val).mp
    (fun i => (u.property i).continuous)

theorem scalar_central (u : SmoothSections F ζ hζ C R P H U) (ε : rootsOfUnity 3 F) (v : X) :
    scalar F ζ hζ C R P H U u (z F ζ hζ V ε v) =
      (chi F ζ hζ ε : ℂ) * scalar F ζ hζ C R P H U u v := by
  exact ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ V R P H).symm u).val.property ε v

theorem pairing_centralAverage (u h : SmoothSections F ζ hζ C R P H U) (v : X) :
    Transport.centralComplexAverage F ζ hζ V
      (fun x => star (scalar F ζ hζ C R P H U u x) * scalar F ζ hζ C R P H U h x) v =
        star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U h v := by
  unfold Transport.centralComplexAverage
  simp_rw [scalar_central]
  have hc (ε : rootsOfUnity 3 F) : star (chi F ζ hζ ε : ℂ) * (chi F ζ hζ ε : ℂ) = 1 := by
    rw [show star (chi F ζ hζ ε : ℂ) = (starRingEnd ℂ) (chi F ζ hζ ε : ℂ) from rfl,
      Complex.conj_mul', Circle.norm_coe]
    norm_num
  have he (ε : rootsOfUnity 3 F) :
      star ((chi F ζ hζ ε : ℂ) * scalar F ζ hζ C R P H U u v) *
        ((chi F ζ hζ ε : ℂ) * scalar F ζ hζ C R P H U h v) =
          star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U h v := by
    rw [star_mul]
    calc
      _ = (star (chi F ζ hζ ε : ℂ) * (chi F ζ hζ ε : ℂ)) *
        (star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U h v) := by ring
      _ = _ := by rw [hc,one_mul]
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,
    KPContSectorFiniteOrbitIntegral.card_cubic_center F ζ hζ,nsmul_eq_mul]
  norm_num
  ring

 theorem chart_pairing (u h : SmoothSections F ζ hζ C R P H U)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ V → ℂ)
    (ha : ∀ v : X, a (q F ζ hζ V v) =
      star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U h v)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (j : KPMsFixedHaarDisintegration.CuspIndex A) (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    a ((H.disintegration V).chart Y hY (⟨j,Quotient.mk _ p⟩,r)) =
      star (frameValue F ζ hζ C R P H U u j
        ((p.1,p.2 + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
          (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩),
            KPMsFixedHaarDisintegration.logHeight (F := F) r.val)) *
      frameValue F ζ hζ C R P H U h j
        ((p.1,p.2 + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
          (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩),
            KPMsFixedHaarDisintegration.logHeight (F := F) r.val) := by
  rw [(H.disintegration V).chart_formula]
  change a (KPContActualCollarBuffer.chartLift F ζ hζ V R P H j
    ((p.1,p.2 + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
      (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩),
        KPMsFixedHaarDisintegration.logHeight (F := F) r.val)) = _
  rw [← KPContActualCutoffSmoothDescent.coveredPoint_base F ζ hζ C R P H U j 1]
  rw [ha,scalar_coveredPoint,scalar_coveredPoint]
  simp

 theorem kernel_pairing_eq_zero
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ V R P H T)
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)
    (u : SmoothSections F ζ hζ C R P H U)
    (hu : IncomingFiberOrthogonality.AllCuspMeanZero F ζ hζ C R P H U u)
    (s : ℂ) (hs : s ∈ Ω)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ V → ℂ) (ha : Measurable a)
    (he : ∀ v : X, a (q F ζ hζ V v) =
      star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U (source.descent.commutator s) v)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (r : Set.Ioi Y) (ht : B.τ < KPMsFixedHaarDisintegration.logHeight (F := F) r.val)
    (ω : KPMsFixedHaarDisintegration.Omega A) :
    (∫ x, a ((H.disintegration V).chart Y hY (x,r)) ∂(H.disintegration V).unipotent ω) = 0 := by
  obtain ⟨j,b⟩ := ω
  obtain ⟨b,rfl⟩ := QuotientAddGroup.mk_surjective b
  obtain ⟨dn,hhaar,hprob,hmap⟩ := (H.disintegration V).fiber_formula j b
  let L := (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U j).L
  let K := KPCuspGenuineMonodromy.kernelLattice
    (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U j)
    (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U j)
    (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U j)
  let μ := KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U j
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U j).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U j
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U j
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U j
  let G := KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U j
  letI : MeasurableSpace (KPCuspCharts.CrossQuotient F
    (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U j)) := borel _
  letI : BorelSpace (KPCuspCharts.CrossQuotient F
    (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U j)) := ⟨rfl⟩
  obtain ⟨hdisc,_⟩ := G.lattice
  letI : DiscreteTopology (KPCuspCharts.translationLattice F L) := hdisc
  letI : IsClosed (KPCuspCharts.translationLattice F L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  letI : BorelSpace (KPCuspCharts.Torus F L) := QuotientAddGroup.borelSpace
  letI : CompactSpace (KPCuspCharts.Torus F L) := G.compact_torus
  letI := hhaar
  letI := hprob
  let π := Transport.horizontalTorusMap F K L
    (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U j).kernel_le
  have hπ : Measure.map π μ = dn :=
    Transport.horizontalTorusMap_probabilityHaar F K L _ μ dn
  have hf : Measurable (fun z : KPCuspCharts.Torus F L =>
      a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (z,b)⟩,r))) :=
    ha.comp ((H.disintegration V).measurable_chart Y hY |>.comp
      (((continuous_sigmaMk (i := j)).measurable.comp (G.atlas.continuous_lift.measurable.comp
        (measurable_id.prodMk measurable_const))).prodMk measurable_const))
  rw [hmap, integral_map]
  · rw [← hπ, integral_map (Transport.horizontalTorusMap_continuous F K L _).measurable.aemeasurable hf.aestronglyMeasurable]
    have hval (q : KPCuspCharts.Torus F K) :
      a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (π q,b)⟩,r)) =
        star (IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U j u
          (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
            (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)
          (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) q) *
        IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U j (source.descent.commutator s)
          (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
            (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)
          (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) q := by
      induction q using Quotient.inductionOn with | h x =>
        change a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (QuotientAddGroup.mk x,b)⟩,r)) = _
        rw [G.atlas.lift_formula]
        rw [chart_pairing F ζ hζ C R P H U u (source.descent.commutator s) a he]
        rw [IncomingFiberOrthogonality.frameFiber_mk,IncomingFiberOrthogonality.frameFiber_mk]
    change (∫ x, a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (π x,b)⟩,r)) ∂μ) = 0
    simp_rw [hval]
    have hz := IncomingFiberOrthogonality.commutator_fiber_pairing_eq_zero
      F ζ hζ C R P H U j ι B Ω f χ source s hs u hu
      (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
        (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)
      (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) ht
    simpa only [mul_comm] using hz
  · exact ((continuous_sigmaMk (i := j)).measurable.comp (G.atlas.continuous_lift.measurable.comp
      (measurable_id.prodMk measurable_const))).aemeasurable
  · exact (ha.comp ((H.disintegration V).measurable_chart Y hY |>.comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable

 theorem logHeight_exp (t : ℝ) (hd : 0 < KPCuspLogShape.dimension F) :
    KPMsFixedHaarDisintegration.logHeight (F := F)
      (Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)) = t := by
  unfold KPMsFixedHaarDisintegration.logHeight
  rw [Real.log_exp]
  field_simp

 theorem logHeight_gt (Y : ℝ) (hY : 0 < Y) (r : Set.Ioi Y)
    (hd : 0 < KPCuspLogShape.dimension F) :
    KPMsFixedHaarDisintegration.logHeight (F := F) Y <
      KPMsFixedHaarDisintegration.logHeight (F := F) r.val := by
  unfold KPMsFixedHaarDisintegration.logHeight
  apply div_lt_div_of_pos_right
  · exact Real.strictMonoOn_log hY (lt_trans hY r.property) r.property
  · positivity

 theorem source_proof
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ V R P H T)
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)
    (u : SmoothSections F ζ hζ C R P H U)
    (u_H : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hu_H : ((u_H.val : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V) : X → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F ζ hζ C R P H U] scalar F ζ hζ C R P H U u)
    (hu : IncomingFiberOrthogonality.AllCuspMeanZero F ζ hζ C R P H U u)
    (s : ℂ) (hs : s ∈ Ω) : inner ℂ u_H (source.h s) = 0 := by
  let m := KPContActualAllCuspSource.measure F ζ hζ C R P H U
  let v := source.descent.commutator s
  let g : X → ℂ := fun x => star (scalar F ζ hζ C R P H U u x) * scalar F ζ hζ C R P H U v x
  have hint : Integrable g m := by
    apply (L2.integrable_inner u_H.val (source.h s).val).congr
    filter_upwards [hu_H, source.source_ae s hs] with x hx hy
    simp only [hx,hy,RCLike.inner_apply]
    exact mul_comm _ _
  change inner ℂ u_H.val (source.h s).val = _
  rw [L2.inner_def]
  have hpair : (∫ x, inner ℂ (u_H.val x) ((source.h s).val x) ∂m) = ∫ x,g x ∂m := by
    apply integral_congr_ae
    filter_upwards [hu_H, source.source_ae s hs] with x hx hy
    simp only [hx,hy,RCLike.inner_apply]
    exact mul_comm _ _
  rw [hpair]
  have hgm : Measurable g := ((scalar_continuous F ζ hζ C R P H U u).star.measurable).mul
    (scalar_continuous F ζ hζ C R P H U v).measurable
  let Y := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * B.τ)
  have hd : 0 < KPCuspLogShape.dimension F := by
    exact KPCuspCharts.positive_dimension F H.totallyComplex
  have hy : KPMsFixedHaarDisintegration.logHeight (F := F) Y = B.τ := logHeight_exp F B.τ hd
  have hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y :=
    ⟨Real.exp_pos _, by rw [hy]; exact B.chart_threshold_le⟩
  apply Transport.covered_integral_eq_zero_of_cusp_kernel F ζ hζ R P H V Y hY g hint hgm
  · intro x hx
    have hx' : ∀ j, x ∉ ends F ζ hζ C R P H U B j := by
      intro j hj
      apply hx
      unfold KPMsFixedHaarDisintegration.cuspEnds
      rw [hy]
      exact Set.mem_iUnion.mpr ⟨j,hj⟩
    exact mul_eq_zero_of_right _ (source.descent.off_ends s hs x hx').2
  · intro a ha he r ω
    have he' : ∀ x : X, a (q F ζ hζ V x) = g x := by
      intro x
      rw [he, pairing_centralAverage]
    exact kernel_pairing_eq_zero F ζ hζ C R P H U ι B Ω f χ source u hu s hs a ha he' Y hY r
      (by rw [← hy]; exact logHeight_gt F Y hY.1 r hd) ω
end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)

theorem source_inner_eq_zero
    (u : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (u_H : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hu_H : ((u_H.val : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R
        (KPContActualAllCuspSource.level F ζ hζ C R P H U)) :
        KPContActualAllCuspSource.Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F ζ hζ C R P H U]
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U u)
    (hu : IncomingFiberOrthogonality.AllCuspMeanZero F ζ hζ C R P H U u)
    (s : ℂ) (hs : s ∈ Ω) : inner ℂ u_H (source.h s) = 0 := by
  exact Bridge.source_proof F ζ hζ C R P H U ι B Ω f χ source u u_H hu_H hu s hs

end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality

end
end
end
end
end
end
