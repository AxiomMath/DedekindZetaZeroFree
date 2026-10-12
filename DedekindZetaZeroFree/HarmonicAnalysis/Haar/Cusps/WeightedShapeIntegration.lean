module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Cusps.LevelCompatibleAngularMeasures
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineNormDisintegration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming angular_measurable → angular_measurable
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming kernel_angular_lintegral → kernel_angular_lintegral
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming angular_marginal_of_disintegration → angular_marginal_of_disintegration
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming cross_section_inclusion_measurable → cross_section_inclusion_measurable
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming weighted_section_measure → weighted_section_measure

namespace DedekindZetaZeroFree.KPMsActualNativeWeightedShapeMeasure

open KPMsFixedHaarDisintegration
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : SphericalTransport F ζ hζ}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

theorem angularProjection_measurable : Measurable (angularProjection A) :=
  angular_measurable A

def actualKernel (D : Disintegration A R P) : KPMsFixedHaar.FiberKernel A where
  unipotent := D.unipotent
  probability_unipotent := D.probability_unipotent
  fiber_support := D.fiber_support
  measurable_kernel := D.measurable_kernel
  fiber_formula := D.fiber_formula

theorem kernel_angular (D : Disintegration A R P) (ω : Omega A)
    (f : Omega A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (angularProjection A x) ∂D.unipotent ω) = f ω :=
  kernel_angular_lintegral A (actualKernel A D) ω f hf

abbrev sectionMeasure (D : Disintegration A R P) : Measure (CrossSection A) :=
  KPMsFixedHaar.WeightedSectionGlobalization.weightedSectionMeasure A D.componentWeight

theorem section_shape_measure (D : Disintegration A R P) :
    Measure.map (angularProjection A) (sectionMeasure A D) = D.beta :=
  angular_marginal_of_disintegration A (actualKernel A D) D.componentWeight D.beta
    D.section_disintegration

theorem offset_section_shape_measure (D : Disintegration A R P)
    (density : Omega A → ℝ≥0∞) (hdensity : Measurable density) :
    Measure.map (angularProjection A)
      ((sectionMeasure A D).withDensity (density ∘ angularProjection A)) =
        D.beta.withDensity density := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (angularProjection_measurable A)]
  change (∫⁻ x, (f ∘ angularProjection A) x
    ∂(sectionMeasure A D).withDensity (density ∘ angularProjection A)) = _
  rw [lintegral_withDensity_eq_lintegral_mul (sectionMeasure A D)
      (hdensity.comp (angularProjection_measurable A)) (hf.comp (angularProjection_measurable A)),
    lintegral_withDensity_eq_lintegral_mul D.beta hdensity hf]
  have hmap := congrArg (fun μ : Measure (Omega A) => ∫⁻ ω, density ω * f ω ∂μ)
    (section_shape_measure A D)
  change (∫⁻ ω, (density * f) ω ∂Measure.map (angularProjection A) (sectionMeasure A D)) = _ at hmap
  rw [lintegral_map (hdensity.mul hf) (angularProjection_measurable A)] at hmap
  exact hmap

theorem spherical_shell_shape_measure (D : Disintegration A R P) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) :
    ∃ s : KPMsFixedHaarDisintegration.Spherical F ζ hζ U →
        KPMsFixedHaarDisintegration.Omega A,
      Measurable s ∧
      (∀ x r, s (D.chart Y hY (x,r)) =
        KPMsFixedHaarDisintegration.angularProjection _ x) ∧
      Measure.map s (ENNReal.ofReal (2 * Y) •
        (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
          (KPMsFixedHaarDisintegration.cuspEnds A Y ∩
            {v | Y < D.modulus v ∧
              D.modulus v ≤ 2 * Y})) =
        D.beta := by
  let DD := D
  let AA := A
  let E := {v | Y < DD.modulus v ∧ DD.modulus v ≤ 2 * Y}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const DD.measurable_modulus).inter
      (measurableSet_le DD.measurable_modulus measurable_const)
  have he : MeasurableSet (KPMsFixedHaarDisintegration.cuspEnds AA Y) := by
    apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro j
    have hm : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U
        (AA.representative j.1)) := by
      have heq : KPFiniteCuspAtlas.componentMap F ζ hζ U
          (AA.representative j.1) = AA.components ∘ Sigma.mk j.1 := by
        funext x
        exact (AA.components_formula j.1 x).symm
      rw [heq]
      exact AA.components.isOpenMap.comp isOpenMap_sigmaMk
    exact hm _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ _)
  letI : Nonempty (KPMsFixedHaarDisintegration.CrossSection AA) := by
    let i : Fin AA.componentCount := ⟨0, AA.positive_componentCount⟩
    let j : KPMsFixedHaarDisintegration.CuspIndex AA :=
      ⟨i, ⟨0, (AA.cuspAtlas i).positive_cuspCount⟩⟩
    exact ⟨⟨j, Quotient.mk _ (0 : KPCuspCharts.Cross F)⟩⟩
  letI : Nonempty (Set.Ioi Y) := ⟨⟨Y + 1, by simp⟩⟩
  let emb := (DD.chart_embedding Y hY).measurableEmbedding (DD.chart_range Y hY ▸ he)
  let s := KPMsFixedHaarDisintegration.angularProjection AA ∘ Prod.fst ∘ emb.invFun
  have hs : Measurable s := (angularProjection_measurable A).comp
    (measurable_fst.comp emb.measurable_invFun)
  have hsc : ∀ x r, s (DD.chart Y hY (x,r)) =
      KPMsFixedHaarDisintegration.angularProjection AA x := by
    intro x r
    simp only [s, Function.comp_apply, emb.leftInverse_invFun (x,r)]
  refine ⟨s, hs, hsc, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hs, lintegral_smul_measure]
  have hi := DD.cusp_integral Y hY (E.indicator (f ∘ s)) ((hf.comp hs).indicator hE)
  have heq : ∀ r : Set.Ioi Y, ∀ x : KPMsFixedHaarDisintegration.CrossSection AA,
      E.indicator (f ∘ s) (DD.chart Y hY (x,r)) =
        (Set.Iic (2 * Y)).indicator (fun _ =>
          f (KPMsFixedHaarDisintegration.angularProjection AA x)) r.val := by
    intro r x
    simp only [E, Set.indicator_apply, Set.mem_ofPred_eq, DD.chart_modulus,
      Function.comp_apply, hsc, Set.mem_Iic]
    have hr : Y < r.val := r.property
    simp only [hr, true_and]
  have hk : ∀ r : Set.Ioi Y, ∀ ω : KPMsFixedHaarDisintegration.Omega AA,
      (∫⁻ x, (Set.Iic (2 * Y)).indicator (fun _ =>
          f (KPMsFixedHaarDisintegration.angularProjection AA x)) r.val ∂DD.unipotent ω) =
        (Set.Iic (2 * Y)).indicator (fun _ => f ω) r.val := by
    intro r ω
    by_cases hr : r.val ∈ Set.Iic (2 * Y)
    · simp only [Set.indicator_of_mem hr]
      exact kernel_angular A D ω f hf
    · simp only [Set.indicator_of_notMem hr, lintegral_zero]
  have ho : ∀ r : Set.Ioi Y,
      (∫⁻ ω, (Set.Iic (2 * Y)).indicator (fun _ => f ω) r.val
        ∂KPMsFixedHaarDisintegration.probability AA DD.beta) =
        (Set.Iic (2 * Y)).indicator
          (fun _ => ∫⁻ ω, f ω ∂KPMsFixedHaarDisintegration.probability AA DD.beta) r.val := by
    intro r
    by_cases hr : r.val ∈ Set.Iic (2 * Y)
    · simp only [Set.indicator_of_mem hr]
    · simp only [Set.indicator_of_notMem hr, lintegral_zero]
  rw [lintegral_indicator hE, Measure.restrict_restrict hE] at hi
  simp_rw [heq] at hi
  simp_rw [hk] at hi
  have ho' : (fun r : Set.Ioi Y => ∫⁻ ω, (Set.Iic (2 * Y)).indicator
      (fun _ => f ω) r.val ∂KPMsFixedHaarDisintegration.probability AA DD.beta) =
      (fun r : Set.Ioi Y => (Set.Iic (2 * Y)).indicator
        (fun _ => ∫⁻ ω, f ω ∂KPMsFixedHaarDisintegration.probability AA DD.beta) r.val) :=
    funext ho
  dsimp only [AA] at ho'
  rw [ho'] at hi
  rw [lintegral_subtype_comap measurableSet_Ioi, lintegral_indicator measurableSet_Iic,
    lintegral_const, Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_apply_univ] at hi
  have hI : Set.Iic (2 * Y) ∩ Set.Ioi Y = Set.Ioc Y (2 * Y) := by
    ext r; simp [and_comm]
  rw [hI] at hi
  have hrad : KPMsFixedHaarDisintegration.radialMeasure (Set.Ioc Y (2 * Y)) =
      ENNReal.ofReal (2 * Y)⁻¹ :=
    KPMsFixedHaar.RadialIntegrationSteps.radial_shell Y hY.1
  have hrestrict :
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (KPMsFixedHaarDisintegration.cuspEnds AA Y ∩ E) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (E ∩ KPMsFixedHaarDisintegration.cuspEnds AA Y) := by
    rw [Set.inter_comm]
  rw [hrestrict]
  change ENNReal.ofReal (2 * Y) •
    (∫⁻ a in E ∩ KPMsFixedHaarDisintegration.cuspEnds A Y,
      (f ∘ s) a ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) = _
  rw [hi, hrad]
  letI := DD.finite_beta
  rw [KPMsFixedHaarDisintegration.probability, lintegral_smul_measure]
  have hc : ENNReal.ofReal (2 * Y) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by linarith [hY.1])
  have hb : DD.beta Set.univ ≠ 0 := DD.positive_beta
  have hbt : DD.beta Set.univ ≠ ⊤ := measure_ne_top DD.beta Set.univ
  simp only [smul_eq_mul]
  rw [ENNReal.ofReal_inv_of_pos (show 0 < 2 * Y by linarith [hY.1])]
  calc
    _ = (ENNReal.ofReal (2 * Y) * (ENNReal.ofReal (2 * Y))⁻¹) *
        (DD.beta Set.univ * (DD.beta Set.univ)⁻¹) * ∫⁻ ω, f ω ∂DD.beta := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hc ENNReal.ofReal_ne_top,
      ENNReal.mul_inv_cancel hb hbt]; simp; rfl

theorem cuspDensity_measurable (c : CuspIndex A → ℝ≥0∞) :
    Measurable (fun ω : Omega A => c ω.1) := by
  have hc : Continuous (fun ω : Omega A => c ω.1) := by
    exact continuous_sigma (σ := fun j : CuspIndex A =>
      KPCuspCharts.Base F hF (Parabolic A j).E (Parabolic A j).integralUnits)
      (fun j => (continuous_const (X := KPCuspCharts.Base F hF
        (Parabolic A j).E (Parabolic A j).integralUnits) (y := c j)))
  exact hc.measurable

def cuspWeightedSection (D : Disintegration A R P) (c : CuspIndex A → ℝ≥0∞) :
    Measure (CrossSection A) :=
  ∑ j : CuspIndex A,
    (c j * (D.componentWeight j.1 /
      ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ)))) •
      Measure.map (fun x => (⟨j,x⟩ : CrossSection A)) (Geometry A j).sectionMeasure

theorem cuspWeightedSection_eq_withDensity (D : Disintegration A R P)
    (c : CuspIndex A → ℝ≥0∞) :
    cuspWeightedSection A D c = (sectionMeasure A D).withDensity
      (fun x => c (angularProjection A x).1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hc : Measurable (fun x : CrossSection A => c (angularProjection A x).1) :=
    (cuspDensity_measurable A c).comp (angularProjection_measurable A)
  rw [lintegral_withDensity_eq_lintegral_mul (sectionMeasure A D) hc hf]
  simp only [cuspWeightedSection, sectionMeasure,
    KPMsFixedHaar.WeightedSectionGlobalization.weightedSectionMeasure,
    weighted_section_measure, lintegral_finsetSum_measure, lintegral_smul_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_map hf (cross_section_inclusion_measurable A j),
    lintegral_map (hc.mul hf) (cross_section_inclusion_measurable A j)]
  change (c j * (D.componentWeight j.1 / ENNReal.ofReal
    (2 * (KPCuspLogShape.dimension F : ℝ)))) * (∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
    (D.componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      (∫⁻ x, c j * f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure)
  have hfj := hf.comp (cross_section_inclusion_measurable A j)
  change Measurable (fun x => f (⟨j,x⟩ : CrossSection A)) at hfj
  rw [lintegral_const_mul (c j) hfj]
  ring

theorem cusp_section_shape_measure (D : Disintegration A R P)
    (c : CuspIndex A → ℝ≥0∞) :
    Measure.map (angularProjection A) (cuspWeightedSection A D c) =
      D.beta.withDensity (fun ω => c ω.1) := by
  rw [cuspWeightedSection_eq_withDensity A D c]
  exact offset_section_shape_measure A D (fun ω => c ω.1) (cuspDensity_measurable A c)

def sphericalShell (D : Disintegration A R P) (Y : ℝ) : Set (Spherical F ζ hζ U) :=
  cuspEnds A Y ∩ {v | Y < D.modulus v ∧ D.modulus v ≤ 2 * Y}

theorem sphericalShell_measurable (D : Disintegration A R P) (Y : ℝ) :
    MeasurableSet (sphericalShell A D Y) := by
  apply MeasurableSet.inter
  · apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro j
    have hm : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)) := by
      have heq : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) =
          A.components ∘ Sigma.mk j.1 := by
        funext x
        exact (A.components_formula j.1 x).symm
      rw [heq]
      exact A.components.isOpenMap.comp isOpenMap_sigmaMk
    exact hm _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ _)
  · exact (measurableSet_lt measurable_const D.measurable_modulus).inter
      (measurableSet_le D.measurable_modulus measurable_const)

end DedekindZetaZeroFree.KPMsActualNativeWeightedShapeMeasure

end
