module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.CoordinateMeasurability

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming component → component
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming ends → ends
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming component_continuous → component_continuous
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming end_measurable → end_measurable
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming end_preimage → end_preimage
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport

namespace DedekindZetaZeroFree.KPMsNativeOffsetMass

 theorem pinned_cusp_lintegral
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaar.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaar.GeometricDisintegration A R P)
    (j : KPMsFixedHaar.CuspIndex A) (Z : ℝ)
    (hZ : KPMsFixedHaar.AdmissibleCutoff A Z)
    (φ : KPMsFixedHaar.Spherical F ζ hζ U → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in component A j.1 '' ends A j (KPMsFixedHaar.logHeight (F := F) Z),
      φ x ∂KPMsFixedHaar.sphericalMeasure F ζ hζ R P U) =
    (D.componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      ∫⁻ r : Set.Ioi Z, ∫⁻ p, φ (D.chart Z hZ (⟨j,p⟩,r))
        ∂(KPMsFixedHaar.Geometry A j).sectionMeasure
        ∂Measure.comap Subtype.val KPMsFixedHaar.radialMeasure := by
  let E := component A j.1 '' ends A j (KPMsFixedHaar.logHeight (F := F) Z)
  have hE : MeasurableSet E := end_measurable A j _
  have heq : ((KPMsFixedHaar.sphericalMeasure F ζ hζ R P U).restrict
      (Set.range (component A j.1))).restrict E =
      (KPMsFixedHaar.sphericalMeasure F ζ hζ R P U).restrict E := by
    rw [Measure.restrict_restrict hE,
      Set.inter_eq_left.mpr (Set.image_subset_range _ _)]
  change (∫⁻ x, φ x ∂(KPMsFixedHaar.sphericalMeasure F ζ hζ R P U).restrict E) = _
  rw [← heq, D.component_measure, Measure.restrict_smul,
    Measure.restrict_map (component_continuous A j.1).measurable hE,
    lintegral_smul_measure, lintegral_map hφ (component_continuous A j.1).measurable,
    end_preimage A j]
  rw [KPMsFixedHaar.RadialIntegrationSteps.pinned_end A R P D j Z hZ φ hφ]
  simp only [div_eq_mul_inv, mul_assoc, smul_eq_mul]

private theorem pinned_cusp_shell_mass
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaar.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaar.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaar.GeometricDisintegration A R P)
    (j : KPMsFixedHaar.CuspIndex A) (Z : ℝ)
    (hZ : KPMsFixedHaar.AdmissibleCutoff A Z) :
    KPMsFixedHaar.sphericalMeasure F ζ hζ R P U
      ((component A j.1 '' ends A j (KPMsFixedHaar.logHeight (F := F) Z)) ∩
        {x | Z < D.modulus x ∧ D.modulus x ≤ 2 * Z}) =
    (D.componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      (KPMsFixedHaar.Geometry A j).sectionMeasure Set.univ *
        (ENNReal.ofReal (2 * Z))⁻¹ := by
  let E := {x : KPMsFixedHaar.Spherical F ζ hζ U | Z < D.modulus x ∧ D.modulus x ≤ 2 * Z}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const D.measurable_modulus).inter
      (measurableSet_le D.measurable_modulus measurable_const)
  have hi := pinned_cusp_lintegral A R P D j Z hZ (E.indicator (fun _ => 1))
    (measurable_const.indicator hE)
  rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ,
    Measure.restrict_apply hE, Set.inter_comm, one_mul] at hi
  have he : ∀ (r : Set.Ioi Z) (p : KPCuspCharts.CrossQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2))),
      E.indicator (fun _ => (1 : ℝ≥0∞)) (D.chart Z hZ (⟨j,p⟩,r)) =
        (Set.Iic (2 * Z)).indicator (fun _ => (1 : ℝ≥0∞)) r.val := by
    intro r p
    have hr : Z < r.val := r.property
    simp only [E, Set.indicator_apply, Set.mem_ofPred_eq, D.chart_modulus, Set.mem_Iic,
      hr, true_and]
  simp_rw [he, lintegral_const, ← Set.indicator_mul_const, one_mul] at hi
  rw [lintegral_subtype_comap measurableSet_Ioi,
    lintegral_indicator measurableSet_Iic, lintegral_const,
    Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic] at hi
  have hI : Set.Iic (2 * Z) ∩ Set.Ioi Z = Set.Ioc Z (2 * Z) := by
    ext r
    simp [and_comm]
  rw [hI, KPMsFixedHaar.RadialIntegrationSteps.radial_shell Z hZ.1] at hi
  have hpos : 0 < 2 * Z := mul_pos (by norm_num) hZ.1
  simpa only [E, mul_assoc, ENNReal.ofReal_inv_of_pos hpos] using hi

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P) (V : KPMsActualAngularSource.Level F ζ hζ)

private theorem actual_cusp_shell_mass
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y) :
    R.quotientHaar (cuspShell F ζ hζ R P S V j Y) =
      ((nativeDisintegration F ζ hζ R P S V).componentWeight j.1 /
        ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      (KPMsFixedHaarDisintegration.Geometry (nativeAtlas F ζ hζ R P S V) j).sectionMeasure
        Set.univ * (ENNReal.ofReal (2 * Y / (cuspOffset F ζ hζ R P S V j).val))⁻¹ := by
  let A := nativeAtlas F ζ hζ R P S V
  let U := S.atlasLevel (cofinalLevel F ζ hζ V)
  let D := (KPMsActualNativeHaarFamily.rawFamily F ζ hζ R P).disintegration U
  let Z := Y / (cuspOffset F ζ hζ R P S V j).val
  let E := (component A j.1 '' ends A j (KPMsFixedHaar.logHeight (F := F) Z)) ∩
    {x | Z < D.modulus x ∧ D.modulus x ≤ 2 * Z}
  have hE : MeasurableSet E :=
    (end_measurable A j _).inter
      ((measurableSet_lt measurable_const D.measurable_modulus).inter
        (measurableSet_le D.measurable_modulus measurable_const))
  have heq : cuspShell F ζ hζ R P S V j Y = P.projection U ⁻¹' E := by
    simp only [cuspShell, KPMsActualCuspSource.cuspEnd, Set.preimage_inter,
      Set.preimage_ofPred_eq, E, Z, A, U, D, nativeDisintegration, nativeAtlas,
      nativeFamily, KPMsActualNativeHaarFamily.family]
    congr 1
    ext x
    rw [mul_div_assoc]
    rfl
  rw [heq, ← Measure.map_apply (P.continuous U).measurable hE]
  have hi := pinned_cusp_shell_mass A R (toRawTransport F ζ hζ P) D j Z (hY j)
  change KPMsFixedHaar.sphericalMeasure F ζ hζ R (toRawTransport F ζ hζ P) U E = _
  convert hi using 1
  rw [mul_div_assoc]
  rfl

 theorem forward_offset_factor (Y c : ℝ) (hY : 0 < Y) (hc : 0 < c) :
    ENNReal.ofReal (2 * Y) * (ENNReal.ofReal (2 * Y / c))⁻¹ = ENNReal.ofReal c := by
  have ht : 0 < 2 * Y := mul_pos (by norm_num) hY
  rw [ENNReal.ofReal_div_of_pos hc,
    ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
      (Or.inr (ENNReal.ofReal_pos.mpr ht).ne'), div_eq_mul_inv,
    ← mul_assoc, mul_comm (ENNReal.ofReal (2 * Y)),
    ENNReal.mul_inv_cancel_right (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top]

theorem fullShell_mass (Y : ℝ) (hY : OffsetAdmissible F ζ hζ R P S V Y) :
    fullShell F ζ hζ R P S V Y Set.univ = weightedBeta F ζ hζ R P S V Set.univ := by
  let A := nativeAtlas F ζ hζ R P S V
  let D := nativeDisintegration F ζ hζ R P S V
  let c : NativeCusp F ζ hζ R P S V → ℝ≥0∞ :=
    fun j => ENNReal.ofReal (cuspOffset F ζ hζ R P S V j).val
  have hweighted := congrArg (fun μ => μ Set.univ)
    (KPMsActualNativeWeightedShapeMeasure.cusp_section_shape_measure A D c)
  rw [Measure.map_apply (KPMsActualNativeWeightedShapeMeasure.angularProjection_measurable A)
    MeasurableSet.univ, Set.preimage_univ] at hweighted
  change _ = weightedBeta F ζ hζ R P S V Set.univ at hweighted
  rw [← hweighted, fullShell, KPMsActualNativeWeightedShapeMeasure.cuspWeightedSection]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply_of_aemeasurable
    (fullCoordinate_aemeasurable F ζ hζ R P S V j Y hY) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ,
    actual_cusp_shell_mass F ζ hζ R P S V j Y hY]
  have hm : Measurable (fun x => (⟨j,x⟩ : KPMsFixedHaarDisintegration.CrossSection A)) :=
    continuous_sigmaMk.measurable
  rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
  have hpos : 0 < Y := by
    have hz := (hY j).1
    exact (div_pos_iff.mp hz).resolve_right (fun h => (not_lt_of_gt
      (cuspOffset F ζ hζ R P S V j).property) h.2) |>.1
  have hf := forward_offset_factor Y (cuspOffset F ζ hζ R P S V j).val hpos
    (cuspOffset F ζ hζ R P S V j).property
  change ENNReal.ofReal (2 * Y) * ((_ / _) * _ * _) = (c j * (_ / _)) * _
  dsimp only [c, A, D]
  rw [← hf]
  ring

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
