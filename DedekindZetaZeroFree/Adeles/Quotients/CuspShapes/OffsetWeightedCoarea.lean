module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.SphericalCoordinateFormula

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.OffsetShapeCoarea

open KPMsActualAngularSource KPMsNativeOffsetMass

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming component → component
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming ends → ends
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming end_measurable → end_measurable
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass renaming pinned_cusp_lintegral → pinned_cusp_lintegral
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass renaming forward_offset_factor → forward_offset_factor
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport

section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming component → component
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming ends → ends
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadialIntegrationSteps renaming end_measurable → end_measurable
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass renaming pinned_cusp_lintegral → pinned_cusp_lintegral
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass renaming forward_offset_factor → forward_offset_factor
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming fromRawDisintegration → fromRawDisintegration
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming actualFrame_spec → actualFrame_spec
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain

 def offsetTranslation (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) :
    KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) :=
  fun ω => ⟨ω.1, ω.2 - QuotientAddGroup.mk
    (KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
      (nativeDisintegration F ζ hζ R P S V).radial.slot
      (cuspOffset F ζ hζ R P S V ω.1))⟩

private theorem offsetTranslation_measurable (S : NativeRecipe F ζ hζ R P)
    (V : Level F ζ hζ) : Measurable (offsetTranslation F ζ hζ R P S V) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro j
  change Continuous (fun x => (⟨j, x - QuotientAddGroup.mk
    (KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
      (nativeDisintegration F ζ hζ R P S V).radial.slot
      (cuspOffset F ζ hζ R P S V j))⟩ : KPMsFixedHaarDisintegration.Omega _))
  apply continuous_sigmaMk.comp
  exact continuous_id.sub (continuous_const (y := QuotientAddGroup.mk _))

private theorem offsetTranslation_section (S : NativeRecipe F ζ hζ R P)
    (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V)
    (φ : KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) → ℝ≥0∞)
    (hφ : Measurable φ) :
    (∫⁻ p, φ (offsetTranslation F ζ hζ R P S V
      (KPMsFixedHaarDisintegration.angularProjection (nativeAtlas F ζ hζ R P S V) ⟨j,p⟩))
      ∂(KPMsFixedHaarDisintegration.Geometry (nativeAtlas F ζ hζ R P S V) j).sectionMeasure) =
    ∫⁻ p, φ (KPMsFixedHaarDisintegration.angularProjection (nativeAtlas F ζ hζ R P S V)
      ⟨j,p⟩) ∂(KPMsFixedHaarDisintegration.Geometry (nativeAtlas F ζ hζ R P S V) j).sectionMeasure := by
  let A := nativeAtlas F ζ hζ R P S V
  let b := KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
    (nativeDisintegration F ζ hζ R P S V).radial.slot (cuspOffset F ζ hζ R P S V j)
  have hm : Measurable (fun p => φ (offsetTranslation F ζ hζ R P S V
      (KPMsFixedHaarDisintegration.angularProjection A ⟨j,p⟩))) :=
    (hφ.comp (offsetTranslation_measurable F ζ hζ R P S V)).comp
      ((KPMsActualNativeWeightedShapeMeasure.angularProjection_measurable A).comp
        continuous_sigmaMk.measurable)
  conv_lhs => rw [(KPMsFixedHaarDisintegration.Geometry A j).sectionMeasure_formula,
    lintegral_map hm measurable_quotient_mk'']
  have ht := KPMsFixedHaar.RadialIntegrationSteps.shape_shift_section_lintegral A j (-b)
    (fun p => φ (KPMsFixedHaarDisintegration.angularProjection A ⟨j,p⟩))
    (hφ.comp ((KPMsActualNativeWeightedShapeMeasure.angularProjection_measurable A).comp
      continuous_sigmaMk.measurable))
  simpa only [offsetTranslation, KPMsFixedHaarDisintegration.angularProjection,
    (KPMsFixedHaarDisintegration.Geometry A j).atlas.projection_formula,
    QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, QuotientAddGroup.mk_neg, sub_eq_add_neg, b] using ht

private theorem spherical_cusp_test (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ
      (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hs : Measurable s)
    (hsc : ∀ z r, s ((nativeDisintegration F ζ hζ R P S V).chart
      (Y / (cuspOffset F ζ hζ R P S V j).val) (hY j) (z,r)) =
      KPMsFixedHaarDisintegration.angularProjection (nativeAtlas F ζ hζ R P S V) z)
    (f : KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) → ℝ≥0∞)
    (hf : Measurable f) :
    ENNReal.ofReal (2 * Y) *
      (∫⁻ x in cuspShell F ζ hζ R P S V j Y,
        f (offsetTranslation F ζ hζ R P S V
          (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x))) ∂ R.quotientHaar) =
    (ENNReal.ofReal (cuspOffset F ζ hζ R P S V j).val *
      ((nativeDisintegration F ζ hζ R P S V).componentWeight j.1 /
        ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ)))) *
      ∫⁻ p, f (KPMsFixedHaarDisintegration.angularProjection (nativeAtlas F ζ hζ R P S V)
        ⟨j,p⟩) ∂(KPMsFixedHaarDisintegration.Geometry (nativeAtlas F ζ hζ R P S V) j).sectionMeasure := by
  let A := nativeAtlas F ζ hζ R P S V
  let U := S.atlasLevel (cofinalLevel F ζ hζ V)
  let D := (KPMsActualNativeHaarFamily.rawFamily F ζ hζ R P).disintegration U
  let Z := Y / (cuspOffset F ζ hζ R P S V j).val
  let E := {x : KPMsFixedHaar.Spherical F ζ hζ U | Z < D.modulus x ∧ D.modulus x ≤ 2 * Z}
  let B := component A j.1 '' ends A j (KPMsFixedHaar.logHeight (F := F) Z)
  let g := f ∘ offsetTranslation F ζ hζ R P S V ∘ s
  have hg : Measurable g := (hf.comp (offsetTranslation_measurable F ζ hζ R P S V)).comp hs
  have hE : MeasurableSet E := (measurableSet_lt measurable_const D.measurable_modulus).inter
    (measurableSet_le D.measurable_modulus measurable_const)
  have hB : MeasurableSet B := end_measurable A j _
  have heq : cuspShell F ζ hζ R P S V j Y = P.projection U ⁻¹' (B ∩ E) := by
    simp only [cuspShell, KPMsActualCuspSource.cuspEnd, Set.preimage_inter,
      Set.preimage_ofPred_eq, E, B, Z, A, U, D, nativeDisintegration, nativeAtlas,
      nativeFamily, KPMsActualNativeHaarFamily.family]
    congr 1
    ext x
    rw [mul_div_assoc]
    rfl
  have hi := pinned_cusp_lintegral A R (toRawTransport F ζ hζ P) D j Z (hY j)
    (E.indicator g) (hg.indicator hE)
  rw [lintegral_indicator hE, Measure.restrict_restrict hE, Set.inter_comm] at hi
  have hinner (r : Set.Ioi Z) :
      (∫⁻ p, E.indicator g (D.chart Z (hY j) (⟨j,p⟩,r))
        ∂(KPMsFixedHaar.Geometry A j).sectionMeasure) =
      (Set.Iic (2 * Z)).indicator (fun _ =>
        ∫⁻ p, f (KPMsFixedHaarDisintegration.angularProjection A ⟨j,p⟩)
          ∂(KPMsFixedHaarDisintegration.Geometry A j).sectionMeasure) r.val := by
    by_cases hr : r.val ≤ 2 * Z
    · simp only [Set.indicator_of_mem (show r.val ∈ Set.Iic (2 * Z) from hr)]
      have hmem : ∀ p, D.chart Z (hY j) (⟨j,p⟩,r) ∈ E := by
        intro p
        simpa only [E, Set.mem_ofPred_eq, D.chart_modulus, Set.mem_Ioi] using And.intro r.property hr
      simp_rw [Set.indicator_of_mem (hmem _)]
      change (∫⁻ p, f (offsetTranslation F ζ hζ R P S V
        (s ((nativeDisintegration F ζ hζ R P S V).chart Z (hY j) (⟨j,p⟩,r))))
        ∂(KPMsFixedHaarDisintegration.Geometry A j).sectionMeasure) = _
      have he (p) := hsc (⟨j,p⟩ : KPMsFixedHaarDisintegration.CrossSection A) r
      dsimp only [Z] at *
      simp_rw [he]
      exact offsetTranslation_section F ζ hζ R P S V j f hf
    · have hmem : ∀ p, D.chart Z (hY j) (⟨j,p⟩,r) ∉ E := by
        intro p
        simp only [E, Set.mem_setOf_eq, D.chart_modulus, not_and_or]
        exact Or.inr hr
      simp only [Set.indicator_of_notMem (show r.val ∉ Set.Iic (2 * Z) from hr)]
      simp_rw [Set.indicator_of_notMem (hmem _)]
      exact lintegral_zero
  simp_rw [hinner] at hi
  rw [lintegral_subtype_comap measurableSet_Ioi, lintegral_indicator measurableSet_Iic,
    lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic] at hi
  have hI : Set.Iic (2 * Z) ∩ Set.Ioi Z = Set.Ioc Z (2 * Z) := by ext r; simp [and_comm]
  rw [hI, KPMsFixedHaar.RadialIntegrationSteps.radial_shell Z (hY j).1] at hi
  have ht : 0 < 2 * Z := mul_pos (by norm_num) (hY j).1
  rw [ENNReal.ofReal_inv_of_pos ht] at hi
  have hpush : Measure.map (P.projection U) (R.quotientHaar.restrict (cuspShell F ζ hζ R P S V j Y)) =
      (KPMsFixedHaar.sphericalMeasure F ζ hζ R (toRawTransport F ζ hζ P) U).restrict (B ∩ E) := by
    rw [heq, ← Measure.restrict_map (P.continuous U).measurable (hB.inter hE)]
    rfl
  change ENNReal.ofReal (2 * Y) * (∫⁻ x, g (P.projection U x)
    ∂ R.quotientHaar.restrict (cuspShell F ζ hζ R P S V j Y)) = _
  rw [← lintegral_map hg (P.continuous U).measurable, hpush, hi]
  have hpos : 0 < Y := (div_pos_iff.mp (hY j).1).resolve_right
    (fun h => (not_lt_of_gt (cuspOffset F ζ hζ R P S V j).property) h.2) |>.1
  have hc := forward_offset_factor Y (cuspOffset F ζ hζ R P S V j).val hpos
    (cuspOffset F ζ hζ R P S V j).property
  rw [show 2 * Z = 2 * Y / (cuspOffset F ζ hζ R P S V j).val by dsimp [Z]; ring]
  rw [← hc]
  change ENNReal.ofReal (2 * Y) * ((_ / _) * (_ * _)) = (_ * _) * _
  dsimp only [D, A, U, nativeDisintegration, nativeFamily, KPMsActualNativeHaarFamily.family, fromRawDisintegration]
  ring

end

theorem native_shape_measure
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (S : NativeRecipe F ζ hζ R P)
    (shape : ∀ V : Level F ζ hζ,
      Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hshape : ∀ V, Measurable (shape V))
    (hframe : ∀ (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V) (Y : ℝ),
      OffsetAdmissible F ζ hζ R P S V Y →
      ∀ (x : KPSmoothLocalQuotientCharts.X F ζ hζ),
        x ∈ cuspShell F ζ hζ R P S V j Y →
      ∀ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
        (t : ℝ) (ε : rootsOfUnity 3 F)
        (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
        actualFrame F ζ hζ R P S V j Y x =
          KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
              KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val →
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t)) →
        shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
          (fullCoordinate F ζ hζ R P S V j Y x)) =
          (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
            (nativeFamily F ζ hζ R P).totallyComplex
            (nativeDisintegration F ζ hζ R P S V).radial.slot
            ⟨(cuspOffset F ζ hζ R P S V j).val *
                Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
              mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩)⟩ :
            KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)))
    (V : Level F ζ hζ) (Y : ℝ) (hY : OffsetAdmissible F ζ hζ R P S V Y) :
    Measure.map (shape V ∘ fullToLevel F ζ hζ (nativeDatum F ζ hζ)
      (cofinalLevel F ζ hζ V)) (fullShell F ζ hζ R P S V Y) =
      weightedBeta F ζ hζ R P S V := by
  let A := nativeAtlas F ζ hζ R P S V
  let D := nativeDisintegration F ζ hζ R P S V
  let c : NativeCusp F ζ hζ R P S V → ℝ≥0∞ :=
    fun j => ENNReal.ofReal (cuspOffset F ζ hζ R P S V j).val
  let q := shape V ∘ fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
  have hq : Measurable q := (hshape V).comp
    (KPMsActualAngularShellSource.fullToLevel_measurable (nativeDatum F ζ hζ) _)
  have hw := KPMsActualNativeWeightedShapeMeasure.cusp_section_shape_measure A D c
  change Measure.map q (fullShell F ζ hζ R P S V Y) = D.beta.withDensity (fun ω => c ω.1)
  rw [← hw]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hq,
    lintegral_map hf (KPMsActualNativeWeightedShapeMeasure.angularProjection_measurable A)]
  simp only [fullShell, KPMsActualNativeWeightedShapeMeasure.cuspWeightedSection,
    lintegral_finsetSum_measure, lintegral_smul_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_map' (f := fun a => f (q a)) (hf.comp hq).aemeasurable
      (fullCoordinate_aemeasurable F ζ hζ R P S V j Y hY),
    lintegral_map (f := fun a => f (KPMsFixedHaarDisintegration.angularProjection A a))
      (hf.comp (KPMsActualNativeWeightedShapeMeasure.angularProjection_measurable A))
      (continuous_sigmaMk.measurable)]
  obtain ⟨s,hs,hsc,_⟩ := KPMsActualNativeWeightedShapeMeasure.spherical_shell_shape_measure A D
    (Y / (cuspOffset F ζ hζ R P S V j).val) (hY j)
  have hpoint : ∀ x ∈ cuspShell F ζ hζ R P S V j Y,
      q (fullCoordinate F ζ hζ R P S V j Y x) =
      offsetTranslation F ζ hζ R P S V
        (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x)) := by
    intro x hx
    obtain ⟨b,hb,hpin⟩ := OffsetShapeFramePin.shaped_fullCoordinate_on_cuspShell
      F ζ hζ R P S shape hshape hframe V j Y hY s hsc x hx
    change shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
      (fullCoordinate F ζ hζ R P S V j Y x)) = _
    rw [hb]
    exact hpin
  have hae : (fun x => f (q (fullCoordinate F ζ hζ R P S V j Y x))) =ᵐ[
      R.quotientHaar.restrict (cuspShell F ζ hζ R P S V j Y)]
      fun x => f (offsetTranslation F ζ hζ R P S V
        (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x))) := by
    exact ae_restrict_of_forall_mem
      (KPMsNativeOffsetMass.FullSupportGeometry.cuspShell_measurable S V j Y hY)
      (fun x hx => congrArg f (hpoint x hx))
  rw [lintegral_congr_ae hae]
  exact spherical_cusp_test F ζ hζ R P S V j Y hY s hs hsc f hf

end DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.OffsetShapeCoarea

end
