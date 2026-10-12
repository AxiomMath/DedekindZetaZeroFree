module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.AngularTestMeasurability
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.StationaryAngularSlices

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass.ShellTestCoarea
open KPMsActualAngularSource KPMsActualAngularDescentSource
open KPCompactStabilizerHaarSources KPActualComponentHaarSources
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming actual_finiteOrbit_positive_finite → actual_finiteOrbit_positive_finite

private theorem point_continuous
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (j : NativeCusp F ζ hζ R P S V) :
    Continuous (fun w : KPCuspCharts.Coordinates F ×
      (K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) =>
      ShellTestFrames.point S V e j w.1.1 w.1.2 w.2) := by
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  exact ((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
    (e.symm.continuous.comp
      (((KPCuspSiegel.continuous_action F _).comp
        ((KPCuspCharts.toArchHomeomorph F
          (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)).continuous.comp
            continuous_fst)).prodMk continuous_snd.fst))).mul
    (continuous_subtype_val.comp continuous_snd.snd)

private theorem end_on_point
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (ht : KPMsFixedHaarDisintegration.logHeight (F := F)
      (Y / (cuspOffset F ζ hζ R P S V j).val) < t)
    (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hz : z.2 ∈ B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
      (S.atlasLevel (cofinalLevel F ζ hζ V)) (nativeAtlas F ζ hζ R P S V) j.1) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (ShellTestFrames.point S V e j p t z) ∈
      KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
        (S.atlasLevel (cofinalLevel F ζ hζ V)) j
        (Y / (cuspOffset F ζ hζ R P S V j).val) := by
  apply FullSupportGeometry.quotientMap_mem_cuspEnd_of_mem_fullCuspDomain S V j _
  obtain ⟨ε,u,hu⟩ := ShellTestFrames.finite_frame S V j z.2 hz
  refine ⟨e.symm
    ((((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) •
      KPCuspCharts.toArch F (p,t),z.1),p,t,ε,u,ht,?_,?_⟩
  · rw [← heBase,e.apply_symm_apply]
    rfl
  · change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ _ * z.2.val = _
    rw [hu]
    group

theorem cusp_test_coefficient
    (j : NativeCusp F ζ hζ R P S V)
    (φ : FullOmega F ζ hζ (nativeDatum F ζ hζ) → ℝ≥0∞) (hφ : Measurable φ) :
    ∃ a : ℝ≥0∞, ∀ Y : ℝ, OffsetAdmissible F ζ hζ R P S V Y →
      ENNReal.ofReal (2 * Y) *
        (∫⁻ x in cuspShell F ζ hζ R P S V j Y,
          φ (fullCoordinate F ζ hζ R P S V j Y x) ∂ R.quotientHaar) = a := by
  obtain ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,hcoarea⟩ :=
    KPMsNativeWeightedShapeSource.NativeCoarea.actual_full_cusp_coarea S V j
  letI := hν
  letI := hνsf
  let Q := (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).geometry j.2)
  letI := Q.haar_shapeMeasure
  let bb := B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
    (S.atlasLevel (cofinalLevel F ζ hζ V)) (nativeAtlas F ζ hζ R P S V) j.1
  have hbb : MeasurableSet bb := (actual_finiteOrbit_positive_finite F ζ hζ
    (S.atlasLevel (cofinalLevel F ζ hζ V)) ((nativeAtlas F ζ hζ R P S V).representative j.1) ν).1
  let μ := (stabilizerHaar (KPCuspLogShape.dimension F)).prod (ν.restrict bb)
  let ρ := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  letI : SFinite ρ := by dsimp [ρ,KPCuspCharts.radialMeasure]; infer_instance
  let μp := (volume.prod Q.shapeMeasure).restrict Q.fundamentalDomain
  letI : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let := ActualQuotient.actual_cover_secondCountable F ζ hζ
  obtain ⟨ep,hep⟩ := actual_product_splitting F ζ hζ
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  let f := fun (p : KPCuspCharts.Coordinates F)
      (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) =>
    φ (framedFullAngular F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ R P S V).radial
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))
      (ShellTestFrames.point S V e j p.1 p.2 z))
  have hf : Measurable (Function.uncurry f) := hφ.comp
    ((framedFullAngular_continuous F ζ hζ (nativeDatum F ζ hζ) _ _).comp
      (point_continuous S V e j)).measurable
  let avg := fun p : KPCuspCharts.Coordinates F => ∫⁻ z, f p z ∂ μ
  have havg : Measurable avg := hf.lintegral_prod_right'
  let t₀ := -Real.log (cuspOffset F ζ hζ R P S V j).val /
    (2 * (KPCuspLogShape.dimension F : ℝ))
  let a := ∫⁻ p, avg (p,t₀) ∂ μp
  have hstat (t : ℝ) : (∫⁻ p, avg (p,t) ∂ μp) = a :=
    (FullTestProof.full_angular_slices_stationary (R := R) (P := P) S V
      e heBase heFiber ν j φ hφ t).trans
      (FullTestProof.full_angular_slices_stationary (R := R) (P := P) S V
        e heBase heFiber ν j φ hφ t₀).symm
  refine ⟨(c : ℝ≥0∞) * ENNReal.ofReal
    ((cuspOffset F ζ hζ R P S V j).val / (2 * (KPCuspLogShape.dimension F : ℝ))) * a, ?_⟩
  intro Y hY
  let Z := Y / (cuspOffset F ζ hζ R P S V j).val
  let E := KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
    (S.atlasLevel (cofinalLevel F ζ hζ V)) j Z
  let W := {x : KPSmoothLocalQuotientCharts.X F ζ hζ |
    Z < (nativeDisintegration F ζ hζ R P S V).modulus
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) ∧
    (nativeDisintegration F ζ hζ R P S V).modulus
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) ≤ 2 * Z}
  have hW : MeasurableSet W :=
    (measurableSet_lt measurable_const ((nativeDisintegration F ζ hζ R P S V).measurable_modulus.comp
      (P.continuous _).measurable)).inter
    (measurableSet_le ((nativeDisintegration F ζ hζ R P S V).measurable_modulus.comp
      (P.continuous _).measurable) measurable_const)
  let T := W.indicator (E.indicator (fun x => φ (fullCoordinate F ζ hζ R P S V j Y x)))
  have hT : Measurable T := (ShellTestFrames.end_test_measurable S V j Y hY φ hφ).indicator hW
  have hi := hcoarea Z (hY j) T hT
  have hleft : (∫⁻ x in E, T x ∂ R.quotientHaar) =
      ∫⁻ x in cuspShell F ζ hζ R P S V j Y,
        φ (fullCoordinate F ζ hζ R P S V j Y x) ∂ R.quotientHaar := by
    dsimp only [T]
    rw [lintegral_indicator hW,Measure.restrict_restrict hW]
    have he : W ∩ E = cuspShell F ζ hζ R P S V j Y := by
      ext x
      simp only [W,E,cuspShell,Z,Set.mem_inter_iff,Set.mem_ofPred_eq]
      rw [mul_div_assoc]
      tauto
    rw [he]
    apply setLIntegral_congr_fun (FullSupportGeometry.cuspShell_measurable S V j Y hY)
    intro x hx
    exact Set.indicator_of_mem hx.1 _
  rw [hleft] at hi
  let g := fun (p : KPCuspCharts.Coordinates F)
      (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) =>
    T (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (ShellTestFrames.point S V e j p.1 p.2 z))
  have hg : Measurable (Function.uncurry g) := hT.comp
    (continuous_quotient_mk'.comp (point_continuous S V e j)).measurable
  have hinner (p : KPCuspCharts.Cross F) (t : ℝ)
      (ht : KPMsFixedHaarDisintegration.logHeight (F := F) Z < t) :
      (∫⁻ z, g (p,t) z ∂ μ) =
        if (cuspOffset F ζ hζ R P S V j).val *
          Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) ≤ 2 * Y
        then avg (p,t) else 0 := by
    have hmem : ∀ᵐ z ∂ μ, z.2 ∈ bb :=
      (Measure.ae_prod_iff_ae_ae (measurable_snd hbb)).mpr
        (Filter.Eventually.of_forall fun _ => ae_restrict_mem hbb)
    have heq : ∀ᵐ z ∂ μ, g (p,t) z =
        if (cuspOffset F ζ hζ R P S V j).val *
          Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) ≤ 2 * Y
        then f (p,t) z else 0 := by
      filter_upwards [hmem] with z hz
      have hx := end_on_point S V e heBase j Y p t ht z hz
      have hm := ShellTestFrames.modulus_on_point S V e heBase j Y hY p t ht z hz
      have hq := ShellTestFrames.coordinate_on_point S V e heBase j Y hY p t ht z hz
      have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) := by
        have := KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex
        positivity
      have hr : Z < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
        apply (Real.log_lt_iff_lt_exp (hY j).1).mp
        simpa only [mul_comm] using (div_lt_iff₀ hd).mp ht
      have hu : Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) ≤ 2 * Z ↔
          (cuspOffset F ζ hζ R P S V j).val *
            Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) ≤ 2 * Y := by
        dsimp only [Z]
        rw [← mul_div_assoc,le_div_iff₀ (cuspOffset F ζ hζ R P S V j).property,mul_comm]
      change KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (ShellTestFrames.point S V e j p t z) ∈ E at hx
      simp only [g,T,W,Set.mem_ofPred_eq,hm,hr,true_and,hu,
        Set.indicator_apply,hx,↓reduceIte,hq,f]
    rw [lintegral_congr_ae heq]
    split_ifs <;> simp [avg]
  have hmeasure : ((((volume.prod Q.shapeMeasure).prod ρ).restrict
      {p : KPCuspCharts.Coordinates F | p.1 ∈ Q.fundamentalDomain}).restrict
      {p | KPMsFixedHaarDisintegration.logHeight (F := F) Z < p.2}) =
      μp.prod (ρ.restrict (Set.Ioi (KPMsFixedHaarDisintegration.logHeight (F := F) Z))) := by
    rw [Measure.restrict_restrict (measurableSet_lt measurable_const measurable_snd)]
    have he : {p : KPCuspCharts.Coordinates F | KPMsFixedHaarDisintegration.logHeight (F := F) Z < p.2} ∩
        {p : KPCuspCharts.Coordinates F | p.1 ∈ Q.fundamentalDomain} =
        Q.fundamentalDomain ×ˢ Set.Ioi (KPMsFixedHaarDisintegration.logHeight (F := F) Z) := by
      ext p; simp [and_comm]
    rw [he,← Measure.prod_restrict]
  change (∫⁻ x in cuspShell F ζ hζ R P S V j Y,
    φ (fullCoordinate F ζ hζ R P S V j Y x) ∂ R.quotientHaar) =
    (c : ℝ≥0∞) * ∫⁻ p, ∫⁻ z, g p z ∂ μ
      ∂((((volume.prod Q.shapeMeasure).prod ρ).restrict
        {p : KPCuspCharts.Coordinates F | p.1 ∈ Q.fundamentalDomain}).restrict
        {p | KPMsFixedHaarDisintegration.logHeight (F := F) Z < p.2}) at hi
  have hgg : Measurable (fun p => ∫⁻ z, g p z ∂ μ) := hg.lintegral_prod_right'
  rw [hmeasure,lintegral_prod_symm _ hgg.aemeasurable] at hi
  have hs : (∫⁻ t in Set.Ioi (KPMsFixedHaarDisintegration.logHeight (F := F) Z),
      ∫⁻ p, ∫⁻ z, g (p,t) z ∂ μ ∂ μp ∂ ρ) =
      ∫⁻ t in Set.Ioi (KPMsFixedHaarDisintegration.logHeight (F := F) Z),
        if (cuspOffset F ζ hζ R P S V j).val *
          Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) ≤ 2 * Y then a else 0 ∂ ρ := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp_rw [hinner _ t ht]
    split_ifs <;> simp [hstat]
  rw [hs] at hi
  rw [hi]
  have hpos : 0 < Y := (div_pos_iff.mp (hY j).1).resolve_right
    (fun h => (not_lt_of_gt (cuspOffset F ζ hζ R P S V j).property) h.2) |>.1
  rw [← mul_assoc, mul_comm (ENNReal.ofReal (2 * Y)), mul_assoc]
  dsimp only [Z,ρ,KPMsFixedHaarDisintegration.logHeight]
  rw [offset_shell_lintegral (KPCuspLogShape.dimension F)
    (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)
    (cuspOffset F ζ hζ R P S V j).val (cuspOffset F ζ hζ R P S V j).property Y hpos a]
  exact (mul_assoc _ _ _).symm

end DedekindZetaZeroFree.KPMsNativeOffsetMass.ShellTestCoarea

end
