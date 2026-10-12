module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.FixedRadiusOpenQuotients
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.RadialShapeRescaling
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.ReducedRootFrames
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.FrameNormCoherence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology ENNReal NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.OffsetShapeDescent
open KPMsActualAngularSource KPMsNativeOffsetMass
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P)
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming radialArch → radialArch
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming archBasepoint_radial_rescale → archBasepoint_radial_rescale
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming radial_conjugation_split → radial_conjugation_split
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming sectionShape_mul → sectionShape_mul

theorem sectionShape_intrinsic_split
    (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V)
    (w : NumberField.InfinitePlace F) (p : KPCuspCharts.Shape F) (t : ℝ) :
    p - KPMsFixedHaarDisintegration.sectionShape F
      (nativeFamily F ζ hζ R P).totallyComplex w
      ⟨(cuspOffset F ζ hζ R P S V j).val *
          Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
        mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩ =
    (p - KPMsFixedHaarDisintegration.sectionShape F
      (nativeFamily F ζ hζ R P).totallyComplex w
      ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩) -
    KPMsFixedHaarDisintegration.sectionShape F
      (nativeFamily F ζ hζ R P).totallyComplex w (cuspOffset F ζ hζ R P S V j) := by
  rw [sectionShape_mul (nativeFamily F ζ hζ R P).totallyComplex w
    (cuspOffset F ζ hζ R P S V j)
    ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩]
  abel

section Proof

open KPMsActualAngularDomainSource
open KPMsActualAngularDescentSource KPMsActualAngularFixedRadiusRelationSource
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
open KPMsActualAngularRadialShapeSource (radialCross)
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeDomainProjects → nativeDomainProjects
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeDomainOpen → nativeDomainOpen
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming radialArch → radialArch
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming radialArch_insertion → radialArch_insertion
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming radialArch_action → radialArch_action
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming archBasepoint_radial_rescale → archBasepoint_radial_rescale
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming radial_conjugation_split → radial_conjugation_split
open _root_.DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource renaming sectionShape_mul → sectionShape_mul

open _root_.DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability renaming level_frame_algebra → level_frame_algebra
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}

 def representative (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) : G F ζ hζ :=
  KPMsActualCuspSource.rationalLift F ζ hζ
    (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)

 abbrev fullDomain (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ) :=
  nativeFullDomain F ζ hζ R P S V j Y

private theorem chart_projection (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V)
    (a : KPSmoothActualFlowData.GInfinity F) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) =
      Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,
        (nativeAtlas F ζ hζ R P S V).representative j.1) := by
  have hu := u.property
  simp only [S.level_matching (cofinalLevel F ζ hζ V)] at hu
  obtain ⟨uf, huf, heq⟩ := hu
  let uf' : (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup := ⟨uf, huf⟩
  have heq' : uf'.val.val = u.val := heq
  have hcentre : (KPCuspGenuineMonodromy.central F ζ hζ ε).val =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := rfl
  rw [← heq', ← hcentre]
  simp only [mul_assoc]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, P.formula]
  apply Quotient.sound
  change (KPFiniteCuspAtlas.sphericalRelation F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V))).r _ _
  refine ⟨1, ε⁻¹, uf'⁻¹, by simp, ?_⟩
  simp only [map_one, one_mul, mul_assoc]
  have hc : KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
      (nativeAtlas F ζ hζ R P S V).representative j.1 =
      (nativeAtlas F ζ hζ R P S V).representative j.1 *
        KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ := by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
        ⟨ε⁻¹, rfl⟩) _).symm
  rw [← mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹), hc]
  simp [map_inv, mul_assoc]

private theorem spherical_projection_right_level
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (g : KPMsActualAngularSource.G F ζ hζ)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * u.val)) =
      P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  obtain ⟨e,he⟩ := product_splitting (F := F) (ζ := ζ) (hζ := hζ)
  obtain ⟨⟨a,c⟩,h⟩ := e.surjective g
  rw [he] at h
  rw [← h]
  have hum := u.property
  simp only [S.level_matching (cofinalLevel F ζ hζ V)] at hum
  obtain ⟨uf,huf,hufeq⟩ := hum
  have hu : (uf : KPMsActualAngularSource.G F ζ hζ) = u.val := hufeq
  rw [← hu, mul_assoc, ← Subgroup.coe_mul, P.formula, P.formula]
  apply Quotient.sound
  refine ⟨1,1, (⟨uf,huf⟩ : (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup)⁻¹, ?_, ?_⟩
  · simp
  · simp

private theorem angularProjection_continuous (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) :
    Continuous (KPMsFixedHaarDisintegration.angularProjection (nativeAtlas F ζ hζ R P S V)) := by
  apply continuous_sigma
  intro j
  exact continuous_sigmaMk.comp
    (KPMsFixedHaarDisintegration.Geometry (nativeAtlas F ζ hζ R P S V) j).atlas.continuous_projection

private theorem pinned_chart_shape (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y) :
    ∃ s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V),
      Measurable s ∧ ContinuousOn s (KPMsFixedHaarDisintegration.cuspEnds (nativeAtlas F ζ hζ R P S V) Y) ∧
      ∀ x r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (x,r)) =
        KPMsFixedHaarDisintegration.angularProjection _ x := by
  let A := nativeAtlas F ζ hζ R P S V
  let D := nativeDisintegration F ζ hζ R P S V
  let i : Fin A.componentCount := ⟨0, A.positive_componentCount⟩
  let j : KPMsFixedHaarDisintegration.CuspIndex A := ⟨i, ⟨0, (A.cuspAtlas i).positive_cuspCount⟩⟩
  letI : Nonempty (KPMsFixedHaarDisintegration.CrossSection A) := ⟨⟨j, Quotient.mk _ (0 : KPCuspCharts.Cross F)⟩⟩
  letI : Nonempty (Set.Ioi Y) := ⟨⟨Y+1, by simp⟩⟩
  have hE := KPMsActualNativeWeightedShapeMeasure.sphericalShell_measurable A D Y
  have he : MeasurableSet (KPMsFixedHaarDisintegration.cuspEnds A Y) := by
    apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro j
    have hm : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ
        (S.atlasLevel (cofinalLevel F ζ hζ V)) (A.representative j.1)) := by
      have heq : KPFiniteCuspAtlas.componentMap F ζ hζ
          (S.atlasLevel (cofinalLevel F ζ hζ V)) (A.representative j.1) =
          A.components ∘ Sigma.mk j.1 := by
        funext x
        exact (A.components_formula j.1 x).symm
      rw [heq]
      exact A.components.isOpenMap.comp isOpenMap_sigmaMk
    exact hm _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ _)
  let emb := (D.chart_embedding Y hY).measurableEmbedding (D.chart_range Y hY ▸ he)
  let s := KPMsFixedHaarDisintegration.angularProjection A ∘ Prod.fst ∘ emb.invFun
  have hs : Measurable s := (angularProjection_continuous S V).measurable.comp
    (measurable_fst.comp emb.measurable_invFun)
  have hsc : ∀ x r, s (D.chart Y hY (x,r)) = KPMsFixedHaarDisintegration.angularProjection A x := by
    intro x r
    simp only [s, Function.comp_apply, emb.leftInverse_invFun (x,r)]
  refine ⟨s,hs,?_,hsc⟩
  rw [← D.chart_range Y hY, ← Set.image_univ]
  apply (D.chart_embedding Y hY).isInducing.continuousOn_image_iff.mpr
  apply ((angularProjection_continuous S V).comp continuous_fst).continuousOn.congr
  rintro ⟨z,r⟩ _
  exact hsc z r

private theorem pinned_shapeCoordinate_on_actual_frame (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (r : Set.Ioi Y) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ x r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (x,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ x)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p, KPMsFixedHaarDisintegration.logHeight (F := F) r.val))) :
    s
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val))) =
      (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
        (nativeDisintegration F ζ hζ R P S V).radial.slot ⟨r.val, lt_trans hY.1 r.property⟩)⟩ :
          KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
  let b := KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
    (nativeDisintegration F ζ hζ R P S V).radial.slot ⟨r.val, lt_trans hY.1 r.property⟩
  let p₀ : KPCuspCharts.Cross F := (p.1, p.2 - b)
  have hcross : (p₀.1, p₀.2 + b) = p := by
    apply Prod.ext
    · rfl
    · exact sub_add_cancel _ _
  have hchart : (nativeDisintegration F ζ hζ R P S V).chart Y hY
      (⟨j, Quotient.mk _ p₀⟩,r) = P.projection (S.atlasLevel (cofinalLevel F ζ hζ V))
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) := by
    rw [chart_projection S V j a ε u, ha]
    rw [(nativeDisintegration F ζ hζ R P S V).chart_formula Y hY j p₀ r]
    simp only [KPFiniteCuspAtlas.componentMap, KPCuspSiegel.projection, Quotient.lift_mk]
    change Quotient.mk _ (_, _) = Quotient.mk _ (_, _)
    rw [hcross]
    rfl
  rw [← hchart, hsc]
  dsimp only [KPMsFixedHaarDisintegration.angularProjection]
  rw [(KPMsFixedHaarDisintegration.Geometry (nativeAtlas F ζ hζ R P S V) j).atlas.projection_formula]

private theorem actual_frame_radial_rescale
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V)
    (w : NumberField.InfinitePlace F) (r : KPMsFixedHaarDisintegration.Radius)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t))) :
    ∃ a' : KPSmoothActualFlowData.GInfinity F,
      representative S V j * KPMsFixedHaarDisintegration.radialSection F ζ hζ w r *
        (representative S V j)⁻¹ *
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
              KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val) =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a' *
          ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val ∧
      KPMsFixedHaarDisintegration.archBasepoint F a' =
        KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (radialCross w (nativeFamily F ζ hζ R P).totallyComplex r p,
            t + KPMsFixedHaarDisintegration.logHeight (F := F) r.val)) := by
  let σ := (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
  refine ⟨archRational σ * radialArch w r * (archRational σ)⁻¹ * a, ?_,
    archBasepoint_radial_rescale σ a w (nativeFamily F ζ hζ R P).totallyComplex r p t ha⟩
  rw [show representative S V j = KPMsActualCuspSource.rationalLift F ζ hζ σ from rfl,
    radial_conjugation_split]
  have hmul := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  simp only [hmul]
  group

private theorem pinned_shape_under_reduced_root
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (r : Set.Ioi Y) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (a₀ : NumberField.InfiniteAdeleRing F)
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)
    (v : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hv : representative S V j =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (archRational (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)) * v.val)
    (hz : (((nativeAtlas F ζ hζ R P S V).representative j.1)⁻¹ * v * finiteRoot F ζ hζ z *
      v⁻¹ * ((nativeAtlas F ζ hζ R P S V).representative j.1)) ∈
        (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ x r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (x,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ x)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p, KPMsFixedHaarDisintegration.logHeight (F := F) r.val))) :
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (representative S V j * KPGlobalTorusFunctionData.N F ζ hζ (a₀,z) *
        (representative S V j)⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)))) =
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val))) := by
  let c := (nativeAtlas F ζ hζ R P S V).representative j.1
  let f := v * finiteRoot F ζ hζ z * v⁻¹
  have hz' : c⁻¹ * f * c ∈ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup := by
    dsimp only [c,f]
    convert hz using 1 <;> group
  have hu : (c⁻¹ * f * c).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V) := by
    rw [S.level_matching (cofinalLevel F ζ hζ V)]
    exact ⟨c⁻¹ * f * c, hz', rfl⟩
  let u' : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V) :=
    ⟨(c⁻¹ * f * c).val * u.val,
      (KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)).mul_mem hu u.property⟩
  let σ := archRational (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
  let a' := σ * archRoot (complexParameter F ζ hζ a₀) * σ⁻¹ * a
  have he : ∀ g : KPMsActualAngularSource.G F ζ hζ,
      g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g :=
    Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩)
  have hsplit := conjugated_root_split F ζ hζ
    (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) v hv a₀ z
  change representative S V j * _ * (representative S V j)⁻¹ = _ at hsplit
  have halg := level_frame_algebra
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (σ * archRoot (complexParameter F ζ hζ a₀) * σ⁻¹))
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) f.val c.val
    (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) u.val
    (insertion_commutes_cover F ζ hζ a f).symm he
  have hframe : representative S V j * KPGlobalTorusFunctionData.N F ζ hζ (a₀,z) *
      (representative S V j)⁻¹ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val) =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a' * c.val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u'.val := by
    rw [hsplit]
    change _ * f.val * _ = _
    rw [halg]
    dsimp only [a',u']
    rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
      (σ * archRoot (complexParameter F ζ hζ a₀) * σ⁻¹) a]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have ha' := archBasepoint_rational_conjugated_root
    (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) a
    (complexParameter F ζ hζ a₀) p (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) ha
  rw [hframe, pinned_shapeCoordinate_on_actual_frame S V j Y hY a'
    (translateCross (complexParameter F ζ hζ a₀) p) r ε u' s hsc ha',
    pinned_shapeCoordinate_on_actual_frame S V j Y hY a p r ε u s hsc ha]
  rfl

private theorem unipotent_fiber_principal_shift
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V)
    (g : G F ζ hζ) (a : KPGlobalTorusFunctionData.Adeles F) (b : F) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (representative S V j * KPGlobalTorusFunctionData.N F ζ hζ
        (a + algebraMap F (KPGlobalTorusFunctionData.Adeles F) b) *
        (representative S V j)⁻¹ * g) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (representative S V j * KPGlobalTorusFunctionData.N F ζ hζ a *
          (representative S V j)⁻¹ * g) := by
  rw [add_comm a, KPGlobalTorusFunctionData.N_add]
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hr : representative S V j ∈
      KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
    unfold representative KPMsActualCuspSource.rationalLift
    exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F _, rfl⟩
  have hn : KPGlobalTorusFunctionData.N F ζ hζ
      (algebraMap F (KPGlobalTorusFunctionData.Adeles F) b) ∈
        KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
    refine ⟨KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.n F b), ?_⟩
    rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
    unfold KPGlobalTorusFunctionData.N
    congr 1
    rw [← KPRationalAdelicSplitting.N_rational F ζ hζ b]
    rfl
  have hmem := (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).mul_mem
    ((KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).mul_mem hr hn)
    ((KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem hr)
  convert (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem hmem using 1 <;> group

private theorem actual_finite_root_shape_invariant
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (r : Set.Ioi Y) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (n : KPGlobalTorusFunctionData.Adeles F)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ z r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (z,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ z)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p, KPMsFixedHaarDisintegration.logHeight (F := F) r.val))) :
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (representative S V j * KPGlobalTorusFunctionData.N F ζ hζ n *
        (representative S V j)⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)))) =
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val))) := by
  obtain ⟨v,hv⟩ := rationalLift_split F ζ hζ
    (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
  obtain ⟨b,hb⟩ := canonical_finite_root_reduction F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) v
    ((nativeAtlas F ζ hζ R P S V).representative j.1) n.2
  have hshift := unipotent_fiber_principal_shift S V j
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)
    (n - algebraMap F (KPGlobalTorusFunctionData.Adeles F) b) b
  simp only [sub_add_cancel] at hshift
  rw [hshift]
  have hn : n - algebraMap F (KPGlobalTorusFunctionData.Adeles F) b =
      ((n - algebraMap F (KPGlobalTorusFunctionData.Adeles F) b).1,
        n.2 - algebraMap F (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) b) := by
    apply Prod.ext <;> rfl
  rw [hn]
  exact pinned_shape_under_reduced_root S V j Y hY a p r ε u _ _ v hv hb s hsc ha

private theorem pinned_shape_unipotent_actual_domain
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (g : KPMsActualAngularSource.G F ζ hζ)
    (hg : g ∈ fullDomain S V j Y)
    (n : KPGlobalTorusFunctionData.Adeles F)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ z r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (z,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ z) :
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (representative S V j * KPGlobalTorusFunctionData.N F ζ hζ n *
        (representative S V j)⁻¹ * g))) =
      s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) := by
  obtain ⟨a,p,t,ε,u,ht,ha,rfl⟩ := hg
  have hd : 0 < (2 : ℝ) * (KPCuspLogShape.dimension F : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex))
  have hr : Y < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
    apply (Real.log_lt_iff_lt_exp hY.1).mp
    simpa only [mul_comm] using (div_lt_iff₀ hd).mp ht
  let r : Set.Ioi Y := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),hr⟩
  have hlog : KPMsFixedHaarDisintegration.logHeight (F := F) r.val = t := by
    unfold KPMsFixedHaarDisintegration.logHeight
    rw [Real.log_exp, mul_div_cancel_left₀ _ hd.ne']
  apply actual_finite_root_shape_invariant S V j Y hY a p r ε u n s hsc
  rwa [hlog]

 def fixedRadiusDomain
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ) (Y : ℝ)
    (r₀ : KPMsFixedHaarDisintegration.Radius) :
    Set (KPMsActualAngularSource.NormOne F ζ hζ (nativeDatum F ζ hζ)) :=
  ⋃ j : NativeCusp F ζ hζ R P S V,
    {g | representative S V j *
      KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (nativeDisintegration F ζ hζ R P S V).radial.slot r₀ * g.val ∈ fullDomain S V j Y}

private theorem fixedRadiusDomain_isOpen
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ) (Y : ℝ)
    (r₀ : KPMsFixedHaarDisintegration.Radius) : IsOpen (fixedRadiusDomain S V Y r₀) := by
  let : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply isOpen_iUnion
  intro j
  exact (nativeDomainOpen F ζ hζ R P S V j Y).preimage (show Continuous (fun g :
    KPMsActualAngularSource.NormOne F ζ hζ (nativeDatum F ζ hζ) =>
      representative S V j * KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (nativeDisintegration F ζ hζ R P S V).radial.slot r₀ * g.val) from
          (continuous_const (y := representative S V j *
            KPMsFixedHaarDisintegration.radialSection F ζ hζ
              (nativeDisintegration F ζ hζ R P S V).radial.slot r₀)).mul continuous_subtype_val)

 theorem fixedRadiusDomain_right_level
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) (Y : ℝ)
    (r₀ : KPMsFixedHaarDisintegration.Radius) (g : NormOne F ζ hζ (nativeDatum F ζ hζ))
    (hg : g ∈ fixedRadiusDomain S V Y r₀)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    ∃ h : NormOne F ζ hζ (nativeDatum F ζ hζ),
      h.val = g.val * u.val ∧ h ∈ fixedRadiusDomain S V Y r₀ := by
  have hn : KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
      (g.val * u.val) = 1 := by
    rw [KPShift81CoherentLevel.norm_right_level F ζ hζ V, g.property]
  refine ⟨⟨g.val * u.val,hn⟩,rfl,?_⟩
  obtain ⟨j,a,p,t,ε,v,ht,ha,he⟩ := Set.mem_iUnion.mp hg
  refine Set.mem_iUnion.mpr ⟨j,a,p,t,ε,v*u,ht,ha,?_⟩
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, he]
  group

 def fixedRadius_right_homeomorph
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ) (Y : ℝ)
    (r₀ : KPMsFixedHaarDisintegration.Radius)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    fixedRadiusDomain S V Y r₀ ≃ₜ fixedRadiusDomain S V Y r₀ := by
  let : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let trans (v : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
      (g : fixedRadiusDomain S V Y r₀) : fixedRadiusDomain S V Y r₀ :=
    ⟨(fixedRadiusDomain_right_level S V Y r₀ g.val g.property v).choose,
      (fixedRadiusDomain_right_level S V Y r₀ g.val g.property v).choose_spec.2⟩
  have hval (v) (g : fixedRadiusDomain S V Y r₀) :
      (trans v g).val.val = g.val.val * v.val :=
    (fixedRadiusDomain_right_level S V Y r₀ g.val g.property v).choose_spec.1
  have hcont (v) : Continuous (trans v) := by
    apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
    apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
    change Continuous (fun g => (trans v g).val.val)
    simp_rw [hval]
    exact (continuous_subtype_val.comp continuous_subtype_val).mul continuous_const
  exact {
    toFun := trans u
    invFun := trans u⁻¹
    left_inv := fun g => by
      apply Subtype.ext; apply Subtype.ext
      rw [hval,hval]; simp
    right_inv := fun g => by
      apply Subtype.ext; apply Subtype.ext
      rw [hval,hval]; simp
    continuous_toFun := hcont u
    continuous_invFun := hcont u⁻¹ }

private theorem fixedRadius_right_homeomorph_val
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ) (Y : ℝ)
    (r₀ : KPMsFixedHaarDisintegration.Radius)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (g : fixedRadiusDomain S V Y r₀) :
    (fixedRadius_right_homeomorph S V Y r₀ u g).val.val = g.val.val * u.val :=
  (fixedRadiusDomain_right_level S V Y r₀ g.val g.property u).choose_spec.1

 def angular_left_homeomorph
    (D : KPMsActualAngularSource.Iwasawa F ζ hζ)
    (y : Fˣ) (n : KPGlobalTorusFunctionData.Adeles F) :
    KPMsActualAngularSource.NormOne F ζ hζ D ≃ₜ
      KPMsActualAngularSource.NormOne F ζ hζ D := by
  let : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  exact (Homeomorph.mulLeft (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
    KPGlobalTorusFunctionData.N F ζ hζ n) : KPMsActualAngularSource.G F ζ hζ)).subtype (by
      intro g
      change _ ↔ KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
        (((KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ n) * g) = 1
      rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul,
        KPGlobalTorusBorelTwistCompatibility.delta_rational,one_mul])

private theorem fixedRadius_angular_quotient_open
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ) (Y : ℝ)
    (r₀ : KPMsFixedHaarDisintegration.Radius) :
    IsOpenMap (fun g : fixedRadiusDomain S V Y r₀ =>
      (Quotient.mk _ g.val : KPMsActualAngularSource.Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V))) := by
  let E := fixedRadiusDomain S V Y r₀
  let q : KPMsActualAngularSource.NormOne F ζ hζ (nativeDatum F ζ hζ) →
      KPMsActualAngularSource.Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) := Quotient.mk _
  intro O hO
  apply isOpen_coinduced.mpr
  change IsOpen (q ⁻¹' ((fun g : E => q g.val) '' O))
  have heq : q ⁻¹' ((fun g : E => q g.val) '' O) =
      ⋃ (y : Fˣ) (n : KPGlobalTorusFunctionData.Adeles F)
        (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
      angular_left_homeomorph (nativeDatum F ζ hζ) y n ''
        (Subtype.val '' (fixedRadius_right_homeomorph S V Y r₀ u '' O)) := by
    ext b
    constructor
    · rintro ⟨a,ha,hq⟩
      have hrel := (KPMsActualAngularFixedRadiusDomainSource.angular_eqvgen_iff (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) a.val b).mp (Quotient.exact hq)
      obtain ⟨y,n,u,hb⟩ := hrel
      refine Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨u,?_⟩⟩⟩
      refine ⟨(fixedRadius_right_homeomorph S V Y r₀ u a).val,
        ⟨_,⟨a,ha,rfl⟩,rfl⟩,?_⟩
      apply Subtype.ext
      change ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
        KPGlobalTorusFunctionData.N F ζ hζ n) *
          (fixedRadius_right_homeomorph S V Y r₀ u a).val.val = b.val
      rw [fixedRadius_right_homeomorph_val]
      exact (mul_assoc _ _ _).symm.trans hb.symm
    · rintro hb
      obtain ⟨y,hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨n,hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨u,hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨c,⟨d,⟨a,ha,rfl⟩,rfl⟩,rfl⟩ := hb
      refine ⟨a,ha,Quotient.sound (Relation.EqvGen.rel _ _ ⟨y,n,u,?_⟩)⟩
      change ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
        KPGlobalTorusFunctionData.N F ζ hζ n) *
          (fixedRadius_right_homeomorph S V Y r₀ u a).val.val = _
      rw [fixedRadius_right_homeomorph_val]
      exact (mul_assoc _ _ _).symm
  rw [heq]
  apply isOpen_iUnion
  intro y
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro u
  exact (angular_left_homeomorph (nativeDatum F ζ hζ) y n).isOpenMap _
    ((fixedRadiusDomain_isOpen S V Y r₀).isOpenMap_subtype_val _
      ((fixedRadius_right_homeomorph S V Y r₀ u).isOpenMap _ hO))

private theorem fixed_radius_shape_angular_relation
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (r₀ : KPMsFixedHaarDisintegration.Radius)
    (g h : KPMsActualAngularSource.NormOne F ζ hζ (nativeDatum F ζ hζ))
    (hg : representative S V j *
      KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (nativeDisintegration F ζ hζ R P S V).radial.slot r₀ * g.val ∈ fullDomain S V j Y)
    (y : Fˣ) (n : KPGlobalTorusFunctionData.Adeles F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (he : h.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ n) * g.val * u.val)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ z r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (z,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ z) :
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (nativeDisintegration F ζ hζ R P S V).radial.slot r₀ * h.val))) =
      s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPMsFixedHaarDisintegration.radialSection F ζ hζ
          (nativeDisintegration F ζ hζ R P S V).radial.slot r₀ * g.val))) := by
  let B := (nativeDisintegration F ζ hζ R P S V).radial
  let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (KPMsFixedHaarDisintegration.positiveSlots F B.slot r₀)
  let n' := (KPGlobalTorusFunctionData.p F ζ hζ t : KPGlobalTorusFunctionData.Adeles F) * n
  have halg : KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r₀ * h.val =
      (KPGlobalTorusFunctionData.s F ζ hζ y).val *
        (KPGlobalTorusFunctionData.N F ζ hζ n' *
          (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r₀ * g.val)) * u.val :=
    by
      have hn := ActualBorelRetraction.torus_conjugates_root F ζ hζ t n
      rw [he]
      dsimp only [n']
      rw [← hn]
      have hc := KPMsActualAngularFixedRadiusRelationSource.radial_s_commute B r₀ y
      change Commute t.val (KPGlobalTorusFunctionData.s F ζ hζ y).val at hc
      change t.val * _ = _
      calc
        _ = t.val * (KPGlobalTorusFunctionData.s F ζ hζ y).val *
            (KPGlobalTorusFunctionData.N F ζ hζ n * g.val * u.val) := by group
        _ = _ := by rw [hc.eq]; change _ = (KPGlobalTorusFunctionData.s F ζ hζ y).val * (t.val * KPGlobalTorusFunctionData.N F ζ hζ n * t.val⁻¹ * (t.val * g.val)) * u.val; group
  change s (P.projection _ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
    (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r₀ * h.val))) = _
  rw [halg, spherical_projection_right_level S V, quotientMap_left_s]
  have hinv := pinned_shape_unipotent_actual_domain S V j Y hY
    (representative S V j *
      KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r₀ * g.val) hg n' s hsc
  have heq : representative S V j * KPGlobalTorusFunctionData.N F ζ hζ n' *
      (representative S V j)⁻¹ *
        (representative S V j *
          KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r₀ * g.val) =
      representative S V j * (KPGlobalTorusFunctionData.N F ζ hζ n' *
        (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r₀ * g.val)) := by group
  rw [heq] at hinv
  simp only [representative, mul_assoc, quotientMap_left_rational] at hinv
  exact hinv

 def correctShape (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) :
    KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) :=
  fun ω => ⟨ω.1, ω.2 - QuotientAddGroup.mk
    (KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
      (nativeDisintegration F ζ hζ R P S V).radial.slot (cuspOffset F ζ hζ R P S V ω.1))⟩

private theorem correctShape_continuous (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) :
    Continuous (correctShape S V) := by
  apply continuous_sigma
  intro j
  change Continuous (fun a => (⟨j, a - QuotientAddGroup.mk
    (KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
      (nativeDisintegration F ζ hζ R P S V).radial.slot (cuspOffset F ζ hζ R P S V j))⟩ :
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)))
  apply continuous_sigmaMk.comp
  apply continuous_id.sub
  exact continuous_const (y := (QuotientAddGroup.mk
    (KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
      (nativeDisintegration F ζ hζ R P S V).radial.slot (cuspOffset F ζ hζ R P S V j)) :
        KPCuspCharts.Base F (nativeFamily F ζ hζ R P).totallyComplex
          (KPMsFixedHaarDisintegration.Parabolic (nativeAtlas F ζ hζ R P S V) j).E
          (KPMsFixedHaarDisintegration.Parabolic (nativeAtlas F ζ hζ R P S V) j).integralUnits))

private theorem corrected_chart_formula (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (r : Set.Ioi Y) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ x r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (x,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ x)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
      (KPCuspCharts.toArch F (p, KPMsFixedHaarDisintegration.logHeight (F := F) r.val))) :
    correctShape S V (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V))
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)))) =
      (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
        (nativeFamily F ζ hζ R P).totallyComplex (nativeDisintegration F ζ hζ R P S V).radial.slot
        ⟨(cuspOffset F ζ hζ R P S V j).val * r.val,
          mul_pos (cuspOffset F ζ hζ R P S V j).property (lt_trans hY.1 r.property)⟩)⟩ :
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
  rw [pinned_shapeCoordinate_on_actual_frame S V j Y hY a p r ε u s hsc ha]
  simp only [correctShape]
  congr 1
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  have hh := sectionShape_mul (nativeFamily F ζ hζ R P).totallyComplex
    (nativeDisintegration F ζ hζ R P S V).radial.slot
    (cuspOffset F ζ hζ R P S V j) (⟨r.val, lt_trans hY.1 r.property⟩ : KPMsFixedHaarDisintegration.Radius)
  rw [hh]
  abel

private theorem source_recovery
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (rb : KPMsFixedHaarDisintegration.Radius)
    (hrb : ∀ j : NativeCusp F ζ hζ R P S V, Y < rb.val / (cuspOffset F ζ hζ R P S V j).val)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ x r, s ((nativeDisintegration F ζ hζ R P S V).chart Y hY (x,r)) =
      KPMsFixedHaarDisintegration.angularProjection _ x)
    (j : NativeCusp F ζ hζ R P S V)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
      (KPCuspCharts.toArch F (p,t))) :
    let frame := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val
    let g : NormOne F ζ hζ (nativeDatum F ζ hζ) :=
      ⟨framedNormalization F ζ hζ (nativeDatum F ζ hζ)
        (nativeDisintegration F ζ hζ R P S V).radial (representative S V j) frame,
        (framedNormalization_normOne_continuous F ζ hζ (nativeDatum F ζ hζ)
          (nativeDisintegration F ζ hζ R P S V).radial (representative S V j)).1 _⟩
    g ∈ fixedRadiusDomain S V Y rb ∧
      correctShape S V (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V))
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPMsFixedHaarDisintegration.radialSection F ζ hζ
            (nativeDisintegration F ζ hζ R P S V).radial.slot rb * g.val)))) =
      (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
        (nativeFamily F ζ hζ R P).totallyComplex (nativeDisintegration F ζ hζ R P S V).radial.slot
        ⟨(cuspOffset F ζ hζ R P S V j).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
          mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩)⟩ :
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
  intro frame g
  let B := (nativeDisintegration F ζ hζ R P S V).radial
  let c := cuspOffset F ζ hζ R P S V j
  let ra : KPMsFixedHaarDisintegration.Radius :=
    ⟨c.val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), mul_pos c.property (Real.exp_pos _)⟩
  let d : KPMsFixedHaarDisintegration.Radius := ⟨rb.val / ra.val, div_pos rb.property ra.property⟩
  have hd : (⟨d.val * ra.val, mul_pos d.property ra.property⟩ : KPMsFixedHaarDisintegration.Radius) = rb := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ ra.property.ne'
  have hrad : framedRadius F ζ hζ (nativeDatum F ζ hζ) (representative S V j) frame = ra := by
    apply Subtype.ext
    exact FrameNorm.actual_frame_norm_coherent F ζ hζ R P S V j a p t ε u ha
  have hm : KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot d =
      KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot rb *
        (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot ra)⁻¹ := by
    apply eq_mul_inv_iff_mul_eq.mpr
    rw [← B.section_mul, hd]
  obtain ⟨a',he,ha'⟩ := actual_frame_radial_rescale S V j B.slot d a p t ε u ha
  have halg : representative S V j * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot rb * g.val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a' *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
    dsimp only [g, framedNormalization]
    rw [hrad, ← he, hm]
    dsimp only [frame, B]
    group
  have hdim : 0 < (2 : ℝ) * (KPCuspLogShape.dimension F : ℝ) := by
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex))
  let r : Set.Ioi Y := ⟨rb.val / c.val,hrb j⟩
  have hlog : t + KPMsFixedHaarDisintegration.logHeight (F := F) d.val =
      KPMsFixedHaarDisintegration.logHeight (F := F) r.val := by
    have h1 : Real.log d.val = Real.log rb.val - Real.log ra.val :=
      Real.log_div rb.property.ne' ra.property.ne'
    have h2 : Real.log ra.val = Real.log c.val + 2 * (KPCuspLogShape.dimension F : ℝ) * t := by
      dsimp only [ra]
      rw [Real.log_mul c.property.ne' (Real.exp_pos _).ne', Real.log_exp]
    unfold KPMsFixedHaarDisintegration.logHeight
    rw [h1,h2]
    change _ = Real.log (rb.val / c.val) / _
    rw [Real.log_div rb.property.ne' c.property.ne']
    apply (eq_div_iff hdim.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hdim.ne']
    ring
  have ht' : KPMsFixedHaarDisintegration.logHeight (F := F) Y <
      t + KPMsFixedHaarDisintegration.logHeight (F := F) d.val := by
    rw [hlog]
    exact div_lt_div_of_pos_right (Real.log_lt_log hY.1 r.property) hdim
  refine ⟨Set.mem_iUnion.mpr ⟨j,?_⟩,?_⟩
  · change representative S V j * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot rb * g.val ∈ fullDomain S V j Y
    rw [halg]
    exact ⟨a',radialCross B.slot (nativeFamily F ζ hζ R P).totallyComplex d p,
      t + KPMsFixedHaarDisintegration.logHeight (F := F) d.val,ε,u,ht',ha',rfl⟩
  · have hdrop := quotientMap_left_rational
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot rb * g.val)
    change KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (representative S V j * _) = _ at hdrop
    have hqa := congrArg (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) halg
    rw [mul_assoc, hdrop] at hqa
    change correctShape S V (s (P.projection _ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot rb * g.val)))) = _
    rw [hqa]
    rw [hlog] at ha'
    rw [corrected_chart_formula S V j Y hY a' (radialCross B.slot (nativeFamily F ζ hζ R P).totallyComplex d p) r ε u s hsc ha']
    have hcr : (⟨c.val * r.val, mul_pos c.property (lt_trans hY.1 r.property)⟩ : KPMsFixedHaarDisintegration.Radius) = rb := by
      apply Subtype.ext
      exact mul_div_cancel₀ _ c.property.ne'
    change (⟨j, QuotientAddGroup.mk (p.2 + KPMsFixedHaarDisintegration.sectionShape F _ B.slot d -
      KPMsFixedHaarDisintegration.sectionShape F _ B.slot
        ⟨c.val * r.val, mul_pos c.property (lt_trans hY.1 r.property)⟩)⟩ :
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) = _
    rw [hcr]
    congr 2
    have hh := sectionShape_mul (nativeFamily F ζ hζ R P).totallyComplex B.slot d ra
    rw [hd] at hh
    rw [hh]
    abel

private theorem fixed_shape_continuous
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (rb : KPMsFixedHaarDisintegration.Radius)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hs : ContinuousOn s (KPMsFixedHaarDisintegration.cuspEnds (nativeAtlas F ζ hζ R P S V) Y)) :
    Continuous (fun g : fixedRadiusDomain S V Y rb =>
      correctShape S V (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V))
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPMsFixedHaarDisintegration.radialSection F ζ hζ (nativeDisintegration F ζ hζ R P S V).radial.slot rb * g.val.val))))) := by
  apply (correctShape_continuous S V).comp
  change Continuous (Set.domRestrict (fixedRadiusDomain S V Y rb) (fun g : NormOne F ζ hζ (nativeDatum F ζ hζ) =>
    s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ (nativeDisintegration F ζ hζ R P S V).radial.slot rb * g.val)))))
  apply continuousOn_iff_continuous_domRestrict.mp
  apply hs.comp (((P.continuous _).comp continuous_quotient_mk').comp
    (continuous_const.mul continuous_subtype_val)).continuousOn
  intro g hg
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hg
  have hx := nativeDomainProjects F ζ hζ R P S V j Y _ hj
  have hdrop := quotientMap_left_rational
    (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
    (KPMsFixedHaarDisintegration.radialSection F ζ hζ (nativeDisintegration F ζ hζ R P S V).radial.slot rb * g.val)
  change KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (representative S V j * _) = _ at hdrop
  rw [mul_assoc,hdrop] at hx
  exact Set.mem_iUnion.mpr ⟨j,hx⟩

theorem fixed_radius_shape_descent
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (rb : KPMsFixedHaarDisintegration.Radius)
    (hrb : ∀ j : NativeCusp F ζ hζ R P S V, Y < rb.val / (cuspOffset F ζ hζ R P S V j).val) :
    ∃ shape : Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V),
      Measurable shape ∧
      ∀ (j : NativeCusp F ζ hζ R P S V) (a : KPSmoothActualFlowData.GInfinity F)
        (p : KPCuspCharts.Cross F) (t : ℝ) (ε : rootsOfUnity 3 F)
        (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
      KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) (KPCuspCharts.toArch F (p,t)) →
      let frame := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val
      shape (Quotient.mk _ (⟨framedNormalization F ζ hζ (nativeDatum F ζ hζ)
        (nativeDisintegration F ζ hζ R P S V).radial (representative S V j) frame,
        (framedNormalization_normOne_continuous F ζ hζ (nativeDatum F ζ hζ)
          (nativeDisintegration F ζ hζ R P S V).radial (representative S V j)).1 _⟩ :
        NormOne F ζ hζ (nativeDatum F ζ hζ))) =
      (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
        (nativeFamily F ζ hζ R P).totallyComplex (nativeDisintegration F ζ hζ R P S V).radial.slot
        ⟨(cuspOffset F ζ hζ R P S V j).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
          mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩)⟩ :
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
  letI : BorelSpace (Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)) := ⟨rfl⟩
  obtain ⟨s,hs,hscnt,hsc⟩ := pinned_chart_shape S V Y hY
  let E := fixedRadiusDomain S V Y rb
  let q : E → Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) := fun g => Quotient.mk _ g.val
  let f : E → KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) := fun g =>
    correctShape S V (s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ (nativeDisintegration F ζ hζ R P S V).radial.slot rb * g.val.val))))
  have hfi : ∀ a b : E, q a = q b → f a = f b := by
    intro a b hab
    obtain ⟨y,n,u,he⟩ := (KPMsActualAngularFixedRadiusDomainSource.angular_eqvgen_iff
      (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) a.val b.val).mp (Quotient.exact hab)
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp a.property
    exact congrArg (correctShape S V) (fixed_radius_shape_angular_relation S V j Y hY rb a.val b.val hj y n u he s hsc).symm
  have hf : Continuous f := fixed_shape_continuous S V Y hY rb s hscnt
  have hqo : IsOpenMap q := fixedRadius_angular_quotient_open S V Y rb
  let Z := Set.range q
  have hZ : IsOpen Z := by simpa only [Set.image_univ] using hqo Set.univ isOpen_univ
  let qr : E → Z := fun a => ⟨q a,Set.mem_range_self a⟩
  have hqc : Continuous qr := (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _
  have hqs : Function.Surjective qr := by rintro ⟨v,a,rfl⟩; exact ⟨a,rfl⟩
  let tr : Z → KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) := fun v => f (Classical.choose v.property)
  have htr : ∀ a, tr (qr a) = f a := fun a => hfi _ a (Classical.choose_spec (qr a).property)
  have hqro : IsOpenMap qr := hqo.codRestrict _
  have htc : Continuous tr := (hqro.isQuotientMap hqc hqs).continuous_iff.mpr (by
    change Continuous (tr ∘ qr)
    have hh : tr ∘ qr = f := funext htr
    rw [hh]
    exact hf)
  let i : Fin (nativeAtlas F ζ hζ R P S V).componentCount := ⟨0,(nativeAtlas F ζ hζ R P S V).positive_componentCount⟩
  let j₀ : NativeCusp F ζ hζ R P S V := ⟨i,⟨0,((nativeAtlas F ζ hζ R P S V).cuspAtlas i).positive_cuspCount⟩⟩
  let ω₀ : KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) := ⟨j₀,QuotientAddGroup.mk 0⟩
  let shape : Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) := fun ω => if h : ω ∈ Z then tr ⟨ω,h⟩ else ω₀
  have hshape : Measurable shape := htc.measurable.dite measurable_const hZ.measurableSet
  refine ⟨shape,hshape,?_⟩
  intro j a p t ε u ha
  have hg := source_recovery S V Y hY rb hrb s hsc j a p t ε u ha
  let frame := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
    ((nativeAtlas F ζ hζ R P S V).representative j.1).val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val
  let g : NormOne F ζ hζ (nativeDatum F ζ hζ) := ⟨framedNormalization F ζ hζ (nativeDatum F ζ hζ)
    (nativeDisintegration F ζ hζ R P S V).radial (representative S V j) frame,
    (framedNormalization_normOne_continuous F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ R P S V).radial (representative S V j)).1 _⟩
  let e : E := ⟨g,hg.1⟩
  change (if h : q e ∈ Z then tr ⟨q e,h⟩ else ω₀) = _
  rw [dif_pos (Set.mem_range_self e)]
  exact (htr e).trans hg.2

end Proof

theorem native_shape_descent :
    ∃ shape : ∀ V : Level F ζ hζ,
      Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V),
      (∀ V, Measurable (shape V)) ∧
      ∀ (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V) (Y : ℝ),
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
                KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
  have hex : ∀ V : Level F ζ hζ, ∃ shape : Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V),
      Measurable shape ∧ ∀ (j : NativeCusp F ζ hζ R P S V) (Y : ℝ),
        OffsetAdmissible F ζ hζ R P S V Y →
        ∀ (x : KPSmoothLocalQuotientCharts.X F ζ hζ), x ∈ cuspShell F ζ hζ R P S V j Y →
        ∀ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F) (t : ℝ) (ε : rootsOfUnity 3 F)
          (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
          actualFrame F ζ hζ R P S V j Y x = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((nativeAtlas F ζ hζ R P S V).representative j.1).val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val →
          KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) (KPCuspCharts.toArch F (p,t)) →
          shape (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) (fullCoordinate F ζ hζ R P S V j Y x)) =
            (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
              (nativeFamily F ζ hζ R P).totallyComplex (nativeDisintegration F ζ hζ R P S V).radial.slot
              ⟨(cuspOffset F ζ hζ R P S V j).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
                mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩)⟩ :
              KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
    intro V
    let Y := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * (nativeAtlas F ζ hζ R P S V).threshold)
    have hd : 0 < (2 : ℝ) * (KPCuspLogShape.dimension F : ℝ) := by
      exact mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex))
    have hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y := by
      refine ⟨Real.exp_pos _,?_⟩
      change _ ≤ Real.log (Real.exp _) / _
      rw [Real.log_exp, mul_div_cancel_left₀ _ hd.ne']
    let rb : KPMsFixedHaarDisintegration.Radius := ⟨1 + ∑ j : NativeCusp F ζ hζ R P S V,
      (cuspOffset F ζ hζ R P S V j).val * Y, by
        apply add_pos_of_pos_of_nonneg zero_lt_one
        exact Finset.sum_nonneg (fun j _ => (mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)).le)⟩
    have hrb : ∀ j : NativeCusp F ζ hζ R P S V, Y < rb.val / (cuspOffset F ζ hζ R P S V j).val := by
      intro j
      rw [lt_div_iff₀ (cuspOffset F ζ hζ R P S V j).property]
      have hh : (cuspOffset F ζ hζ R P S V j).val * Y ≤
          ∑ k : NativeCusp F ζ hζ R P S V, (cuspOffset F ζ hζ R P S V k).val * Y :=
        Finset.single_le_sum (fun k _ => (mul_pos (cuspOffset F ζ hζ R P S V k).property (Real.exp_pos _)).le) (Finset.mem_univ j)
      dsimp only [rb]
      rw [mul_comm Y]
      linarith
    obtain ⟨shape,hs,hframe⟩ := fixed_radius_shape_descent S V Y hY rb hrb
    refine ⟨shape,hs,?_⟩
    intro j Z hZ x hx a p t ε u he ha
    have hh := hframe j a p t ε u ha
    change shape (Quotient.mk _ _) = _
    simpa only [fullCoordinate, fullToLevel_mk, representative, he] using hh
  choose shape hs hframe using hex
  exact ⟨shape,hs,hframe⟩

structure NativeShapeData where
  shape : ∀ V : Level F ζ hζ,
      Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)
  specification :
    (∀ V, Measurable (shape V)) ∧
    ∀ (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V) (Y : ℝ),
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
              KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))

end DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.OffsetShapeDescent

end
