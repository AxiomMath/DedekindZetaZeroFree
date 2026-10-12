module

public import DedekindZetaZeroFree.Eisenstein.Residues.SmoothOrbitsAndRightJets
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothSections.CoherentSpatialSeries
public import DedekindZetaZeroFree.Eisenstein.Induction.PrincipalSeries.InducingModelEquivalence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
open Filter
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualSectionLift
open KPContSectorSmoothFramesSupport KPContActualCommonDiskRightHolomorphy
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def scalarLift : Sections F ζ hζ U R P H →ₗ[ℂ] (G F ζ hζ → ℂ) where
  toFun u := lift F ζ hζ U R P H u
  map_add' u v := by
    funext g
    simp [lift, KPContSectorLineL2Isometry.scalarRepresentative, map_add]
  map_smul' c u := by
    funext g
    simp [lift, KPContSectorLineL2Isometry.scalarRepresentative, map_smul]

theorem lift_continuous (u : smoothSections F ζ hζ U R P H) :
    Continuous (lift F ζ hζ U R P H u.val) := by
  have hc := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ U R P H u.val).mp
    (fun i => (u.property i).continuous)
  exact hc.comp ((KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ U).comp
    continuous_quotient_mk')

theorem lift_genuine (u : Sections F ζ hζ U R P H) (ε : rootsOfUnity 3 F)
    (g : G F ζ hζ) :
    lift F ζ hζ U R P H u (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) * lift F ζ hζ U R P H u g := by
  obtain ⟨e, he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
  obtain ⟨⟨a,c⟩, rfl⟩ := e.surjective g
  rw [he]
  have hcomm := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
    (show KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε,rfl⟩)
  have hprod : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (KPCuspGenuineMonodromy.central F ζ hζ ε * c).val := by
    change _ = _ * (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * c.val)
    rw [← mul_assoc, (Subgroup.mem_center_iff.mp hcomm _).symm, mul_assoc]
  rw [hprod]
  unfold lift
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
    KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
    ← KPContSectorCoveredQuotientVocabulary.z_mk]
  exact (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H u).property ε _

theorem coefficient_smooth (u : smoothSections F ζ hζ U R P H)
    (A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val A) A.ball.carrier := by
  obtain ⟨ε, hε⟩ := QuotientGroup.mk'_surjective
    (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ U) A.phase
  have heq : KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val A =
      fun x => (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (u.val A.component).val (KPContActualChartRestrictionDensity.coordinates F x) := by
    funext x
    unfold KPContActualSmoothLineGluing.coefficient
    have hphase : A.phase = KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε := hε.symm
    rw [hphase, KPContActualChartRestrictionDensity.frameCoefficient_class,
      KPContSectorLineL2Isometry.scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  rw [heq]
  exact (contDiff_const.mul ((u.property A.component).comp
    (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_contDiff
      (KPCuspLogShape.dimension F)))).contDiffOn

theorem lift_arch_smooth (u : smoothSections F ζ hζ U R P H) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => lift F ζ hζ U R P H u.val
      (g * archChart F ζ hζ x)) (archDomain F) := by
  apply (ActualDifferentialData.archDomain_isOpen F).contDiffOn_iff.mpr
  intro x hx
  obtain ⟨Q, W, hWo, hpx, hWd, A, ρ, τ, hρsm, hρA, hτc, hτQ, hτsm, hτj, hbase, heq⟩ :=
    ActualMovingCompactGeometry.local_moving_word_normal_form F ζ hζ U R P H g x hx
  let V : Set (ArchCoordinates F) := {y | (g,y) ∈ W}
  have hVo : IsOpen V := hWo.preimage (continuous_const.prodMk continuous_id)
  have hxV : x ∈ V := hpx
  have hsm := ((coefficient_smooth F ζ hζ U R P H u A).comp hρsm hρA).comp
    (hτsm g) (fun y hy => hτQ hy)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => lift F ζ hζ U R P H u.val (g * archChart F ζ hζ y)) V := by
    apply hsm.congr
    intro y hy
    simpa only [KPContActualSphericalRightFieldIdentification.actualRightWord,
      KPContRightJets.rightWord, Function.comp_apply] using (heq u.val (coefficient_smooth F ζ hζ U R P H u A) [] (g,y) hy)
  exact hf.contDiffAt (hVo.mem_nhds hxV)

 theorem finitePart_eq : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure,
    ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
  exact KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ

 def finiteEquiv : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ*
    KPFiniteCuspAtlas.FiniteCover F ζ hζ where
  toMulEquiv := MulEquiv.subgroupCongr (finitePart_eq F ζ hζ)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def nativeLevel : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ where
  toOpenSubgroup := U.toOpenSubgroup.comap (finiteEquiv F ζ hζ).toMonoidHom
    (finiteEquiv F ζ hζ).continuous
  isCompact := by
    have heq : ((U.toOpenSubgroup.comap (finiteEquiv F ζ hζ).toMonoidHom
        (finiteEquiv F ζ hζ).continuous) : Set _) =
        (finiteEquiv F ζ hζ).symm '' (U.toOpenSubgroup : Set _) := by
      ext x
      constructor
      · intro hx
        exact ⟨finiteEquiv F ζ hζ x, hx, (finiteEquiv F ζ hζ).symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        change finiteEquiv F ζ hζ ((finiteEquiv F ζ hζ).symm y) ∈ U.toOpenSubgroup
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact hy
    rw [heq]
    exact U.isCompact.image (finiteEquiv F ζ hζ).symm.continuous

theorem lift_native_level (u : Sections F ζ hζ U R P H) (g : G F ζ hζ)
    (v : G F ζ hζ) (hv : v ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ
      (nativeLevel F ζ hζ U)) :
    lift F ζ hζ U R P H u (g * v) = lift F ζ hζ U R P H u g := by
  obtain ⟨v,hv,rfl⟩ := hv
  exact ActualMovingCompactGeometry.section_lift_finite_level F ζ hζ U R P H u g
    ⟨finiteEquiv F ζ hζ v,hv⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualSectionLift

end
