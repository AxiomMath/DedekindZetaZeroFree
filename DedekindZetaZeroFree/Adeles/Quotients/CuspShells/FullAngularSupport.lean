module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.OffsetWeightedMass

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal Matrix MatrixGroups LinearAlgebra.Projectivization BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
namespace FullSupportGeometry
open KPMsActualAngularSource KPMsActualCuspSource KPMsActualAngularDescentSource
open KPMsActualAngularTransitionSource KPAdelicCoverRestrictedProduct
open KPMsResidualTailRestoration.SharpConstantTerm
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (S : NativeRecipe F ζ hζ R P) (U : KPMsActualAngularSource.Level F ζ hζ)
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
abbrev Cusp := NativeCusp F ζ hζ R P S U
abbrev cuspEnd (j : Cusp S U) (Y : ℝ) := KPMsActualCuspSource.cuspEnd
  (H := nativeFamily F ζ hζ R P) (S.atlasLevel (cofinalLevel F ζ hζ U)) j Y
abbrev cuspRepresentative (j : Cusp S U) := rationalLift F ζ hζ
  (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
def cuspLift (j : Cusp S U) (Y : ℝ) (x : X F ζ hζ) : KPMsActualAngularSource.G F ζ hζ :=
  if hx : x ∈ cuspEnd S U j Y then
    Classical.choose (cusp_lift_exists (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ U)) (S.level_matching _) j Y x hx)
  else Quotient.out x
theorem cuspLift_frame (j : Cusp S U) (Y : ℝ) (x : X F ζ hζ)
    (hx : x ∈ cuspEnd S U j Y) :
    AdmissibleFrame (H := nativeFamily F ζ hζ R P) (U := cofinalLevel F ζ hζ U)
      (S.atlasLevel (cofinalLevel F ζ hζ U)) j Y x (cuspLift S U j Y x) := by
  rw [cuspLift, dif_pos hx]
  exact (Classical.choose_spec (cusp_lift_exists (H := nativeFamily F ζ hζ R P)
    (S.atlasLevel (cofinalLevel F ζ hζ U)) (S.level_matching _) j Y x hx)).2
theorem cuspLift_quotient (j : Cusp S U) (Y : ℝ) (x : X F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (cuspLift S U j Y x) = x := by
  by_cases hx : x ∈ cuspEnd S U j Y
  · exact (cuspLift_frame S U j Y x hx).1
  · simp only [cuspLift, dif_neg hx]; exact Quotient.out_eq x
def fullCuspDomain (j : Cusp S U) (Y : ℝ) : Set (KPMsActualAngularSource.G F ζ hζ) :=
  {g | ∃ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U)),
    KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
    KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)) ∧
    g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val}

theorem cuspLift_mem_fullCuspDomain (j : Cusp S U) (Y : ℝ)
    (x : X F ζ hζ) (hx : x ∈ cuspEnd S U j Y) :
    cuspLift S U j Y x ∈ fullCuspDomain S U j Y := (cuspLift_frame S U j Y x hx).2

theorem quotientMap_mem_cuspEnd_of_mem_fullCuspDomain
    (j : Cusp S U) (Y : ℝ)
    (g : KPMsActualAngularSource.G F ζ hζ) (hg : g ∈ fullCuspDomain S U j Y) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g ∈ cuspEnd S U j Y := by
  obtain ⟨a,p,t,ε,u,ht,ha,rfl⟩ := hg
  have hu : (u.val : KPMsActualAngularSource.G F ζ hζ) ∈ (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.toSubgroup.map
      (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
    simpa only [← S.level_matching (cofinalLevel F ζ hζ U)] using u.property
  obtain ⟨v,hv,hu⟩ := hu
  let v' : (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup := ⟨v,hv⟩
  let c : KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
    (nativeAtlas F ζ hζ R P S U).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * v
  have he : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
    rw [← hu]
    simp only [c, Subgroup.coe_mul, mul_assoc]
    rfl
  rw [he]
  unfold FullSupportGeometry.cuspEnd KPMsActualCuspSource.cuspEnd
  simp only [Set.mem_preimage]
  rw [P.formula]
  have hc : (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ U)))
      (KPMsFixedHaarDisintegration.archBasepoint F a,c)) =
      Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,
        (nativeAtlas F ζ hζ R P S U).representative j.1) := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨1, ε, v', by simp, ?_⟩
    simp only [map_one, one_mul]
    change c = KPCuspGenuineMonodromy.central F ζ hζ ε *
      (nativeAtlas F ζ hζ R P S U).representative j.1 * v
    unfold c
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
        ⟨ε, rfl⟩) _
  rw [hc]
  refine ⟨KPCuspSiegel.projection F _
    (KPMsFixedHaarDisintegration.archBasepoint F a), ?_, rfl⟩
  refine ⟨KPMsFixedHaarDisintegration.archBasepoint F a, ?_, rfl⟩
  refine ⟨KPCuspCharts.toArch F (p,t), ?_, ha.symm⟩
  change KPMsFixedHaarDisintegration.logHeight (F := F) Y <
    KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F (p,t))
  rw [KPCuspCharts.toArch_meanHeight F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)]
  exact ht

theorem quotientMap_image_fullCuspDomain
    (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (nativeAtlas F ζ hζ R P S U) Y) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ '' fullCuspDomain S U j Y =
      cuspEnd S U j Y := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact quotientMap_mem_cuspEnd_of_mem_fullCuspDomain S U j Y g hg
  · intro x hx
    exact ⟨cuspLift S U j Y x, cuspLift_mem_fullCuspDomain S U j Y x hx,
      cuspLift_quotient S U j Y x⟩

theorem fullCusp_arch_constraint_iff
    (j : Cusp S U) (Y : ℝ)
    (a : KPSmoothActualFlowData.GInfinity F) :
    (∃ (p : KPCuspCharts.Cross F) (t : ℝ),
      KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      KPMsFixedHaarDisintegration.archBasepoint F a =
        KPCuspSiegel.action F
          (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (p,t))) ↔
    KPMsFixedHaarDisintegration.archBasepoint F a ∈
      KPCuspSiegel.highCusp F
        (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
        (KPMsFixedHaarDisintegration.logHeight (F := F) Y) := by
  have hd := KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex
  constructor
  · rintro ⟨p,t,ht,ha⟩
    refine ⟨KPCuspCharts.toArch F (p,t), ?_, ha.symm⟩
    change KPMsFixedHaarDisintegration.logHeight (F := F) Y <
      KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F (p,t))
    rwa [KPCuspCharts.toArch_meanHeight F hd]
  · rintro ⟨z,hz,he⟩
    let c := (KPCuspCharts.toArchHomeomorph F hd).symm z
    have hc : KPCuspCharts.toArch F c = z :=
      (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply z
    refine ⟨c.1,c.2,?_,?_⟩
    · rw [← KPCuspCharts.toArch_meanHeight F hd c, hc]
      exact hz
    · rw [show (c.1,c.2) = c from rfl, hc]
      exact he.symm

theorem isOpen_fullCusp_arch_constraint
    (j : Cusp S U) (Y : ℝ) :
    IsOpen {a : KPSmoothActualFlowData.GInfinity F |
      ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t))} := by
  have he : {a : KPSmoothActualFlowData.GInfinity F |
      ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t))} =
      KPMsFixedHaarDisintegration.archBasepoint F ⁻¹'
        KPCuspSiegel.highCusp F
          (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
          (KPMsFixedHaarDisintegration.logHeight (F := F) Y) := by
    ext a
    exact fullCusp_arch_constraint_iff S U j Y a
  rw [he]
  exact (KPCuspSiegel.isOpen_highCusp F _ _).preimage KPMsActualAngularDomainSource.continuous_archBasepoint

def fullCuspFiniteDomain (j : Cusp S U) : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
  ⋃ ε : rootsOfUnity 3 F,
    (fun u => (nativeAtlas F ζ hζ R P S U).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * u) ''
        ((S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem isOpen_fullCuspFiniteDomain (j : Cusp S U) :
    IsOpen (fullCuspFiniteDomain S U j) := by
  letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply isOpen_iUnion
  intro ε
  exact (Homeomorph.mulLeft _).isOpenMap _ (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.isOpen

theorem fullCuspDomain_product_image (j : Cusp S U) (Y : ℝ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* KPMsActualAngularSource.G F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) :
    fullCuspDomain S U j Y = e ''
      ({a | ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t))} ×ˢ fullCuspFiniteDomain S U j) := by
  ext g
  constructor
  · rintro ⟨a,p,t,ε,u,ht,ha,hg⟩
    have hu : (u.val : KPMsActualAngularSource.G F ζ hζ) ∈ (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
      simpa only [← S.level_matching (cofinalLevel F ζ hζ U)] using u.property
    obtain ⟨v,hv,hu⟩ := hu
    refine ⟨(a, (nativeAtlas F ζ hζ R P S U).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * v), ⟨⟨p,t,ht,ha⟩, ?_⟩, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨ε, ⟨v,hv,rfl⟩⟩
    · rw [he, hg, ← hu]
      simp only [Subgroup.coe_mul, mul_assoc]
      rfl
  · rintro ⟨⟨a,c⟩,⟨⟨p,t,ht,ha⟩,hc⟩,rfl⟩
    obtain ⟨ε,v,hv,hc⟩ := Set.mem_iUnion.mp hc
    have hu : v.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U) := by
      rw [S.level_matching (cofinalLevel F ζ hζ U)]
      exact ⟨v,hv,rfl⟩
    refine ⟨a,p,t,ε,⟨v.val,hu⟩,ht,ha,?_⟩
    change (nativeAtlas F ζ hζ R P S U).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * v = c at hc
    rw [he, ← hc]
    simp only [Subgroup.coe_mul, mul_assoc]
    rfl

theorem isOpen_fullCuspDomain (j : Cusp S U) (Y : ℝ) :
    IsOpen (fullCuspDomain S U j Y) := by
  obtain ⟨e,he⟩ := KPMsActualAngularDomainSource.product_splitting (F := F) (ζ := ζ) (hζ := hζ)
  rw [fullCuspDomain_product_image S U j Y e he]
  exact e.toHomeomorph.isOpenMap _
    ((isOpen_fullCusp_arch_constraint S U j Y).prod (isOpen_fullCuspFiniteDomain S U j))

theorem finiteProjection_level (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U)) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ u.val ∈
      (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ) := by
  have hu : u.val ∈ (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.toSubgroup.map
      (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
    simpa only [← S.level_matching (cofinalLevel F ζ hζ U)] using u.property
  obtain ⟨w, hw, hwu⟩ := hu
  exact ⟨w, hw, congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hwu⟩

theorem frame_transition_component
    (j : Cusp S U)
    (a₁ a₂ : KPSmoothActualFlowData.GInfinity F)
    (ε₁ ε₂ : rootsOfUnity 3 F)
    (u₁ u₂ : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U))
    (γ : KPCuspArithmetic.PGL2 F)
    (he : rationalLift F ζ hζ γ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₁ *
        ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₁ * u₁.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₂ *
        ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₂ * u₂.val) :
    γ ∈ KPCuspGenuineMonodromy.Component F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ U))
      ((nativeAtlas F ζ hζ R P S U).representative j.1) := by
  have hp := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) he
  simp only [map_mul, KPMsActualCuspSource.finiteProjection_rationalLift, KPMsActualCuspSource.finiteProjection_insertion,
    KPMsActualAngularTransitionSource.finiteProjection_centre, one_mul, mul_one] at hp
  let c := KPCuspGenuineMonodromy.finiteBase F ζ hζ
    ((nativeAtlas F ζ hζ R P S U).representative j.1)
  let w := KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₂.val *
    (KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₁.val)⁻¹
  change KPFiniteComponents.diagonal F γ ∈
    (((S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
      (MulAut.conj c).toMonoidHom)
  refine ⟨w, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (finiteProjection_level S U u₂)
      (Subgroup.inv_mem _ (finiteProjection_level S U u₁))
  · change c * w * c⁻¹ = KPFiniteComponents.diagonal F γ
    change KPFiniteComponents.diagonal F γ * (c * _) = c * _ at hp
    dsimp [w]
    calc
      _ = (c * KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₂.val) *
          (c * KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₁.val)⁻¹ := by group
      _ = KPFiniteComponents.diagonal F γ := by rw [← hp]; group

theorem high_frame_transition_fixes_cusp
    (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y)
    (a₁ a₂ : KPSmoothActualFlowData.GInfinity F)
    (p₁ p₂ : KPCuspCharts.Cross F) (t₁ t₂ : ℝ)
    (ε₁ ε₂ : rootsOfUnity 3 F)
    (u₁ u₂ : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U))
    (ht₁ : KPMsFixedHaarDisintegration.logHeight (F := F) Y < t₁)
    (ht₂ : KPMsFixedHaarDisintegration.logHeight (F := F) Y < t₂)
    (ha₁ : KPMsFixedHaarDisintegration.archBasepoint F a₁ =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p₁,t₁)))
    (ha₂ : KPMsFixedHaarDisintegration.archBasepoint F a₂ =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p₂,t₂)))
    (γ : KPCuspArithmetic.PGL2 F)
    (he : rationalLift F ζ hζ γ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₁ *
        ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₁ * u₁.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₂ *
        ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₂ * u₂.val) :
    γ • (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).cusp j.2) =
      (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).cusp j.2) := by
  let c := (nativeAtlas F ζ hζ R P S U).representative j.1
  have hlevel_arch (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U)) :
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ u.val = 1 := by
    have hu : u.val ∈ (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
      simpa only [← S.level_matching (cofinalLevel F ζ hζ U)] using u.property
    obtain ⟨w, hw, hwu⟩ := hu
    change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ u.val = 1
    rw [← hwu]
    change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ w.val = 1
    funext v
    rw [KPMsActualCuspSource.projection_compare]
    have h := MonoidHom.mem_ker.mp w.property
    rw [h]
    exact map_one _
  have hfinite_arch (w : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ w.val = 1 := by
    funext v
    rw [KPMsActualCuspSource.projection_compare]
    rw [MonoidHom.mem_ker.mp w.property]
    exact map_one _
  have hcentre_arch (ε : rootsOfUnity 3 F) :
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
        (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) = 1 :=
    hfinite_arch (KPCuspGenuineMonodromy.central F ζ hζ ε)
  have hp := congrArg (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ) he
  simp only [map_mul, KPMsActualCuspSource.rationalLift_archProjection,
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion,
    hfinite_arch, hlevel_arch, hcentre_arch, mul_one] at hp
  have hi (a : KPSmoothActualFlowData.GInfinity F) :
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = a :=
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ a
  rw [hi, hi] at hp
  have hbp : KPCuspSiegel.action F γ (KPMsFixedHaarDisintegration.archBasepoint F a₁) =
      KPMsFixedHaarDisintegration.archBasepoint F a₂ := by
    rw [← hp, KPMsActualCuspSource.archBasepoint_rational_mul]
  have hγ := frame_transition_component S U j a₁ a₂ ε₁ ε₂ u₁ u₂ γ he
  apply atlas_high_overlap_stabilizes_cusp (nativeAtlas F ζ hζ R P S U) j Y hY
    ⟨γ, hγ⟩ (KPMsFixedHaarDisintegration.archBasepoint F a₁)
  · rw [ha₁]
    refine ⟨KPCuspCharts.toArch F (p₁,t₁), ?_, rfl⟩
    change KPMsFixedHaarDisintegration.logHeight (F := F) Y < _
    rw [KPCuspCharts.toArch_meanHeight F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)]
    exact ht₁
  · change KPCuspSiegel.action F γ _ ∈ _
    rw [hbp, ha₂]
    refine ⟨KPCuspCharts.toArch F (p₂,t₂), ?_, rfl⟩
    change KPMsFixedHaarDisintegration.logHeight (F := F) Y < _
    rw [KPCuspCharts.toArch_meanHeight F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)]
    exact ht₂

theorem actual_full_frame_invariant (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y)
    (a b : KPMsActualAngularSource.G F ζ hζ) (ha : a ∈ fullCuspDomain S U j Y) (hb : b ∈ fullCuspDomain S U j Y)
    (he : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ b) :
    framedFullAngular F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S U).radial
        (cuspRepresentative S U j) a =
      framedFullAngular F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S U).radial
        (cuspRepresentative S U j) b := by
  obtain ⟨η,rfl⟩ := (full_quotient_eq_iff_rational_left a b).mp he
  obtain ⟨a₁,p₁,t₁,ε₁,u₁,ht₁,ha₁,he₁⟩ := ha
  obtain ⟨a₂,p₂,t₂,ε₂,u₂,ht₂,ha₂,he₂⟩ := hb
  have hfix := high_frame_transition_fixes_cusp S U j Y hY a₁ a₂ p₁ p₂ t₁ t₂
    ε₁ ε₂ u₁ u₂ ht₁ ht₂ ha₁ ha₂ η (he₁ ▸ he₂)
  let σ := ((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2
  obtain ⟨y,x,hupper⟩ := rational_upper_literal_factorization F ζ hζ (σ⁻¹ * η * σ)
    (KPMsActualAngularTransitionSource.cusp_fixing_upper F _ σ η
      (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative_formula j.2) hfix)
  apply Eq.symm
  apply framedFullAngular_upper_transition F ζ hζ (nativeDatum F ζ hζ)
    (nativeDisintegration F ζ hζ R P S U).radial (cuspRepresentative S U j) a _ y x
  rw [← hupper, KPMsActualAngularTransitionSource.rationalLift_mul, KPMsActualAngularTransitionSource.rationalLift_mul, KPMsActualAngularTransitionSource.rationalLift_inv]
  dsimp [σ, cuspRepresentative]
  group

theorem cuspFullAngular_continuousOn (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y) :
    ContinuousOn (fun x => (framedFullAngular F ζ hζ (nativeDatum F ζ hζ)
        (nativeDisintegration F ζ hζ R P S U).radial (cuspRepresentative S U j) (cuspLift S U j Y x) :
      FullOmega F ζ hζ (nativeDatum F ζ hζ))) (cuspEnd S U j Y) := by
  letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hq : Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := continuous_quotient_mk'
  have hqo : IsOpenMap (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := isOpenMap_quotient_mk'_mul
  have hs : ∀ x ∈ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ '' fullCuspDomain S U j Y,
      cuspLift S U j Y x ∈ fullCuspDomain S U j Y ∧
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (cuspLift S U j Y x) = x := by
    intro x hx
    rw [quotientMap_image_fullCuspDomain S U j Y hY] at hx
    exact ⟨cuspLift_mem_fullCuspDomain S U j Y x hx, cuspLift_quotient S U j Y x⟩
  have hc := continuousOn_section_of_fiber_invariance hq hqo
    (isOpen_fullCuspDomain S U j Y) hs
    (framedFullAngular_continuous F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S U).radial
      (cuspRepresentative S U j)).continuousOn
    (fun a ha b hb he => actual_full_frame_invariant S U j Y hY a b ha hb he)
  rw [quotientMap_image_fullCuspDomain S U j Y hY] at hc
  exact hc
theorem cuspEnd_isOpen (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y) :
    IsOpen (cuspEnd S U j Y) := by
  letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  rw [← quotientMap_image_fullCuspDomain S U j Y hY]
  exact isOpenMap_quotient_mk'_mul _ (isOpen_fullCuspDomain S U j Y)

theorem chart_projection (j : Cusp S U)
    (a : KPSmoothActualFlowData.GInfinity F) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U)) :
    P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) =
      Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,
        (nativeAtlas F ζ hζ R P S U).representative j.1) := by
  have hu := u.property
  simp only [S.level_matching (cofinalLevel F ζ hζ U)] at hu
  obtain ⟨uf, huf, heq⟩ := hu
  let uf' : (S.atlasLevel (cofinalLevel F ζ hζ U)).toOpenSubgroup := ⟨uf, huf⟩
  have heq' : uf'.val.val = u.val := heq
  have hcentre : (KPCuspGenuineMonodromy.central F ζ hζ ε).val =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := rfl
  rw [← heq', ← hcentre]
  simp only [mul_assoc]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, P.formula]
  apply Quotient.sound
  change (KPFiniteCuspAtlas.sphericalRelation F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ U))).r _ _
  refine ⟨1, ε⁻¹, uf'⁻¹, by simp, ?_⟩
  simp only [map_one, one_mul, mul_assoc]
  have hc : KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
      (nativeAtlas F ζ hζ R P S U).representative j.1 =
      (nativeAtlas F ζ hζ R P S U).representative j.1 *
        KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ := by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
        ⟨ε⁻¹, rfl⟩) _).symm
  rw [← mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹), hc]
  simp [map_inv, mul_assoc]

theorem spherical_modulus_of_cusp_basepoint
    (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (nativeAtlas F ζ hζ R P S U) Y)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U))
    (ht : KPMsFixedHaarDisintegration.logHeight (F := F) Y < t)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t))) :
    (nativeDisintegration F ζ hζ R P S U).modulus
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U))
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val))) =
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  have hd : (0 : ℝ) < (KPCuspLogShape.dimension F : ℝ) := by
    exact_mod_cast KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex
  have hd2 : (0 : ℝ) < 2 * (KPCuspLogShape.dimension F : ℝ) := by linarith
  have hlog : Real.log Y < 2 * (KPCuspLogShape.dimension F : ℝ) * t := by
    have h1 : Real.log Y < t * (2 * (KPCuspLogShape.dimension F : ℝ)) :=
      (div_lt_iff₀ hd2).mp ht
    linarith [mul_comm t (2 * (KPCuspLogShape.dimension F : ℝ))]
  have hYexp : Y < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) :=
    (Real.log_lt_iff_lt_exp hY.1).mp hlog
  let r : Set.Ioi Y := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), hYexp⟩
  have hrval : r.val = Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := rfl
  have hlh : KPMsFixedHaarDisintegration.logHeight (F := F) r.val = t := by
    rw [KPMsFixedHaarDisintegration.logHeight, hrval, Real.log_exp]
    exact mul_div_cancel_left₀ t (ne_of_gt hd2)
  have hproj := chart_projection S U j a ε u
  rw [hproj, ha]
  set shift : KPCuspCharts.Shape F :=
    KPMsFixedHaarDisintegration.sectionShape F (nativeFamily F ζ hζ R P).totallyComplex
      ((nativeDisintegration F ζ hζ R P S U).radial.slot)
      ⟨r.val, lt_trans hY.1 r.property⟩ with hS
  let p₀ : KPCuspCharts.Cross F := (p.1, p.2 - shift)
  have hcross : (p₀.1, p₀.2 + shift) = p := by
    apply Prod.ext
    · rfl
    · dsimp only [p₀]; exact sub_add_cancel p.2 shift
  have hcoord : ((p₀.1, p₀.2 + shift),
      KPMsFixedHaarDisintegration.logHeight (F := F) r.val) = (p, t) := by
    rw [hcross, hlh]
  have hchart : (nativeDisintegration F ζ hζ R P S U).chart Y hY
      (⟨j, Quotient.mk _ p₀⟩, r) =
      Quotient.mk _ (KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)),
        (nativeAtlas F ζ hζ R P S U).representative j.1) := by
    rw [(nativeDisintegration F ζ hζ R P S U).chart_formula Y hY j p₀ r]
    simp only [KPFiniteCuspAtlas.componentMap, KPCuspSiegel.projection,
      Quotient.lift_mk]
    rw [← hS, hcoord]
    rfl
  rw [← hchart, (nativeDisintegration F ζ hζ R P S U).chart_modulus Y hY _ r]

private lemma upper_of_infinity_fixed (b : KPCuspArithmetic.PGL2 F)
    (hb : b • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F) :
    KPCuspArithmetic.IsUpperTriangular F b := by
  simpa using KPMsActualAngularTransitionSource.cusp_fixing_upper (F := F) (KPCuspArithmetic.infinity F) 1 b (by simp) hb

theorem finite_frame (S : NativeRecipe F ζ hζ R P)
    (U : KPMsActualAngularSource.Level F ζ hζ) (g : KPMsActualAngularSource.G F ζ hζ) :
    ∃ (j : Cusp S U) (b : KPCuspArithmetic.PGL2 F)
      (a : KPSmoothActualFlowData.GInfinity F) (ε : rootsOfUnity 3 F)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U)),
      KPCuspArithmetic.IsUpperTriangular F b ∧
      cuspRepresentative S U j * rationalLift F ζ hζ b * g =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
  obtain ⟨a,c,hg⟩ := KPMsActualCuspSource.arch_finite_factorization F ζ hζ g
  let T := nativeAtlas F ζ hζ R P S U
  obtain ⟨⟨i,q⟩,hq⟩ := T.components.surjective (Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,c))
  obtain ⟨z,rfl⟩ := Quotient.mk_surjective q
  rw [T.components_formula] at hq
  obtain ⟨δ,ε,u,hz,hc⟩ := Quotient.exact hq.symm
  change T.representative i = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
    KPCuspGenuineMonodromy.central F ζ hζ ε * c * u.val at hc
  obtain ⟨j,η,hη⟩ := (T.cuspAtlas i).exhaustive (δ • KPCuspArithmetic.infinity F)
  change η.val • (T.cuspAtlas i).cusp j = δ • KPCuspArithmetic.infinity F at hη
  let σ := (T.cuspAtlas i).representative j
  let b := σ⁻¹ * η.val⁻¹ * δ
  have hb : b • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F := by
    dsimp [b]
    rw [mul_smul, mul_smul, ← hη, inv_smul_smul,
      ← (T.cuspAtlas i).representative_formula j, inv_smul_smul]
  obtain ⟨θ,v,hv⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ
    (S.atlasLevel (cofinalLevel F ζ hζ U)) (T.representative i) η⁻¹
  let tau := η.val⁻¹ * δ
  obtain ⟨ρ,hρ⟩ := KPMsActualCuspSource.rationalLift_finite_factor F ζ hζ tau
  change rationalLift F ζ hζ tau = _ at hρ
  let a' := KPMsActualCuspSource.archRational F tau * a
  let e := ρ * θ * ε⁻¹
  let w : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U) :=
    ⟨((v * u⁻¹).val : KPFiniteCuspAtlas.FiniteCover F ζ hζ).val, by
      rw [S.level_matching (cofinalLevel F ζ hζ U)]
      exact ⟨(v*u⁻¹).val,(v*u⁻¹).property,rfl⟩⟩
  have hfin : KPCuspGenuineMonodromy.central F ζ hζ ρ *
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ tau * c =
      T.representative i * KPCuspGenuineMonodromy.central F ζ hζ e * (v*u⁻¹).val := by
    have comm : ∀ (e : rootsOfUnity 3 F) (d : KPFiniteCuspAtlas.FiniteCover F ζ hζ),
        KPCuspGenuineMonodromy.central F ζ hζ e * d = d * KPCuspGenuineMonodromy.central F ζ hζ e := by
      intro e d
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨e,rfl⟩) _).symm
    have hc' : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ * c =
        KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ * T.representative i * u.val⁻¹ := by
      rw [hc, map_inv]
      rw [← comm ε (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ)]
      group
    dsimp only [tau,e]
    rw [map_mul]
    rw [mul_assoc, mul_assoc, hc']
    calc
      _ = KPCuspGenuineMonodromy.central F ζ hζ ρ *
          KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
          (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ η.val⁻¹ * T.representative i) * u.val⁻¹ := by
        simp only [← mul_assoc]
        rw [mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ρ), ← comm ε⁻¹]
        simp only [←mul_assoc]
      _ = _ := by
        rw [show η.val⁻¹ = (η⁻¹).val from rfl, hv]
        simp only [map_mul]
        have h1 : KPCuspGenuineMonodromy.central F ζ hζ ρ *
            KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ * KPCuspGenuineMonodromy.central F ζ hζ θ =
            KPCuspGenuineMonodromy.central F ζ hζ (ρ*θ*ε⁻¹) := by
          rw [← map_mul, ← map_mul]
          congr 1
          exact by ac_rfl
        simp only [← mul_assoc]
        rw [h1, comm]
        simp only [mul_assoc]
        simp only [map_mul,mul_assoc]
        rfl
  refine ⟨⟨i,j⟩,b,a',e,w,upper_of_infinity_fixed b hb,?_⟩
  have htau : cuspRepresentative S U (⟨i,j⟩ : Cusp S U) * rationalLift F ζ hζ b = rationalLift F ζ hζ tau := by
    change rationalLift F ζ hζ σ * rationalLift F ζ hζ b = _
    rw [← KPMsActualAngularTransitionSource.rationalLift_mul]
    congr 1
    dsimp [cuspRepresentative, b, σ, tau, T]
    group
  rw [htau, hg, hρ]
  calc
    _ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a' *
        (((KPCuspGenuineMonodromy.central F ζ hζ ρ * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ tau) * c).val) := by
      rw [show KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a' =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPMsActualCuspSource.archRational F tau) *
          KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a from
          (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1 _ _]
      rw [Subgroup.coe_mul]
      let d := KPCuspGenuineMonodromy.central F ζ hζ ρ * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ tau
      change _ * d.val * (_ * c.val) = (_ * _) * (d.val * c.val)
      rw [mul_assoc, ← mul_assoc d.val, ← (insertion_commutes F ζ hζ a d).eq]
      group
    _ = _ := by
      have hfin' := congrArg Subtype.val hfin
      have hcentre : (KPCuspGenuineMonodromy.central F ζ hζ e).val = KPSmoothLocalQuotientCharts.centreMap F ζ hζ e := rfl
      simp only [Subgroup.coe_mul,hcentre] at hfin'
      simpa only [w,T,Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc] using
        congrArg (fun d : KPMsActualAngularSource.G F ζ hζ => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a' * d) hfin'

theorem finite_archProjection (w : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ w.val = 1 := by
  funext v
  rw [KPMsActualCuspSource.projection_compare]
  rw [MonoidHom.mem_ker.mp w.property]
  exact map_one _

theorem norm_centre (g : KPMsActualAngularSource.G F ζ hζ) (ε : rootsOfUnity 3 F) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
      (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) =
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ) g := by
  let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
  have hz : z.val.val = KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.centralRoot_formula F ζ hζ ε
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ z.val = 1 := by
    apply Units.val_injective
    apply NNReal.rpow_left_injective (show (1 / 6 : ℝ) ≠ 0 by norm_num)
    change (KPGlobalCenterRationalCharacter.nu F ζ hζ z.val : ℝ≥0) =
      (1 : ℝ≥0) ^ (1 / 6 : ℝ)
    rw [KPGlobalCenterRationalCharacter.nu_centralRoot]
    simp
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have he := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul F ζ hζ
    (nativeDatum F ζ hζ) z.val 0 g
  have hc := Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) g
  simpa only [hn, mul_one, hd, one_mul, hz, hc] using he

theorem offset_frame (j : Cusp S U) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U)) :
    KPMsAngularSourceRecipe.finiteOffset F ζ hζ (cuspRepresentative S U j)
      (((nativeAtlas F ζ hζ R P S U).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val) =
      cuspOffset F ζ hζ R P S U j := by
  have hu := u.property
  simp only [S.level_matching (cofinalLevel F ζ hζ U)] at hu
  obtain ⟨w, hw, hwu⟩ := hu
  have hp : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ u.val = 1 := by
    rw [← hwu]; exact finite_archProjection w
  have hz := finite_archProjection (KPCuspGenuineMonodromy.central F ζ hζ ε)
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
    (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) = 1 at hz
  have hf : KPMsAngularSourceRecipe.finiteComponent F ζ hζ
      ((cuspRepresentative S U j)⁻¹ *
        (((nativeAtlas F ζ hζ R P S U).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) =
      KPMsAngularSourceRecipe.finiteComponent F ζ hζ
        ((cuspRepresentative S U j)⁻¹ *
          ((nativeAtlas F ζ hζ R P S U).representative j.1).val) *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
    unfold KPMsAngularSourceRecipe.finiteComponent
    simp only [map_mul, hz, hp, mul_one]
    group
  apply Subtype.ext
  change ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
    (KPMsAngularSourceRecipe.finiteComponent F ζ hζ _) : ℝ≥0) : ℝ) = _
  rw [hf, KPShift81CoherentLevel.norm_right_level, norm_centre]
  rfl

theorem frame_norm (j : Cusp S U)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ U))
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F
      (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2)
      (KPCuspCharts.toArch F (p,t))) :
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
      ((cuspRepresentative S U j)⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S U).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) : ℝ≥0) : ℝ) =
      (cuspOffset F ζ hζ R P S U j).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  have he := S.height_normalized (cofinalLevel F ζ hζ U) j a p t ε u ha
  dsimp only at he
  rw [offset_frame S U j ε u] at he
  simpa only [KPMsAngularSourceRecipe.frame, mul_assoc] using he

theorem radius_eq_offset_modulus (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y)
    (x : X F ζ hζ) (hx : x ∈ cuspEnd S U j Y) :
    (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j)
      (cuspLift S U j Y x)).val = (cuspOffset F ζ hζ R P S U j).val *
        (nativeDisintegration F ζ hζ R P S U).modulus (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) := by
  have hg := cuspLift_frame S U j Y x hx
  obtain ⟨a,p,t,ε,u,ht,ha,he⟩ := hg.2
  have hm := spherical_modulus_of_cusp_basepoint S U j Y hY a p t ε u ht ha
  rw [← he, hg.1] at hm
  rw [hm]
  change ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
    ((cuspRepresentative S U j)⁻¹ * cuspLift S U j Y x) : ℝ≥0) : ℝ) = _
  rw [he]
  exact frame_norm S U j a p t ε u ha

theorem cuspRadius_continuousOn (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y) :
    ContinuousOn (fun x => (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) (cuspLift S U j Y x)).val) (cuspEnd S U j Y) := by
  letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hq : Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := continuous_quotient_mk'
  have hqo : IsOpenMap (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := isOpenMap_quotient_mk'_mul
  have hs : ∀ x ∈ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ '' fullCuspDomain S U j Y,
      cuspLift S U j Y x ∈ fullCuspDomain S U j Y ∧
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (cuspLift S U j Y x) = x := by
    intro x hx
    rw [quotientMap_image_fullCuspDomain S U j Y hY] at hx
    exact ⟨cuspLift_mem_fullCuspDomain S U j Y x hx, cuspLift_quotient S U j Y x⟩
  have hfi : ∀ a ∈ fullCuspDomain S U j Y, ∀ b ∈ fullCuspDomain S U j Y,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a =
        KPSmoothLocalQuotientCharts.quotientMap F ζ hζ b →
      (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) a).val =
        (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) b).val := by
    intro a ha b hb he
    obtain ⟨η,rfl⟩ := (full_quotient_eq_iff_rational_left a b).mp he
    obtain ⟨a₁,p₁,t₁,ε₁,u₁,ht₁,ha₁,he₁⟩ := ha
    obtain ⟨a₂,p₂,t₂,ε₂,u₂,ht₂,ha₂,he₂⟩ := hb
    have hfix := high_frame_transition_fixes_cusp S U j Y hY a₁ a₂ p₁ p₂ t₁ t₂
      ε₁ ε₂ u₁ u₂ ht₁ ht₂ ha₁ ha₂ η (he₁ ▸ he₂)
    let σ := ((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2
    obtain ⟨y,x,hupper⟩ := rational_upper_literal_factorization F ζ hζ (σ⁻¹ * η * σ)
      (KPMsActualAngularTransitionSource.cusp_fixing_upper F _ σ η
        (((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative_formula j.2) hfix)
    have hframe : (cuspRepresentative S U j)⁻¹ * (KPMsActualCuspSource.rationalLift F ζ hζ η * a) =
        ((KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ x) *
          ((cuspRepresentative S U j)⁻¹ * a) := by
      rw [← hupper, KPMsActualAngularTransitionSource.rationalLift_mul, KPMsActualAngularTransitionSource.rationalLift_mul, KPMsActualAngularTransitionSource.rationalLift_inv]
      dsimp [σ, cuspRepresentative]
      group
    change ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
      ((cuspRepresentative S U j)⁻¹ * a) : ℝ≥0) : ℝ) = _
    rw [show (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j)
      (KPMsActualCuspSource.rationalLift F ζ hζ η * a)).val =
      ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
        ((cuspRepresentative S U j)⁻¹ * (KPMsActualCuspSource.rationalLift F ζ hζ η * a)) : ℝ≥0) : ℝ) from rfl,
      hframe, KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul,
      KPGlobalTorusBorelNormTwistTransport.delta_rational, one_mul]
  have hf : Continuous (fun a : KPMsActualAngularSource.G F ζ hζ =>
      (framedRadius F ζ hζ (nativeDatum F ζ hζ) (cuspRepresentative S U j) a).val) :=
    (KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous
      F ζ hζ (nativeDatum F ζ hζ)).comp (by fun_prop)
  have hc := continuousOn_section_of_fiber_invariance hq hqo
    (isOpen_fullCuspDomain S U j Y) hs hf.continuousOn hfi
  rw [quotientMap_image_fullCuspDomain S U j Y hY] at hc
  exact hc

theorem fullCoordinate_continuousOn (j : Cusp S U) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y) :
    ContinuousOn (fullCoordinate F ζ hζ R P S U j Y)
      (cuspEnd S U j (Y / (cuspOffset F ζ hζ R P S U j).val)) :=
  cuspFullAngular_continuousOn S U j _ (hY j)

theorem modulus_continuousOn (j : Cusp S U) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S U) Y) :
    ContinuousOn (fun x => (nativeDisintegration F ζ hζ R P S U).modulus
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x)) (cuspEnd S U j Y) := by
  apply ((cuspRadius_continuousOn S U j Y hY).div_const
    (cuspOffset F ζ hζ R P S U j).val).congr
  intro x hx
  dsimp only
  rw [radius_eq_offset_modulus S U j Y hY x hx,
    mul_div_cancel_left₀ _ (ne_of_gt (cuspOffset F ζ hζ R P S U j).property)]

theorem cuspShell_measurable (j : Cusp S U) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y) :
    MeasurableSet (cuspShell F ζ hζ R P S U j Y) := by
  have hm := ((nativeDisintegration F ζ hζ R P S U).measurable_modulus.comp
    (P.continuous (S.atlasLevel (cofinalLevel F ζ hζ U))).measurable) (measurableSet_Ioc (a := Y / (cuspOffset F ζ hζ R P S U j).val)
      (b := 2 * Y / (cuspOffset F ζ hζ R P S U j).val))
  exact (cuspEnd_isOpen S U j _ (hY j)).measurableSet.inter hm

theorem fullCoordinate_aemeasurable (j : Cusp S U) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S U Y) :
    AEMeasurable (fullCoordinate F ζ hζ R P S U j Y)
      (R.quotientHaar.restrict (cuspShell F ζ hζ R P S U j Y)) := by
  letI : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  exact ((fullCoordinate_continuousOn S U j Y hY).mono Set.inter_subset_left).aemeasurable
    (cuspShell_measurable S U j Y hY)

theorem shell_reaches (S : NativeRecipe F ζ hζ R P)
    (U : KPMsActualAngularSource.Level F ζ hζ) (Y r₀ : ℝ)
    (hYpos : 0 < Y) (hY : OffsetAdmissible F ζ hζ R P S U Y)
    (hr : Y < r₀ ∧ r₀ < 2 * Y) (q : FullOmega F ζ hζ (nativeDatum F ζ hζ)) :
    ∃ (j : NativeCusp F ζ hζ R P S U) (x : X F ζ hζ),
      x ∈ cuspEnd S U j (Y / (cuspOffset F ζ hζ R P S U j).val) ∧
      Y / (cuspOffset F ζ hζ R P S U j).val <
        (nativeDisintegration F ζ hζ R P S U).modulus (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) ∧
      (nativeDisintegration F ζ hζ R P S U).modulus (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) <
        2 * Y / (cuspOffset F ζ hζ R P S U j).val ∧
      (nativeDisintegration F ζ hζ R P S U).modulus
        (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) =
          r₀ / (cuspOffset F ζ hζ R P S U j).val ∧
      fullCoordinate F ζ hζ R P S U j Y x = q := by
  obtain ⟨g,rfl⟩ := Quotient.mk_surjective q
  let B := (nativeDisintegration F ζ hζ R P S U).radial
  let r : KPMsFixedHaarDisintegration.Radius := ⟨r₀, lt_trans hYpos hr.1⟩
  let t₀ := KPGlobalTorusFunctionData.torusArchChart F ζ hζ (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
  let v := KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * g.val
  have hdelt : ((KPGlobalTorusFunctionData.delta F ζ hζ t₀ : ℝ≥0) : ℝ) = r.val := by
    change ((KPGlobalTorusFunctionData.ideleAbs F
      (KPGlobalTorusFunctionData.p F ζ hζ t₀) : ℝ≥0) : ℝ) = _
    rw [B.lift_ratio, B.ell_norm]
  have hvnorm : ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ) v : ℝ≥0) : ℝ) = r.val := by
    have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    have hm := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul F ζ hζ (nativeDatum F ζ hζ) t₀ 0 g.val
    simp only [hn, mul_one, g.property] at hm
    exact (congrArg (fun n : (ℝ≥0)ˣ => ((n : ℝ≥0) : ℝ)) hm).trans hdelt
  obtain ⟨j,b,a,ε,u,hb,he⟩ := finite_frame S U v
  obtain ⟨y,z,hb'⟩ := rational_upper_literal_factorization F ζ hζ b hb
  let σ := cuspRepresentative S U j
  let h := σ * rationalLift F ζ hζ b * v
  have hframe : σ⁻¹ * h = (KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ z * v := by
    dsimp only [h]
    rw [hb']
    group
  have hnorm : ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ) (σ⁻¹*h) : ℝ≥0) : ℝ) = r.val := by
    rw [hframe, KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul,
      KPGlobalTorusBorelNormTwistTransport.delta_rational, one_mul]
    exact hvnorm
  let Z := Y / (cuspOffset F ζ hζ R P S U j).val
  have hZ := hY j
  let σ₀ := ((nativeAtlas F ζ hζ R P S U).cuspAtlas j.1).representative j.2
  let c := (KPCuspCharts.toArchHomeomorph F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)).symm
    (KPCuspSiegel.action F σ₀⁻¹ (KPMsFixedHaarDisintegration.archBasepoint F a))
  have hc : KPMsFixedHaarDisintegration.archBasepoint F a = KPCuspSiegel.action F σ₀ (KPCuspCharts.toArch F c) := by
    have hc₀ : KPCuspCharts.toArch F c = KPCuspSiegel.action F σ₀⁻¹ (KPMsFixedHaarDisintegration.archBasepoint F a) :=
      (KPCuspCharts.toArchHomeomorph F (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex)).apply_symm_apply _
    rw [hc₀]
    exact (smul_inv_smul σ₀ _).symm
  have hnsource : r.val = (cuspOffset F ζ hζ R P S U j).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * c.2) := by
    apply hnorm.symm.trans
    dsimp only [h, σ]
    rw [he]
    exact frame_norm S U j a c.1 c.2 ε u hc
  have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex))
  have ht : KPMsFixedHaarDisintegration.logHeight (F := F) Z < c.2 := by
    rw [KPMsFixedHaarDisintegration.logHeight,div_lt_iff₀ hd]
    have hzexp : Z < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * c.2) := by
      apply (div_lt_iff₀ (cuspOffset F ζ hζ R P S U j).property).mpr
      rw [mul_comm, ← hnsource]
      exact hr.1
    rw [← Real.exp_log (show 0 < Z from hZ.1)] at hzexp
    simpa only [mul_comm] using Real.exp_lt_exp.mp hzexp
  have hh : h ∈ fullCuspDomain S U j Z := ⟨a,c.1,c.2,ε,u,ht,hc,he⟩
  let x := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ h
  have hx : x ∈ cuspEnd S U j Z := quotientMap_mem_cuspEnd_of_mem_fullCuspDomain S U j Z h hh
  have hbmem := cuspLift_mem_fullCuspDomain S U j Z x hx
  have heq : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ h =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (cuspLift S U j Z x) := (cuspLift_quotient S U j Z x).symm
  have hang := actual_full_frame_invariant S U j Z hZ h (cuspLift S U j Z x) hh hbmem heq
  have hm := spherical_modulus_of_cusp_basepoint S U j Z hZ a c.1 c.2 ε u ht hc
  rw [← he] at hm
  have hmod : (nativeDisintegration F ζ hζ R P S U).modulus
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) = r.val / (cuspOffset F ζ hζ R P S U j).val := by
    rw [hm, hnsource, mul_div_cancel_left₀ _ (ne_of_gt (cuspOffset F ζ hζ R P S U j).property)]
  have hang₀ := framedFullAngular_upper_transition F ζ hζ (nativeDatum F ζ hζ) B σ (σ*v) h y z (by
    simpa only [inv_mul_cancel_left] using hframe)
  have hangg : framedFullAngular F ζ hζ (nativeDatum F ζ hζ) B σ (σ*v) = Quotient.mk _ g := by
    unfold framedFullAngular framedNormOne framedNormalization
    congr 1
    apply Subtype.ext
    simp only [inv_mul_cancel_left]
    have hr₀ : framedRadius F ζ hζ (nativeDatum F ζ hζ) σ (σ*v) = r := by
      apply Subtype.ext
      simpa only [framedRadius,inv_mul_cancel_left] using hvnorm
    change (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot
      (framedRadius F ζ hζ (nativeDatum F ζ hζ) σ (σ*v)))⁻¹ * v = g.val
    rw [hr₀]
    dsimp [v]
    group
  have hfull : fullCoordinate F ζ hζ R P S U j Y x = Quotient.mk _ g := by
    change framedFullAngular F ζ hζ (nativeDatum F ζ hζ) B σ (cuspLift S U j Z x) = _
    exact hang.symm.trans (hang₀.trans hangg)
  refine ⟨j, x, hx, ?_, ?_, hmod, hfull⟩
  · rw [hmod]; exact (div_lt_div_iff_of_pos_right (cuspOffset F ζ hζ R P S U j).property).mpr hr.1
  · rw [hmod]; exact (div_lt_div_iff_of_pos_right (cuspOffset F ζ hζ R P S U j).property).mpr hr.2

theorem cusp_mass_pos (j : Cusp S U) (Y : ℝ)
    (hYpos : 0 < Y) (hY : OffsetAdmissible F ζ hζ R P S U Y)
    (E : Set (FullOmega F ζ hζ (nativeDatum F ζ hζ))) (hE : IsOpen E)
    (x : X F ζ hζ)
    (hx : x ∈ cuspEnd S U j (Y / (cuspOffset F ζ hζ R P S U j).val))
    (hr : Y / (cuspOffset F ζ hζ R P S U j).val <
        (nativeDisintegration F ζ hζ R P S U).modulus (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) ∧
      (nativeDisintegration F ζ hζ R P S U).modulus (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) x) <
        2 * Y / (cuspOffset F ζ hζ R P S U j).val)
    (hEx : fullCoordinate F ζ hζ R P S U j Y x ∈ E) :
    0 < (ENNReal.ofReal (2 * Y) • Measure.map (fullCoordinate F ζ hζ R P S U j Y)
      (R.quotientHaar.restrict (cuspShell F ζ hζ R P S U j Y))) E := by
  letI : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  letI : R.quotientHaar.IsOpenPosMeasure :=
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1
  let Z := Y / (cuspOffset F ζ hζ R P S U j).val
  let m := fun z => (nativeDisintegration F ζ hζ R P S U).modulus
    (P.projection (S.atlasLevel (cofinalLevel F ζ hζ U)) z)
  let A := cuspEnd S U j Z ∩ m ⁻¹' Set.Ioo Z (2 * Y / (cuspOffset F ζ hζ R P S U j).val)
  have hopenA : IsOpen A := (modulus_continuousOn S U j Z (hY j)).isOpen_inter_preimage
    (cuspEnd_isOpen S U j Z (hY j)) isOpen_Ioo
  let T := A ∩ fullCoordinate F ζ hζ R P S U j Y ⁻¹' E
  have hopen : IsOpen T := ((fullCoordinate_continuousOn S U j Y hY).mono
    Set.inter_subset_left).isOpen_inter_preimage hopenA hE
  have hpos : 0 < R.quotientHaar T := hopen.measure_pos _ ⟨x, ⟨⟨hx, hr⟩, hEx⟩⟩
  have hsub : T ⊆ fullCoordinate F ζ hζ R P S U j Y ⁻¹' E ∩ cuspShell F ζ hζ R P S U j Y := by
    rintro z ⟨⟨hz, hzr⟩, hzE⟩
    exact ⟨hzE, hz, hzr.1, hzr.2.le⟩
  rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable
    (fullCoordinate_aemeasurable S U j Y hY) hE.measurableSet,
    Measure.restrict_apply' (cuspShell_measurable S U j Y hY), smul_eq_mul]
  exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hYpos),
    lt_of_lt_of_le hpos (measure_mono hsub)⟩

end FullSupportGeometry

open KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)

theorem full_shell_reaches (Y r : ℝ) (hYpos : 0 < Y)
    (hY : OffsetAdmissible F ζ hζ R P S V Y) (hr : Y < r ∧ r < 2 * Y)
    (q : FullOmega F ζ hζ (nativeDatum F ζ hζ)) :
    ∃ (j : NativeCusp F ζ hζ R P S V) (x : KPSmoothLocalQuotientCharts.X F ζ hζ),
      x ∈ cuspShell F ζ hζ R P S V j Y ∧
      (nativeDisintegration F ζ hζ R P S V).modulus
        (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) =
          r / (cuspOffset F ζ hζ R P S V j).val ∧
      fullCoordinate F ζ hζ R P S V j Y x = q := by
  obtain ⟨j,x,hx,hlo,hhi,hm,hq⟩ := FullSupportGeometry.shell_reaches S V Y r hYpos hY hr q
  exact ⟨j,x,⟨hx,hlo,hhi.le⟩,hm,hq⟩

theorem fullShell_support (Y : ℝ) (hY : OffsetAdmissible F ζ hζ R P S V Y) :
    (fullShell F ζ hζ R P S V Y).IsOpenPosMeasure := by
  refine ⟨?_⟩
  intro E hE hNE
  obtain ⟨q,hq⟩ := hNE
  obtain ⟨g,hg⟩ := Quotient.mk_surjective q
  obtain ⟨j₀,b,a,ε,u,hb,he⟩ := FullSupportGeometry.finite_frame S V g.val
  have hYpos : 0 < Y := (div_pos_iff_of_pos_right (cuspOffset F ζ hζ R P S V j₀).property).mp (hY j₀).1
  obtain ⟨j,x,hx,hlo,hhi,hm,hxq⟩ := FullSupportGeometry.shell_reaches S V Y (3*Y/2)
    hYpos hY (by constructor <;> linarith) q
  have hp := FullSupportGeometry.cusp_mass_pos S V j Y hYpos hY E hE x hx ⟨hlo,hhi⟩ (hxq.symm ▸ hq)
  apply ne_of_gt
  apply lt_of_lt_of_le hp
  rw [fullShell, Measure.finsetSum_apply]
  exact Finset.single_le_sum
    (f := fun k : NativeCusp F ζ hζ R P S V =>
      (ENNReal.ofReal (2 * Y) • Measure.map (fullCoordinate F ζ hζ R P S V k Y)
        (R.quotientHaar.restrict (cuspShell F ζ hζ R P S V k Y))) E)
    (fun k _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ j)

end DedekindZetaZeroFree.KPMsNativeOffsetMass

namespace DedekindZetaZeroFree.KPMsNativeOffsetMass.FullSupportProof
open KPMsActualAngularSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}

theorem finiteOffset_right_center_level
    (S : NativeRecipe F ζ hζ R P)
    (V : KPMsActualAngularSource.Level F ζ hζ) (σ f : KPMsActualAngularSource.G F ζ hζ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    KPMsAngularSourceRecipe.finiteOffset F ζ hζ σ
      (f * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val) =
        KPMsAngularSourceRecipe.finiteOffset F ζ hζ σ f := by
  have hu : u.val ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    have hm := u.property
    simp only [S.level_matching (cofinalLevel F ζ hζ V)] at hm
    obtain ⟨v,hv,he⟩ := hm
    rw [← he]
    exact v.property
  have hp := FullSupportGeometry.finite_archProjection (ζ := ζ) (hζ := hζ) ⟨u.val,hu⟩
  have he := FullSupportGeometry.finite_archProjection (ζ := ζ) (hζ := hζ)
    (KPCuspGenuineMonodromy.central F ζ hζ ε)
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
    (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) = 1 at he
  have hf : KPMsAngularSourceRecipe.finiteComponent F ζ hζ
      (σ⁻¹ * (f * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) =
        KPMsAngularSourceRecipe.finiteComponent F ζ hζ (σ⁻¹*f) *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
    unfold KPMsAngularSourceRecipe.finiteComponent
    simp only [map_mul,he,hp,mul_one]
    group
  apply Subtype.ext
  change ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (nativeDatum F ζ hζ)
    (KPMsAngularSourceRecipe.finiteComponent F ζ hζ _) : ℝ≥0) : ℝ) = _
  rw [hf,KPShift81CoherentLevel.norm_right_level,FullSupportGeometry.norm_centre]
  rfl

end DedekindZetaZeroFree.KPMsNativeOffsetMass.FullSupportProof

end
