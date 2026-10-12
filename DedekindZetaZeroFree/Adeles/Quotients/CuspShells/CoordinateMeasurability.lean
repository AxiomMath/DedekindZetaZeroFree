module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.TransitionsAndCoordinateDescent
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.Definitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology ENNReal NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P) (V : KPMsActualAngularSource.Level F ζ hζ)

namespace CoordinateProof
open KPMsActualAngularSource KPMsActualCuspSource
open KPMsActualAngularDomainSource KPMsActualAngularTransitionSource KPMsActualAngularDescentSource
open KPMsResidualTailRestoration.SharpConstantTerm
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
open KPAdelicCoverRestrictedProduct

 def nativeFullDomain (j : NativeCusp F ζ hζ R P S V) (Y : ℝ) : Set (KPMsActualAngularSource.G F ζ hζ) :=
  {g | ∃ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
    KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
    KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)) ∧
    g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val}

 theorem nativeDomainProjects
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (g : KPMsActualAngularSource.G F ζ hζ) (hg : g ∈ nativeFullDomain F ζ hζ R P S V j Y) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g ∈ KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P) (S.atlasLevel (cofinalLevel F ζ hζ V)) j Y := by
  obtain ⟨a,p,t,ε,u,ht,ha,rfl⟩ := hg
  have hu : (u.val : KPMsActualAngularSource.G F ζ hζ) ∈ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map
      (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
    simpa only [← S.level_matching (cofinalLevel F ζ hζ V)] using u.property
  obtain ⟨v,hv,hu⟩ := hu
  let v' : (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup := ⟨v,hv⟩
  let c : KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
    (nativeAtlas F ζ hζ R P S V).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * v
  have he : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
    rw [← hu]
    simp only [c, Subgroup.coe_mul, mul_assoc]
    rfl
  rw [he]
  unfold KPMsActualCuspSource.cuspEnd
  simp only [Set.mem_preimage]
  rw [P.formula]
  have hc : (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V)))
      (KPMsFixedHaarDisintegration.archBasepoint F a,c)) =
      Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,
        (nativeAtlas F ζ hζ R P S V).representative j.1) := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨1, ε, v', by simp, ?_⟩
    simp only [map_one, one_mul]
    change c = KPCuspGenuineMonodromy.central F ζ hζ ε *
      (nativeAtlas F ζ hζ R P S V).representative j.1 * v
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

private theorem nativeArchConstraint
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (a : KPSmoothActualFlowData.GInfinity F) :
    (∃ (p : KPCuspCharts.Cross F) (t : ℝ),
      KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      KPMsFixedHaarDisintegration.archBasepoint F a =
        KPCuspSiegel.action F
          (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (p,t))) ↔
    KPMsFixedHaarDisintegration.archBasepoint F a ∈
      KPCuspSiegel.highCusp F
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
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

private theorem nativeArchOpen
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ) :
    IsOpen {a : KPSmoothActualFlowData.GInfinity F |
      ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t))} := by
  have he : {a : KPSmoothActualFlowData.GInfinity F |
      ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t))} =
      KPMsFixedHaarDisintegration.archBasepoint F ⁻¹'
        KPCuspSiegel.highCusp F
          (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
          (KPMsFixedHaarDisintegration.logHeight (F := F) Y) := by
    ext a
    exact nativeArchConstraint F ζ hζ R P S V j Y a
  rw [he]
  exact (KPCuspSiegel.isOpen_highCusp F _ _).preimage continuous_archBasepoint

 def nativeFiniteDomain (j : NativeCusp F ζ hζ R P S V) : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
  ⋃ ε : rootsOfUnity 3 F,
    (fun u => (nativeAtlas F ζ hζ R P S V).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * u) ''
        ((S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

private theorem nativeFiniteOpen (j : NativeCusp F ζ hζ R P S V) :
    IsOpen (nativeFiniteDomain F ζ hζ R P S V j) := by
  letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply isOpen_iUnion
  intro ε
  exact (Homeomorph.mulLeft _).isOpenMap _ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.isOpen

private theorem nativeDomainProduct (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* KPMsActualAngularSource.G F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) :
    nativeFullDomain F ζ hζ R P S V j Y = e ''
      ({a | ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t))} ×ˢ nativeFiniteDomain F ζ hζ R P S V j) := by
  ext g
  constructor
  · rintro ⟨a,p,t,ε,u,ht,ha,hg⟩
    have hu : (u.val : KPMsActualAngularSource.G F ζ hζ) ∈ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
      simpa only [← S.level_matching (cofinalLevel F ζ hζ V)] using u.property
    obtain ⟨v,hv,hu⟩ := hu
    refine ⟨(a, (nativeAtlas F ζ hζ R P S V).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * v), ⟨⟨p,t,ht,ha⟩, ?_⟩, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨ε, ⟨v,hv,rfl⟩⟩
    · rw [he, hg, ← hu]
      simp only [Subgroup.coe_mul, mul_assoc]
      rfl
  · rintro ⟨⟨a,c⟩,⟨⟨p,t,ht,ha⟩,hc⟩,rfl⟩
    obtain ⟨ε,v,hv,hc⟩ := Set.mem_iUnion.mp hc
    have hu : v.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V) := by
      rw [S.level_matching (cofinalLevel F ζ hζ V)]
      exact ⟨v,hv,rfl⟩
    refine ⟨a,p,t,ε,⟨v.val,hu⟩,ht,ha,?_⟩
    change (nativeAtlas F ζ hζ R P S V).representative j.1 *
      KPCuspGenuineMonodromy.central F ζ hζ ε * v = c at hc
    rw [he, ← hc]
    simp only [Subgroup.coe_mul, mul_assoc]
    rfl

 theorem nativeDomainOpen (j : NativeCusp F ζ hζ R P S V) (Y : ℝ) :
    IsOpen (nativeFullDomain F ζ hζ R P S V j Y) := by
  obtain ⟨e,he⟩ := product_splitting (F := F) (ζ := ζ) (hζ := hζ)
  rw [nativeDomainProduct F ζ hζ R P S V j Y e he]
  exact e.toHomeomorph.isOpenMap _
    ((nativeArchOpen F ζ hζ R P S V j Y).prod (nativeFiniteOpen F ζ hζ R P S V j))

private theorem nativeLevelProjection (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ u.val ∈
      (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ) := by
  have hu : u.val ∈ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map
      (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
    simpa only [← S.level_matching (cofinalLevel F ζ hζ V)] using u.property
  obtain ⟨w, hw, hwu⟩ := hu
  exact ⟨w, hw, congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hwu⟩

private theorem nativeFrameComponent
    (j : NativeCusp F ζ hζ R P S V)
    (a₁ a₂ : KPSmoothActualFlowData.GInfinity F)
    (ε₁ ε₂ : rootsOfUnity 3 F)
    (u₁ u₂ : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (γ : KPCuspArithmetic.PGL2 F)
    (he : rationalLift F ζ hζ γ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₁ *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₁ * u₁.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₂ *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₂ * u₂.val) :
    γ ∈ KPCuspGenuineMonodromy.Component F ζ hζ (S.atlasLevel (cofinalLevel F ζ hζ V))
      ((nativeAtlas F ζ hζ R P S V).representative j.1) := by
  have hp := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) he
  simp only [map_mul, KPMsActualCuspSource.finiteProjection_rationalLift, KPMsActualCuspSource.finiteProjection_insertion,
    KPMsActualAngularTransitionSource.finiteProjection_centre, one_mul, mul_one] at hp
  let c := KPCuspGenuineMonodromy.finiteBase F ζ hζ
    ((nativeAtlas F ζ hζ R P S V).representative j.1)
  let w := KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₂.val *
    (KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₁.val)⁻¹
  change KPFiniteComponents.diagonal F γ ∈
    (((S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
      (MulAut.conj c).toMonoidHom)
  refine ⟨w, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (nativeLevelProjection F ζ hζ R P S V u₂)
      (Subgroup.inv_mem _ (nativeLevelProjection F ζ hζ R P S V u₁))
  · change c * w * c⁻¹ = KPFiniteComponents.diagonal F γ
    change KPFiniteComponents.diagonal F γ * (c * _) = c * _ at hp
    dsimp [w]
    calc
      _ = (c * KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₂.val) *
          (c * KPCuspGenuineMonodromy.finiteProjection F ζ hζ u₁.val)⁻¹ := by group
      _ = KPFiniteComponents.diagonal F γ := by rw [← hp]; group

private theorem nativeHighTransition
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (a₁ a₂ : KPSmoothActualFlowData.GInfinity F)
    (p₁ p₂ : KPCuspCharts.Cross F) (t₁ t₂ : ℝ)
    (ε₁ ε₂ : rootsOfUnity 3 F)
    (u₁ u₂ : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (ht₁ : KPMsFixedHaarDisintegration.logHeight (F := F) Y < t₁)
    (ht₂ : KPMsFixedHaarDisintegration.logHeight (F := F) Y < t₂)
    (ha₁ : KPMsFixedHaarDisintegration.archBasepoint F a₁ =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p₁,t₁)))
    (ha₂ : KPMsFixedHaarDisintegration.archBasepoint F a₂ =
      KPCuspSiegel.action F (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p₂,t₂)))
    (γ : KPCuspArithmetic.PGL2 F)
    (he : rationalLift F ζ hζ γ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₁ *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₁ * u₁.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a₂ *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε₂ * u₂.val) :
    γ • (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).cusp j.2) =
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).cusp j.2) := by
  let c := (nativeAtlas F ζ hζ R P S V).representative j.1
  have hlevel_arch (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)) :
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ u.val = 1 := by
    have hu : u.val ∈ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
      simpa only [← S.level_matching (cofinalLevel F ζ hζ V)] using u.property
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
  have hγ := nativeFrameComponent F ζ hζ R P S V j a₁ a₂ ε₁ ε₂ u₁ u₂ γ he
  apply atlas_high_overlap_stabilizes_cusp (nativeAtlas F ζ hζ R P S V) j Y hY
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

 theorem nativeFrameInvariant (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V) Y)
    (a b : KPMsActualAngularSource.G F ζ hζ) (ha : a ∈ nativeFullDomain F ζ hζ R P S V j Y) (hb : b ∈ nativeFullDomain F ζ hζ R P S V j Y)
    (he : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ b) :
    framedFullAngular F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S V).radial
        (KPMsActualCuspSource.rationalLift F ζ hζ (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)) a =
      framedFullAngular F ζ hζ (nativeDatum F ζ hζ) (nativeDisintegration F ζ hζ R P S V).radial
        (KPMsActualCuspSource.rationalLift F ζ hζ (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)) b := by
  obtain ⟨η,rfl⟩ := (full_quotient_eq_iff_rational_left a b).mp he
  obtain ⟨a₁,p₁,t₁,ε₁,u₁,ht₁,ha₁,he₁⟩ := ha
  obtain ⟨a₂,p₂,t₂,ε₂,u₂,ht₂,ha₂,he₂⟩ := hb
  have hfix := nativeHighTransition F ζ hζ R P S V j Y hY a₁ a₂ p₁ p₂ t₁ t₂
    ε₁ ε₂ u₁ u₂ ht₁ ht₂ ha₁ ha₂ η (he₁ ▸ he₂)
  let σ := ((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2
  obtain ⟨y,x,hupper⟩ := rational_upper_literal_factorization F ζ hζ (σ⁻¹ * η * σ)
    (KPMsActualAngularTransitionSource.cusp_fixing_upper F _ σ η
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative_formula j.2) hfix)
  apply Eq.symm
  apply framedFullAngular_upper_transition F ζ hζ (nativeDatum F ζ hζ)
    (nativeDisintegration F ζ hζ R P S V).radial (KPMsActualCuspSource.rationalLift F ζ hζ (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)) a _ y x
  rw [← hupper, KPMsActualAngularTransitionSource.rationalLift_mul, KPMsActualAngularTransitionSource.rationalLift_mul, KPMsActualAngularTransitionSource.rationalLift_inv]
  dsimp [σ]
  group

 theorem actualFrame_spec (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ)
    (hx : x ∈ KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j (Y / (cuspOffset F ζ hζ R P S V j).val)) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (actualFrame F ζ hζ R P S V j Y x) = x ∧
      actualFrame F ζ hζ R P S V j Y x ∈ nativeFullDomain F ζ hζ R P S V j
        (Y / (cuspOffset F ζ hζ R P S V j).val) := by
  rw [actualFrame, dif_pos hx]
  exact (Classical.choose_spec (KPMsActualCuspSource.cusp_lift_exists
    (H := nativeFamily F ζ hζ R P) (S.atlasLevel (cofinalLevel F ζ hζ V))
    (S.level_matching (cofinalLevel F ζ hζ V)) j _ x hx)).2

 theorem nativeDomainImage (j : NativeCusp F ζ hζ R P S V) (Y : ℝ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ '' nativeFullDomain F ζ hζ R P S V j
      (Y / (cuspOffset F ζ hζ R P S V j).val) =
    KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j (Y / (cuspOffset F ζ hζ R P S V j).val) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact nativeDomainProjects F ζ hζ R P S V j _ g hg
  · intro x hx
    have hf := actualFrame_spec F ζ hζ R P S V j Y x hx
    exact ⟨actualFrame F ζ hζ R P S V j Y x,hf.2,hf.1⟩

 theorem fullCoordinate_continuousOn_end
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y) :
    ContinuousOn (fullCoordinate F ζ hζ R P S V j Y)
      (KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
        (S.atlasLevel (cofinalLevel F ζ hζ V)) j (Y / (cuspOffset F ζ hζ R P S V j).val)) := by
  letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let q := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
  let Z := Y / (cuspOffset F ζ hζ R P S V j).val
  have hq : Continuous q := continuous_quotient_mk'
  have hqo : IsOpenMap q := isOpenMap_quotient_mk'_mul
  have hs : ∀ x ∈ q '' nativeFullDomain F ζ hζ R P S V j Z,
      actualFrame F ζ hζ R P S V j Y x ∈ nativeFullDomain F ζ hζ R P S V j Z ∧
      q (actualFrame F ζ hζ R P S V j Y x) = x := by
    intro x hx
    rw [nativeDomainImage F ζ hζ R P S V j Y] at hx
    exact ⟨(actualFrame_spec F ζ hζ R P S V j Y x hx).2,
      (actualFrame_spec F ζ hζ R P S V j Y x hx).1⟩
  have hc := continuousOn_section_of_fiber_invariance hq hqo
    (nativeDomainOpen F ζ hζ R P S V j Z) hs
    (framedFullAngular_continuous F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ R P S V).radial
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))).continuousOn
    (fun a ha b hb he => nativeFrameInvariant F ζ hζ R P S V j Z (hY j) a b ha hb he)
  rw [nativeDomainImage F ζ hζ R P S V j Y] at hc
  exact hc

end CoordinateProof

theorem fullCoordinate_aemeasurable
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y) :
    AEMeasurable (fullCoordinate F ζ hζ R P S V j Y)
      (R.quotientHaar.restrict (cuspShell F ζ hζ R P S V j Y)) := by
  have hc := CoordinateProof.fullCoordinate_continuousOn_end F ζ hζ R P S V j Y hY
  letI : BorelSpace (KPMsActualAngularSource.FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  have he : IsOpen (KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j (Y / (cuspOffset F ζ hζ R P S V j).val)) := by
    rw [← CoordinateProof.nativeDomainImage F ζ hζ R P S V j Y]
    letI : IsTopologicalGroup (KPMsActualAngularSource.G F ζ hζ) :=
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    exact isOpenMap_quotient_mk'_mul _ (CoordinateProof.nativeDomainOpen F ζ hζ R P S V j _)
  exact (hc.aemeasurable he.measurableSet).mono_set (fun _ hx => hx.1)

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
