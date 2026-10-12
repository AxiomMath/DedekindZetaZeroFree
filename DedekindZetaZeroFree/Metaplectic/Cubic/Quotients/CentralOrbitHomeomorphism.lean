module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RationalSplitting.ArchimedeanFiniteFactorization
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspDomainOpenness
public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.CoveredSphericalSpaces

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison

open KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : CompactOpenLevel (FiniteCover F ζ hζ))

 theorem doubleCoset_open {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ K : Subgroup G) : IsOpenMap (DoubleCoset.mk Γ K) := by
  intro s hs
  have hq : IsQuotientMap (DoubleCoset.mk Γ K) := isQuotientMap_quotient_mk'
  rw [← hq.isCoinducing.isOpen_preimage]
  have heq : DoubleCoset.mk Γ K ⁻¹' (DoubleCoset.mk Γ K '' s) =
      ⋃ (γ : Γ) (k : K), (fun x : G => (γ : G) * x * (k : G)) '' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, he⟩
      obtain ⟨γ, hγ, k, hk, rfl⟩ := DoubleCoset.eq.mp he
      exact ⟨⟨γ, hγ⟩, ⟨k, hk⟩, y, hy, rfl⟩
    · rintro ⟨γ, k, y, hy, rfl⟩
      exact ⟨y, hy, DoubleCoset.eq.mpr ⟨γ, γ.property, k, k.property, rfl⟩⟩
  rw [heq]
  exact isOpen_iUnion fun γ => isOpen_iUnion fun k =>
    ((Homeomorph.mulLeft (γ : G)).trans (Homeomorph.mulRight (k : G))).isOpenMap s hs

 def finiteEquiv : FiniteCover F ζ hζ ≃ₜ*
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ where
  toMulEquiv := MulEquiv.subgroupCongr
    (KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_finiteSubgroup_eq F ζ hζ).symm
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

 def productEquiv : (KPSmoothActualFlowData.GInfinity F × FiniteCover F ζ hζ) ≃ₜ*
    ActualCover F ζ hζ :=
  (show (KPSmoothActualFlowData.GInfinity F × FiniteCover F ζ hζ) ≃ₜ*
      (KPSmoothActualFlowData.GInfinity F × PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) from
    { toMulEquiv := (MulEquiv.refl _).prodCongr (finiteEquiv F ζ hζ).toMulEquiv
      continuous_toFun := continuous_fst.prodMk ((finiteEquiv F ζ hζ).continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk ((finiteEquiv F ζ hζ).symm.continuous.comp continuous_snd) }).trans
    (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose

 theorem productEquiv_apply (a : KPSmoothActualFlowData.GInfinity F)
    (c : FiniteCover F ζ hζ) : productEquiv F ζ hζ (a, c) =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c := by
  exact (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.1 a
    (finiteEquiv F ζ hζ c)

 theorem K_U_eq : K_U F ζ hζ U =
    ((KPContSectorArchSphericalFibers.KInfinity F).prod U.toOpenSubgroup.toSubgroup).map
      (productEquiv F ζ hζ).toMonoidHom := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact ⟨(a, 1), ⟨ha, U.toOpenSubgroup.one_mem⟩,
        by change productEquiv F ζ hζ (a, 1) = _
           rw [productEquiv_apply]; simp⟩
    · exact ⟨(1, c), ⟨(KPContSectorArchSphericalFibers.KInfinity F).one_mem, hc⟩,
        by change productEquiv F ζ hζ (1, c) = _
           have h := (productEquiv_apply F ζ hζ 1 c)
           have h1 := productEquiv_apply F ζ hζ 1 1
           have hi : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ 1 = 1 := by
             change productEquiv F ζ hζ (1 : KPSmoothActualFlowData.GInfinity F × FiniteCover F ζ hζ) = _ at h1
             rw [map_one] at h1
             simpa using h1.symm
           simpa [hi] using h⟩
  · rintro g ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩
    change productEquiv F ζ hζ (a, c) ∈ K_U F ζ hζ U
    rw [productEquiv_apply]
    apply Subgroup.mul_mem
    · exact Subgroup.subset_closure (Set.mem_union_left _ ⟨a, ha, rfl⟩)
    · exact Subgroup.subset_closure (Set.mem_union_right _ ⟨c, hc, rfl⟩)

 theorem K_U_compact : IsCompact (K_U F ζ hζ U : Set (ActualCover F ζ hζ)) := by
  rw [K_U_eq]
  change IsCompact ((productEquiv F ζ hζ) ''
    ((KPContSectorArchSphericalFibers.KInfinity F : Set _) ×ˢ (U.toOpenSubgroup : Set _)))
  exact ((KPContSectorArchSphericalFibers.KInfinity_compact F ζ hζ).prod U.isCompact).image
    (productEquiv F ζ hζ).continuous

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
open KPContinuation.RationalArchFiniteSplitting

private theorem archBasepoint_rational (σ : KPCuspArithmetic.PGL2 F)
    (a : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F (archRational σ * a) =
      σ • KPMsFixedHaarDisintegration.archBasepoint F a := by
  rw [archBasepoint_mul, archRational_action]
  rfl

private theorem productEquiv_rational (σ : KPCuspArithmetic.PGL2 F) :
    productEquiv F ζ hζ (archRational σ, KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ) =
      KPMsClearedTruncationL2.rationalLift F ζ hζ σ := by
  rw [productEquiv_apply, rationalLift_product]

 theorem relation_comparison (a b : KPSmoothActualFlowData.GInfinity F)
    (c d : FiniteCover F ζ hζ) :
    DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U) (productEquiv F ζ hζ (a,c)) =
      DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U) (productEquiv F ζ hζ (b,d)) ↔
    (coveredRelation F ζ hζ U)
      (KPMsFixedHaarDisintegration.archBasepoint F a,c)
      (KPMsFixedHaarDisintegration.archBasepoint F b,d) := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨g, hg, k, hk, he⟩
    obtain ⟨σ, rfl⟩ : ∃ σ, KPMsClearedTruncationL2.rationalLift F ζ hζ σ = g := by
      change g ∈ (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ : Set _) at hg
      rw [rationalSubgroup_eq_lift_range] at hg
      exact hg
    rw [K_U_eq] at hk
    obtain ⟨⟨t,u⟩, ⟨ht,hu⟩, rfl⟩ := hk
    change productEquiv F ζ hζ (b,d) =
      KPMsClearedTruncationL2.rationalLift F ζ hζ σ *
      productEquiv F ζ hζ (a,c) * productEquiv F ζ hζ (t,u) at he
    rw [← productEquiv_rational, ← map_mul, ← map_mul] at he
    have he' := (productEquiv F ζ hζ).injective he
    have ha := congrArg Prod.fst he'
    have hc := congrArg Prod.snd he'
    change b = (archRational σ * a) * t at ha
    change d = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ * c * u at hc
    refine ⟨σ, ⟨u,hu⟩, ?_, hc⟩
    have hf := (KPContSectorArchSphericalFibers.archBasepoint_eq_iff F
      (archRational σ * a) b).mpr ⟨⟨t,ht⟩,ha⟩
    exact hf.symm.trans (archBasepoint_rational F σ a)
  · rintro ⟨σ,u,hx,hc⟩
    have hf : KPMsFixedHaarDisintegration.archBasepoint F (archRational σ * a) =
        KPMsFixedHaarDisintegration.archBasepoint F b := by
      rw [archBasepoint_rational]
      exact hx.symm
    obtain ⟨t,ht⟩ := (KPContSectorArchSphericalFibers.archBasepoint_eq_iff F _ _).mp hf
    refine ⟨KPMsClearedTruncationL2.rationalLift F ζ hζ σ, ?_,
      productEquiv F ζ hζ (t,u), ?_, ?_⟩
    · change KPMsClearedTruncationL2.rationalLift F ζ hζ σ ∈
        (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ : Set _)
      rw [rationalSubgroup_eq_lift_range]
      exact ⟨σ,rfl⟩
    · rw [K_U_eq]
      exact ⟨(t,u), ⟨t.property,u.property⟩, rfl⟩
    · rw [← productEquiv_rational, ← map_mul, ← map_mul]
      apply congrArg (productEquiv F ζ hζ)
      apply Prod.ext ht hc
 def presentationMap (g : ActualCover F ζ hζ) : CoveredSpherical F ζ hζ U :=
  Quotient.mk (coveredRelation F ζ hζ U)
    (KPMsFixedHaarDisintegration.archBasepoint F ((productEquiv F ζ hζ).symm g).1,
      ((productEquiv F ζ hζ).symm g).2)

 theorem presentationMap_product (a : KPSmoothActualFlowData.GInfinity F)
    (c : FiniteCover F ζ hζ) :
    presentationMap F ζ hζ U (productEquiv F ζ hζ (a,c)) =
      Quotient.mk (coveredRelation F ζ hζ U)
        (KPMsFixedHaarDisintegration.archBasepoint F a,c) := by
  simp [presentationMap]

 def sectionMap (p : SymmetricSpace F × FiniteCover F ζ hζ) : CoveredActual F ζ hζ U :=
  DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U)
    (productEquiv F ζ hζ (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ p.1,p.2))

def e : CoveredActual F ζ hζ U ≃ₜ CoveredSpherical F ζ hζ U where
  toFun := Quotient.lift (presentationMap F ζ hζ U) (by
    intro g h he
    obtain ⟨⟨a,c⟩,rfl⟩ := (productEquiv F ζ hζ).surjective g
    obtain ⟨⟨b,d⟩,rfl⟩ := (productEquiv F ζ hζ).surjective h
    rw [presentationMap_product, presentationMap_product]
    apply Quotient.sound
    exact (relation_comparison F ζ hζ U a b c d).mp (Quotient.sound he))
  invFun := Quotient.lift (sectionMap F ζ hζ U) (by
    intro p q he
    apply (relation_comparison F ζ hζ U _ _ _ _).mpr
    simpa only [KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection] using he)
  left_inv := by
    intro y
    refine Quotient.inductionOn y (fun g => ?_)
    obtain ⟨⟨a,c⟩,rfl⟩ := (productEquiv F ζ hζ).surjective g
    change Quotient.lift (sectionMap F ζ hζ U) _
      (presentationMap F ζ hζ U (productEquiv F ζ hζ (a,c))) = _
    rw [presentationMap_product]
    change sectionMap F ζ hζ U
      (KPMsFixedHaarDisintegration.archBasepoint F a,c) = _
    apply (relation_comparison F ζ hζ U _ _ _ _).mpr
    rw [KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  right_inv := by
    intro y
    refine Quotient.inductionOn y (fun p => ?_)
    change presentationMap F ζ hζ U
      (productEquiv F ζ hζ (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ p.1,p.2)) = _
    rw [presentationMap_product, KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  continuous_toFun := by
    apply Continuous.quotient_lift
    apply continuous_quotient_mk'.comp
    exact ((KPContSectorArchSphericalFibers.archBasepoint_continuous F).comp
      (continuous_fst.comp (productEquiv F ζ hζ).symm.continuous)).prodMk
      (continuous_snd.comp (productEquiv F ζ hζ).symm.continuous)
  continuous_invFun := by
    apply Continuous.quotient_lift
    apply continuous_quotient_mk'.comp
    exact (productEquiv F ζ hζ).continuous.comp
      (((KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp continuous_fst).prodMk
        continuous_snd)

theorem e_mk (a : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ) :
    e F ζ hζ U
      (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U)
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          (c : ActualCover F ζ hζ))) =
      Quotient.mk (coveredRelation F ζ hζ U)
        (KPMsFixedHaarDisintegration.archBasepoint F a, c) := by
  rw [← productEquiv_apply]
  exact presentationMap_product F ζ hζ U a c

def piTilde : KPSmoothLocalQuotientCharts.X F ζ hζ → CoveredSpherical F ζ hζ U :=
  e F ζ hζ U ∘ coveredActualMap F ζ hζ U

theorem piTilde_quotientMap
    (a : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ) :
    piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          (c : ActualCover F ζ hζ))) =
      Quotient.mk (coveredRelation F ζ hζ U)
        (KPMsFixedHaarDisintegration.archBasepoint F a, c) := by
  exact e_mk F ζ hζ U a c

theorem piTilde_continuous : Continuous (piTilde F ζ hζ U) := by
  rw [piTilde]
  apply (e F ζ hζ U).continuous.comp
  have hq : IsQuotientMap (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_iff.mpr
  have hcomp : coveredActualMap F ζ hζ U ∘
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ =
      DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U) := by
    funext g
    exact coveredActualMap_mk F ζ hζ U g
  rw [hcomp]
  exact continuous_quotient_mk'

theorem piTilde_isOpenMap : IsOpenMap (piTilde F ζ hζ U) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  apply (e F ζ hζ U).isOpenMap.comp
  apply IsOpenMap.of_comp (f := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
  · exact continuous_quotient_mk'
  · intro y
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    exact ⟨g, rfl⟩
  · exact doubleCoset_open (Gamma F ζ hζ) (K_U F ζ hζ U)

theorem piTilde_surjective : Function.Surjective (piTilde F ζ hζ U) := by
  rw [piTilde]
  exact (e F ζ hζ U).surjective.comp (by
    intro y
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    exact ⟨KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g, rfl⟩)

theorem q_continuous : Continuous (q F ζ hζ U) := by
  have hq : IsQuotientMap (Quotient.mk (coveredRelation F ζ hζ U)) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_iff.mpr
  have hcomp : q F ζ hζ U ∘ Quotient.mk (coveredRelation F ζ hζ U) =
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) := by
    funext p
    exact q_mk F ζ hζ U p.1 p.2
  rw [hcomp]
  exact continuous_quotient_mk'

theorem q_surjective : Function.Surjective (q F ζ hζ U) := by
  intro y
  obtain ⟨p, rfl⟩ := Quotient.exists_rep y
  exact ⟨Quotient.mk _ p, rfl⟩

theorem q_eq_iff (v w : CoveredSpherical F ζ hζ U) :
    q F ζ hζ U v = q F ζ hζ U w ↔
      ∃ ε : rootsOfUnity 3 F, w = z F ζ hζ U ε v := by
  constructor
  · revert w
    refine Quotient.inductionOn v (fun p => ?_)
    intro w
    refine Quotient.inductionOn w (fun p' => ?_)
    intro h
    change Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) p =
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) p' at h
    have hs : (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U).r p p' := Quotient.exact h
    obtain ⟨γ, ε, u, hx, hc⟩ := hs
    refine ⟨ε, ?_⟩
    rw [z_mk]
    apply Eq.symm
    apply Quotient.sound
    refine ⟨γ, u, hx, ?_⟩
    rw [hc]
    simp only [mul_assoc]
  · rintro ⟨ε, rfl⟩
    rw [q_z]

 theorem q_isQuotientMap : IsQuotientMap (q F ζ hζ U) := by
  have hcomp : IsQuotientMap ((q F ζ hζ U) ∘ Quotient.mk (coveredRelation F ζ hζ U)) :=
    isQuotientMap_quotient_mk'
  exact hcomp.of_comp_of_isCoinducing isQuotientMap_quotient_mk'.isCoinducing

theorem q_isOpenMap : IsOpenMap (q F ζ hζ U) := by
  intro s hs
  rw [← (q_isQuotientMap F ζ hζ U).isCoinducing.isOpen_preimage]
  have heq : q F ζ hζ U ⁻¹' (q F ζ hζ U '' s) =
      ⋃ ε : rootsOfUnity 3 F, z F ζ hζ U ε '' s := by
    ext w
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨v, hv, h⟩
      obtain ⟨ε, hε⟩ := (q_eq_iff F ζ hζ U v w).mp h
      exact ⟨ε, v, hv, hε.symm⟩
    · rintro ⟨ε, v, hv, rfl⟩
      exact ⟨v, hv, (q_z F ζ hζ U ε v).symm⟩
  rw [heq]
  exact isOpen_iUnion (fun ε => (z F ζ hζ U ε).isOpenMap s hs)

abbrev CentralOrbitQuotient :=
  Quotient (MulAction.orbitRel (rootsOfUnity 3 F) (CoveredSpherical F ζ hζ U))

def centralOrbitHomeomorph :
    CentralOrbitQuotient F ζ hζ U ≃ₜ KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  (Homeomorph.Quotient.congrRight (r' := Setoid.ker (q F ζ hζ U)) (fun v w => by
    change (MulAction.orbitRel (rootsOfUnity 3 F) (CoveredSpherical F ζ hζ U)) v w ↔
      q F ζ hζ U v = q F ζ hζ U w
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, eq_comm, q_eq_iff]
    exact exists_congr (fun ε => eq_comm))).trans
    (IsQuotientMap.homeomorph (f := ⟨q F ζ hζ U, q_continuous F ζ hζ U⟩)
      (q_isQuotientMap F ζ hζ U))

theorem centralOrbitHomeomorph_mk (v : CoveredSpherical F ζ hζ U) :
    centralOrbitHomeomorph F ζ hζ U
      (Quotient.mk
        (MulAction.orbitRel (rootsOfUnity 3 F) (CoveredSpherical F ζ hζ U)) v) =
      q F ζ hζ U v := rfl

instance instT2SpaceCoveredSpherical : T2Space (CoveredSpherical F ζ hζ U) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  have hp := ActualQuotient.proper_actionCorrespondence
    (Gamma F ζ hζ) (K_U F ζ hζ U)
    (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1
    (ActualQuotient.actual_rational_closed_discrete F ζ hζ).2
    (K_U_compact F ζ hζ U)
  letI : T2Space (CoveredActual F ζ hζ U) :=
    (ActualQuotient.proper_doubleQuotient_certificate (Gamma F ζ hζ) (K_U F ζ hζ U) hp).hausdorff
  exact (e F ζ hζ U).t2Space

instance instLocallyCompactSpaceCoveredSpherical : LocallyCompactSpace (CoveredSpherical F ζ hζ U) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI : LocallyCompactSpace (CoveredActual F ζ hζ U) :=
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap
      (doubleCoset_open (Gamma F ζ hζ) (K_U F ζ hζ U))
      isQuotientMap_quotient_mk').locallyCompactSpace
  exact (e F ζ hζ U).symm.isClosedEmbedding.locallyCompactSpace

instance instPolishSpaceCoveredSpherical : PolishSpace (CoveredSpherical F ζ hζ U) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  have ho : IsOpenMap (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U)) :=
    doubleCoset_open _ _
  letI : SecondCountableTopology (CoveredActual F ζ hζ U) :=
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap ho isQuotientMap_quotient_mk').secondCountableTopology
  letI := (e F ζ hζ U).symm.secondCountableTopology
  exact ActualQuotient.lcsc_polish _

instance instBorelSpaceCoveredSpherical : BorelSpace (CoveredSpherical F ζ hζ U) :=
  ⟨rfl⟩

instance instMeasurableSpaceRawXU : MeasurableSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  borel _

instance instT2SpaceRawXU : T2Space (KPFiniteCuspAtlas.rawXU F ζ hζ U) := by
  have hq := q_isQuotientMap F ζ hζ U
  apply (t2Space_iff_of_isOpenQuotientMap
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap (q_isOpenMap F ζ hζ U) hq)).mpr
  have heq : {p : CoveredSpherical F ζ hζ U × CoveredSpherical F ζ hζ U |
      q F ζ hζ U p.1 = q F ζ hζ U p.2} =
      ⋃ ε : rootsOfUnity 3 F, {p | p.2 = z F ζ hζ U ε p.1} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, q_eq_iff]
  rw [heq]
  exact isClosed_iUnion_of_finite (fun ε => isClosed_eq continuous_snd
    ((z F ζ hζ U ε).continuous.comp continuous_fst))

instance instLocallyCompactSpaceRawXU :
    LocallyCompactSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  (IsOpenQuotientMap.of_isOpenMap_isQuotientMap (q_isOpenMap F ζ hζ U)
    (q_isQuotientMap F ζ hζ U)).locallyCompactSpace

instance instPolishSpaceRawXU : PolishSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) := by
  have hq := q_isQuotientMap F ζ hζ U
  letI : SecondCountableTopology (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap (q_isOpenMap F ζ hζ U) hq).secondCountableTopology
  exact ActualQuotient.lcsc_polish _

instance instBorelSpaceRawXU : BorelSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⟨rfl⟩

end DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison

end
