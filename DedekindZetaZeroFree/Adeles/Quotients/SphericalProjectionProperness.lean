module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.FullFrameRootNormalization
public import DedekindZetaZeroFree.Metaplectic.Unipotent.RationalFrameConjugation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology
open Topology

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
open KPGlobalResidualKernel.RawStageL2.Measurability

section ActualGeometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actual_arch_finite_transport_homeomorph : ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ
    KPMsFixedHaarDisintegration.Cover F ζ hζ,
    ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, _, _, hker, _, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hf : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ = KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    rw [← hker]
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      funext w
      have hw := congrFun h w
      rw [archProjection_compare] at hw
      let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)
      change Matrix.ProjGenLinGroup.map e.toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) = 1 at hw
      have hh := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) hw
      simpa only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp,
        RingEquiv.symm_toRingHom_comp_toRingHom, Matrix.ProjGenLinGroup.map_id, MonoidHom.id_apply,
        map_one, Pi.one_apply] using hh
    · intro h
      funext w
      rw [archProjection_compare, h]
      exact map_one _
  let ee : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ
      KPMsFixedHaarDisintegration.Cover F ζ hζ :=
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (Homeomorph.setCongr (congrArg (fun L : Subgroup (KPMsFixedHaarDisintegration.Cover F ζ hζ) =>
        (L : Set (KPMsFixedHaarDisintegration.Cover F ζ hζ))) hf.symm))).trans e.toHomeomorph
  exact ⟨ee, fun a c => he a _⟩

theorem rational_lift_finite_factor_mod_center (γ : KPCuspArithmetic.PGL2 F) :
    ∃ ε : rootsOfUnity 3 F,
      KPMsClearedTruncationL2.rationalLift F ζ hζ γ =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational γ) *
          ((KPCuspGenuineMonodromy.central F ζ hζ ε *
            KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) : KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
  obtain ⟨s, hs⟩ := rationalLift_split F ζ hζ γ
  have hp := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hs
  simp only [finiteProjection_rationalLift, map_mul, finiteProjection_archimedeanInsertion,
    one_mul] at hp
  have hf : KPCuspGenuineMonodromy.finiteBase F ζ hζ s =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ
        (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) := by
    rw [← MonoidHom.comp_apply, (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1]
    exact hp.symm
  have hm : s * (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)⁻¹ ∈
      (KPCuspGenuineMonodromy.central F ζ hζ).range := by
    rw [(KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1, MonoidHom.mem_ker,
      map_mul, map_inv, hf, mul_inv_cancel]
  obtain ⟨ε, hε⟩ := hm
  refine ⟨ε, ?_⟩
  have he : s = KPCuspGenuineMonodromy.central F ζ hζ ε *
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ := by
    rw [hε]
    group
  exact hs.trans (congrArg (fun c : KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational γ) * c.val) he)

private theorem basepoint_eq_smul (g : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F g =
      (fun i => g (KPCusp.complexPlace F i) • ((0,0) : KPArch.H3)) := by
  funext i
  have h := Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action
    (g (KPCusp.complexPlace F i)).out ((0,0) : KPArch.H3)
  have he : Matrix.ProjGenLinGroup.mk (g (KPCusp.complexPlace F i)).out =
      g (KPCusp.complexPlace F i) := Quotient.out_eq _
  rw [he] at h
  exact h.symm

private theorem local_basepoint_fiber_compact (x : KPArch.H3) :
    IsCompact {g : Matrix.ProjGenLinGroup (Fin 2) ℂ | g • ((0,0) : KPArch.H3) = x} := by
  have h := KPArithmeticAction.compact_transporter_of_section ((0,0) : KPArch.H3)
    KPArithmeticAction.hyperbolicProjectiveSection
    KPArithmeticAction.hyperbolicProjectiveSection_continuous
    (fun z => KPArithmeticAction.hyperbolicGLSection_action z)
    KPArithmeticAction.hyperbolic_origin_stabilizer_compact
    (isCompact_singleton (x := ((0,0) : KPArch.H3))) (isCompact_singleton (x := x))
  simpa only [Set.image_singleton, Set.singleton_inter_nonempty, Set.mem_singleton_iff,
    eq_comm] using h

theorem arch_basepoint_compact_fiber (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    IsCompact (KPMsFixedHaarDisintegration.archBasepoint F ⁻¹' {x}) := by
  let ix : NumberField.InfinitePlace F → Fin (NumberField.InfinitePlace.nrComplexPlaces F) :=
    fun w => Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}
      ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  have hix : ∀ w, KPCusp.complexPlace F (ix w) = w := by
    intro w
    exact congrArg Subtype.val ((Fintype.equivFin _).symm_apply_apply _)
  have hi : ∀ i, ix (KPCusp.complexPlace F i) = i := by
    intro i
    unfold ix KPCusp.complexPlace
    convert (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}).apply_symm_apply i
  have he : KPMsFixedHaarDisintegration.archBasepoint F ⁻¹' {x} =
      {g : KPSmoothActualFlowData.GInfinity F | ∀ w, g w • ((0,0) : KPArch.H3) = x (ix w)} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, basepoint_eq_smul,
      funext_iff]
    constructor
    · intro hg w
      simpa only [hix] using hg (ix w)
    · intro hg i
      simpa only [hi] using hg (KPCusp.complexPlace F i)
  rw [he]
  exact isCompact_pi_infinite fun w => local_basepoint_fiber_compact (x (ix w))

theorem arch_basepoint_continuous : Continuous (KPMsFixedHaarDisintegration.archBasepoint F) := by
  simp only [show KPMsFixedHaarDisintegration.archBasepoint F =
    (fun g i => g (KPCusp.complexPlace F i) • ((0,0) : KPArch.H3)) from funext (basepoint_eq_smul F)]
  change Continuous (fun g : KPSmoothActualFlowData.GInfinity F =>
    fun i => g (KPCusp.complexPlace F i) • ((0,0) : KPArch.H3))
  letI := KPArithmeticAction.hyperbolicContinuousSMul
  exact continuous_pi fun i => (continuous_apply _).smul continuous_const
private theorem local_bp_compact (C : Set KPArch.H3) (hC : IsCompact C) :
    IsCompact {g : Matrix.ProjGenLinGroup (Fin 2) ℂ | g • ((0,0) : KPArch.H3) ∈ C} := by
  have h := KPArithmeticAction.compact_transporter_of_section ((0,0) : KPArch.H3)
    KPArithmeticAction.hyperbolicProjectiveSection
    KPArithmeticAction.hyperbolicProjectiveSection_continuous
    (fun z => KPArithmeticAction.hyperbolicGLSection_action z)
    KPArithmeticAction.hyperbolic_origin_stabilizer_compact
    (isCompact_singleton (x := ((0,0) : KPArch.H3))) hC
  simpa only [Set.image_singleton, Set.singleton_inter_nonempty] using h

theorem arch_basepoint_compact_preimage (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (C : Set (KPFiniteCuspAtlas.SymmetricSpace F)) (hC : IsCompact C) :
    IsCompact (KPMsFixedHaarDisintegration.archBasepoint F ⁻¹' C) := by
  let ix : NumberField.InfinitePlace F → Fin (NumberField.InfinitePlace.nrComplexPlaces F) :=
    fun w => Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}
      ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  have hix : ∀ w, KPCusp.complexPlace F (ix w) = w := by
    intro w
    exact congrArg Subtype.val ((Fintype.equivFin _).symm_apply_apply _)
  let B : Set (KPSmoothActualFlowData.GInfinity F) :=
    {g | ∀ w, g w • ((0,0) : KPArch.H3) ∈ (fun x => x (ix w)) '' C}
  have hB : IsCompact B := isCompact_pi_infinite fun w =>
    local_bp_compact _ (hC.image (continuous_apply (ix w)))
  apply hB.of_isClosed_subset (hC.isClosed.preimage (arch_basepoint_continuous F))
  intro g hg w
  refine ⟨KPMsFixedHaarDisintegration.archBasepoint F g, hg, ?_⟩
  simp only [basepoint_eq_smul, hix]

theorem arch_basepoint_proper (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : IsProperMap (KPMsFixedHaarDisintegration.archBasepoint F) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  exact ⟨arch_basepoint_continuous F, arch_basepoint_compact_preimage F ζ hζ⟩

local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPFiniteCuspAtlas.SymmetricSpace F) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
private theorem cent_comm (ε : rootsOfUnity 3 F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPCuspGenuineMonodromy.central F ζ hζ ε) c := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) c).symm
private theorem q_rat (γ : KPCuspArithmetic.PGL2 F) (g : KPMsFixedHaarDisintegration.Cover F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (KPMsClearedTruncationL2.rationalLift F ζ hζ γ * g) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g := by
  apply Eq.symm
  apply Quotient.sound
  change (QuotientGroup.rightRel (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)) _ _
  rw [QuotientGroup.rightRel_apply]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  let m := Classical.choose (Matrix.ProjGenLinGroup.mk_surjective γ)
  exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F m,
    KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ m⟩
private theorem remove_rat (γ : KPCuspArithmetic.PGL2 F)
    (ε : rootsOfUnity 3 F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    ∃ η : rootsOfUnity 3 F,
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
          KPCuspGenuineMonodromy.central F ζ hζ ε * c) : KPFiniteCuspAtlas.FiniteCover F ζ hζ)) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ ((archRational γ)⁻¹ * a) *
          ((KPCuspGenuineMonodromy.central F ζ hζ η * c) : KPFiniteCuspAtlas.FiniteCover F ζ hζ)) := by
  obtain ⟨δ,hδ⟩ := rational_lift_finite_factor_mod_center F ζ hζ γ
  refine ⟨δ⁻¹ * ε, ?_⟩
  let b := (archRational γ)⁻¹ * a
  let d := KPCuspGenuineMonodromy.central F ζ hζ (δ⁻¹ * ε) * c
  have hh : KPMsClearedTruncationL2.rationalLift F ζ hζ γ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ b * d.val) =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε * c) : KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
    rw [hδ]
    have hc := insertion_commutes_cover F ζ hζ b
      (KPCuspGenuineMonodromy.central F ζ hζ δ * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)
    rw [mul_assoc, ← mul_assoc _ _ d.val, ← hc.eq, ← mul_assoc, ← mul_assoc,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1, show archRational γ * b = a by dsimp [b]; group]
    rw [mul_assoc]
    congr 1
    change ((KPCuspGenuineMonodromy.central F ζ hζ δ * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) * d).val = _
    congr 1
    dsimp [d]
    rw [(cent_comm F ζ hζ δ _).eq, map_mul, map_inv]
    group
  rw [← hh]
  exact q_rat F ζ hζ γ _
private theorem bp_unrat (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (γ : KPCuspArithmetic.PGL2 F)
    (a : KPSmoothActualFlowData.GInfinity F) (x : KPFiniteCuspAtlas.SymmetricSpace F)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a = γ • x) :
    KPMsFixedHaarDisintegration.archBasepoint F ((archRational γ)⁻¹ * a) = x := by
  have he : (archRational γ)⁻¹ = archRational γ⁻¹ := by
    funext w
    have hh (δ : KPCuspArithmetic.PGL2 F) : archRational δ w = Matrix.ProjGenLinGroup.map w.embedding δ := by
      unfold archRational
      rw [← Matrix.ProjGenLinGroup.map_mk]
      exact congrArg (Matrix.ProjGenLinGroup.map w.embedding) (show Matrix.ProjGenLinGroup.mk δ.out = δ from Quotient.out_eq _)
    change (archRational γ w)⁻¹ = archRational γ⁻¹ w
    rw [hh, hh, map_inv]
  rw [he, archBasepoint_mul, ha, archRational_action]
  exact inv_smul_smul γ x

theorem spherical_projection_compact_fiber (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    IsCompact (P.projection U ⁻¹' {Quotient.mk _ (x,c)}) := by
  let f := fun p : KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2.val)
  have hf : Continuous f := continuous_quot_mk.comp
    (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  let D := ⋃ ε : rootsOfUnity 3 F,
    (fun u : KPFiniteCuspAtlas.FiniteCover F ζ hζ => KPCuspGenuineMonodromy.central F ζ hζ ε * c * u) ''
      (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
  have hD : IsCompact D := isCompact_iUnion fun ε => U.isCompact.image
    ((continuous_const.mul continuous_const).mul continuous_id)
  have he : P.projection U ⁻¹' {Quotient.mk _ (x,c)} =
      f '' ((KPMsFixedHaarDisintegration.archBasepoint F ⁻¹' {x}) ×ˢ D) := by
    ext z
    constructor
    · intro hz
      obtain ⟨e,he⟩ := actual_arch_finite_transport_homeomorph F ζ hζ
      obtain ⟨g,rfl⟩ := Quotient.mk_surjective z
      obtain ⟨⟨a,d⟩,hd⟩ := e.surjective g
      rw [he] at hd
      subst g
      have hh : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (KPMsFixedHaarDisintegration.archBasepoint F a,d) = Quotient.mk _ (x,c) := by
        change P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ _) = _ at hz
        rw [P.formula] at hz
        exact hz
      obtain ⟨γ,ε,u,ha,hc⟩ := Quotient.exact hh.symm
      dsimp only at ha hc
      obtain ⟨η,hη⟩ := remove_rat F ζ hζ γ ε a (c * u.val)
      refine ⟨((archRational γ)⁻¹ * a, KPCuspGenuineMonodromy.central F ζ hζ η * c * u.val), ?_, ?_⟩
      · exact ⟨bp_unrat F ζ hζ γ a x ha,
          Set.mem_iUnion.mpr ⟨η, ⟨u.val,u.property,rfl⟩⟩⟩
      · dsimp only [f]
        rw [hc]
        simpa only [mul_assoc, KPSmoothLocalQuotientCharts.quotientMap] using hη.symm
    · rintro ⟨⟨a,d⟩,⟨ha,hd⟩,rfl⟩
      obtain ⟨ε,u,hu,rfl⟩ := Set.mem_iUnion.mp hd
      change P.projection U (f _) = _
      rw [P.formula]
      apply Quotient.sound
      apply (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U).symm
      refine ⟨1,ε,⟨u,hu⟩,?_,?_⟩
      · simpa only [one_smul, Set.mem_preimage, Set.mem_singleton_iff] using ha
      · simp
  rw [he]
  exact ((arch_basepoint_compact_fiber F ζ hζ x).prod hD).image hf
private theorem finite_saturation_closed
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (B : Set (KPFiniteCuspAtlas.SymmetricSpace F × KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (hB : IsClosed B) :
    IsClosed {p : KPFiniteCuspAtlas.SymmetricSpace F × KPFiniteCuspAtlas.FiniteCover F ζ hζ |
      ∃ ε : rootsOfUnity 3 F, ∃ u : U.toOpenSubgroup,
        (p.1, (KPCuspGenuineMonodromy.central F ζ hζ ε) * p.2 * u.val) ∈ B} := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  letI : CompactSpace U.toOpenSubgroup := isCompact_iff_compactSpace.mp U.isCompact
  let T := {q : (KPFiniteCuspAtlas.SymmetricSpace F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ×
        (rootsOfUnity 3 F × U.toOpenSubgroup) |
    (q.1.1, (KPCuspGenuineMonodromy.central F ζ hζ q.2.1) * q.1.2 * q.2.2.val) ∈ B}
  have hc : Continuous (KPCuspGenuineMonodromy.central F ζ hζ) := continuous_of_discreteTopology
  have hT : IsClosed T := hB.preimage
    ((continuous_fst.comp continuous_fst).prodMk
      (((hc.comp (continuous_fst.comp continuous_snd)).mul
        (continuous_snd.comp continuous_fst)).mul
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  convert isClosedMap_fst_of_compactSpace T hT using 1
  ext p
  simp only [Set.mem_image, T, Set.mem_setOf_eq, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨ε,u,h⟩
    exact ⟨p.1,p.2,ε,u,h,rfl⟩
  · rintro ⟨x,c,ε,u,h,rfl⟩
    exact ⟨ε,u,h⟩

theorem spherical_projection_isClosedMap (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) : IsClosedMap (P.projection U) := by
  intro A hA
  let f := fun p : KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2.val)
  have hf : Continuous f := continuous_quot_mk.comp
    (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  let H := Prod.map (KPMsFixedHaarDisintegration.archBasepoint F) (id : KPFiniteCuspAtlas.FiniteCover F ζ hζ → _)
  let B := H '' (f ⁻¹' A)
  have hB : IsClosed B := ((arch_basepoint_proper F ζ hζ).prodMap isProperMap_id).isClosedMap _ (hA.preimage hf)
  letI := KPFiniteCuspAtlas.sphericalRelation F ζ hζ U
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  have he : (Quotient.mk' : KPFiniteCuspAtlas.SymmetricSpace F × KPFiniteCuspAtlas.FiniteCover F ζ hζ →
      KPMsFixedHaarDisintegration.Spherical F ζ hζ U) ⁻¹' (P.projection U '' A) =
      {p : KPFiniteCuspAtlas.SymmetricSpace F × KPFiniteCuspAtlas.FiniteCover F ζ hζ |
        ∃ ε : rootsOfUnity 3 F, ∃ u : U.toOpenSubgroup,
          (p.1, KPCuspGenuineMonodromy.central F ζ hζ ε * p.2 * u.val) ∈ B} := by
    ext p
    constructor
    · rintro ⟨z,hz,hp⟩
      obtain ⟨e,he⟩ := actual_arch_finite_transport_homeomorph F ζ hζ
      obtain ⟨g,rfl⟩ := Quotient.mk_surjective z
      obtain ⟨⟨a,d⟩,hd⟩ := e.surjective g
      rw [he] at hd
      subst g
      have hh : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (KPMsFixedHaarDisintegration.archBasepoint F a,d) = Quotient.mk _ p := by
        change P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ _) = _ at hp
        rw [P.formula] at hp
        exact hp
      obtain ⟨γ,ε,u,ha,hc⟩ := Quotient.exact hh.symm
      dsimp only at ha hc
      obtain ⟨η,hη⟩ := remove_rat F ζ hζ γ ε a (p.2 * u.val)
      refine ⟨η,u,((archRational γ)⁻¹ * a, KPCuspGenuineMonodromy.central F ζ hζ η * p.2 * u.val), ?_, ?_⟩
      · change f _ ∈ A
        have hh : f ((archRational γ)⁻¹ * a, KPCuspGenuineMonodromy.central F ζ hζ η * p.2 * u.val) =
            KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * d.val) := by
          dsimp only [f]
          rw [hc]
          simpa only [mul_assoc] using hη.symm
        rw [hh]
        exact hz
      · exact Prod.ext (bp_unrat F ζ hζ γ a p.1 ha) rfl
    · rintro ⟨ε,u,⟨a,d⟩,had,he⟩
      have ha : KPMsFixedHaarDisintegration.archBasepoint F a = p.1 := congrArg Prod.fst he
      have hd : d = KPCuspGenuineMonodromy.central F ζ hζ ε * p.2 * u.val := congrArg Prod.snd he
      refine ⟨f (a,d),had,?_⟩
      change P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ _) = _
      rw [P.formula]
      apply Quotient.sound
      apply (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U).symm
      exact ⟨1,ε,u,by simpa using ha,by simpa using hd⟩
  rw [he]
  exact finite_saturation_closed F ζ hζ U B hB

end ActualGeometry

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem spherical_projection_compact_preimage
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (C : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U))
    (hC : IsCompact C) :
    IsCompact (P.projection U ⁻¹' C) := by
  have hp : IsProperMap (P.projection U) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨P.continuous U, spherical_projection_isClosedMap F ζ hζ P U, fun y => by
        induction y using Quotient.inductionOn with
        | h p => exact spherical_projection_compact_fiber F ζ hζ P U p.1 p.2⟩
  exact hp.isCompact_preimage hC

end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry

end
