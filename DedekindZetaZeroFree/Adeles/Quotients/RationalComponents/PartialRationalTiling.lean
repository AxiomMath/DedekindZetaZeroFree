module

public import DedekindZetaZeroFree.Adeles.Quotients.RationalComponents.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Pointwise
open MeasureTheory Function

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem actual_archProjection_compare
    (g : KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by
  open KPAdelicCoverRestrictedProduct in
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) g
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _ (projection F ζ hζ g)) =
    Matrix.ProjGenLinGroup.map _ (Matrix.ProjGenLinGroup.mk
      (matrixEval F (Sum.inl w) (projection F ζ hζ g)))
  rw [Matrix.ProjGenLinGroup.map_mk, Matrix.GeneralLinearGroup.map_comp]
  rfl

private theorem actual_finiteSubgroup_eq :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  obtain ⟨e, he, hi, hs, hker, hrest⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [← hker]
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg
    funext w
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have hw := congrFun hg w
    rw [actual_archProjection_compare] at hw
    have hw' := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) hw
    simp only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp] at hw'
    simpa [e] using hw'
  · intro hg
    funext w
    rw [actual_archProjection_compare, hg]
    exact map_one _

 theorem actual_product_splitting :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ*
      KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ,
      ∀ a c, e (a, c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, hrest⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hf := actual_finiteSubgroup_eq F ζ hζ
  change ∃ e : (PGLComplex.AdelicSlicesRaw.ArchGroup F ×
    KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* _, _
  rw [← hf]
  exact ⟨e, he⟩

open KPAdelicCoverRestrictedProduct

private theorem finiteProjection_local_infinite (v : NumberField.InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v)) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v) g)) = 1 := by
  classical
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (restrictedProjection F ζ hζ (localToRestricted F ζ hζ (Sum.inl v) g))) = 1
  have he : Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
      (restrictedProjection F ζ hζ (localToRestricted F ζ hζ (Sum.inl v) g)) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply Subtype.ext
    funext q
    have h := restrictedProjection_eval F ζ hζ (localToRestricted F ζ hζ (Sum.inl v) g) (Sum.inr q)
    have hn : localToRestricted F ζ hζ (Sum.inl v) g (Sum.inr q) = 1 := by
      exact RestrictedProduct.mulSingle_eq_of_ne' _ _ (by simp)
    rw [hn, map_one] at h
    convert congrArg (fun m => m i j) h using 1
    · rfl
    · by_cases hij : i = j <;> subst_vars <;> simp [Matrix.one_apply, *] <;> rfl
  rw [he, map_one]

private theorem finiteProjection_archimedeanInsertion (a : KPSmoothActualFlowData.GInfinity F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = 1 := by
  unfold KPSmoothActualFlowData.archimedeanInsertion
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, finiteProjection_local_infinite]
  simp

 def tilingLift : KPCuspArithmetic.PGL2 F →* Cover F ζ hζ :=
  (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp (rationalEquiv F).toMonoidHom

 def tilingArch : KPCuspArithmetic.PGL2 F →* KPSmoothActualFlowData.GInfinity F :=
  (KPSmoothLocalQuotientCharts.archProjection F ζ hζ).comp (tilingLift F ζ hζ)

 theorem tilingLift_finite (γ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ (tilingLift F ζ hζ γ) =
      KPFiniteComponents.diagonal F γ := by
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have he : rationalEquiv F (Matrix.ProjGenLinGroup.mk a) =
      KPRationalAdelicSplitting.rationalPGLQuotient F a :=
    QuotientGroup.quotientMulEquivOfEq_mk _ a
  simp only [tilingLift, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, he, KPRationalAdelicSplitting.rationalPGLHom_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (projection F ζ hζ (rationalSection F ζ hζ a))) = _
  exact congrArg (fun k => Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (RingHom.snd _ _) k))
      (projection_rationalSection F ζ hζ a)

 theorem tilingArch_injective : Function.Injective (tilingArch F ζ hζ) := by
  have hi : Function.Injective (tilingLift F ζ hζ) :=
    (KPRationalAdelicSplitting.rationalPGL_splitting F ζ hζ).1.comp (rationalEquiv F).injective
  intro x y hxy
  apply hi
  have hx : tilingLift F ζ hζ x ∈ ActualQuotient.rationalSubgroup F ζ hζ :=
    ⟨rationalEquiv F x, rfl⟩
  have hy : tilingLift F ζ hζ y ∈ ActualQuotient.rationalSubgroup F ζ hζ :=
    ⟨rationalEquiv F y, rfl⟩
  exact congrArg Subtype.val (ActualQuotient.actual_rational_arch_injective F ζ hζ
    (a₁ := ⟨tilingLift F ζ hζ x, hx⟩) (a₂ := ⟨tilingLift F ζ hζ y, hy⟩) hxy)

 theorem tiling_arch_m (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPSmoothLocalQuotientCharts.archProjection F ζ hζ (m F ζ hζ (a,c)) = a := by
  have hc : KPSmoothLocalQuotientCharts.archProjection F ζ hζ c.val = 1 := by
    change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1
    funext w
    rw [actual_archProjection_compare]
    have hh := c.property
    change KPCuspGenuineMonodromy.archProjection F ζ hζ c.val = 1 at hh
    rw [hh]
    exact map_one _
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * c.val) = a
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1 at hc
  rw [map_mul, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, hc, mul_one]

 theorem tiling_finite_m (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ (m F ζ hζ (a,c)) =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ c := by
  simp only [m, map_mul, finiteProjection_archimedeanInsertion, one_mul]
  rfl

 theorem tiling_central_base (ε : rootsOfUnity 3 F) :
    KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.central F ζ hζ ε) = 1 := by
  have hm : KPCuspGenuineMonodromy.central F ζ hζ ε ∈
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ).ker := by
    rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1]
    exact ⟨ε, rfl⟩
  exact hm

 theorem tiling_orbit_base (U : Level F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g ↔
      ∃ u : U.toOpenSubgroup,
        KPCuspGenuineMonodromy.finiteBase F ζ hζ c =
          KPCuspGenuineMonodromy.finiteBase F ζ hζ g *
            KPCuspGenuineMonodromy.finiteBase F ζ hζ u := by
  constructor
  · rintro ⟨ε,u,rfl⟩
    exact ⟨u, by simp only [map_mul, tiling_central_base, one_mul]⟩
  · rintro ⟨u, hu⟩
    have hk : c * (g * u)⁻¹ ∈ (KPCuspGenuineMonodromy.central F ζ hζ).range := by
      rw [(KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1,
        MonoidHom.mem_ker, map_mul, map_inv, map_mul, hu, mul_inv_cancel]
    obtain ⟨ε, hε⟩ := hk
    refine ⟨ε, u, ?_⟩
    rw [hε]
    group

 theorem tiling_overlap_primitive (U : Level F ζ hζ)
    (g b c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (δ : KPCuspArithmetic.PGL2 F)
    (hb : b ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (hc : c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (he : KPFiniteComponents.diagonal F δ * KPCuspGenuineMonodromy.finiteBase F ζ hζ b =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ c) :
    δ ∈ KPCuspGenuineMonodromy.Component F ζ hζ U g := by
  obtain ⟨u,hu⟩ := (tiling_orbit_base F ζ hζ U g b).mp hb
  obtain ⟨v,hv⟩ := (tiling_orbit_base F ζ hζ U g c).mp hc
  change KPFiniteComponents.diagonal F δ ∈
    (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
      (MulAut.conj (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)).toMonoidHom
  refine ⟨KPCuspGenuineMonodromy.finiteBase F ζ hζ (v * u⁻¹),
    ⟨v * u⁻¹, (v * u⁻¹).property, rfl⟩, ?_⟩
  rw [hu,hv] at he
  simp only [MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hh := congrArg (fun x => x * (KPCuspGenuineMonodromy.finiteBase F ζ hζ u)⁻¹ *
    (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)⁻¹) he
  simpa [mul_assoc] using hh.symm

 theorem tiling_preserve_base (U : Level F ζ hζ)
    (g b c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (δ : KPCuspGenuineMonodromy.Component F ζ hζ U g)
    (hb : b ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (he : KPCuspGenuineMonodromy.finiteBase F ζ hζ c =
      KPFiniteComponents.diagonal F δ * KPCuspGenuineMonodromy.finiteBase F ζ hζ b) :
    c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g := by
  obtain ⟨u,hu⟩ := (tiling_orbit_base F ζ hζ U g b).mp hb
  obtain ⟨ε,v,hv⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U g δ
  have hh := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) hv
  simp only [map_mul, tiling_central_base, one_mul] at hh
  rw [← MonoidHom.comp_apply,
    (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1] at hh
  apply (tiling_orbit_base F ζ hζ U g c).mpr
  refine ⟨v*u, ?_⟩
  rw [he,hu,← mul_assoc,hh]
  change _ = KPCuspGenuineMonodromy.finiteBase F ζ hζ g *
    KPCuspGenuineMonodromy.finiteBase F ζ hζ (v.val*u.val)
  simp only [map_mul,mul_assoc]

 def tilingRational (δ : KPCuspArithmetic.PGL2 F) :
    KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
  ⟨tilingLift F ζ hζ δ, ⟨rationalEquiv F δ, rfl⟩⟩

 theorem tilingRational_surjective : Function.Surjective (tilingRational F ζ hζ) := by
  rintro ⟨x,δ,hδ⟩
  exact ⟨(rationalEquiv F).symm δ, Subtype.ext (by simpa [tilingRational,tilingLift] using hδ)⟩

 theorem tiling_quotient_invariant
    (δ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (x : Cover F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (δ.val*x) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  change x*(δ.val*x)⁻¹ ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ
  simpa [mul_inv_rev, mul_assoc] using
    (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem δ.property

 theorem tiling_projection_mem (U : Level F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (g b : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (a : KPSmoothActualFlowData.GInfinity F)
    (hb : b ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) :
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (a,b))) ∈
      Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U g) := by
  obtain ⟨ε,u,rfl⟩ := hb
  refine ⟨Quotient.mk _ (archBasepoint F a), ?_⟩
  simp only [m, P.formula]
  change Quotient.mk _ (archBasepoint F a,g) =
    Quotient.mk _ (archBasepoint F a,KPCuspGenuineMonodromy.central F ζ hζ ε * g * u)
  apply Quotient.sound
  exact ⟨1,ε,u,by simp,by simp⟩

 theorem tiling_projection_cover (U : Level F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (a : KPSmoothActualFlowData.GInfinity F)
    (hc : P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (m F ζ hζ (a,c))) ∈
      Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U g)) :
    ∃ δ : KPCuspArithmetic.PGL2 F, ∃ u : U.toOpenSubgroup,
      KPFiniteComponents.diagonal F δ * KPCuspGenuineMonodromy.finiteBase F ζ hζ c =
        KPCuspGenuineMonodromy.finiteBase F ζ hζ g *
          KPCuspGenuineMonodromy.finiteBase F ζ hζ u := by
  obtain ⟨y,hy⟩ := hc
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective y
  simp only [m, P.formula] at hy
  change Quotient.mk _ (y,g) = Quotient.mk _ (archBasepoint F a,c) at hy
  obtain ⟨δ,ε,u,hx,he⟩ := Quotient.exact hy.symm
  refine ⟨δ,u⁻¹,?_⟩
  have hh := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) he
  simp only [map_mul,tiling_central_base, mul_one] at hh
  rw [← MonoidHom.comp_apply,
    (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1] at hh
  have hh' := congrArg (fun x => x * (KPCuspGenuineMonodromy.finiteBase F ζ hζ u.val)⁻¹) hh
  simpa [mul_assoc] using hh'.symm

private theorem tiling_normalize
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount)
    (D : Set (KPSmoothActualFlowData.GInfinity F))
    (hDexact : ∀ x : KPSmoothActualFlowData.GInfinity F,
      ∃! γ : Ga F ζ hζ hF U A i, γ.val*x ∈ D)
    (a : KPSmoothActualFlowData.GInfinity F)
    (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) (hb : b ∈ B F ζ hζ hF U A i) :
    ∃ δ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
      δ.val * m F ζ hζ (a,b) ∈ m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i) := by
  obtain ⟨γ,hγ,_⟩ := hDexact a
  obtain ⟨δ,hδ,he⟩ := γ.property
  let δ' : Gi F ζ hζ hF U A i := ⟨δ,hδ⟩
  obtain ⟨e,heq⟩ := actual_product_splitting F ζ hζ
  obtain ⟨⟨v,c⟩,hc⟩ := e.surjective (tilingLift F ζ hζ δ * m F ζ hζ (a,b))
  have hc' : m F ζ hζ (v,c) = tilingLift F ζ hζ δ * m F ζ hζ (a,b) :=
    (heq v c).symm.trans hc
  have hv := congrArg (KPSmoothLocalQuotientCharts.archProjection F ζ hζ) hc'
  rw [tiling_arch_m,map_mul,tiling_arch_m] at hv
  have hbase := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hc'
  rw [tiling_finite_m,map_mul,tilingLift_finite,tiling_finite_m] at hbase
  have hcb : c ∈ B F ζ hζ hF U A i :=
    tiling_preserve_base F ζ hζ U (A.representative i) b c δ' hb hbase
  refine ⟨tilingRational F ζ hζ δ, ⟨(v,c), ⟨?_,hcb⟩,hc'⟩⟩
  change tilingArch F ζ hζ δ = γ.val at he
  change v ∈ D
  change v = tilingArch F ζ hζ δ * a at hv
  rw [hv,he]
  exact hγ

theorem actual_component_partial_rational_tiling
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (P : SphericalTransport F ζ hζ) (i : Fin A.componentCount)
    (D : Set (KPSmoothActualFlowData.GInfinity F)) (hDm : MeasurableSet D)
    (hDexact : ∀ x : KPSmoothActualFlowData.GInfinity F,
      ∃! γ : Ga F ζ hζ hF U A i, γ.val * x ∈ D) :
    let S := m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)
    Pairwise (Disjoint on fun γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ =>
      γ • S) ∧
    (⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • S) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹'
        (P.projection U ⁻¹' C F ζ hζ hF U A i) := by
  let S := m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)
  change Pairwise (Disjoint on fun γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ =>
    γ • S) ∧ (⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • S) = _
  constructor
  · intro γ η hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hyS,hye⟩ := Set.mem_smul_set.mp hx
    obtain ⟨z,hz,hze⟩ := Set.mem_smul_set.mp hy
    have he := hze.trans hye.symm
    obtain ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩ := hyS
    obtain ⟨⟨v,c⟩,⟨hv,hc⟩,rfl⟩ := hz
    obtain ⟨δ,rfl⟩ := tilingRational_surjective F ζ hζ γ
    obtain ⟨θ,rfl⟩ := tilingRational_surjective F ζ hζ η
    have hh : tilingLift F ζ hζ (θ⁻¹*δ) * m F ζ hζ (a,b) =
        m F ζ hζ (v,c) := by
      change tilingLift F ζ hζ θ * m F ζ hζ (v,c) =
        tilingLift F ζ hζ δ * m F ζ hζ (a,b) at he
      rw [map_mul,map_inv]
      rw [mul_assoc, ← he]
      group
    have hhf := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hh
    rw [map_mul,tilingLift_finite,tiling_finite_m,tiling_finite_m] at hhf
    have hδ : θ⁻¹*δ ∈ Gi F ζ hζ hF U A i :=
      tiling_overlap_primitive F ζ hζ U (A.representative i) b c _ hb hc hhf
    let α : Ga F ζ hζ hF U A i :=
      ⟨tilingArch F ζ hζ (θ⁻¹*δ), ⟨θ⁻¹*δ,hδ,rfl⟩⟩
    have hha := congrArg (KPSmoothLocalQuotientCharts.archProjection F ζ hζ) hh
    rw [map_mul,tiling_arch_m,tiling_arch_m] at hha
    have hα : α.val*a ∈ D := by
      change KPSmoothLocalQuotientCharts.archProjection F ζ hζ
        (tilingLift F ζ hζ (θ⁻¹*δ))*a ∈ D
      rw [hha]
      exact hv
    obtain ⟨ω,hω,huniq⟩ := hDexact a
    have hα1 : α = 1 := (huniq α hα).trans (huniq 1 (by simpa using ha)).symm
    have harch : tilingArch F ζ hζ (θ⁻¹*δ) = tilingArch F ζ hζ 1 := by
      simpa [α] using congrArg Subtype.val hα1
    have hr : θ⁻¹*δ = 1 := tilingArch_injective F ζ hζ harch
    have hδθ : δ = θ := by
      have hh' := congrArg (fun x => θ*x) hr
      simpa [mul_assoc] using hh'
    exact hne (congrArg (tilingRational F ζ hζ) hδθ)
  · ext x
    constructor
    · intro hx
      obtain ⟨γ,hγ⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hγ
      obtain ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩ := hy
      change P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (γ.val*m F ζ hζ (a,b))) ∈ C F ζ hζ hF U A i
      rw [tiling_quotient_invariant]
      exact tiling_projection_mem F ζ hζ U P (A.representative i) b a hb
    · intro hx
      obtain ⟨e,heq⟩ := actual_product_splitting F ζ hζ
      obtain ⟨⟨a,c⟩,hc⟩ := e.surjective x
      have he : m F ζ hζ (a,c) = x := (heq a c).symm.trans hc
      rw [← he] at hx ⊢
      obtain ⟨δ,u,hδ⟩ := tiling_projection_cover F ζ hζ U P (A.representative i) c a hx
      obtain ⟨⟨v,b⟩,hb⟩ := e.surjective
        (tilingLift F ζ hζ δ*m F ζ hζ (a,c))
      have hb' : m F ζ hζ (v,b) = tilingLift F ζ hζ δ*m F ζ hζ (a,c) :=
        (heq v b).symm.trans hb
      have hbase := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hb'
      rw [tiling_finite_m,map_mul,tilingLift_finite,tiling_finite_m] at hbase
      have hbB : b ∈ B F ζ hζ hF U A i :=
        (tiling_orbit_base F ζ hζ U (A.representative i) b).mpr ⟨u,hbase.trans hδ⟩
      obtain ⟨ρ,hρ⟩ := tiling_normalize F ζ hζ hF U A i D hDexact v b hbB
      rw [hb'] at hρ
      apply Set.mem_iUnion.mpr
      refine ⟨(ρ*tilingRational F ζ hζ δ)⁻¹, Set.mem_smul_set.mpr ?_⟩
      refine ⟨ρ.val*(tilingLift F ζ hζ δ*m F ζ hζ (a,c)), hρ, ?_⟩
      change (ρ.val * tilingLift F ζ hζ δ)⁻¹ *
        (ρ.val*(tilingLift F ζ hζ δ*m F ζ hζ (a,c))) = m F ζ hζ (a,c)
      group

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
