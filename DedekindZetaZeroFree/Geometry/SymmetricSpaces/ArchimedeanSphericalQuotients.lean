module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField Matrix ContDiff Matrix.Norms.Operator Pointwise
open NumberField Topology

namespace DedekindZetaZeroFree.KPContSectorArchSphericalFibers

variable (F : Type) [Field F] [NumberField F]

def origin : KPFiniteCuspAtlas.SymmetricSpace F := fun _ => (0, 0)

def complexPlaceHom : KPSmoothActualFlowData.GInfinity F →*
    KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F) where
  toFun g := fun i => g (KPCusp.complexPlace F i)
  map_one' := rfl
  map_mul' _ _ := rfl

def KInfinity : Subgroup (KPSmoothActualFlowData.GInfinity F) :=
  (MulAction.stabilizer
    (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F))
    (origin F)).comap (complexPlaceHom F)

private lemma archBasepoint_eq_smul (g : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F g = complexPlaceHom F g • origin F := by
  funext i
  show KPArch.action (g (KPCusp.complexPlace F i)).out (0, 0) =
    (g (KPCusp.complexPlace F i)) • ((0, 0) : KPArch.H3)
  conv_rhs => rw [← Quotient.out_eq (g (KPCusp.complexPlace F i))]
  change KPArch.action (Quotient.out (g (KPCusp.complexPlace F i))) (0, 0) =
    Matrix.ProjGenLinGroup.mk (Quotient.out (g (KPCusp.complexPlace F i))) •
      ((0, 0) : KPArch.H3)
  rw [Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action]
  rfl

theorem mem_KInfinity_iff (g : KPSmoothActualFlowData.GInfinity F) :
    g ∈ KInfinity F ↔
      KPMsFixedHaarDisintegration.archBasepoint F g = origin F := by
  rw [KInfinity, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
    archBasepoint_eq_smul F g]

def infinitePlaceEquiv (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    InfinitePlace F ≃ Fin (InfinitePlace.nrComplexPlaces F) where
  toFun w := Fintype.equivFin {v : InfinitePlace F // v.IsComplex}
    ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  invFun := KPCusp.complexPlace F
  left_inv w := congrArg Subtype.val
    ((Fintype.equivFin {v : InfinitePlace F // v.IsComplex}).symm_apply_apply
      ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩)
  right_inv i := by
    change Fintype.equivFin {v : InfinitePlace F // v.IsComplex}
      ⟨KPCusp.complexPlace F i, _⟩ = i
    unfold KPCusp.complexPlace
    convert (Fintype.equivFin {v : InfinitePlace F // v.IsComplex}).apply_symm_apply i

private lemma infinitePlaceEquiv_complexPlace (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (i : Fin (InfinitePlace.nrComplexPlaces F)) :
    infinitePlaceEquiv F ζ hζ (KPCusp.complexPlace F i) = i :=
  (infinitePlaceEquiv F ζ hζ).right_inv i

private lemma complexPlace_infinitePlaceEquiv (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) :
    KPCusp.complexPlace F (infinitePlaceEquiv F ζ hζ w) = w :=
  (infinitePlaceEquiv F ζ hζ).left_inv w

private lemma product_origin_stabilizer_compact :
    IsCompact (MulAction.stabilizer
      (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F))
      (origin F) : Set (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F))) := by
  change IsCompact (MulAction.stabilizer
      (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F))
      (fun _ : Fin (KPCuspLogShape.dimension F) => ((0, 0) : KPArch.H3)) :
        Set (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F)))
  exact KPArithmeticAction.product_origin_stabilizer_compact (KPCuspLogShape.dimension F)

private lemma mem_product_origin_stabilizer_iff
    (h : KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F)) :
    h ∈ MulAction.stabilizer
        (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F)) (origin F) ↔
      ∀ i, h i ∈ MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) ℂ)
        ((0, 0) : KPArch.H3) := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hh i
    rw [MulAction.mem_stabilizer_iff]
    have := congrFun hh i
    show h i • ((0, 0) : KPArch.H3) = (0, 0)
    exact this
  · intro hh
    funext i
    show h i • ((0, 0) : KPArch.H3) = (0, 0)
    exact MulAction.mem_stabilizer_iff.mp (hh i)

 lemma mem_KInfinity_iff_stab (g : KPSmoothActualFlowData.GInfinity F) :
    g ∈ KInfinity F ↔ ∀ i, g (KPCusp.complexPlace F i) ∈
      MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) ℂ) ((0, 0) : KPArch.H3) := by
  rw [mem_KInfinity_iff, archBasepoint_eq_smul]
  constructor
  · intro h i
    rw [MulAction.mem_stabilizer_iff]
    exact congrFun h i
  · intro h
    funext i
    exact MulAction.mem_stabilizer_iff.mp (h i)

theorem KInfinity_compact (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    IsCompact (KInfinity F : Set (KPSmoothActualFlowData.GInfinity F)) := by
  have hcont : Continuous (fun h : KPArithmeticAction.ProjectiveGroup
      (KPCuspLogShape.dimension F) => fun w : InfinitePlace F =>
        h (infinitePlaceEquiv F ζ hζ w)) :=
    continuous_pi fun w => continuous_apply _
  have himage : (KInfinity F : Set (KPSmoothActualFlowData.GInfinity F)) =
      (fun h : KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F) =>
        fun w : InfinitePlace F => h (infinitePlaceEquiv F ζ hζ w)) ''
      (MulAction.stabilizer
        (KPArithmeticAction.ProjectiveGroup (KPCuspLogShape.dimension F))
        (origin F) : Set (KPArithmeticAction.ProjectiveGroup
          (KPCuspLogShape.dimension F))) := by
    ext g
    constructor
    · intro hg
      rw [SetLike.mem_coe] at hg
      refine ⟨fun i => g (KPCusp.complexPlace F i), ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_product_origin_stabilizer_iff]
        intro i
        exact (mem_KInfinity_iff_stab F g).mp hg i
      · funext w
        show g (KPCusp.complexPlace F (infinitePlaceEquiv F ζ hζ w)) = g w
        rw [complexPlace_infinitePlaceEquiv F ζ hζ w]
    · rintro ⟨h, hh, rfl⟩
      rw [SetLike.mem_coe, mem_KInfinity_iff_stab]
      intro i
      have hh' := (mem_product_origin_stabilizer_iff F h).mp hh
      change h (infinitePlaceEquiv F ζ hζ (KPCusp.complexPlace F i)) ∈
        MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) ℂ) ((0, 0) : KPArch.H3)
      rw [infinitePlaceEquiv_complexPlace F ζ hζ i]
      exact hh' i
  rw [himage]
  exact (product_origin_stabilizer_compact F).image hcont

theorem archBasepoint_continuous :
    Continuous (KPMsFixedHaarDisintegration.archBasepoint F) := by
  rw [show KPMsFixedHaarDisintegration.archBasepoint F =
      (fun g => complexPlaceHom F g • origin F) from funext (archBasepoint_eq_smul F)]
  change Continuous (fun g : KPSmoothActualFlowData.GInfinity F =>
    fun i => g (KPCusp.complexPlace F i) • ((0,0) : KPArch.H3))
  refine continuous_pi fun i => ?_
  have hpair : Continuous (fun g : KPSmoothActualFlowData.GInfinity F =>
      (g (KPCusp.complexPlace F i), ((0,0) : KPArch.H3))) :=
    (continuous_apply (KPCusp.complexPlace F i)).prodMk continuous_const
  simpa only [Function.comp_def] using
    KPArithmeticAction.hyperbolicContinuousSMul.continuous_smul.comp hpair

theorem archBasepoint_eq_iff (a b : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F a =
        KPMsFixedHaarDisintegration.archBasepoint F b ↔
      ∃ k : KInfinity F, b = a * (k : KPSmoothActualFlowData.GInfinity F) := by
  rw [archBasepoint_eq_smul F a, archBasepoint_eq_smul F b]
  constructor
  · intro h
    refine ⟨⟨a⁻¹ * b, ?_⟩, by simp⟩
    rw [mem_KInfinity_iff, archBasepoint_eq_smul]
    show (complexPlaceHom F (a⁻¹ * b)) • origin F = origin F
    rw [map_mul, map_inv, mul_smul, ← h, inv_smul_smul]
  · rintro ⟨k, rfl⟩
    have hk : complexPlaceHom F (k : KPSmoothActualFlowData.GInfinity F) • origin F =
        origin F := by
      rw [← archBasepoint_eq_smul F (k : KPSmoothActualFlowData.GInfinity F)]
      exact (mem_KInfinity_iff F (k : KPSmoothActualFlowData.GInfinity F)).mp k.2
    rw [map_mul, mul_smul, hk]

def sectionGL (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    InfinitePlace F → GL (Fin 2) ℂ := fun w =>
  KPArithmeticAction.hyperbolicGLSection (x (infinitePlaceEquiv F ζ hζ w))

def sectionMatrix (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ := fun w =>
  (sectionGL F ζ hζ x w : Matrix (Fin 2) (Fin 2) ℂ)

theorem sectionMatrix_formula (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) (w : InfinitePlace F) :
    sectionMatrix F ζ hζ x w =
      !![(Real.exp (x (infinitePlaceEquiv F ζ hζ w)).2 : ℂ),
          (x (infinitePlaceEquiv F ζ hζ w)).1; 0, 1] := by
  simp only [sectionMatrix, sectionGL, KPArithmeticAction.hyperbolicGLSection,
    KPArch.height]
  rfl

def iwasawaSection (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    KPSmoothActualFlowData.GInfinity F := fun w =>
  Matrix.ProjGenLinGroup.mk (sectionGL F ζ hζ x w)

theorem archBasepoint_iwasawaSection (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    KPMsFixedHaarDisintegration.archBasepoint F (iwasawaSection F ζ hζ x) = x := by
  funext i
  rw [archBasepoint_eq_smul]
  show (complexPlaceHom F (iwasawaSection F ζ hζ x)) i • (origin F i) = x i
  show Matrix.ProjGenLinGroup.mk
      (sectionGL F ζ hζ x (KPCusp.complexPlace F i)) • ((0, 0) : KPArch.H3) = x i
  rw [Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action]
  show KPArch.action (KPArithmeticAction.hyperbolicGLSection
    (x (infinitePlaceEquiv F ζ hζ (KPCusp.complexPlace F i)))) (0, 0) = x i
  rw [KPArithmeticAction.hyperbolicGLSection_action,
    infinitePlaceEquiv_complexPlace F ζ hζ i]

theorem section_continuous (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    Continuous (iwasawaSection F ζ hζ) := by
  apply continuous_pi
  intro w
  refine QuotientGroup.continuous_mk.comp ?_
  exact KPArithmeticAction.hyperbolicGLSection_continuous.comp (continuous_apply _)

end DedekindZetaZeroFree.KPContSectorArchSphericalFibers

end
