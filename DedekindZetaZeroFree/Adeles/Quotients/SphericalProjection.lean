module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SphericalHaarDisintegrationData

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace DedekindZetaZeroFree.KPMsFixedHaar
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F

 theorem archProjection_compare (g : KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) g
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _ (projection F ζ hζ g)) =
    Matrix.ProjGenLinGroup.map _ (Matrix.ProjGenLinGroup.mk (matrixEval F (Sum.inl w) (projection F ζ hζ g)))
  rw [Matrix.ProjGenLinGroup.map_mk, Matrix.GeneralLinearGroup.map_comp]
  rfl

private theorem insertion_commutes_cover (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  have hc : c.val ∈ (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
    rw [MonoidHom.mem_ker]
    funext w
    rw [archProjection_compare]
    have he := c.property
    rw [MonoidHom.mem_ker] at he
    rw [he]
    exact map_one _
  have hm := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.2.2.2.1
  rw [hm] at hc
  exact RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a ⟨c.val, hc⟩

private theorem projective_equiv_injective {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) : Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) e.toRingHom) := by
  intro x y h
  have h' := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) h
  simp only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp] at h'
  simpa using h'

private theorem complex_kernel_mem {g : KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ}
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g = 1) :
    g ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [MonoidHom.mem_ker]
  funext w
  apply projective_equiv_injective
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w))
  rw [← archProjection_compare, hg]
  exact (map_one _).symm

 theorem projective_action_mk (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action (Matrix.ProjGenLinGroup.mk g).out q = KPArch.action g q := by
  have he : Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out =
      Matrix.ProjGenLinGroup.mk g := Quotient.out_eq _
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  calc
    _ = KPArch.action ((Matrix.ProjGenLinGroup.mk g).out *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) q := by
      rw [(KPArch.action_laws _ _ _).2, KPArch.scalar_action]
    _ = KPArch.action g q := congrArg (fun k => KPArch.action k q) hu

 theorem projective_action_mul (g h : Matrix.ProjGenLinGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action (g * h).out q =
      KPArch.action g.out (KPArch.action h.out q) := by
  have he : g * h = Matrix.ProjGenLinGroup.mk (g.out * h.out) := by
    rw [map_mul]
    exact congrArg₂ (· * ·) (Quotient.out_eq g).symm (Quotient.out_eq h).symm
  rw [he, projective_action_mk, (KPArch.action_laws _ _ _).2]

private theorem archBasepoint_mul (g h : KPSmoothActualFlowData.GInfinity F) :
    archBasepoint F (g * h) = fun i =>
      KPArch.action (g (KPCusp.complexPlace F i)).out
        (archBasepoint F h i) := by
  funext i
  exact projective_action_mul _ _ _

 def archRational (σ : KPCuspArithmetic.PGL2 F) :
    KPSmoothActualFlowData.GInfinity F := fun v =>
  Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map v.embedding σ.out)

 theorem archRational_action (σ : KPCuspArithmetic.PGL2 F)
    (q : KPFiniteCuspAtlas.SymmetricSpace F) :
    (fun i => KPArch.action (archRational F σ (KPCusp.complexPlace F i)).out (q i)) =
      KPCuspSiegel.action F σ q := by
  have he : σ = Matrix.ProjGenLinGroup.mk σ.out := (Quotient.out_eq σ).symm
  conv_rhs => rw [he, KPCuspSiegel.action_mk]
  funext i
  exact projective_action_mk _ _

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

 def rationalEquiv : KPCuspArithmetic.PGL2 F ≃* KPRationalAdelicSplitting.RationalPGL2 F :=
  QuotientGroup.quotientMulEquivOfEq Matrix.GeneralLinearGroup.center_eq_range_scalar

private theorem rationalEquiv_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalEquiv F (Matrix.ProjGenLinGroup.mk m) = KPRationalAdelicSplitting.rationalPGLQuotient F m :=
  QuotientGroup.quotientMulEquivOfEq_mk _ m

 def rationalLift : KPCuspArithmetic.PGL2 F →* Cover F ζ hζ :=
  (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp (rationalEquiv F).toMonoidHom

private theorem rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk m) = scalarQuotient F ζ hζ (rationalSection F ζ hζ m) := by
  simp [rationalLift, rationalEquiv_mk]

 theorem rationalLift_finite (γ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ (rationalLift F ζ hζ γ) = KPFiniteComponents.diagonal F γ := by
  obtain ⟨m, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  rw [rationalLift_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (projection F ζ hζ (rationalSection F ζ hζ m))) = _
  exact congrArg (fun k => Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (RingHom.snd _ _) k))
      (projection_rationalSection F ζ hζ m)

 theorem rationalLift_arch (γ : KPCuspArithmetic.PGL2 F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (rationalLift F ζ hζ γ) = archRational F γ := by
  obtain ⟨m, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  rw [rationalLift_mk]
  funext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (projection F ζ hζ (rationalSection F ζ hζ m))) = _
  rw [projection_rationalSection]
  have hmap : (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
      ((adeleEval F (Sum.inl w)).comp (algebraMap F (Adeles F))) = w.embedding := by
    ext x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap F w.Completion x) = w.embedding x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      ((WithAbs.equiv w.1).symm x : w.Completion) = _
    simp
  change Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ m)) = _
  simp only [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
  rw [RingHom.comp_assoc, hmap]
  unfold archRational
  simp only [MonoidHom.comp_apply]
  rw [← Matrix.ProjGenLinGroup.map_mk, ← Matrix.ProjGenLinGroup.map_mk]
  exact congrArg (Matrix.ProjGenLinGroup.map w.embedding)
    (Quotient.out_eq (Matrix.ProjGenLinGroup.mk m)).symm

 theorem rationalLift_split (γ : KPCuspArithmetic.PGL2 F) :
    ∃ ε : rootsOfUnity 3 F, rationalLift F ζ hζ γ =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) *
        ((KPCuspGenuineMonodromy.central F ζ hζ ε *
          KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) : KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
  let r := rationalLift F ζ hζ γ
  let i := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ)
  have hm : i⁻¹ * r ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    apply complex_kernel_mem F ζ hζ
    rw [map_mul, map_inv]
    change (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (archRational F γ)))⁻¹ *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ r = 1
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, rationalLift_arch, inv_mul_cancel]
  let s : KPFiniteCuspAtlas.FiniteCover F ζ hζ := ⟨i⁻¹ * r, hm⟩
  have hs : r = i * s.val := by dsimp [s]; group
  have hp := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hs
  simp only [r, i, rationalLift_finite, map_mul, finiteProjection_archimedeanInsertion, one_mul] at hp
  have hf : KPCuspGenuineMonodromy.finiteBase F ζ hζ s =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) := by
    rw [← MonoidHom.comp_apply, (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1]
    exact hp.symm
  have hm' : s * (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)⁻¹ ∈
      (KPCuspGenuineMonodromy.central F ζ hζ).range := by
    rw [(KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1, MonoidHom.mem_ker,
      map_mul, map_inv, hf, mul_inv_cancel]
  obtain ⟨ε, hε⟩ := hm'
  refine ⟨ε, ?_⟩
  have he : s = KPCuspGenuineMonodromy.central F ζ hζ ε * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ := by
    rw [hε]; group
  exact hs.trans (congrArg (fun c : KPFiniteCuspAtlas.FiniteCover F ζ hζ => i * c.val) he)

 theorem actual_split : ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ,
    ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, _, _, hker, _, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hf : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ = KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    rw [← hker]
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      exact MonoidHom.mem_ker.mp (complex_kernel_mem F ζ hζ h)
    · intro h
      funext w
      rw [archProjection_compare, h]
      exact map_one _
  let ee : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ :=
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (Homeomorph.setCongr (congrArg (fun L : Subgroup (Cover F ζ hζ) =>
        (L : Set (Cover F ζ hζ))) hf.symm))).trans e.toHomeomorph
  exact ⟨ee, fun a c => he a _⟩

private theorem insertion_mul (a b : KPSmoothActualFlowData.GInfinity F) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (a * b) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ b := by
  obtain ⟨i, hi⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ (a * b) =
    RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ a * RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ b
  rw [← hi, ← hi, ← hi]
  exact map_mul i a b

private theorem central_comm (ε : rootsOfUnity 3 F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c = c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

private theorem archBasepoint_rational (γ : KPCuspArithmetic.PGL2 F) (a : KPSmoothActualFlowData.GInfinity F) :
    archBasepoint F (archRational F γ * a) = γ • archBasepoint F a := by
  rw [archBasepoint_mul, archRational_action]
  rfl

private theorem glOrbit_continuous (z : KPArch.H3) :
    Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ => KPArch.action g z) := by
  have hc (i j : Fin 2) : Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ => g i j) :=
    Units.continuous_val.matrix_elem i j
  have hd : Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ => KPArch.actionDenominator g z) := by
    unfold KPArch.actionDenominator
    fun_prop
  have hn : ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ, KPArch.actionDenominator g z ≠ 0 :=
    fun g => ne_of_gt (KPArch.actionDenominator_pos g z)
  apply Continuous.prodMk
  · exact (((hc 0 0 |>.mul continuous_const |>.add (hc 0 1)).mul
      (hc 1 0 |>.mul continuous_const |>.add (hc 1 1)).star).add
        (((hc 0 0).mul (hc 1 0).star).mul continuous_const)).div
          (Complex.continuous_ofReal.comp hd) (fun g => by exact_mod_cast hn g)
  · have hp : ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * KPArch.height z /
          KPArch.actionDenominator g z ≠ 0 := by
      intro g
      exact ne_of_gt (div_pos (mul_pos (norm_pos_iff.mpr g.det_ne_zero)
        (Real.exp_pos _)) (KPArch.actionDenominator_pos g z))
    exact (((Units.continuous_val.matrix_det).norm.mul continuous_const).div hd hn).log hp

 theorem projectiveOrbit_continuous (z : KPArch.H3) :
    Continuous (fun g : Matrix.ProjGenLinGroup (Fin 2) ℂ => KPArch.action g.out z) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ => KPArch.action (Matrix.ProjGenLinGroup.mk g).out z)
  simpa only [projective_action_mk] using glOrbit_continuous z

private theorem archBasepoint_continuous : Continuous (archBasepoint F) := by
  apply continuous_pi
  intro i
  exact (projectiveOrbit_continuous (0,0)).comp (continuous_apply (KPCusp.complexPlace F i))

 def forgetMap (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup) : Spherical F ζ hζ V → Spherical F ζ hζ U :=
  Quotient.lift (fun p => Quotient.mk _ p) (by
    intro p q hpq
    obtain ⟨γ, ε, u, hx, hc⟩ := hpq
    apply Quotient.sound
    exact ⟨γ, ε, ⟨u.val, h u.property⟩, hx, hc⟩)

private theorem forgetMap_continuous (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup) : Continuous (forgetMap F ζ hζ V U h) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact continuous_quotient_mk'

 def rawProjection (U : Level F ζ hζ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ)
    (g : Cover F ζ hζ) : Spherical F ζ hζ U :=
  Quotient.mk _ (archBasepoint F (e.symm g).1, (e.symm g).2)

private theorem rawProjection_formula (U : Level F ζ hζ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)
    (a : KPSmoothActualFlowData.GInfinity F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    rawProjection F ζ hζ U e (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) =
      Quotient.mk _ (archBasepoint F a, c) := by
  rw [← he]
  simp [rawProjection]

 theorem rawProjection_rational (U : Level F ζ hζ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)
    (γ : KPCuspArithmetic.PGL2 F) (g : Cover F ζ hζ) :
    rawProjection F ζ hζ U e g = rawProjection F ζ hζ U e (rationalLift F ζ hζ γ * g) := by
  obtain ⟨ε, hε⟩ := rationalLift_split F ζ hζ γ
  let a := (e.symm g).1
  let c := (e.symm g).2
  have hg : g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
    rw [← he]
    exact (e.apply_symm_apply g).symm
  let d := KPCuspGenuineMonodromy.central F ζ hζ ε * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ
  have hprod : rationalLift F ζ hζ γ * g =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ * a) * (d * c).val := by
    rw [hε, hg, insertion_mul]
    change (_ * d.val) * (_ * c.val) = (_ * _) * (d.val * c.val)
    have hcomm := (insertion_commutes_cover F ζ hζ a d).symm
    exact hcomm.mul_mul_mul_comm _ _
  rw [hg, rawProjection_formula F ζ hζ U e he, ← hg, hprod, rawProjection_formula F ζ hζ U e he]
  apply Quotient.sound
  refine ⟨γ, ε, 1, archBasepoint_rational F γ a, ?_⟩
  change d * c = _
  dsimp [d]
  rw [central_comm]
  simp

 def projection (U : Level F ζ hζ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) :
    X F ζ hζ → Spherical F ζ hζ U :=
  Quotient.lift (rawProjection F ζ hζ U e) (by
    intro x y h
    obtain ⟨δ, hδ⟩ := QuotientGroup.rightRel_apply.mp h
    let γ := (rationalEquiv F).symm δ
    have hl : rationalLift F ζ hζ γ = KPRationalAdelicSplitting.rationalPGLHom F ζ hζ δ := by
      simp [rationalLift, γ]
    have hy : y = rationalLift F ζ hζ γ * x := by
      rw [hl, hδ]
      group
    rw [hy]
    exact rawProjection_rational F ζ hζ U e he γ x)

private theorem projection_continuous (U : Level F ζ hζ)
    (e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ Cover F ζ hζ)
    (he : ∀ a c, e (a,c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) :
    Continuous (projection F ζ hζ U e he) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (rawProjection F ζ hζ U e)
  exact continuous_quotient_mk'.comp
    (((archBasepoint_continuous F).comp (continuous_fst.comp e.symm.continuous)).prodMk
      (continuous_snd.comp e.symm.continuous))

theorem spherical_transport_exists
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    Nonempty (SphericalTransport F ζ hζ) := by
  obtain ⟨e, he⟩ := actual_split F ζ hζ
  refine ⟨{
    projection := fun U => projection F ζ hζ U e he
    continuous := fun U => projection_continuous F ζ hζ U e he
    formula := ?_
    forget := fun V U h => forgetMap F ζ hζ V U h
    forget_formula := ?_
    forget_continuous := fun V U h => forgetMap_continuous F ζ hζ V U h
    compatible := ?_
  }⟩
  · intro U a c
    exact rawProjection_formula F ζ hζ U e he a c
  · intro V U h x c
    rfl
  · intro V U h x
    induction x using Quotient.inductionOn with
    | h g => rfl

end DedekindZetaZeroFree.KPMsFixedHaar

end
