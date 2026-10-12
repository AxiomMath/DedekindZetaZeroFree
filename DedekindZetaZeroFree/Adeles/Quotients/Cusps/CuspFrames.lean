module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsActualCuspSource
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev X := KPSmoothLocalQuotientCharts.X F ζ hζ
abbrev Level := KPGlobalTorusFunctionData.FiniteLevel F ζ hζ
abbrev rationalLift (γ : Matrix.ProjGenLinGroup (Fin 2) F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ
      (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective γ)))
theorem projection_compare (g : G F ζ hζ) (w : NumberField.InfinitePlace F) :
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

theorem arch_finite_factorization (g : G F ζ hζ) :
    ∃ (a : KPSmoothActualFlowData.GInfinity F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ),
      g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by

  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  let c := (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)⁻¹ * g
  have h : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c = 1 := by
    dsimp only [c]
    rw [map_mul, map_inv]
    change (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a))⁻¹ * a = 1
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, inv_mul_cancel]
  have hc : c ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    change KPCuspGenuineMonodromy.archProjection F ζ hζ c = 1
    funext w
    have hw := congrFun h w
    rw [projection_compare] at hw
    let eqv := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have hh := congrArg (Matrix.ProjGenLinGroup.map eqv.symm.toRingHom) hw
    dsimp only [eqv] at hh
    simpa only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom, Matrix.ProjGenLinGroup.map_id,
      MonoidHom.id_apply, map_one, Pi.one_apply] using hh
  refine ⟨a, ⟨c, hc⟩, ?_⟩
  change g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
    ((KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)⁻¹ * g)
  rw [mul_inv_cancel_left]

def archRational (σ : KPCuspArithmetic.PGL2 F) : KPSmoothActualFlowData.GInfinity F :=
  fun v => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map v.embedding σ.out)

theorem rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk m) =
      scalarQuotient F ζ hζ (rationalHom F ζ hζ m) := by
  let n := Classical.choose (Matrix.ProjGenLinGroup.mk_surjective (Matrix.ProjGenLinGroup.mk m))
  have hn : Matrix.ProjGenLinGroup.mk n = Matrix.ProjGenLinGroup.mk m :=
    Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective (Matrix.ProjGenLinGroup.mk m))
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hn
  let φ := (scalarQuotient F ζ hζ).comp (rationalHom F ζ hζ)
  have hscalar : φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1 :=
    KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨z, rfl⟩
  change φ n = φ m
  rw [← hz, map_mul, hscalar, mul_one]

theorem rationalLift_archProjection (σ : KPCuspArithmetic.PGL2 F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (rationalLift F ζ hζ σ) = archRational F σ := by
  have hs : σ = Matrix.ProjGenLinGroup.mk σ.out := (Quotient.out_eq σ).symm
  rw [hs, rationalLift_mk]
  funext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (projection F ζ hζ (rationalSection F ζ hζ σ.out))) = _
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
    (Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ σ.out)) = _
  simp only [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
  rw [RingHom.comp_assoc, hmap]
  unfold archRational
  simp only [MonoidHom.comp_apply]
  rw [← Matrix.ProjGenLinGroup.map_mk, ← Matrix.ProjGenLinGroup.map_mk]
  exact congrArg (Matrix.ProjGenLinGroup.map w.embedding)
    (Quotient.out_eq (Matrix.ProjGenLinGroup.mk σ.out)).symm

theorem finiteProjection_local_infinite (v : NumberField.InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v)) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v) g)) = 1 := by
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
    · by_cases hij : i = j <;> subst_vars <;> simp [*] <;> rfl
  rw [he, map_one]

theorem finiteProjection_insertion (a : KPSmoothActualFlowData.GInfinity F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = 1 := by
  unfold KPSmoothActualFlowData.archimedeanInsertion
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, finiteProjection_local_infinite]
  simp

theorem finiteProjection_rationalLift (σ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (rationalLift F ζ hζ σ) = KPFiniteComponents.diagonal F σ := by
  obtain ⟨m, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  rw [rationalLift_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (projection F ζ hζ (rationalHom F ζ hζ m))) = _
  exact congrArg (fun k => Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (RingHom.snd _ _) k))
      (projection_rationalSection F ζ hζ m)

theorem rationalLift_finite_factor (γ : KPCuspArithmetic.PGL2 F) :
    ∃ ε : rootsOfUnity 3 F,
      rationalLift F ζ hζ γ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) *
        ((KPCuspGenuineMonodromy.central F ζ hζ ε *
          KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) : KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
  obtain ⟨a, s, hs⟩ := arch_finite_factorization F ζ hζ (rationalLift F ζ hζ γ)
  have ha : a = archRational F γ := by
    have h := congrArg (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ) hs
    have hf : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ s.val = 1 := by
      funext w
      rw [projection_compare]
      have hh := MonoidHom.mem_ker.mp s.property
      rw [hh]
      exact map_one _
    rw [map_mul, hf, mul_one, rationalLift_archProjection] at h
    change archRational F γ = PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) at h
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion] at h
    exact h.symm
  subst a
  have hp := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hs
  simp only [finiteProjection_rationalLift, map_mul, finiteProjection_insertion, one_mul] at hp
  have hf : KPCuspGenuineMonodromy.finiteBase F ζ hζ s =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) := by
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
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) * c.val) he)

theorem insertion_commutes (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  obtain ⟨e, he, _, _, hker, _, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hc : c.val ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
    rw [← hker, MonoidHom.mem_ker]
    funext w
    rw [projection_compare]
    have h := MonoidHom.mem_ker.mp c.property
    rw [h]
    exact map_one _
  exact RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a ⟨c.val, hc⟩

theorem central_comm (ε : rootsOfUnity 3 F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c = c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

theorem projective_action_mk (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (q : KPArch.H3) :
    KPArch.action (Matrix.ProjGenLinGroup.mk g).out q = KPArch.action g q := by
  have he : Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out =
      Matrix.ProjGenLinGroup.mk g := Quotient.out_eq _
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  calc
    _ = KPArch.action ((Matrix.ProjGenLinGroup.mk g).out *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) q := by
      rw [(KPArch.action_laws _ _ _).2, KPArch.scalar_action]
    _ = KPArch.action g q := congrArg (fun k => KPArch.action k q) hu

theorem archBasepoint_rational_mul (γ : KPCuspArithmetic.PGL2 F)
    (a : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F (archRational F γ * a) =
      KPCuspSiegel.action F γ (KPMsFixedHaarDisintegration.archBasepoint F a) := by
  have he : γ = Matrix.ProjGenLinGroup.mk γ.out := (Quotient.out_eq γ).symm
  conv_rhs => rw [he, KPCuspSiegel.action_mk]
  funext i
  change KPArch.action ((archRational F γ * a) (KPCusp.complexPlace F i)).out (0,0) = _
  have hm : ∀ g h : Matrix.ProjGenLinGroup (Fin 2) ℂ,
      KPArch.action (g * h).out (0,0) = KPArch.action g.out (KPArch.action h.out (0,0)) := by
    intro g h
    have he : g * h = Matrix.ProjGenLinGroup.mk (g.out * h.out) := by
      rw [map_mul]
      exact congrArg₂ (· * ·) (Quotient.out_eq g).symm (Quotient.out_eq h).symm
    rw [he, projective_action_mk, (KPArch.action_laws _ _ _).2]
  change KPArch.action (archRational F γ (KPCusp.complexPlace F i) *
    a (KPCusp.complexPlace F i)).out (0,0) = _
  rw [hm]
  exact congrArg (fun k => k (KPArch.action (a (KPCusp.complexPlace F i)).out (0,0)))
    (funext (fun q => projective_action_mk _ q))

variable {F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (J : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable {U : Level F ζ hζ}

abbrev Atlas := H.atlas J
abbrev Cusp := KPMsFixedHaarDisintegration.CuspIndex (Atlas (H := H) J)

def cuspEnd (j : Cusp (H := H) J) (Y : ℝ) : Set (X F ζ hζ) :=
  (P.projection J) ⁻¹'
    (KPFiniteCuspAtlas.componentMap F ζ hζ J
      ((Atlas (H := H) J).representative j.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ J
          ((Atlas (H := H) J).representative j.1))
        (((Atlas (H := H) J).cuspAtlas j.1).representative j.2)
        (KPMsFixedHaarDisintegration.logHeight (F := F) Y))

def AdmissibleFrame (j : Cusp (H := H) J) (Y : ℝ)
    (x : X F ζ hζ) (g : G F ζ hζ) : Prop :=
  KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x ∧
    ∃ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
      (t : ℝ) (ε : rootsOfUnity 3 F)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      KPMsFixedHaarDisintegration.archBasepoint F a =
        KPCuspSiegel.action F
          (((Atlas (H := H) J).cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (p,t)) ∧
      g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((Atlas (H := H) J).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val

theorem spherical_cusp_representative (j : Cusp (H := H) J) (Y : ℝ)
    (x : X F ζ hζ) (hx : x ∈ cuspEnd J j Y) :
    ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
      KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      P.projection J x = Quotient.mk _
        (KPCuspSiegel.action F
          (((Atlas (H := H) J).cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (p,t)),
          (Atlas (H := H) J).representative j.1) := by
  obtain ⟨z, hz, he⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hz
  obtain ⟨v, hv, rfl⟩ := hq
  let hd := KPCuspCharts.positive_dimension F H.totallyComplex
  let c := (KPCuspCharts.toArchHomeomorph F hd).symm v
  have hc : KPCuspCharts.toArch F c = v :=
    (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply v
  refine ⟨c.1, c.2, ?_, ?_⟩
  · change KPMsFixedHaarDisintegration.logHeight (F := F) Y <
      KPCuspLogShape.meanHeight _ v at hv
    rw [← hc, KPCuspCharts.toArch_meanHeight F hd] at hv
    exact hv
  · rw [← he, ← hc]
    rfl

theorem cusp_lift_exists
    (hlevel : KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
      J.toOpenSubgroup.toSubgroup.map (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype)
    (j : Cusp (H := H) J) (Y : ℝ)
    (x : X F ζ hζ) (hx : x ∈ cuspEnd J j Y) :
    ∃ g : G F ζ hζ,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x ∧
      AdmissibleFrame (U := U) J j Y x g := by
  obtain ⟨p, t, ht, hx'⟩ := spherical_cusp_representative J j Y x hx
  obtain ⟨a, c, hc⟩ := arch_finite_factorization F ζ hζ (Quotient.out x)
  have hqx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) = x := by
    rw [← hc]
    exact Quotient.out_eq x
  have he := (P.formula J a c).symm.trans
    ((congrArg (P.projection J) hqx).trans hx')
  obtain ⟨γ, ε, u, ha, hf⟩ := Quotient.exact he
  change (Atlas (H := H) J).representative j.1 =
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u.val at hf
  obtain ⟨η, hγ⟩ := rationalLift_finite_factor F ζ hζ γ
  let a' := archRational F γ * a
  let ε' := η * ε⁻¹
  let u' : KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    ⟨((u⁻¹).val : KPFiniteCuspAtlas.FiniteCover F ζ hζ).val, by
      rw [hlevel]
      exact ⟨(u⁻¹).val, (u⁻¹).property, rfl⟩⟩
  let g' := rationalLift F ζ hζ γ * Quotient.out x
  have hgx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g' = x := by
    change Quotient.mk (QuotientGroup.rightRel
      (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)) _ = _
    rw [← Quotient.out_eq x]
    apply Quotient.sound
    have hrat : rationalLift F ζ hζ γ ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
      let m := Classical.choose (Matrix.ProjGenLinGroup.mk_surjective γ)
      exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F m,
        KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ m⟩
    exact ⟨⟨rationalLift F ζ hζ γ, hrat⟩, rfl⟩
  refine ⟨g', hgx, hgx, a', p, t, ε', u', ht, ?_, ?_⟩
  · rw [archBasepoint_rational_mul]
    exact ha.symm
  · change rationalLift F ζ hζ γ * Quotient.out x = _
    rw [hc, hγ]
    have hm := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
    change _ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ * a) * _ * _ * _
    rw [hm]
    rw [mul_assoc, ← mul_assoc
      ((KPCuspGenuineMonodromy.central F ζ hζ η * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) :
        KPFiniteCuspAtlas.FiniteCover F ζ hζ).val,
      (insertion_commutes F ζ hζ a _).symm.eq]
    have hfin : KPCuspGenuineMonodromy.central F ζ hζ η *
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c =
        (Atlas (H := H) J).representative j.1 *
          KPCuspGenuineMonodromy.central F ζ hζ ε' * (u⁻¹).val := by
      calc
        _ = KPCuspGenuineMonodromy.central F ζ hζ η *
          KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
          (Atlas (H := H) J).representative j.1 * (u⁻¹).val := by
            rw [hf, map_inv]
            rw [← central_comm F ζ hζ ε (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)]
            change _ = _ * _ * _ * (u.val)⁻¹
            group
        _ = _ := by
          rw [← map_mul, central_comm]
    have hfin' := congrArg Subtype.val hfin
    dsimp only [a', ε', u'] at *
    simp only [Subgroup.coe_mul] at hfin'
    change _ = _ at hfin'
    simpa only [mul_assoc, Subgroup.coe_mul, KPCuspGenuineMonodromy.central,
      MonoidHom.codRestrict_apply, KPSmoothLocalQuotientCharts.centreMap] using congrArg
      (fun k : G F ζ hζ => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * k) hfin'
end DedekindZetaZeroFree.KPMsActualCuspSource

end
