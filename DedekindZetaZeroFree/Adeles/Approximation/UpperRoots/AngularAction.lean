module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Matrix
namespace DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource

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

variable {F : Type} [Field F] [NumberField F]

theorem archBasepoint_mul (g h : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F (g * h) = fun i =>
      KPArch.action (g (KPCusp.complexPlace F i)).out
        (KPMsFixedHaarDisintegration.archBasepoint F h i) := by
  funext i
  exact projective_action_mul _ _ _

theorem projective_action_inv_cancel (g : Matrix.ProjGenLinGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action g⁻¹.out (KPArch.action g.out q) = q := by
  rw [← projective_action_mul, inv_mul_cancel]
  have he : (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ) =
      Matrix.ProjGenLinGroup.mk 1 := (map_one _).symm
  rw [he, projective_action_mk]
  exact (KPArch.action_laws 1 1 q).1

def archRational (σ : KPCuspArithmetic.PGL2 F) :
    KPSmoothActualFlowData.GInfinity F := fun v =>
  Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map v.embedding σ.out)

theorem archRational_action (σ : KPCuspArithmetic.PGL2 F)
    (q : KPFiniteCuspAtlas.SymmetricSpace F) :
    (fun i => KPArch.action (archRational σ (KPCusp.complexPlace F i)).out (q i)) =
      KPCuspSiegel.action F σ q := by
  have he : σ = Matrix.ProjGenLinGroup.mk σ.out := (Quotient.out_eq σ).symm
  conv_rhs => rw [he, KPCuspSiegel.action_mk]
  funext i
  exact projective_action_mk _ _

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteParameter (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPGlobalTorusFunctionData.Adeles F := (0,z)

theorem finite_root_mem
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z) ∈
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [MonoidHom.mem_ker]
  unfold KPGlobalTorusFunctionData.N KPAdelicCoverRestrictedProduct.scalarQuotient
    KPCuspGenuineMonodromy.archProjection
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.lift_mk']
  simp only [MonoidHom.comp_apply, KPAdelicCoverRestrictedProduct.projection_amalgamation]
  funext w
  change Matrix.ProjGenLinGroup.mk
    (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
      (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
        (KPGlobalTorusFunctionData.rootTuple F ζ hζ (finiteParameter F z)))) = 1
  change Matrix.ProjGenLinGroup.mk
    (KPLocalCover.projection F ζ hζ (Sum.inl w)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w)
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w) (finiteParameter F z)))) = 1
  simp [finiteParameter, KPAdelicCoverRestrictedProduct.adeleEval,
    KPStandardLocalRootLifts.N, KPLocalCover.sectionMap, KPLocalCover.projection,
    KubotaRankTwo.n, RingHom.fst]
  have he : Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))
      (by simp [Matrix.det_fin_two]) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  change Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w))) _ ∈ _
  exact he.symm ▸ Subgroup.one_mem _

def finiteRoot
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
  ⟨KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z), finite_root_mem F ζ hζ z⟩

@[simp] theorem finiteRoot_zero : finiteRoot F ζ hζ 0 = 1 := by
  apply Subtype.ext
  change KPGlobalTorusFunctionData.N F ζ hζ 0 = 1
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPRationalAdelicSplitting.N F ζ hζ 0) = 1
  rw [KPRationalAdelicSplitting.N_zero, map_one]

open KPAdelicCoverRestrictedProduct
attribute [local instance] localTopology

 def finiteRootTupleHom :
    Multiplicative (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) →*
      RestrictedCover F ζ hζ where
  toFun z := KPGlobalTorusFunctionData.rootTuple F ζ hζ (finiteParameter F z.toAdd)
  map_one' := by
    apply Subtype.ext
    funext v
    change KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v 0) = 1
    rw [map_zero, KPStandardLocalRootLifts.N_zero]
  map_mul' z w := by
    apply Subtype.ext
    funext v
    change KPStandardLocalRootLifts.N F ζ hζ v
      (adeleEval F v (finiteParameter F (z.toAdd + w.toAdd))) =
        KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v (finiteParameter F z.toAdd)) *
        KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v (finiteParameter F w.toAdd))
    have he : finiteParameter F (z.toAdd + w.toAdd) =
        finiteParameter F z.toAdd + finiteParameter F w.toAdd := by
      apply Prod.ext
      · exact (add_zero 0).symm
      · rfl
    rw [he, map_add, KPStandardLocalRootLifts.N_add]

end DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource

end
