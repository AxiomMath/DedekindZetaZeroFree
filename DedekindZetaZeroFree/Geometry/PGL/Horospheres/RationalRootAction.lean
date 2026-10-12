module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Matrix

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

theorem upper_root_action (z : ℂ) (q : KPArch.H3) :
    KPArch.action (KubotaRankTwo.n ℂ z) q = (q.1 + z, q.2) := by
  apply Prod.ext
  · simp [KPArch.action, KPArch.actionDenominator, KubotaRankTwo.coe_n]
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KubotaRankTwo.coe_n, Matrix.det_fin_two]

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

def archRoot (z : NumberField.InfinitePlace F → ℂ) :
    KPSmoothActualFlowData.GInfinity F :=
  fun v => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ (z v))

def translateCross (z : NumberField.InfinitePlace F → ℂ)
    (p : KPCuspCharts.Cross F) : KPCuspCharts.Cross F :=
  (fun i => p.1 i + z (KPCusp.complexPlace F i), p.2)

theorem projective_action_inv_cancel (g : Matrix.ProjGenLinGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action g⁻¹.out (KPArch.action g.out q) = q := by
  rw [← projective_action_mul, inv_mul_cancel]
  have he : (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ) =
      Matrix.ProjGenLinGroup.mk 1 := (map_one _).symm
  rw [he, projective_action_mk]
  exact (KPArch.action_laws 1 1 q).1

theorem archBasepoint_conjugated_root
    (σ a : KPSmoothActualFlowData.GInfinity F)
    (z : NumberField.InfinitePlace F → ℂ) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a = fun i =>
      KPArch.action (σ (KPCusp.complexPlace F i)).out
        (KPCuspCharts.toArch F (p,t) i)) :
    KPMsFixedHaarDisintegration.archBasepoint F
      (σ * archRoot z * σ⁻¹ * a) = fun i =>
      KPArch.action (σ (KPCusp.complexPlace F i)).out
        (KPCuspCharts.toArch F (translateCross z p,t) i) := by
  funext i
  rw [archBasepoint_mul]
  change KPArch.action ((σ (KPCusp.complexPlace F i) *
      archRoot z (KPCusp.complexPlace F i)) *
      (σ (KPCusp.complexPlace F i))⁻¹).out
    (KPMsFixedHaarDisintegration.archBasepoint F a i) = _
  rw [ha, projective_action_mul, projective_action_mul,
    projective_action_inv_cancel]
  congr 1
  rw [archRoot, projective_action_mk, upper_root_action]
  rfl

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

theorem archBasepoint_rational_conjugated_root
    (σ : KPCuspArithmetic.PGL2 F) (a : KPSmoothActualFlowData.GInfinity F)
    (z : NumberField.InfinitePlace F → ℂ) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t))) :
    KPMsFixedHaarDisintegration.archBasepoint F
      (archRational σ * archRoot z * (archRational σ)⁻¹ * a) =
        KPCuspSiegel.action F σ (KPCuspCharts.toArch F (translateCross z p,t)) := by
  rw [← archRational_action] at ha ⊢
  exact archBasepoint_conjugated_root _ _ _ _ _ ha

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end
