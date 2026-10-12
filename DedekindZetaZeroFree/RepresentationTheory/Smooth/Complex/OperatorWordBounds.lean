module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.SmoothExtensionByHarmonicDensity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCyclicity

@[expose] public section

noncomputable section
open scoped Topology NNReal Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_principalSeries_barrelled_complex → evaluation_principalSeries_barrelled_complex
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_linearMap_continuous_of_point_evaluations → evaluation_linearMap_continuous_of_point_evaluations
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_point_eval_continuous → evaluation_point_eval_continuous
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem actualDerivative_continuous (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (NativeComplexHCOperators.derivative s X) := by
  apply evaluation_linearMap_continuous_of_point_evaluations
  intro g
  letI := evaluation_principalSeries_barrelled_complex s
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  let ev (a : ComplexGL2) : PrincipalSeries s →L[ℂ] ℂ :=
    { toFun := fun f => f a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      cont := evaluation_point_eval_continuous s a }
  let D (t : ℝ) : PrincipalSeries s →L[ℂ] ℂ :=
    (t : ℂ)⁻¹ • (ev (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)) - ev g)
  have ht : Filter.Tendsto (fun t f => D t f) (nhdsWithin 0 {0}ᶜ)
      (nhds (fun f => NativeComplexHCOperators.derivative s X f g)) := by
    rw [tendsto_pi_nhds]
    intro f
    have hd := NativeComplexHCOperators.hasDerivAt_flow s X f g
    have hz : KPSmoothActualFlowData.matrixExponential ((0 : ℂ) • X) = 1 := by
      apply Units.ext
      simp [KPSmoothActualFlowData.matrixExponential]
    convert hd.tendsto_slope_zero using 1
    funext t
    simp only [D, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ev,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, zero_add,
      Complex.ofReal_zero, hz, mul_one]
  exact (continuousLinearMapOfTendsto D ht).continuous

theorem native_operators_continuous (i : Fin 6) :
    Continuous (NativeComplexHCOperators.operators i) := by
  exact ((actualDerivative_continuous negativeParameter (KPSmoothActualFlowData.basisMatrix i)).comp
    continuous_subtype_val).subtype_mk _

theorem complexGenerator_continuous (a : HCGeneration.ComplexGenerator) :
    Continuous (HCGeneration.complexGenerator a) := by
  cases a with
  | inr i => exact native_operators_continuous i
  | inl k =>
    apply Continuous.subtype_mk
    have hc : Continuous (fun f : complexCore =>
        (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k),f.val)) :=
      continuous_const.prodMk continuous_subtype_val
    exact (pi_continuous negativeParameter).comp hc

theorem complexWord_continuous (a : List HCGeneration.ComplexGenerator) :
    Continuous (HCGeneration.complexWord a) := by
  induction a with
  | nil => exact continuous_id
  | cons a w hw => exact (complexGenerator_continuous a).comp hw

theorem complexWord_seminorm_bound (a : List HCGeneration.ComplexGenerator) (orders : Finset ℕ) :
    ∃ inputOrders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ v : complexCore, (orders.sup coreSeminorm) (HCGeneration.complexWord a v) ≤
        B * (inputOrders.sup coreSeminorm) v := by
  let Q : Seminorm ℂ complexCore := (orders.sup coreSeminorm).comp (HCGeneration.complexWord a)
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (fun i _ => core_withSeminorms.continuous_seminorm i)).comp (complexWord_continuous a)
  exact Seminorm.bound_of_continuous core_withSeminorms Q hQ
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
