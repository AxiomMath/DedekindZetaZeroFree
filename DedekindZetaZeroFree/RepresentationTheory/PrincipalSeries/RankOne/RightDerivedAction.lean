module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows

@[expose] public section

noncomputable section
open MeasureTheory NumberField
open scoped Matrix BigOperators Classical InnerProductSpace
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

def noncompactMatrix (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (Real.sqrt 2 : ℂ)) •
    (![!![1, 0; 0, -1], !![0, 1; 1, 0],
      !![0, Complex.I; -Complex.I, 0]] j)

def compactMatrix (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • noncompactMatrix j

abbrev LocalBasis := Bool × Fin 3

def cartanMatrix (b : LocalBasis) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b.1 then compactMatrix b.2 else noncompactMatrix b.2

open scoped Matrix.Norms.Operator in
private theorem matrix_path_diff (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, DifferentiableAt ℝ (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j) 0 := by
  have hmat : DifferentiableAt ℝ (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) 0 := by
    exact (differentiableAt_const _).mul ((differentiable_exp_smul_const ℂ M).differentiableAt.restrictScalars ℝ |>.comp 0 Complex.ofRealCLM.differentiableAt)
  intro i j
  exact (ContinuousLinearMap.proj j).differentiableAt.comp 0
    ((ContinuousLinearMap.proj i).differentiableAt.comp 0 hmat)
open scoped Matrix.Norms.Elementwise in
private theorem local_path_differentiable (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : DifferentiableAt ℝ (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) 0 :=
    differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (matrix_path_diff g M i))
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp (((0 : ℝ) : ℂ) • M)).det ≠ 0 := by
    simpa using Matrix.GeneralLinearGroup.det_ne_zero g
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds hdet)
  have hc := hh.comp 0 hmat
  convert hc using 1
  funext t
  have hu := Matrix.GeneralLinearGroup.det_ne_zero (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))
  have he : ((g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M)) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M) := by
    congr 1
  dsimp only [Function.comp_def]
  rw [← he]
  unfold KPCplxPrincipalSeriesCharts.matrixFunction
  rw [dif_pos (show ((g : Matrix (Fin 2) (Fin 2) ℂ) *
    (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
      simpa only [Units.val_mul] using hu)]
  apply congrArg f.val
  apply Units.ext
  rfl

open scoped Matrix.Norms.Operator in
private theorem matrix_path_hasDeriv_components (g : KPCplxCharacterHaar.ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, HasDerivAt (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j) (((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) M ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hmat := h.const_mul (g : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul, NormedSpace.exp_zero, mul_one, one_mul] at hmat
  intro i j
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) i j)
    (((g : Matrix (Fin 2) (Fin 2) ℂ) *
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (NormedSpace.exp (((0 : ℝ) : ℂ) • M) * M))) 1) i j) 0 at hj
  simpa using hj

open scoped Matrix.Norms.Elementwise in
private theorem raw_derivative_eq (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 =
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val) (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : HasDerivAt (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M))
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) 0 :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (matrix_path_hasDeriv_components g M i))
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hc := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hmat (by simp)
  have heq : (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) =
      KPCplxPrincipalSeriesCharts.matrixFunction f.val ∘ (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M)) := by
    funext t
    have hu := Matrix.GeneralLinearGroup.det_ne_zero (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))
    have he : ((g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M)) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M) := by congr 1
    dsimp only [Function.comp_def]
    rw [← he]
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos (show ((g : Matrix (Fin 2) (Fin 2) ℂ) *
      (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
        simpa only [Units.val_mul] using hu)]
    apply congrArg f.val
    apply Units.ext
    rfl
  rw [heq]
  exact hc.deriv

open scoped Matrix.Norms.Elementwise in
 theorem local_derivative_mem (s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    (fun g => deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0) ∈ KPCplxPrincipalSeriesCharts.principalSeriesSubmodule s := by
  apply (KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s _).mpr
  constructor
  · intro a d b g
    have he : (fun t : ℝ => f (KPCplxPrincipalSeriesCharts.upperTriangular a d b * g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) =
        (fun t : ℝ => (KPCplxPrincipalSeriesCharts.inductionWeight s a d : ℂ) • f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) := by
      funext t
      rw [mul_assoc]
      exact f.property.1 a d b _
    dsimp only
    rw [he]
    exact deriv_const_smul (KPCplxPrincipalSeriesCharts.inductionWeight s a d : ℂ)
      (f := fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) (local_path_differentiable s f g M)
  · have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
    have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
    have hs : IsOpen {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} := isOpen_ne.preimage hcont
    have hd := hf.fderiv_of_isOpen hs (m := (⊤ : ℕ∞)) (by simp)
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m * M) := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => fun i j => ∑ k, m i k * M k j)
      fun_prop
    apply (hd.clm_apply hm.contDiffOn).congr
    intro m hm
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos (show m.det ≠ 0 from hm)]
    exact raw_derivative_eq s f (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm) M

 def rightDerivative (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.PrincipalSeries s :=
  ⟨fun g => deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0,
    local_derivative_mem s X f⟩

private theorem rightDerivative_add (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f h : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    rightDerivative s X (f + h) = rightDerivative s X f + rightDerivative s X h := by
  apply Subtype.ext
  funext g
  have hfh : (fun t : ℝ => (f + h) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) =
      (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) +
        (fun t : ℝ => h (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) := by
    funext t
    rfl
  show deriv (fun t : ℝ =>
      (f + h) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 +
    deriv (fun t : ℝ =>
      h (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0
  rw [hfh]
  exact deriv_add (local_path_differentiable s f g X) (local_path_differentiable s h g X)

private theorem rightDerivative_smul (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    rightDerivative s X (a • f) = a • rightDerivative s X f := by
  apply Subtype.ext
  funext g
  have hsf : (fun t : ℝ => (a • f) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) =
      (fun t : ℝ => a • f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) := by
    funext t
    rfl
  show deriv (fun t : ℝ =>
      (a • f) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 =
    a • deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0
  rw [hsf]
  exact deriv_const_smul a (local_path_differentiable s f g X)

theorem right_derivative_linear_exists (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ D : KPCplxPrincipalSeriesCharts.PrincipalSeries s →ₗ[ℂ]
        KPCplxPrincipalSeriesCharts.PrincipalSeries s,
      ∀ f g, D f g = deriv (fun t : ℝ =>
        f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 := by
  let D : KPCplxPrincipalSeriesCharts.PrincipalSeries s →ₗ[ℂ]
      KPCplxPrincipalSeriesCharts.PrincipalSeries s :=
    { toFun := rightDerivative s X
      map_add' := rightDerivative_add s X
      map_smul' := rightDerivative_smul s X }
  exact ⟨D, fun f g => rfl⟩

def rightDerivativeLinear (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :=
  (right_derivative_linear_exists s X).choose

theorem rightDerivativeLinear_apply (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (g) :
    rightDerivativeLinear s X f g = deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 :=
  (right_derivative_linear_exists s X).choose_spec f g

theorem right_derivative_mem (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    (fun g => deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0) ∈
      KPCplxPrincipalSeriesCharts.principalSeriesSubmodule s := by
  have he : (fun g => deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0) =
      (rightDerivativeLinear s X f).val := by
    funext g
    exact (rightDerivativeLinear_apply s X f g).symm
  rw [he]
  exact (rightDerivativeLinear s X f).property

def localDerivative (s : ℝ) (b : LocalBasis)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.PrincipalSeries s :=
  ⟨fun g => deriv (fun t : ℝ =>
    f (g * KPSmoothActualFlowData.matrixExponential
      ((t : ℂ) • cartanMatrix b))) 0, by
      exact right_derivative_mem s (cartanMatrix b) f⟩

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

end
