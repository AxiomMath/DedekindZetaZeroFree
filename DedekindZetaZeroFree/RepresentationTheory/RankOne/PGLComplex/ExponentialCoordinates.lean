module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph
public import DedekindZetaZeroFree.Geometry.PGL.TranslatedExponentialFrame
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.ChartDensity

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex
open MeasureTheory Topology
open scoped Matrix.Norms.Operator Manifold ContDiff Classical

section Products
variable (ι : Type) [Fintype ι]

abbrev ProductCoordinates := (ι × Fin 6) → ℝ

end Products

end DedekindZetaZeroFree.PGLComplex

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex
open MeasureTheory Topology
open scoped Matrix.Norms.Operator Manifold ContDiff Classical

def sl2Matrix (a : Coordinates) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a 0 : ℂ) + Complex.I * (a 1 : ℂ), (a 2 : ℂ) + Complex.I * (a 3 : ℂ);
    (a 4 : ℂ) + Complex.I * (a 5 : ℂ), -((a 0 : ℂ) + Complex.I * (a 1 : ℂ))]

def exponential (a : Coordinates) : Group :=
  Matrix.ProjGenLinGroup.mk ((NormedSpace.isUnit_exp (sl2Matrix a)).unit)

def affineExpDerivative : Coordinates →L[ℝ] Coordinates :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a i => (if i < 2 then -2 else 1) * a i
      map_add' := by intro a b; ext i; simp [mul_add]
      map_smul' := by intro r a; ext i; simp [mul_left_comm] }

def basisMatrix (j : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  sl2Matrix (fun k => if k = j then 1 else 0)

def matrixCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : Coordinates :=
  ![(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im, (M 1 0).re, (M 1 0).im]

def entryLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ where
  toFun M := M i j
  map_add' M N := by simp
  map_smul' r M := by simp

def entry (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  (entryLM i j).toContinuousLinearMap

def adjointMatrix (g : Group) : Matrix (Fin 6) (Fin 6) ℝ := fun a b =>
  matrixCoordinates (g.out.val * basisMatrix b * g.out⁻¹.val) a

theorem sl2Matrix_zero : sl2Matrix 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Matrix]

theorem sl2Matrix_add (a b : Coordinates) :
    sl2Matrix (a + b) = sl2Matrix a + sl2Matrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Matrix] <;> ring

theorem sl2Matrix_smul (r : ℝ) (a : Coordinates) :
    sl2Matrix (r • a) = r • sl2Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Matrix, Complex.real_smul] <;> ring

theorem affineExpDerivative_det : affineExpDerivative.toLinearMap.det = 4 := by
  rw [← LinearMap.det_toMatrix']
  have h : LinearMap.toMatrix' affineExpDerivative.toLinearMap =
      Matrix.diagonal (fun i : Fin 6 => (if i < 2 then -2 else 1 : ℝ)) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, affineExpDerivative, Matrix.diagonal_apply,
      Pi.single_apply, eq_comm]
    split_ifs <;> simp_all
  rw [h, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

section ExponentialDerivative
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem affineInverse_mk (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    affineInverse (Matrix.ProjGenLinGroup.mk g) =
      ![(g.val 1 1 / g.val 0 0 - 1).re, (g.val 1 1 / g.val 0 0 - 1).im,
      (g.val 0 1 / g.val 0 0).re, (g.val 0 1 / g.val 0 0).im,
      (g.val 1 0 / g.val 0 0).re, (g.val 1 0 / g.val 0 0).im] := by
  have he : Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out =
      Matrix.ProjGenLinGroup.mk g := Quotient.out_eq _
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  have hv := congrArg Units.val hu
  have hentry (i j : Fin 2) : g.val i j = (Matrix.ProjGenLinGroup.mk g).out.val i j * (u : ℂ) := by
    rw [← hv]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal]
  simp only [affineInverse, ← hentry]
  have ratio (i j : Fin 2) :
      (Matrix.ProjGenLinGroup.mk g).out.val i j / (Matrix.ProjGenLinGroup.mk g).out.val 0 0 =
        g.val i j / g.val 0 0 := by
    rw [hentry i j, hentry 0 0]
    exact (mul_div_mul_right _ _ u.ne_zero).symm
  simp only [ratio]

private def sl2CLM : Coordinates →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := sl2Matrix
      map_add' := sl2Matrix_add
      map_smul' := sl2Matrix_smul }

private def entryCLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem hentryExp (i j : Fin 2) : HasStrictFDerivAt (fun a => NormedSpace.exp (sl2Matrix a) i j)
    ((entryCLM i j).comp sl2CLM) 0 := by
  have h : HasStrictFDerivAt (fun a => NormedSpace.exp (sl2Matrix a)) sl2CLM 0 := by
    have h : HasStrictFDerivAt NormedSpace.exp
        (1 : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (sl2CLM 0) := by
      simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin 2) (Fin 2) ℂ))
    convert h.comp 0 sl2CLM.hasStrictFDerivAt using 1 <;> ext a <;> rfl
  exact (entryCLM i j).hasStrictFDerivAt.comp 0 h

private def expEntry (i j : Fin 2) (a : Coordinates) : ℂ := NormedSpace.exp (sl2Matrix a) i j

private theorem expEntry_zero (i j : Fin 2) : expEntry i j 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp [expEntry, sl2Matrix_zero, NormedSpace.exp_zero]

private theorem hdenInv : HasStrictFDerivAt (fun a => (expEntry 0 0 a)⁻¹)
    (-((entryCLM 0 0).comp sl2CLM)) 0 := by
  have hi := (hasStrictFDerivAt_inv' (𝕜 := ℝ) (R := ℂ)
    (x := expEntry 0 0 0) (by simp [expEntry_zero])).comp 0 (hentryExp 0 0)
  convert hi using 1 <;> first | rfl | (ext a; simp [expEntry_zero, ContinuousLinearMap.mulLeftRight_apply])

private theorem hratio (i j : Fin 2) : HasStrictFDerivAt (fun a => expEntry i j a / expEntry 0 0 a)
    ((entryCLM i j).comp sl2CLM -
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j) • ((entryCLM 0 0).comp sl2CLM)) 0 := by
  have hm := (hentryExp i j).mul hdenInv
  convert hm using 1 <;> first
    | rfl
    | (ext a; simp [expEntry, div_eq_mul_inv, sl2Matrix_zero, NormedSpace.exp_zero,
        sub_eq_add_neg, smul_eq_mul]; ring)

private theorem hcoordinates : HasStrictFDerivAt (fun a =>
    ![(expEntry 1 1 a / expEntry 0 0 a - 1).re,
      (expEntry 1 1 a / expEntry 0 0 a - 1).im,
      (expEntry 0 1 a / expEntry 0 0 a).re,
      (expEntry 0 1 a / expEntry 0 0 a).im,
      (expEntry 1 0 a / expEntry 0 0 a).re,
      (expEntry 1 0 a / expEntry 0 0 a).im]) affineExpDerivative 0 := by
  have hu := (hratio 1 1).sub_const (1 : ℂ)
  have hb := hratio 0 1
  have hc := hratio 1 0
  have hur := Complex.reCLM.hasStrictFDerivAt.comp 0 hu
  have hui := Complex.imCLM.hasStrictFDerivAt.comp 0 hu
  have hbr := Complex.reCLM.hasStrictFDerivAt.comp 0 hb
  have hbi := Complex.imCLM.hasStrictFDerivAt.comp 0 hb
  have hcr := Complex.reCLM.hasStrictFDerivAt.comp 0 hc
  have hci := Complex.imCLM.hasStrictFDerivAt.comp 0 hc
  have hp : affineExpDerivative = ContinuousLinearMap.pi
      (fun i => (ContinuousLinearMap.proj i).comp affineExpDerivative) := by ext a i; rfl
  rw [hp]
  apply hasStrictFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hur using 1 <;> first | rfl | (ext a; simp [entryCLM, sl2CLM, sl2Matrix, affineExpDerivative]; ring)
  · convert hui using 1 <;> first | rfl | (ext a; simp [entryCLM, sl2CLM, sl2Matrix, affineExpDerivative]; ring)
  · convert hbr using 1 <;> first | rfl | (ext a; simp [entryCLM, sl2CLM, sl2Matrix, affineExpDerivative])
  · convert hbi using 1 <;> first | rfl | (ext a; simp [entryCLM, sl2CLM, sl2Matrix, affineExpDerivative])
  · convert hcr using 1 <;> first | rfl | (ext a; simp [entryCLM, sl2CLM, sl2Matrix, affineExpDerivative])
  · convert hci using 1 <;> first | rfl | (ext a; simp [entryCLM, sl2CLM, sl2Matrix, affineExpDerivative])

theorem exponential_hasStrictFDerivAt_zero : HasStrictFDerivAt (fun a => affineInverse (exponential a)) affineExpDerivative 0 := by
  convert hcoordinates using 1
  ext a i
  simp [exponential, affineInverse_mk, expEntry]

theorem exponential_hasFDerivAt_zero :
    HasFDerivAt (fun a => affineInverse (exponential a)) affineExpDerivative 0 :=
  exponential_hasStrictFDerivAt_zero.hasFDerivAt

end ExponentialDerivative

section ExponentialHomeomorph
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem affine_exponential_local_homeomorph : ∃ e : OpenPartialHomeomorph Coordinates Coordinates,
    (0 : Coordinates) ∈ e.source ∧
    (∀ a, e a = affineInverse (exponential a)) := by
  let d := affineExpDerivative.toContinuousLinearEquivOfDetNeZero
    (by change affineExpDerivative.toLinearMap.det ≠ 0; rw [affineExpDerivative_det]; norm_num)
  have hd : (d : Coordinates →L[ℝ] Coordinates) = affineExpDerivative :=
    affineExpDerivative.coe_toContinuousLinearEquivOfDetNeZero _
  have h : HasStrictFDerivAt (fun a => affineInverse (exponential a))
      (d : Coordinates →L[ℝ] Coordinates) 0 := by
    rw [hd]
    exact exponential_hasStrictFDerivAt_zero
  refine ⟨h.toOpenPartialHomeomorph _, h.mem_toOpenPartialHomeomorph_source, ?_⟩
  intro a
  rw [h.toOpenPartialHomeomorph_coe]

theorem exponential_zero : exponential 0 = 1 := by
  have h : (NormedSpace.isUnit_exp (sl2Matrix 0)).unit = 1 := by
    apply Units.ext
    simp [sl2Matrix_zero, NormedSpace.exp_zero]
  simp [exponential, h]

theorem mk_mem_affineTarget_iff (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Matrix.ProjGenLinGroup.mk g ∈ affineTarget ↔ g.val 0 0 ≠ 0 := by
  have he : Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out =
      Matrix.ProjGenLinGroup.mk g := Quotient.out_eq _
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  have hv := congrArg Units.val hu
  have hentry (i j : Fin 2) : g.val i j = (Matrix.ProjGenLinGroup.mk g).out.val i j * (u : ℂ) := by
    rw [← hv]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal]
  change (Matrix.ProjGenLinGroup.mk g).out.val 0 0 ≠ 0 ↔ _
  rw [hentry, mul_ne_zero_iff]
  simp [u.ne_zero]

end ExponentialHomeomorph

section ExponentialAnalytic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exponential_analyticAt_zero : AnalyticAt ℝ (fun a => affineInverse (exponential a)) 0 := by
  let l : Coordinates →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := sl2Matrix, map_add' := sl2Matrix_add, map_smul' := sl2Matrix_smul }
  let eval (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  have hm : AnalyticAt ℝ (fun a => NormedSpace.exp (sl2Matrix a)) 0 := by
    convert (NormedSpace.exp_analytic (𝕂 := ℝ) (l 0)).comp (l.analyticAt 0) using 1 <;> rfl
  have he (i j : Fin 2) : AnalyticAt ℝ (fun a => NormedSpace.exp (sl2Matrix a) i j) 0 := by
    convert (eval i j |>.analyticAt _).comp hm using 1 <;> rfl
  have hn : NormedSpace.exp (sl2Matrix 0) 0 0 ≠ 0 := by
    simp [sl2Matrix_zero, NormedSpace.exp_zero]
  have hu := ((he 1 1).div (he 0 0) hn).sub (analyticAt_const (v := (1 : ℂ)))
  have hb := (he 0 1).div (he 0 0) hn
  have hc := (he 1 0).div (he 0 0) hn
  have hur := Complex.reCLM.analyticAt _ |>.comp hu
  have hui := Complex.imCLM.analyticAt _ |>.comp hu
  have hbr := Complex.reCLM.analyticAt _ |>.comp hb
  have hbi := Complex.imCLM.analyticAt _ |>.comp hb
  have hcr := Complex.reCLM.analyticAt _ |>.comp hc
  have hci := Complex.imCLM.analyticAt _ |>.comp hc
  simp only [exponential, affineInverse_mk]
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · convert hur using 1 <;> rfl
  · convert hui using 1 <;> rfl
  · convert hbr using 1 <;> rfl
  · convert hbi using 1 <;> rfl
  · convert hcr using 1 <;> rfl
  · convert hci using 1 <;> rfl

end ExponentialAnalytic

theorem sl2Matrix_trace (a : Coordinates) : Matrix.trace (sl2Matrix a) = 0 := by
  simp [Matrix.trace, sl2Matrix, Fin.sum_univ_two]
theorem matrixCoordinates_sl2Matrix (a : Coordinates) : matrixCoordinates (sl2Matrix a) = a := by
  ext i
  fin_cases i <;> simp [matrixCoordinates, sl2Matrix]
theorem exponential_add_ray (a : Coordinates) (s t : ℝ) :
    exponential ((s + t) • a) = exponential (s • a) * exponential (t • a) := by
  rw [exponential, exponential, exponential, ← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, IsUnit.unit_spec]
  rw [sl2Matrix_smul, add_smul, NormedSpace.exp_add_of_commute]
  · rw [sl2Matrix_smul, sl2Matrix_smul]
  · exact ((Commute.refl (sl2Matrix a)).smul_left s).smul_right t

theorem sl2Matrix_matrixCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : Matrix.trace M = 0) :
    sl2Matrix (matrixCoordinates M) = M := by
  have hd : M 1 1 = -M 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [sl2Matrix, matrixCoordinates, Matrix.cons_val,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
  all_goals simp [sl2Matrix, matrixCoordinates]
  all_goals first | (rw [mul_comm Complex.I, Complex.re_add_im]) |
    (rw [hd]; calc
      -(Complex.I * ↑(M 0 0).im) + -↑(M 0 0).re = -((M 0 0).re + (M 0 0).im * Complex.I) := by ring
      _ = -M 0 0 := congrArg Neg.neg (Complex.re_add_im (M 0 0)))
theorem trace_conjugation (h : Matrix.GeneralLinearGroup (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (h.val * M * h⁻¹.val) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle]
  simp
theorem exponential_conjugation (g : Group) (a : Coordinates) :
    g * exponential a * g⁻¹ = exponential (matrixCoordinates (g.out.val * sl2Matrix a * g.out⁻¹.val)) := by
  have hmk : Matrix.ProjGenLinGroup.mk g.out = g := Quotient.out_eq _
  rw [← hmk, exponential, exponential, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  rw [sl2Matrix_matrixCoordinates _ (by rw [trace_conjugation, sl2Matrix_trace])]
  rw [hmk]
  exact (NormedSpace.exp_units_conj g.out (sl2Matrix a)).symm
private theorem affine_exponential_smooth_local_homeomorph :
    ∃ e : OpenPartialHomeomorph Coordinates Coordinates,
      (0 : Coordinates) ∈ e.source ∧
      (∀ a, e a = affineInverse (exponential a)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  obtain ⟨e, he0, he⟩ := affine_exponential_local_homeomorph
  have hefun : (e : Coordinates → Coordinates) =
      (fun a => affineInverse (exponential a)) := funext he
  have hf : AnalyticAt ℝ e 0 := by rw [hefun]; exact exponential_analyticAt_zero
  let d := affineExpDerivative.toContinuousLinearEquivOfDetNeZero
    (by change affineExpDerivative.toLinearMap.det ≠ 0; rw [affineExpDerivative_det]; norm_num)
  have hd : (d : Coordinates →L[ℝ] Coordinates) = affineExpDerivative :=
    affineExpDerivative.coe_toContinuousLinearEquivOfDetNeZero _
  have hfd : fderiv ℝ e 0 = (d : Coordinates →L[ℝ] Coordinates) := by
    rw [hefun, hd]
    exact exponential_hasFDerivAt_zero.fderiv
  have hi : AnalyticAt ℝ e.symm (e 0) := e.analyticAt_symm' he0 hf hfd
  let U : Set Coordinates := {a | AnalyticAt ℝ e a} ∩
    e ⁻¹' {a | AnalyticAt ℝ e.symm a}
  have hU : (0 : Coordinates) ∈ interior U := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.inter_mem hf.eventually_analyticAt
      ((e.continuousAt he0) hi.eventually_analyticAt)
  let f := e.restr U
  refine ⟨f, ⟨he0, hU⟩, ?_, ?_, ?_⟩
  · intro a; exact he a
  · intro a ha
    have ha' : a ∈ U := interior_subset ha.2
    exact ha'.1.contDiffAt.contDiffWithinAt
  · intro a ha
    have hs := f.map_target ha
    have hs' : f.symm a ∈ U := interior_subset hs.2
    have heq : e (f.symm a) = a := f.right_inv ha
    have hi' : AnalyticAt ℝ e.symm a := by
      rw [← heq]
      exact hs'.2
    exact hi'.contDiffAt.contDiffWithinAt

private theorem coords_add (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixCoordinates (M + N) = matrixCoordinates M + matrixCoordinates N := by
  ext i; fin_cases i <;> simp [matrixCoordinates]
private theorem coords_smul (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixCoordinates (r • M) = r • matrixCoordinates M := by
  ext i; fin_cases i <;> simp [matrixCoordinates, Complex.real_smul]
def adjointLinearEquiv (g : Group) : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun a := matrixCoordinates (g.out.val * sl2Matrix a * g.out⁻¹.val)
  invFun a := matrixCoordinates (g.out⁻¹.val * sl2Matrix a * g.out.val)
  map_add' a b := by simp [sl2Matrix_add, Matrix.mul_add, Matrix.add_mul, coords_add]
  map_smul' r a := by simp [sl2Matrix_smul, Matrix.mul_smul, Matrix.smul_mul, coords_smul]
  left_inv a := by
    change matrixCoordinates (g.out⁻¹.val * sl2Matrix (matrixCoordinates
      (g.out.val * sl2Matrix a * g.out⁻¹.val)) * g.out.val) = a
    rw [sl2Matrix_matrixCoordinates _ (by rw [trace_conjugation, sl2Matrix_trace])]
    simp [Matrix.mul_assoc, ← Matrix.mul_assoc g.out⁻¹.val g.out.val]
    exact matrixCoordinates_sl2Matrix a
  right_inv a := by
    change matrixCoordinates (g.out.val * sl2Matrix (matrixCoordinates
      (g.out⁻¹.val * sl2Matrix a * g.out.val)) * g.out⁻¹.val) = a
    have ht : Matrix.trace (g.out⁻¹.val * sl2Matrix a * g.out.val) = 0 := by
      simpa using (trace_conjugation g.out⁻¹ (sl2Matrix a)).trans (sl2Matrix_trace a)
    rw [sl2Matrix_matrixCoordinates _ ht]
    simp [Matrix.mul_assoc, ← Matrix.mul_assoc g.out.val g.out⁻¹.val]
    exact matrixCoordinates_sl2Matrix a
theorem exponential_adjoint (g : Group) (a : Coordinates) :
    g * exponential a * g⁻¹ = exponential (adjointLinearEquiv g a) := exponential_conjugation g a
theorem adjointLinearEquiv_basis (g : Group) (a b : Fin 6) :
    (adjointLinearEquiv g ((Pi.basisFun ℝ (Fin 6)) b)) a = adjointMatrix g a b := by
  have hs : (Pi.single b (1 : ℝ) : Coordinates) = (fun k => if k = b then 1 else 0) := by
    ext k; simp [Pi.single_apply]
  simp [adjointLinearEquiv, adjointMatrix, basisMatrix, Pi.basisFun_apply, hs]

theorem exponential_local_coordinates :
    HasFDerivAt (fun a => affineInverse (exponential a)) affineExpDerivative 0 ∧
    affineExpDerivative.toLinearMap.det = 4 ∧
    ∃ E : OpenPartialHomeomorph Coordinates Group,
      (0 : Coordinates) ∈ E.source ∧
      (∀ a ∈ E.source, E a = exponential a) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun a => affineInverse (E a)) E.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun a => E.symm (affinePoint a)) (affinePoint ⁻¹' E.target ∩ affineSource) := by
  refine ⟨exponential_hasFDerivAt_zero, affineExpDerivative_det, ?_⟩
  obtain ⟨e, he0, he, hf, hi⟩ := affine_exponential_smooth_local_homeomorph
  let U : Set Coordinates := {a | exponential a ∈ affineTarget}
  have hU : (0 : Coordinates) ∈ interior U := by
    have h00 : ContinuousAt (fun a => NormedSpace.exp (sl2Matrix a) 0 0) 0 :=
      (hentryExp 0 0).continuousAt
    have hn : ∀ᶠ a in 𝓝 (0 : Coordinates), NormedSpace.exp (sl2Matrix a) 0 0 ≠ 0 :=
      h00.eventually_ne (by simp [sl2Matrix_zero, NormedSpace.exp_zero])
    exact mem_interior_iff_mem_nhds.mpr
      (hn.mono (fun a ha => (mk_mem_affineTarget_iff _).mpr ha))
  let E := (e.restr U).trans affineChart
  have hEexp : ∀ a ∈ E.source, E a = exponential a := by
    intro a ha
    have haU : a ∈ U := interior_subset ha.1.2
    change affineChart ((e.restr U) a) = exponential a
    rw [OpenPartialHomeomorph.restr_apply, he,
      ← affineChart_symm_apply _ haU]
    exact affineChart.right_inv (by simpa [U] using haU)
  have h0 : affineInverse 1 = 0 := by
    rw [← Matrix.ProjGenLinGroup.mk_one, affineInverse_mk]
    ext i; fin_cases i <;> simp
  refine ⟨E, ?_, hEexp, ?_, ?_⟩
  · change 0 ∈ (e.restr U).source ∩ (e.restr U) ⁻¹' affineChart.source
    refine ⟨⟨he0, hU⟩, ?_⟩
    change (e.restr U) 0 ∈ affineChart.source
    rw [OpenPartialHomeomorph.restr_apply, he, exponential_zero, h0]
    simpa using zero_mem_affineSource
  · apply (hf.mono (fun a ha => ha.1.1)).congr
    intro a ha
    rw [hEexp a ha]
    exact (he a).symm
  · have hinv : ∀ a ∈ affinePoint ⁻¹' E.target ∩ affineSource,
        E.symm (affinePoint a) = e.symm a := by
      intro a ha
      change (e.restr U).symm (affineChart.symm (affinePoint a)) = e.symm a
      have hleft : affineChart.symm (affinePoint a) = a := by
        rw [← affineChart_apply a ha.2]
        exact affineChart.left_inv (by simpa using ha.2)
      rw [hleft]
      rfl
    have hsub : affinePoint ⁻¹' E.target ∩ affineSource ⊆ e.target := by
      intro a ha
      have hta : affineChart.symm (affinePoint a) ∈ (e.restr U).target := ha.1.2
      have hleft : affineChart.symm (affinePoint a) = a := by
        rw [← affineChart_apply a ha.2]
        exact affineChart.left_inv (by simpa using ha.2)
      rw [hleft] at hta
      exact hta.1
    exact (hi.mono hsub).congr hinv

section ExponentialSmooth
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def smoothSl2CLM : Coordinates →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := sl2Matrix, map_add' := sl2Matrix_add, map_smul' := sl2Matrix_smul }
theorem exponential_continuous : Continuous exponential := by
  have hc : Continuous (fun a => (NormedSpace.isUnit_exp (sl2Matrix a)).unit) := by
    apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
    exact (NormedSpace.exp_continuous (𝔸 := Matrix (Fin 2) (Fin 2) ℂ)).comp smoothSl2CLM.continuous
  exact QuotientGroup.continuous_mk.comp hc

theorem exponential_contMDiff {C : ChartedSpace Coordinates Group}
    (hC : ∀ g : Group, chartAt Coordinates g =
      ((affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm)) :
    ContMDiff (𝓘(ℝ, Coordinates)) (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) exponential := by
  intro a
  apply contMDiffAt_iff.mpr
  refine ⟨exponential_continuous.continuousAt, ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.comp_id,
    extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  rw [hC]
  let g := exponential a
  let m := g.out⁻¹
  have hmg : Matrix.ProjGenLinGroup.mk m = g⁻¹ := by
    change Matrix.ProjGenLinGroup.mk (g.out⁻¹) = g⁻¹
    rw [map_inv]
    exact congrArg Inv.inv (Quotient.out_eq g)
  have hchart : ∀ x, ((affineChart.trans
      (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm) (exponential x) =
      affineChart.symm (g⁻¹ * exponential x) := by intro x; rfl
  simp only [Function.comp_def, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Set.range_id]
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun x => affineChart.symm (g⁻¹ * exponential x)) Set.univ a
  let f (x : Coordinates) := m * (NormedSpace.isUnit_exp (sl2Matrix x)).unit
  have hclass (x : Coordinates) : Matrix.ProjGenLinGroup.mk (f x) =
      g⁻¹ * exponential x := by change Matrix.ProjGenLinGroup.mk (m * _) = _; rw [map_mul, hmg]; rfl
  have htarget : ∀ᶠ x in 𝓝 a, g⁻¹ * exponential x ∈ affineTarget := by
    have hopen : IsOpen affineTarget := by rw [← affineChart_target]; exact affineChart.open_target
    have hone : g⁻¹ * exponential a ∈ affineTarget := by simpa [g] using one_mem_affineTarget
    exact (continuous_const.mul exponential_continuous).continuousAt.eventually (hopen.mem_nhds hone)
  have heq : (fun x => affineChart.symm (g⁻¹ * exponential x)) =ᶠ[𝓝 a]
      (fun x => matrixRatios (m.val * NormedSpace.exp (sl2Matrix x))) := by
    filter_upwards [htarget] with x hx
    rw [affineChart_symm_apply _ hx, ← hclass x, matrixRatios_mk (f x)]
    rfl
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.congr_of_eventuallyEq _ heq
  have hn : (m.val * NormedSpace.exp (sl2Matrix a)) 0 0 ≠ 0 := by
    have ht : Matrix.ProjGenLinGroup.mk (f a) ∈ affineTarget := by
      rw [hclass]; simpa [g] using one_mem_affineTarget
    exact (mk_mem_affineTarget_iff (f a)).mp ht
  have hm : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => m.val * NormedSpace.exp (sl2Matrix x)) a :=
    contDiffAt_const.mul (((NormedSpace.exp_analytic (𝕂 := ℝ) (smoothSl2CLM a)).comp
      (smoothSl2CLM.analyticAt a)).contDiffAt)
  have hen (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => (m.val * NormedSpace.exp (sl2Matrix x)) i j) a :=
    (entry i j).contDiff.contDiffAt.comp a hm
  have hd (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => (m.val * NormedSpace.exp (sl2Matrix x)) i j /
        (m.val * NormedSpace.exp (sl2Matrix x)) 0 0) a := by
    simpa only [div_eq_mul_inv] using! (hen i j).mul ((hen 0 0).inv hn)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp only [matrixRatios, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  · exact (Complex.reCLM.contDiff.contDiffAt.comp a (hd 1 1)).sub contDiffAt_const
  · exact Complex.imCLM.contDiff.contDiffAt.comp a (hd 1 1)
  · exact Complex.reCLM.contDiff.contDiffAt.comp a (hd 0 1)
  · exact Complex.imCLM.contDiff.contDiffAt.comp a (hd 0 1)
  · exact Complex.reCLM.contDiff.contDiffAt.comp a (hd 1 0)
  · exact Complex.imCLM.contDiff.contDiffAt.comp a (hd 1 0)

theorem exponential_partialDiffeomorph_exists {C : ChartedSpace Coordinates Group}
    [LieGroup (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group]
    (hC : ∀ g : Group, chartAt Coordinates g =
      ((affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm)) :
    ∃ D : PartialDiffeomorph (𝓘(ℝ, Coordinates)) (𝓘(ℝ, Coordinates))
      Coordinates Group (⊤ : ℕ∞),
      0 ∈ D.source ∧ (∀ a ∈ D.source, D a = exponential a) := by
  obtain ⟨_, _, E, h0, hexp, hf, hi⟩ := exponential_local_coordinates
  let U : Set Coordinates := E ⁻¹' affineTarget
  have hU : (0 : Coordinates) ∈ interior U := by
    apply mem_interior_iff_mem_nhds.mpr
    have ht : E 0 ∈ affineTarget := by rw [hexp 0 h0, exponential_zero]; exact one_mem_affineTarget
    have hopen : IsOpen affineTarget := by rw [← affineChart_target]; exact affineChart.open_target
    exact (E.continuousAt h0) (hopen.mem_nhds ht)
  let F := E.restr U
  have hFt : F.target ⊆ affineTarget := by
    intro y hy
    have hs := F.map_target hy
    have hsU : F.symm y ∈ U := interior_subset hs.2
    have hr : E (F.symm y) = y := F.right_inv hy
    change E (F.symm y) ∈ affineTarget at hsU
    rwa [hr] at hsU
  have hInv : ContMDiffOn (𝓘(ℝ, Coordinates)) (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞)
      F.symm F.target := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    have hCy : y ∈ (chartAt Coordinates (1 : Group)).source := by
      rw [hC]
      change y ∈ Set.univ ∩ (fun y => (1 : Group)⁻¹ * y) ⁻¹' affineChart.target
      simpa using hFt hy
    apply (contMDiffAt_iff_source_of_mem_source hCy).mpr
    have hchartFun : (extChartAt (𝓘(ℝ, Coordinates)) (1 : Group) : Group → Coordinates) = affineChart.symm := by
      rw [extChartAt_coe, hC]
      funext y
      change affineChart.symm ((1 : Group)⁻¹ * y) = affineChart.symm y
      simp
    have hchartInv : ((extChartAt (𝓘(ℝ, Coordinates)) (1 : Group)).symm : Coordinates → Group) = affineChart := by
      rw [extChartAt_coe_symm, hC]
      ext a
      change (1 : Group) * affineChart a = affineChart a
      simp
    rw [hchartFun, hchartInv]
    simp only [modelWithCornersSelf_coe, Set.range_id]
    apply ContMDiffAt.contMDiffWithinAt
    apply ContDiffAt.contMDiffAt
    let S : Set Coordinates := affinePoint ⁻¹' E.target ∩ affineSource
    have haS : affineChart.symm y ∈ S := by
      have hys : y ∈ affineChart.target := by simpa using hFt hy
      have has := affineChart.map_target hys
      refine ⟨?_, by simpa using has⟩
      change affinePoint (affineChart.symm y) ∈ E.target
      rw [← affineChart_apply _ (by simpa using has), affineChart.right_inv hys]
      exact hy.1
    have hopenS : IsOpen S := by
      change IsOpen (affinePoint ⁻¹' E.target ∩ affineSource)
      have heq : affinePoint ⁻¹' E.target ∩ affineSource = affineChart.source ∩ affineChart ⁻¹' E.target := by
        ext a
        simp only [affineChart_source, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · intro ha; exact ⟨ha.2, by rw [affineChart_apply a ha.2]; exact ha.1⟩
        · intro ha; exact ⟨by rw [← affineChart_apply a ha.1]; exact ha.2, ha.1⟩
      rw [heq]
      exact affineChart.isOpen_inter_preimage E.open_target
    have hdiff := hi.contDiffAt (hopenS.mem_nhds haS)
    have heq : (F.symm ∘ affineChart) =ᶠ[𝓝 (affineChart.symm y)] (fun a => E.symm (affinePoint a)) := by
      filter_upwards [hopenS.mem_nhds haS] with a ha
      rw [Function.comp_apply, OpenPartialHomeomorph.restr_symm_apply,
        affineChart_apply a ha.2]
    exact hdiff.congr_of_eventuallyEq heq
  refine ⟨{ toPartialEquiv := F.toPartialEquiv
            open_source := F.open_source
            open_target := F.open_target
            contMDiffOn_toFun := ?_
            contMDiffOn_invFun := hInv }, ⟨h0, hU⟩, ?_⟩
  · exact (exponential_contMDiff hC).contMDiffOn.congr (fun a ha => hexp a ha.1)
  · intro a ha; exact hexp a ha.1

private theorem conjugation_scalar (h : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : ℂˣ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (h * Matrix.GeneralLinearGroup.scalar (Fin 2) z).val * M *
    (h * Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹.val = h.val * M * h⁻¹.val := by
  simp only [mul_inv_rev, Units.val_mul]
  have hv : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹.val =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹).val := by rw [map_inv]
  rw [hv]
  simp only [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp
  <;> ring
theorem adjointLinearEquiv_mk (h : Matrix.GeneralLinearGroup (Fin 2) ℂ) (a : Coordinates) :
    adjointLinearEquiv (Matrix.ProjGenLinGroup.mk h) a =
      matrixCoordinates (h.val * sl2Matrix a * h⁻¹.val) := by
  have he : Matrix.ProjGenLinGroup.mk h = Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk h).out := (Quotient.out_eq _).symm
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  change matrixCoordinates ((Matrix.ProjGenLinGroup.mk h).out.val * sl2Matrix a *
    (Matrix.ProjGenLinGroup.mk h).out⁻¹.val) = _
  rw [← hz, conjugation_scalar]
private def affineLinear : Coordinates →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun x := affineMatrix x - 1
      map_add' := by
        intro x y
        ext i j
        fin_cases i <;> fin_cases j <;> simp [affineMatrix, complexCoordinates] <;>
          apply Complex.ext <;> simp <;> ring
      map_smul' := by
        intro r x
        ext i j
        fin_cases i <;> fin_cases j <;> simp [affineMatrix, complexCoordinates, Complex.real_smul] <;>
          apply Complex.ext <;> simp <;> ring }
private theorem affineMatrix_smooth_op : ContDiff ℝ (⊤ : ℕ∞) affineMatrix := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x => affineLinear x + 1) :=
    affineLinear.contDiff.add contDiff_const
  convert h using 1
  funext x
  simp [affineLinear]
private def readCoordinate (a : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun M := matrixCoordinates M a
      map_add' M N := by fin_cases a <;> simp [matrixCoordinates]
      map_smul' r M := by fin_cases a <;> simp [matrixCoordinates, Complex.real_smul] }

theorem adjointMatrix_contMDiff {C : ChartedSpace Coordinates Group}
    [LieGroup (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group]
    (hC : ∀ g : Group, chartAt Coordinates g =
      ((affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm))
    (a b : Fin 6) :
    ContMDiff (𝓘(ℝ, Coordinates)) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
      (fun g => adjointMatrix g a b) := by
  intro g
  apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source Coordinates g)).mpr
  simp only [extChartAt_coe, extChartAt_coe_symm, hC,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id]
  have h0 : ((affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm) g = 0 := by
    change affineChart.symm (g⁻¹ * g) = 0
    rw [inv_mul_cancel]
    simpa only [affineChart_zero] using affineChart.left_inv (show (0 : Coordinates) ∈ affineChart.source by simp)
  rw [h0]
  apply ContMDiffAt.contMDiffWithinAt
  apply ContDiffAt.contMDiffAt
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun x => adjointMatrix (g * affineChart x) a b) 0
  let f (x : Coordinates) := g.out.val * affineMatrix x
  have hfu : IsUnit (f 0) := by
    have hz : affineMatrix 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [affineMatrix, complexCoordinates, show (⟨0, 0⟩ : ℂ) = 0 from rfl]
    simpa [f, hz] using g.out.isUnit
  have hm : ContDiffAt ℝ (⊤ : ℕ∞) f 0 :=
    contDiffAt_const.mul affineMatrix_smooth_op.contDiffAt
  have hri : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse (f 0) := by
    simpa only [IsUnit.unit_spec] using
      (contDiffAt_ringInverse (n := (⊤ : ℕ∞)) ℝ hfu.unit)
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => Ring.inverse (f x)) 0 := hri.comp 0 hm
  have hs : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => readCoordinate a (f x * basisMatrix b * Ring.inverse (f x))) 0 :=
    (readCoordinate a).contDiff.contDiffAt.comp 0 ((hm.mul contDiffAt_const).mul hi)
  apply hs.congr_of_eventuallyEq
  filter_upwards [affineChart.open_source.mem_nhds (show (0 : Coordinates) ∈ affineChart.source by simp)] with x hx
  rw [affineChart_apply x (by simpa using hx)]
  have hx' : delta x ≠ 0 := by simpa [affineSource] using hx
  let u := Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix x)
    (by rwa [affineMatrix_det])
  have hp : affinePoint x = Matrix.ProjGenLinGroup.mk u := by
    simp [affinePoint, hx', u]
  have hmk : g * affinePoint x = Matrix.ProjGenLinGroup.mk (g.out * u) := by
    rw [map_mul, show Matrix.ProjGenLinGroup.mk g.out = g from Quotient.out_eq g, hp]
  rw [hmk, ← adjointLinearEquiv_basis]
  change (adjointLinearEquiv (Matrix.ProjGenLinGroup.mk (g.out * u))
      ((Pi.basisFun ℝ (Fin 6)) b)) a = _
  rw [adjointLinearEquiv_mk]
  have hv : (g.out * u).val = f x := rfl
  rw [hv]
  have hb : sl2Matrix ((Pi.basisFun ℝ (Fin 6)) b) = basisMatrix b := by
    congr 1
    ext k
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [hb]
  change matrixCoordinates (f x * basisMatrix b * (g.out * u)⁻¹.val) a =
    matrixCoordinates (f x * basisMatrix b * Ring.inverse (f x)) a
  rw [← hv, Ring.inverse_unit]

theorem single_lie_exponential_data {C : ChartedSpace Coordinates Group}
    [LieGroup (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group]
    (hC : ∀ g : Group, chartAt Coordinates g =
      ((affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm)) :
    ∃ D : HilbertLieExponentialData Group Coordinates (Fin 6),
      D.exponential = exponential ∧
      (∀ b c, D.basis b c = if c = b then 1 else 0) ∧
      (∀ g a b, D.basis.equivFun (D.adjoint g (D.basis b)) a = adjointMatrix g a b) := by
  obtain ⟨E, h0, he⟩ := exponential_partialDiffeomorph_exists hC
  let D : HilbertLieExponentialData Group Coordinates (Fin 6) :=
    { basis := Pi.basisFun ℝ (Fin 6)
      exponential := exponential
      exponential_zero := exponential_zero
      exponential_add_ray := exponential_add_ray
      exponential_smooth := exponential_contMDiff hC
      exponentialChart := E
      zero_mem_source := h0
      chart_eq_exponential := he
      adjoint := adjointLinearEquiv
      adjoint_smooth := ?_
      exponential_conjugation := exponential_adjoint }
  refine ⟨D, rfl, ?_, ?_⟩
  · intro b c
    simp [D, Pi.basisFun_apply, Pi.single_apply]
  · intro g a b
    exact adjointLinearEquiv_basis g a b
  · intro a b
    simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply,
      adjointLinearEquiv_basis] using adjointMatrix_contMDiff hC a b

end ExponentialSmooth

section Products
variable (ι : Type) [Fintype ι]
abbrev ProductGroup := ι → Group

def productExponential (a : ProductCoordinates ι) : ProductGroup ι :=
  fun v => exponential (fun j => a (v, j))

def productAdjointMatrix (g : ProductGroup ι) : Matrix (ι × Fin 6) (ι × Fin 6) ℝ :=
  fun a b => if a.1 = b.1 then adjointMatrix (g a.1) a.2 b.2 else 0

theorem productExponential_zero : productExponential ι 0 = 1 := by
  funext v
  exact exponential_zero
theorem productExponential_add_ray (a : ProductCoordinates ι) (s t : ℝ) :
    productExponential ι ((s+t) • a) = productExponential ι (s • a) * productExponential ι (t • a) := by
  funext v
  exact exponential_add_ray (fun j => a (v,j)) s t
def productAdjointLinearEquiv (g : ProductGroup ι) : ProductCoordinates ι ≃ₗ[ℝ] ProductCoordinates ι where
  toFun a c := adjointLinearEquiv (g c.1) (fun j => a (c.1,j)) c.2
  invFun a c := (adjointLinearEquiv (g c.1)).symm (fun j => a (c.1,j)) c.2
  map_add' a b := by
    ext c
    exact congrFun ((adjointLinearEquiv (g c.1)).map_add (fun j => a (c.1,j)) (fun j => b (c.1,j))) c.2
  map_smul' r a := by
    ext c
    exact congrFun ((adjointLinearEquiv (g c.1)).map_smul r (fun j => a (c.1,j))) c.2
  left_inv a := by ext c; exact congrFun ((adjointLinearEquiv (g c.1)).symm_apply_apply (fun j => a (c.1,j))) c.2
  right_inv a := by ext c; exact congrFun ((adjointLinearEquiv (g c.1)).apply_symm_apply (fun j => a (c.1,j))) c.2
theorem productExponential_adjoint (g : ProductGroup ι) (a : ProductCoordinates ι) :
    g * productExponential ι a * g⁻¹ = productExponential ι (productAdjointLinearEquiv ι g a) := by
  funext v
  exact exponential_adjoint (g v) (fun j => a (v,j))

theorem productAdjointLinearEquiv_basis (g : ProductGroup ι) (a b : ι × Fin 6) :
    (productAdjointLinearEquiv ι g ((Pi.basisFun ℝ (ι × Fin 6)) b)) a =
      productAdjointMatrix ι g a b := by
  classical
  change (adjointLinearEquiv (g a.1)) (fun j => (Pi.basisFun ℝ (ι × Fin 6)) b (a.1,j)) a.2 = _
  by_cases hab : a.1 = b.1
  · have hslice : (fun j => (Pi.basisFun ℝ (ι × Fin 6)) b (a.1,j)) =
        (Pi.basisFun ℝ (Fin 6)) b.2 := by
      ext j
      simp [Pi.basisFun_apply, Pi.single_apply, hab, Prod.ext_iff]
    rw [hslice, adjointLinearEquiv_basis]
    simp [productAdjointMatrix, hab]
  · have hslice : (fun j => (Pi.basisFun ℝ (ι × Fin 6)) b (a.1,j)) = 0 := by
      ext j
      simp [Pi.basisFun_apply, Pi.single_apply, Prod.ext_iff, hab]
    rw [hslice, map_zero]
    simp [productAdjointMatrix, hab]

open Set in
def productCoordinatesFlatten : (ι → Coordinates) ≃L[ℝ] ProductCoordinates ι :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun a c => a c.1 c.2
    invFun := fun a i j => a (i,j)
    left_inv := by intro a; rfl
    right_inv := by intro a; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
open Set

def productAffineChart (e : ι → OpenPartialHomeomorph Group Coordinates) :
    OpenPartialHomeomorph (ProductGroup ι) (ProductCoordinates ι) :=
  (OpenPartialHomeomorph.pi e).trans (productCoordinatesFlatten ι).toHomeomorph.toOpenPartialHomeomorph
@[instance_reducible] def productAffineChartedSpace {C : ChartedSpace Coordinates Group} :
    ChartedSpace (ProductCoordinates ι) (ProductGroup ι) where
  atlas := productAffineChart ι '' Set.pi univ (fun _ => atlas Coordinates Group)
  chartAt g := productAffineChart ι (fun i => chartAt Coordinates (g i))
  mem_chart_source g := by
    change g ∈ (OpenPartialHomeomorph.pi _).source ∩ _
    exact ⟨fun i _ => mem_chart_source Coordinates (g i), Set.mem_univ _⟩
  chart_mem_atlas g := ⟨_, (fun i _ => chart_mem_atlas Coordinates (g i)), rfl⟩
theorem productAffineIsManifold {C : ChartedSpace Coordinates Group}
    [IsManifold (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group] :
    letI := productAffineChartedSpace ι (C := C)
    IsManifold (𝓘(ℝ, ProductCoordinates ι)) (⊤ : ℕ∞) (ProductGroup ι) := by
  letI := productAffineChartedSpace ι (C := C)
  apply isManifold_of_contDiffOn
  intro e f he hf
  obtain ⟨e, he, rfl⟩ := he
  obtain ⟨f, hf, rfl⟩ := hf
  have hc (i : ι) : ContDiffOn ℝ (⊤ : ℕ∞) ((e i).symm.trans (f i))
      ((e i).symm.trans (f i)).source := by
    have h := (𝓘(ℝ, Coordinates)).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Coordinates)) (n := (⊤ : ℕ∞)) (he i (mem_univ i)))
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Coordinates)) (n := (⊤ : ℕ∞)) (hf i (mem_univ i)))
    simpa [ModelWithCorners.extendCoordChange, Function.comp_def] using h
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun a => productCoordinatesFlatten ι (fun i => f i ((e i).symm ((productCoordinatesFlatten ι).symm a i)))) _
  apply (productCoordinatesFlatten ι).contDiff.contDiffOn.comp
  · apply contDiffOn_pi.mpr
    intro i
    exact (hc i).comp ((contDiff_apply ℝ Coordinates i).comp
      (productCoordinatesFlatten ι).symm.contDiff).contDiffOn (by
        intro a ha
        simp only [modelWithCornersSelf_coe, PartialEquiv.refl_symm,
          PartialEquiv.refl_coe, Set.preimage_id_eq, Set.range_id, Set.inter_univ] at ha
        change a ∈ ((productAffineChart ι e).symm.trans (productAffineChart ι f)).source at ha
        have h1 := ha.1.2
        have h2 := ha.2.1
        exact ⟨h1 i (mem_univ i), h2 i (mem_univ i)⟩)
  · exact mapsTo_univ _ _

section Maps
variable {ι} {C : ChartedSpace Coordinates Group}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
theorem product_contMDiff {f : M → ProductGroup ι} {n : ℕ∞ω}
    (hf : ∀ i, ContMDiff I (𝓘(ℝ, Coordinates)) n (fun x => f x i)) :
    letI := productAffineChartedSpace ι (C := C)
    ContMDiff I (𝓘(ℝ, ProductCoordinates ι)) n f := by
  letI := productAffineChartedSpace ι (C := C)
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_pi.mpr (fun i => (hf i x).continuousAt), ?_⟩
  have hc (i : ι) := (contMDiffAt_iff.mp (hf i x)).2
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at hc ⊢
  change ContDiffWithinAt ℝ n
    (fun a => productCoordinatesFlatten ι (fun i => chartAt Coordinates (f x i) (f ((extChartAt I x).symm a) i))) _ _
  apply (productCoordinatesFlatten ι).contDiff.contDiffAt.comp_contDiffWithinAt
  exact contDiffWithinAt_pi.mpr hc

theorem product_projection_contMDiff [IsManifold (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group] (i : ι) :
    letI := productAffineChartedSpace ι (C := C)
    ContMDiff (𝓘(ℝ, ProductCoordinates ι)) (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞)
      (fun g : ProductGroup ι => g i) := by
  letI := productAffineChartedSpace ι (C := C)
  intro g
  apply contMDiffAt_iff.mpr
  refine ⟨(continuous_apply i).continuousAt, ?_⟩
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
    Set.range_id]
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun a => chartAt Coordinates (g i) ((chartAt Coordinates (g i)).symm ((productCoordinatesFlatten ι).symm a i)))
    Set.univ (productCoordinatesFlatten ι (fun j => chartAt Coordinates (g j) (g j)))
  let a0 := productCoordinatesFlatten ι (fun j => chartAt Coordinates (g j) (g j))
  have ht : ((productCoordinatesFlatten ι).symm a0 i) ∈ (chartAt Coordinates (g i)).target :=
    (chartAt Coordinates (g i)).map_source (mem_chart_source _ _)
  have he : (fun a => chartAt Coordinates (g i) ((chartAt Coordinates (g i)).symm ((productCoordinatesFlatten ι).symm a i)))
      =ᶠ[nhds a0] (fun a => (productCoordinatesFlatten ι).symm a i) := by
    have hc : ContinuousAt (fun a => (productCoordinatesFlatten ι).symm a i) a0 :=
      ((continuous_apply i).comp (productCoordinatesFlatten ι).symm.continuous).continuousAt
    filter_upwards [hc.eventually ((chartAt Coordinates (g i)).open_target.mem_nhds ht)] with a ha
    exact (chartAt Coordinates (g i)).right_inv ha
  apply ContDiffAt.contDiffWithinAt
  exact (((contDiff_apply ℝ Coordinates i).comp (productCoordinatesFlatten ι).symm.contDiff).contDiffAt).congr_of_eventuallyEq he
end Maps

theorem productAffineLieGroup {C : ChartedSpace Coordinates Group}
    [LieGroup (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group] :
    letI := productAffineChartedSpace ι (C := C)
    LieGroup (𝓘(ℝ, ProductCoordinates ι)) (⊤ : ℕ∞) (ProductGroup ι) := by
  letI := productAffineChartedSpace ι (C := C)
  letI := productAffineIsManifold ι (C := C)
  letI : ContMDiffMul (𝓘(ℝ, ProductCoordinates ι)) (⊤ : ℕ∞) (ProductGroup ι) := {
    contMDiff_mul := product_contMDiff (C := C) (fun i =>
      ((product_projection_contMDiff i).comp contMDiff_fst).mul
        ((product_projection_contMDiff i).comp contMDiff_snd)) }
  exact { contMDiff_inv := product_contMDiff (C := C) (fun i => (product_projection_contMDiff i).inv) }

section ProductExponentialData
variable {C : ChartedSpace Coordinates Group}
  [LieGroup (𝓘(ℝ, Coordinates)) (⊤ : ℕ∞) Group]
variable (D : HilbertLieExponentialData Group Coordinates (Fin 6))
def productExponentialHomeomorph := (productAffineChart ι (fun _ => D.exponentialChart.toOpenPartialHomeomorph.symm)).symm

theorem product_contMDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → ProductGroup ι} {s : Set M} {n : ℕ∞ω}
    (hf : ∀ i, ContMDiffOn I (𝓘(ℝ, Coordinates)) n (fun x => f x i) s) :
    letI := productAffineChartedSpace ι (C := C)
    ContMDiffOn I (𝓘(ℝ, ProductCoordinates ι)) n f s := by
  letI := productAffineChartedSpace ι (C := C)
  intro x hx
  apply contMDiffWithinAt_iff.mpr
  refine ⟨continuousWithinAt_pi.mpr (fun i => (hf i x hx).continuousWithinAt), ?_⟩
  have hc (i : ι) := (contMDiffWithinAt_iff.mp (hf i x hx)).2
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at hc ⊢
  change ContDiffWithinAt ℝ n
    (fun a => productCoordinatesFlatten ι (fun i => chartAt Coordinates (f x i) (f ((extChartAt I x).symm a) i))) _ _
  apply (productCoordinatesFlatten ι).contDiff.contDiffAt.comp_contDiffWithinAt
  exact contDiffWithinAt_pi.mpr hc

def productExponentialDiffeomorph : letI := productAffineChartedSpace ι (C := C)
    PartialDiffeomorph (𝓘(ℝ, ProductCoordinates ι)) (𝓘(ℝ, ProductCoordinates ι))
      (ProductCoordinates ι) (ProductGroup ι) (⊤ : ℕ∞) := by
  letI := productAffineChartedSpace ι (C := C)
  letI := productAffineLieGroup ι (C := C)
  refine { (productExponentialHomeomorph ι D) with contMDiffOn_toFun := ?_, contMDiffOn_invFun := ?_ }
  · apply product_contMDiffOn ι
    intro i
    apply D.exponentialChart.contMDiffOn.comp
      (((contDiff_apply ℝ Coordinates i).comp (productCoordinatesFlatten ι).symm.contDiff).contMDiff.contMDiffOn)
    intro a ha
    exact ha.2 i (mem_univ i)
  · change ContMDiffOn (𝓘(ℝ, ProductCoordinates ι)) (𝓘(ℝ, ProductCoordinates ι)) (⊤ : ℕ∞)
      (fun g : ProductGroup ι => productCoordinatesFlatten ι (fun i => D.exponentialChart.invFun (g i))) (productExponentialHomeomorph ι D).target
    apply (productCoordinatesFlatten ι).contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply D.exponentialChart.contMDiffOn_invFun.comp
      ((product_projection_contMDiff i).contMDiffOn)
    intro g hg
    exact hg.1 i (mem_univ i)

end ProductExponentialData

theorem product_lie_exponential_data :
    ∃ C : ChartedSpace (ProductCoordinates ι) (ProductGroup ι),
      letI := C
      ∃ L : LieGroup (𝓘(ℝ, ProductCoordinates ι)) (↑(⊤ : ℕ∞) : ℕ∞ω) (ProductGroup ι),
        letI := L
        ∃ D : HilbertLieExponentialData (ProductGroup ι) (ProductCoordinates ι) (ι × Fin 6),
          D.exponential = productExponential ι ∧
          (∀ b c, D.basis b c = if c = b then 1 else 0) ∧
          (∀ g a b, D.basis.equivFun (D.adjoint g (D.basis b)) a =
            productAdjointMatrix ι g a b) := by
  obtain ⟨C, L, hC⟩ := affine_lie_structure
  letI := C
  letI := L
  obtain ⟨D₀, hD₀, _, _⟩ := single_lie_exponential_data hC
  let CP := productAffineChartedSpace ι (C := C)
  letI := CP
  let LP := productAffineLieGroup ι (C := C)
  letI := LP
  let EP := productExponentialDiffeomorph ι D₀
  have hs : ContMDiff (𝓘(ℝ, ProductCoordinates ι)) (𝓘(ℝ, ProductCoordinates ι))
      (⊤ : ℕ∞) (productExponential ι) := by
    apply product_contMDiff
    intro i
    exact (exponential_contMDiff hC).comp
      (((contDiff_apply ℝ Coordinates i).comp
        (productCoordinatesFlatten ι).symm.contDiff).contMDiff)
  have ha (a b : ι × Fin 6) :
      ContMDiff (𝓘(ℝ, ProductCoordinates ι)) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
        (fun g : ProductGroup ι => productAdjointMatrix ι g a b) := by
    by_cases hab : a.1 = b.1
    · have hh := (adjointMatrix_contMDiff hC a.2 b.2).comp
          (product_projection_contMDiff (C := C) a.1)
      change ContMDiff (𝓘(ℝ, ProductCoordinates ι)) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
        (fun g : ProductGroup ι => adjointMatrix (g a.1) a.2 b.2) at hh
      exact hh.congr (fun g => by simp [productAdjointMatrix, hab])
    · simp only [productAdjointMatrix, hab, ↓reduceIte]
      exact contMDiff_const
  let D : HilbertLieExponentialData (ProductGroup ι) (ProductCoordinates ι) (ι × Fin 6) :=
    { basis := Pi.basisFun ℝ (ι × Fin 6)
      exponential := productExponential ι
      exponential_zero := productExponential_zero ι
      exponential_add_ray := productExponential_add_ray ι
      exponential_smooth := hs
      exponentialChart := EP
      zero_mem_source := ⟨Set.mem_univ _, fun i _ => D₀.zero_mem_source⟩
      chart_eq_exponential := by
        intro a ha
        funext i
        change D₀.exponentialChart ((productCoordinatesFlatten ι).symm a i) = _
        have hi : (productCoordinatesFlatten ι).symm a i ∈ D₀.exponentialChart.source :=
          ha.2 i (mem_univ i)
        rw [D₀.chart_eq_exponential _ hi, hD₀]
        rfl
      adjoint := productAdjointLinearEquiv ι
      adjoint_smooth := by
        intro a b
        simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply,
          productAdjointLinearEquiv_basis] using ha a b
      exponential_conjugation := productExponential_adjoint ι }
  refine ⟨CP, LP, D, rfl, ?_, ?_⟩
  · intro b c
    simp [D, Pi.basisFun_apply, Pi.single_apply]
  · intro g a b
    exact productAdjointLinearEquiv_basis ι g a b
end Products

end DedekindZetaZeroFree.PGLComplex

end
end
