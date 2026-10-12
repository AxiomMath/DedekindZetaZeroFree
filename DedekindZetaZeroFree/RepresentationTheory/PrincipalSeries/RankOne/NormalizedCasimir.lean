module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.RightDerivedAction

@[expose] public section

section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.PauliContraction
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

 abbrev M := Matrix (Fin 2) (Fin 2) ℂ
 abbrev Idx := Fin 2 × Fin 2 × Bool
 def e (p : Idx) : M := Matrix.single p.1 p.2.1 (if p.2.2 then Complex.I else 1)
 def c (x : M) (p : Idx) : ℝ := if p.2.2 then (x p.1 p.2.1).im else (x p.1 p.2.1).re
private lemma expansion (x : M) : x = ∑ p : Idx, c x p • e p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, c, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.single, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, Complex.real_smul] <;>
    apply Complex.ext <;> simp

private lemma bilinear_expand (B : M →L[ℝ] M →L[ℝ] ℂ) (x y : M) :
    B x y = ∑ p : Idx, ∑ q : Idx, (c x p * c y q) • B (e p) (e q) := by
  conv_lhs => rw [expansion x, expansion y]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]
set_option maxHeartbeats 2000000 in
private lemma tensor (m : M) (p q : Idx) :
    (∑ j : Fin 3, c (m * noncompactMatrix j) p * c (m * noncompactMatrix j) q) -
    (∑ j : Fin 3, c (m * compactMatrix j) p * c (m * compactMatrix j) q) =
    (∑ j : Fin 3, c (noncompactMatrix j * m) p * c (noncompactMatrix j * m) q) -
    (∑ j : Fin 3, c (compactMatrix j * m) p * c (compactMatrix j * m) q) := by
  rcases p with ⟨a,b,s⟩
  rcases q with ⟨d,f,t⟩
  fin_cases a <;> fin_cases b <;> cases s <;>
    fin_cases d <;> fin_cases f <;> cases t <;>
    simp [c, noncompactMatrix, compactMatrix, Fin.sum_univ_three,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring
private lemma contraction_expand (B : M →L[ℝ] M →L[ℝ] ℂ) (X : Fin 3 → M) :
    (∑ j, B (X j) (X j)) =
    ∑ p : Idx, ∑ q : Idx, (∑ j, c (X j) p * c (X j) q) • B (e p) (e q) := by
  simp only [bilinear_expand B (X _) (X _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_smul]

theorem pauli_contraction_left_right
    (B : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ]
      Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    (∑ j : Fin 3, B ((g : Matrix (Fin 2) (Fin 2) ℂ) * noncompactMatrix j)
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * noncompactMatrix j)) -
    (∑ j : Fin 3, B ((g : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j)
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j)) =
    (∑ j : Fin 3, B (noncompactMatrix j * (g : Matrix (Fin 2) (Fin 2) ℂ))
      (noncompactMatrix j * (g : Matrix (Fin 2) (Fin 2) ℂ))) -
    (∑ j : Fin 3, B (compactMatrix j * (g : Matrix (Fin 2) (Fin 2) ℂ))
      (compactMatrix j * (g : Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [contraction_expand B (fun j => (g : M) * noncompactMatrix j),
    contraction_expand B (fun j => (g : M) * compactMatrix j),
    contraction_expand B (fun j => noncompactMatrix j * (g : M)),
    contraction_expand B (fun j => compactMatrix j * (g : M))]
  simp only [← Finset.sum_sub_distrib, ← sub_smul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, tensor]

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.PauliContraction

end

end

section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.Diagonal
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction
open KPCplxPrincipalSeriesCharts

 abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

 def diagFlow (c : ℂ) (t : ℝ) : KPCplxCharacterHaar.ComplexGL2 :=
  upperTriangular (Units.mk0 (Complex.exp (t * c)) (Complex.exp_ne_zero _))
    (Units.mk0 (Complex.exp (-(t * c))) (Complex.exp_ne_zero _)) 0

 def diagPath (c : ℂ) (m : Mat) (t : ℝ) : Mat :=
  !![Complex.exp (t * c), 0; 0, Complex.exp (-(t * c))] * m

 def diagVel (c : ℂ) (m : Mat) (t : ℝ) : Mat :=
  !![c * Complex.exp (t * c), 0; 0, -c * Complex.exp (-(t * c))] * m

private theorem diagPath_zero (c : ℂ) (m : Mat) : diagPath c m 0 = m := by
  simp [diagPath, Matrix.mul_apply, Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem diagPath_deriv (c : ℂ) (m : Mat) (t : ℝ) :
    HasDerivAt (diagPath c m) (diagVel c m t) t := by
  have h := ((Complex.hasDerivAt_exp (t * c)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (Complex.ofRealCLM.hasDerivAt.mul_const c)
  have hn := ((Complex.hasDerivAt_exp (-(t * c))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (Complex.ofRealCLM.hasDerivAt.mul_const c).neg
  simp only [Complex.ofRealCLM_apply, mul_one, one_mul,
    ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul] at h hn
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i
  · simpa [diagPath, diagVel, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using h.mul_const (m 0 j)
  · simpa [diagPath, diagVel, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hn.mul_const (m 1 j)

private theorem diagVel_deriv (c : ℂ) (m : Mat) :
    HasDerivAt (diagVel c m) ((c ^ 2) • m) 0 := by
  have h := ((Complex.hasDerivAt_exp (0 * c)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    (Complex.ofRealCLM.hasDerivAt.mul_const c)
  have hn := ((Complex.hasDerivAt_exp (-(0 * c))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    (Complex.ofRealCLM.hasDerivAt.mul_const c).neg
  simp only [Complex.ofRealCLM_apply, mul_one, one_mul,
    ContinuousLinearMap.coe_restrictScalars, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, zero_mul, neg_zero, Complex.exp_zero] at h hn
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i
  · simpa [diagVel, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul, pow_two, mul_assoc] using (h.const_mul c).mul_const (m 0 j)
  · simpa [diagVel, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul, pow_two, mul_assoc] using (hn.const_mul (-c)).mul_const (m 1 j)

private theorem diag_weight (s : ℝ) (c : ℂ) (t : ℝ) :
    inductionWeight s (Units.mk0 (Complex.exp (t * c)) (Complex.exp_ne_zero _))
      (Units.mk0 (Complex.exp (-(t * c))) (Complex.exp_ne_zero _)) =
      Real.exp ((2 * (1 + 2 * s) * c.re) * t) := by
  unfold inductionWeight complexAbs
  simp only [Units.val_mk0, norm_div, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Real.exp_sub, ← Real.exp_nat_mul]
  change (Real.exp (2 * (t * c.re - -(t * c.re)))) ^ (1 / 2 + s) = _
  rw [← Real.exp_mul]
  congr 1
  ring

private theorem diag_covariance (s : ℝ) (f : PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) (c : ℂ) (t : ℝ) :
    matrixFunction f.val (diagPath c (g : Mat) t) =
      (Real.exp ((2 * (1 + 2 * s) * c.re) * t) : ℂ) * f g := by
  have he : diagPath c (g : Mat) t = ((diagFlow c t * g) : Mat) := by
    rfl
  rw [he]
  unfold matrixFunction
  rw [dif_pos (show ((diagFlow c t : Mat) * (g : Mat)).det ≠ 0 from Matrix.GeneralLinearGroup.det_ne_zero (diagFlow c t * g))]
  have hh : Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((diagFlow c t * g) : Mat) (show ((diagFlow c t : Mat) * (g : Mat)).det ≠ 0 from Matrix.GeneralLinearGroup.det_ne_zero (diagFlow c t * g)) = diagFlow c t * g := by
    apply Units.ext
    rfl
  rw [hh]
  have hc := (principalSeries_mem_iff s f.val).mp f.property
  unfold diagFlow
  rw [hc.1]
  rw [diag_weight]

private theorem diag_hessian (s : ℝ) (f : PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) (c : ℂ) :
    fderiv ℝ (fderiv ℝ (matrixFunction f.val)) (g : Mat)
      (diagVel c (g : Mat) 0) (diagVel c (g : Mat) 0) +
    fderiv ℝ (matrixFunction f.val) (g : Mat) ((c ^ 2) • (g : Mat)) =
      (((2 * (1 + 2 * s) * c.re) ^ 2 : ℝ) : ℂ) * f g := by
  letI : NormedAddCommGroup (Mat →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Mat →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
  let F := matrixFunction f.val
  let m : Mat := g
  let k : ℝ := 2 * (1 + 2 * s) * c.re
  have ho : IsOpen {m : Mat | m.det ≠ 0} := by
    exact isOpen_ne.preimage (by fun_prop)
  have hf := ((principalSeries_mem_iff s f.val).mp f.property).2
  have hd := hf.fderiv_of_isOpen ho (m := (⊤ : ℕ∞)) (by simp)
  have hpdet (t : ℝ) : (diagPath c m t).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero (diagFlow c t * g)
  have hF (t : ℝ) : DifferentiableAt ℝ F (diagPath c m t) :=
    (hf.differentiableOn (by simp)).differentiableAt (ho.mem_nhds (hpdet t))
  have hD : DifferentiableAt ℝ (fderiv ℝ F) m :=
    (hd.differentiableOn (by simp)).differentiableAt (ho.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have he (t : ℝ) : fderiv ℝ F (diagPath c m t) (diagVel c m t) =
      (k : ℂ) * (Real.exp (k * t) : ℂ) * f g := by
    have hh := (hF t).hasFDerivAt.comp_hasDerivAt t (diagPath_deriv c m t)
    have heq : (fun t : ℝ => F (diagPath c m t)) =
        (fun t : ℝ => (Real.exp (k * t) : ℂ) * f g) := by
      funext t
      exact diag_covariance s f g c t
    have hx := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((Real.hasDerivAt_exp (k * t)).comp t ((hasDerivAt_id t).const_mul k))).mul_const (f g)
    dsimp only [Function.comp_def] at hh hx
    rw [heq] at hh
    convert hh.unique hx using 1 <;> simp [mul_comm, mul_left_comm, mul_assoc]
  have hD0 : DifferentiableAt ℝ (fderiv ℝ F) (diagPath c m 0) := by
    rw [diagPath_zero]; exact hD
  have hchain := HasFDerivAt.comp_hasDerivAt (E := Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ) 0 hD0.hasFDerivAt (diagPath_deriv c m 0)
  have ha := hchain.clm_apply (diagVel_deriv c m)
  have heq : (fun t : ℝ => fderiv ℝ F (diagPath c m t) (diagVel c m t)) =
      (fun t : ℝ => (k : ℂ) * (Real.exp (k * t) : ℂ) * f g) := funext he
  dsimp only [Function.comp_def] at ha
  erw [heq] at ha
  have hx := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    ((Real.hasDerivAt_exp (k * 0)).comp 0 ((hasDerivAt_id 0).const_mul k))).const_mul (k : ℂ)).mul_const (f g)
  convert ha.unique hx using 1 <;> simp [F, m, k, diagPath_zero, pow_two, mul_assoc]
  all_goals rfl

theorem diagonal_hessian_covariance (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
      (g : Matrix (Fin 2) (Fin 2) ℂ)
      (noncompactMatrix 0 * (g : Matrix (Fin 2) (Fin 2) ℂ))
      (noncompactMatrix 0 * (g : Matrix (Fin 2) (Fin 2) ℂ)) -
    fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
      (g : Matrix (Fin 2) (Fin 2) ℂ)
      (compactMatrix 0 * (g : Matrix (Fin 2) (Fin 2) ℂ))
      (compactMatrix 0 * (g : Matrix (Fin 2) (Fin 2) ℂ)) =
    ((2 * (1 + 2 * s) ^ 2 : ℝ) : ℂ) * f g -
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
        (g : Matrix (Fin 2) (Fin 2) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  let r : ℝ := 1 / Real.sqrt 2
  have hr : r ^ 2 = 1 / 2 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hv : diagVel (r : ℂ) (g : Mat) 0 = noncompactMatrix 0 * (g : Mat) := by
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagVel, noncompactMatrix, r, Matrix.smul_apply, smul_eq_mul]
  have hvi : diagVel (Complex.I * r) (g : Mat) 0 = compactMatrix 0 * (g : Mat) := by
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagVel, compactMatrix, noncompactMatrix, r, Matrix.smul_apply, smul_eq_mul]
  have hc : (r : ℂ) ^ 2 = ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast hr
  have hci : (Complex.I * (r : ℂ)) ^ 2 = ((-(1 / 2) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq, hc]
    push_cast
    ring
  have hk : (2 * (1 + 2 * s) * r) ^ 2 = 2 * (1 + 2 * s) ^ 2 := by
    rw [mul_pow, hr]
    ring
  have h1 := diag_hessian s f g (r : ℂ)
  have h2 := diag_hessian s f g (Complex.I * r)
  rw [hv, hc] at h1
  rw [hvi, hci] at h2
  simp only [Complex.ofReal_re, hk] at h1
  have hi : (Complex.I * (r : ℂ)).re = 0 := by simp
  rw [hi] at h2
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, zero_mul] at h2
  have hs1 : (((1 / 2 : ℝ) : ℂ) • (g : Mat)) = (1 / 2 : ℝ) • (g : Mat) := by
    ext i j
    simp [smul_eq_mul]
  have hs2 : (((-(1 / 2) : ℝ) : ℂ) • (g : Mat)) = (-(1 / 2) : ℝ) • (g : Mat) := by
    ext i j
    simp [smul_eq_mul]
  rw [hs1, map_smul] at h1
  rw [hs2, map_smul] at h2
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h1 h2
  linear_combination h1 - h2

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.Diagonal

end

end

section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

def upperRoot : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

def lowerRoot : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

theorem offdiagonal_pauli_contraction
    (B : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ]
      Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ)
    (m : Matrix (Fin 2) (Fin 2) ℂ) :
    B (noncompactMatrix 1 * m) (noncompactMatrix 1 * m) +
      B (noncompactMatrix 2 * m) (noncompactMatrix 2 * m) -
      (B (compactMatrix 1 * m) (compactMatrix 1 * m) +
        B (compactMatrix 2 * m) (compactMatrix 2 * m)) =
    (B (upperRoot * m) (lowerRoot * m) + B (lowerRoot * m) (upperRoot * m)) -
      (B ((Complex.I • upperRoot) * m) ((Complex.I • lowerRoot) * m) +
        B ((Complex.I • lowerRoot) * m) ((Complex.I • upperRoot) * m)) := by
  let a : ℝ := (Real.sqrt 2)⁻¹
  have h1 : noncompactMatrix 1 = a • (upperRoot + lowerRoot) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [noncompactMatrix, upperRoot, lowerRoot, a, Complex.real_smul]
  have h2 : noncompactMatrix 2 = a • (Complex.I • upperRoot - Complex.I • lowerRoot) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [noncompactMatrix, upperRoot, lowerRoot, a, Complex.real_smul]
  have k1 : compactMatrix 1 = a • (Complex.I • upperRoot + Complex.I • lowerRoot) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compactMatrix, noncompactMatrix, upperRoot, lowerRoot, a, Complex.real_smul]
    <;> ring
  have k2 : compactMatrix 2 = a • (-upperRoot + lowerRoot) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compactMatrix, noncompactMatrix, upperRoot, lowerRoot, a, Complex.real_smul]
    <;> simp [mul_left_comm Complex.I, ← mul_assoc, Complex.I_mul_I]
  rw [h1, h2, k1, k2]
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul,
    map_smul, map_add, map_sub, map_neg, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, Complex.real_smul]
  have ha : (a : ℂ) * a = 1 / 2 := by
    have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    dsimp [a]
    rw [Complex.ofReal_inv, ← mul_inv, hs]
    norm_num
  ring_nf
  rw [pow_two, ha]
  ring

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections

end

end

section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.RootProducts
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections
open KPCplxPrincipalSeriesCharts

 def a (t : ℝ) : ℂˣ := Units.mk0 (Real.exp t : ℂ) (by exact_mod_cast Real.exp_ne_zero t)
private lemma weight (t s : ℝ) : inductionWeight s (a t) 1 = Real.exp ((1 + 2*s)*t) := by
  simp only [inductionWeight, complexAbs, a, Units.val_mk0, Units.val_one, div_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_exp]
  congr 1
  ring
private lemma path (g : KPCplxCharacterHaar.ComplexGL2) :
    HasDerivAt (fun t : ℝ => !![(Real.exp t : ℂ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℂ))
      (upperRoot * (lowerRoot * (g : Matrix (Fin 2) (Fin 2) ℂ))) 0 := by
  have h : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ)) 1 0 := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Real.exp_zero,
      Complex.ofReal_one, one_smul] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Real.hasDerivAt_exp 0)
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [upperRoot, lowerRoot, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.head_cons,
      zero_mul, one_mul, add_zero, zero_add]
  · simpa using h.mul_const ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  · simpa using h.mul_const ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

private lemma cov (s t : ℝ) (f : PrincipalSeries s) (g : KPCplxCharacterHaar.ComplexGL2) :
    matrixFunction f.val (!![(Real.exp t : ℂ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Real.exp ((1+2*s)*t) : ℂ) * f g := by
  have hc := ((principalSeries_mem_iff s f.val).mp f.property).1 (a t) 1 0 g
  rw [weight] at hc
  convert hc using 1
  have hdet : (!![(Real.exp t : ℂ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
    rw [Matrix.det_mul]
    apply mul_ne_zero
    · simpa [Matrix.det_fin_two] using (a t).ne_zero
    · exact Matrix.GeneralLinearGroup.det_ne_zero g
  rw [matrixFunction, dif_pos hdet]
  apply congrArg f.val
  apply Units.ext
  rfl

private lemma firstDerivative (s : ℝ) (f : PrincipalSeries s) (g : KPCplxCharacterHaar.ComplexGL2) :
    fderiv ℝ (matrixFunction f.val) (g : Matrix (Fin 2) (Fin 2) ℂ)
      (upperRoot * (lowerRoot * (g : Matrix (Fin 2) (Fin 2) ℂ))) =
      ((1+2*s : ℝ) : ℂ) * f g := by
  have hf := ((principalSeries_mem_iff s f.val).mp f.property).2
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hd := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hp := path g
  have hz : !![(Real.exp (0 : ℝ) : ℂ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℂ) = g := by
    have h1 : !![(Real.exp (0 : ℝ) : ℂ), 0; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    rw [h1, one_mul]
  have hdf : HasFDerivAt (matrixFunction f.val)
      (fderiv ℝ (matrixFunction f.val) (g : Matrix (Fin 2) (Fin 2) ℂ))
      (!![(Real.exp (0 : ℝ) : ℂ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [hz]
    exact hd.hasFDerivAt
  have hc := hdf.comp_hasDerivAt 0 hp
  have he : HasDerivAt (fun t : ℝ => (Real.exp ((1+2*s)*t) : ℂ) * f g)
      (((1+2*s : ℝ) : ℂ) * f g) 0 := by
    have h := (Real.hasDerivAt_exp ((1+2*s) * (0 : ℝ))).comp 0 ((hasDerivAt_id 0).const_mul (1+2*s))
    have h' := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 h
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Real.exp_zero,
      mul_zero, mul_one, one_mul, Complex.ofReal_mul, Complex.ofReal_one, ContinuousLinearMap.coe_coe] using
      h'.mul_const (f g)
  have hh : (matrixFunction f.val ∘ (fun t : ℝ => !![(Real.exp t : ℂ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℂ))) =
      (fun t : ℝ => (Real.exp ((1+2*s)*t) : ℂ) * f g) := by
    funext t
    exact cov s t f g
  rw [hh] at hc
  exact hc.unique he

theorem root_product_fderiv_covariance (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
      (g : Matrix (Fin 2) (Fin 2) ℂ)
      (upperRoot * (lowerRoot * (g : Matrix (Fin 2) (Fin 2) ℂ))) -
    fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
      (g : Matrix (Fin 2) (Fin 2) ℂ)
      ((Complex.I • upperRoot) *
        ((Complex.I • lowerRoot) * (g : Matrix (Fin 2) (Fin 2) ℂ))) =
    ((2 * (1 + 2 * s) : ℝ) : ℂ) * f g := by
  have hi : (Complex.I • upperRoot) *
      ((Complex.I • lowerRoot) * (g : Matrix (Fin 2) (Fin 2) ℂ)) =
      -(upperRoot * (lowerRoot * (g : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, neg_one_smul]
  rw [hi, map_neg, firstDerivative]
  push_cast
  ring

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.RootProducts

end

end

section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.UpperUnipotent
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

private theorem invertible_open : IsOpen {m : Mat | m.det ≠ 0} := by
  have hc : Continuous (fun m : Mat => m.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  exact isOpen_ne_fun hc continuous_const

private theorem matrixFunction_coe (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Mat) = f g := by
  unfold matrixFunction
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

private theorem affine_upper (z : ℂ) (t : ℝ) :
    (upperUnipotent ((t : ℂ) * z) : Mat) = 1 + t • (z • upperRoot) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, upperRoot, Matrix.one_apply, Complex.real_smul,
      Matrix.smul_apply]

private theorem upper_invariant (s : ℝ) (f : PrincipalSeries s)
    (g : ComplexGL2) (x : ℂ) : f.val (upperUnipotent x * g) = f.val g := by
  have hc := ((principalSeries_mem_iff s f.val).mp f.property).1 (1 : ℂˣ) 1 x g
  have he : upperTriangular (1 : ℂˣ) 1 x = upperUnipotent x := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  simpa [he, inductionWeight, complexAbs] using hc

private theorem upper_differential_zero (s : ℝ) (f : PrincipalSeries s)
    (g : ComplexGL2) (z : ℂ) :
    fderiv ℝ (matrixFunction f.val) (g : Mat) ((z • upperRoot) * (g : Mat)) = 0 := by
  let X := (z • upperRoot) * (g : Mat)
  have hf := ((principalSeries_mem_iff s f.val).mp f.property).2
  have hsm := hf.contDiffAt (invertible_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hd := hsm.differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => (g : Mat) + t • X) X 0 := by
    convert (hasDerivAt_const (0 : ℝ) (g : Mat)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const X) using 1 <;>
      first | rfl | simp only [one_smul, zero_add]
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he : (fun t : ℝ => matrixFunction f.val ((g : Mat) + t • X)) =
      (fun _ : ℝ => f.val g) := by
    funext t
    have hm : (g : Mat) + t • X =
        (upperUnipotent ((t : ℂ) * z) * g : ComplexGL2) := by
      rw [Matrix.GeneralLinearGroup.coe_mul, affine_upper, Matrix.add_mul,
        Matrix.one_mul, Matrix.smul_mul]
    rw [hm, matrixFunction_coe, upper_invariant]
  dsimp only [Function.comp_def] at hc
  rw [he] at hc
  exact hc.unique (hasDerivAt_const 0 (f.val g))

theorem upper_unipotent_hessian_covariance (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2)
    (z : ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
      (g : Matrix (Fin 2) (Fin 2) ℂ)
      ((z • upperRoot) * (g : Matrix (Fin 2) (Fin 2) ℂ)) V +
    fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
      (g : Matrix (Fin 2) (Fin 2) ℂ)
      V ((z • upperRoot) * (g : Matrix (Fin 2) (Fin 2) ℂ)) =
    -(2 : ℂ) * fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
      (g : Matrix (Fin 2) (Fin 2) ℂ) ((z • upperRoot) * V) := by
  let m : Mat := g
  let F : Mat → ℂ := matrixFunction f.val
  let L : Mat →L[ℝ] Mat := (LinearMap.mulLeft ℝ (z • upperRoot)).toContinuousLinearMap
  have hL (a : Mat) : L a = (z • upperRoot) * a := rfl
  have hsm : ContDiffAt ℝ (⊤ : ℕ∞) F m :=
    ((principalSeries_mem_iff s f.val).mp f.property).2.contDiffAt
      (invertible_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hD : DifferentiableAt ℝ (fderiv ℝ F) m :=
    (hsm.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have he : (fun a : Mat => fderiv ℝ F a (L a)) =ᶠ[nhds m] (fun _ => (0 : ℂ)) := by
    filter_upwards [invertible_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g)] with a ha
    let ga : ComplexGL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha
    exact upper_differential_zero s f ga z
  have hh := hD.hasFDerivAt.clm_apply (L.hasFDerivAt (x := m))
  have hzero : fderiv ℝ (fun a : Mat => fderiv ℝ F a (L a)) m = 0 := by
    rw [he.fderiv_eq]
    exact (hasFDerivAt_const (0 : ℂ) m).fderiv
  have hv := congrArg (fun A : Mat →L[ℝ] ℂ => A V) (hh.fderiv.symm.trans hzero)
  have hsum : fderiv ℝ F m (L V) + fderiv ℝ (fderiv ℝ F) m V (L m) = 0 := by
    convert hv using 1 <;> rfl
  have hsym := hsm.isSymmSndFDerivAt (by simp [minSmoothness]) (L m) V
  change fderiv ℝ (fderiv ℝ F) m (L m) V +
    fderiv ℝ (fderiv ℝ F) m V (L m) = -(2 : ℂ) * fderiv ℝ F m (L V)
  have hsym' : fderiv ℝ (fderiv ℝ F) m (L m) V =
      fderiv ℝ (fderiv ℝ F) m V (L m) := by
    convert hsym using 1 <;> rfl
  rw [hsym']
  linear_combination (2 : ℂ) * hsum

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.UpperUnipotent

end

end

section
noncomputable section
open scoped BigOperators Classical
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian
open InfinitesimalAction

theorem pauli_square_sum :
    (∑ j : Fin 3, noncompactMatrix j * noncompactMatrix j) -
      (∑ j : Fin 3, compactMatrix j * compactMatrix j) =
        (3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_succ, noncompactMatrix, compactMatrix, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.one_apply] <;> field_simp <;>
    simp [Complex.I_sq, hsq] <;> norm_num

open scoped Matrix.Norms.Operator in
private theorem casimir_path_hasDeriv_components (g : KPCplxCharacterHaar.ComplexGL2)
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
theorem rightDerivative_fderiv (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 =
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val) (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : HasDerivAt (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M))
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) 0 :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (casimir_path_hasDeriv_components g M i))
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

open scoped Matrix.Norms.Elementwise in

theorem localDerivative_fderiv (s : ℝ) (b : LocalBasis)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    localDerivative s b f g =
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
        (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * cartanMatrix b) := by
  exact rightDerivative_fderiv s f g (cartanMatrix b)

open scoped Matrix.Norms.Elementwise in

theorem localDerivative_twice_fderiv (s : ℝ) (b : LocalBasis)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    localDerivative s b (localDerivative s b f) g =
      fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
        (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * cartanMatrix b)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * cartanMatrix b) +
      fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
        (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * (cartanMatrix b * cartanMatrix b)) := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := g
  let F := KPCplxPrincipalSeriesCharts.matrixFunction f.val
  let X := cartanMatrix b
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hopen : IsOpen {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} :=
    isOpen_ne.preimage hcont
  have hmem : {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} ∈ nhds m :=
    hopen.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g)
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hd : DifferentiableAt ℝ (fderiv ℝ F) m :=
    ((hf.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)).differentiableOn
      (by simp)).differentiableAt hmem
  let R : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => y * X
        map_add' := fun y z => Matrix.add_mul y z X
        map_smul' := fun a y => Matrix.smul_mul a y X }
  have hmul : HasFDerivAt (fun y : Matrix (Fin 2) (Fin 2) ℂ => y * X) R m :=
    R.hasFDerivAt
  have he : KPCplxPrincipalSeriesCharts.matrixFunction (localDerivative s b f).val =ᶠ[nhds m]
      (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ F y (y * X)) := by
    filter_upwards [hmem] with y hy
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos hy]
    exact localDerivative_fderiv s b f (Matrix.GeneralLinearGroup.mkOfDetNeZero y hy)
  rw [localDerivative_fderiv, he.fderiv_eq]
  have hh := (hd.hasFDerivAt.clm_apply hmul).fderiv
  have hh' := congrArg (fun D : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ => D (m * X)) hh
  change (fderiv ℝ (fun y => fderiv ℝ F y (y * X)) m) (m * X) =
    fderiv ℝ (fderiv ℝ F) m (m * X) (m * X) + fderiv ℝ F m (m * (X * X))
  exact hh'.trans (by
    change fderiv ℝ F m ((m * X) * X) + fderiv ℝ (fderiv ℝ F) m (m * X) (m * X) = _
    rw [Matrix.mul_assoc, add_comm])

open scoped Matrix.Norms.Elementwise in

theorem radial_fderiv_zero (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val)
      (g : Matrix (Fin 2) (Fin 2) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := g
  let F := KPCplxPrincipalSeriesCharts.matrixFunction f.val
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hmem : {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} ∈ nhds m :=
    (isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g)
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hd : DifferentiableAt ℝ F m :=
    (hf.differentiableOn (by simp)).differentiableAt hmem
  have hp : HasDerivAt (fun t : ℝ => (t + 1) • m) m 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa using ((hasDerivAt_id (0 : ℝ)).add_const 1).smul_const (m i j)
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hn : ∀ᶠ t : ℝ in nhds 0, t + 1 ≠ 0 := by
    exact (isOpen_ne.preimage (by fun_prop : Continuous (fun t : ℝ => t + 1))).mem_nhds (by norm_num)
  have he : F ∘ (fun t : ℝ => (t + 1) • m) =ᶠ[nhds 0] (fun _ => f g) := by
    filter_upwards [hn] with t ht
    let c : ℂˣ := Units.mk0 ((t + 1 : ℝ) : ℂ) (by exact_mod_cast ht)
    have hc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) : Matrix (Fin 2) (Fin 2) ℂ) =
        (t + 1) • m := by
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, c, Units.val_mk0]
      rw [Matrix.scalar_apply]
      ext i j
      simp [Matrix.diagonal_mul, m, Complex.real_smul]
    have hdet : ((t + 1) • m).det ≠ 0 := by
      rw [← hc]
      exact Matrix.GeneralLinearGroup.det_ne_zero (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)
    change KPCplxPrincipalSeriesCharts.matrixFunction f.val ((t + 1) • m) = f g
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos hdet]
    have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero ((t + 1) • m) hdet =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * g := by
      apply Units.ext
      exact hc.symm
    rw [hg]
    exact KPCplxPrincipalSeriesCharts.central_invariance s f c g
  have hh' := hh.congr_of_eventuallyEq he.symm
  exact hh'.unique (hasDerivAt_const (0 : ℝ) (f g))

open scoped Matrix.Norms.Elementwise in

theorem casimir_hessian (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    ((∑ j : Fin 3, localDerivative s (false, j) (localDerivative s (false, j) f)) -
      (∑ j : Fin 3, localDerivative s (true, j) (localDerivative s (true, j) f))) g =
    (∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
        (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * noncompactMatrix j)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * noncompactMatrix j)) -
    (∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val))
        (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * compactMatrix j)) := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := g
  let D := fderiv ℝ (KPCplxPrincipalSeriesCharts.matrixFunction f.val) m
  have hz :
      (∑ j : Fin 3, D (m * (noncompactMatrix j * noncompactMatrix j))) -
      (∑ j : Fin 3, D (m * (compactMatrix j * compactMatrix j))) = 0 := by
    rw [← map_sum, ← map_sum, ← map_sub]
    rw [← Matrix.mul_sum, ← Matrix.mul_sum, ← Matrix.mul_sub, pauli_square_sum]
    rw [Matrix.mul_smul, Matrix.mul_one]
    change D ((3 : ℝ) • m) = 0
    rw [map_smul]
    have hd : D m = 0 := radial_fderiv_zero s f g
    rw [hd, smul_zero]
  change (∑ j : Fin 3, localDerivative s (false, j) (localDerivative s (false, j) f) g) -
    (∑ j : Fin 3, localDerivative s (true, j) (localDerivative s (true, j) f) g) = _
  simp only [localDerivative_twice_fderiv, cartanMatrix, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_add_distrib]
  linear_combination hz

theorem normalized_casimir (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    (∑ j : Fin 3, localDerivative s (false, j) (localDerivative s (false, j) f)) -
      (∑ j : Fin 3, localDerivative s (true, j) (localDerivative s (true, j) f)) =
        ((8 * s ^ 2 - 2 : ℝ) : ℂ) • f := by
  apply Subtype.ext
  funext g
  let m : Matrix (Fin 2) (Fin 2) ℂ := g
  let F := KPCplxPrincipalSeriesCharts.matrixFunction f.val
  let D := fderiv ℝ F m
  let B := fderiv ℝ (fderiv ℝ F) m
  let E := KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections.upperRoot
  let L := KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections.lowerRoot
  change ((∑ j : Fin 3, localDerivative s (false, j) (localDerivative s (false, j) f)) -
    (∑ j : Fin 3, localDerivative s (true, j) (localDerivative s (true, j) f))) g =
    ((8 * s ^ 2 - 2 : ℝ) : ℂ) * f g
  rw [casimir_hessian]
  rw [KPSmoothCoreCasimirEnergyHessianCovariance.PauliContraction.pauli_contraction_left_right B g]
  have hd : B (noncompactMatrix 0 * m) (noncompactMatrix 0 * m) -
      B (compactMatrix 0 * m) (compactMatrix 0 * m) =
      ((2 * (1 + 2 * s) ^ 2 : ℝ) : ℂ) * f g := by
    have h := KPSmoothCoreCasimirEnergyHessianCovariance.Diagonal.diagonal_hessian_covariance s f g
    have hz := radial_fderiv_zero s f g
    simpa only [hz, sub_zero] using h
  have he : B (E * m) (L * m) + B (L * m) (E * m) =
      -(2 : ℂ) * D (E * (L * m)) := by
    simpa only [one_smul] using
      KPSmoothCoreCasimirEnergyHessianCovariance.UpperUnipotent.upper_unipotent_hessian_covariance s f g 1 (L * m)
  have hi : B ((Complex.I • E) * m) ((Complex.I • L) * m) +
      B ((Complex.I • L) * m) ((Complex.I • E) * m) =
      -(2 : ℂ) * D ((Complex.I • E) * ((Complex.I • L) * m)) :=
    KPSmoothCoreCasimirEnergyHessianCovariance.UpperUnipotent.upper_unipotent_hessian_covariance s f g
      Complex.I ((Complex.I • L) * m)
  have hr : D (E * (L * m)) - D ((Complex.I • E) * ((Complex.I • L) * m)) =
      ((2 * (1 + 2 * s) : ℝ) : ℂ) * f g :=
    KPSmoothCoreCasimirEnergyHessianCovariance.RootProducts.root_product_fderiv_covariance s f g
  have ho : B (noncompactMatrix 1 * m) (noncompactMatrix 1 * m) +
      B (noncompactMatrix 2 * m) (noncompactMatrix 2 * m) -
      (B (compactMatrix 1 * m) (compactMatrix 1 * m) +
        B (compactMatrix 2 * m) (compactMatrix 2 * m)) =
      -((4 * (1 + 2 * s) : ℝ) : ℂ) * f g := by
    rw [KPSmoothCoreCasimirEnergyHessianCovariance.RootDirections.offdiagonal_pauli_contraction B m,
      he, hi]
    calc
      _ = -(2 : ℂ) *
          (D (E * (L * m)) - D ((Complex.I • E) * ((Complex.I • L) * m))) := by ring
      _ = _ := by rw [hr]; push_cast; ring
  change (∑ j : Fin 3, B (noncompactMatrix j * m) (noncompactMatrix j * m)) -
    (∑ j : Fin 3, B (compactMatrix j * m) (compactMatrix j * m)) = _
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  calc
    _ = (B (noncompactMatrix 0 * m) (noncompactMatrix 0 * m) -
        B (compactMatrix 0 * m) (compactMatrix 0 * m)) +
        (B (noncompactMatrix 1 * m) (noncompactMatrix 1 * m) +
          B (noncompactMatrix 2 * m) (noncompactMatrix 2 * m) -
          (B (compactMatrix 1 * m) (compactMatrix 1 * m) +
            B (compactMatrix 2 * m) (compactMatrix 2 * m))) := by ring
    _ = _ := by rw [hd, ho]; push_cast; ring

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian

end

end
