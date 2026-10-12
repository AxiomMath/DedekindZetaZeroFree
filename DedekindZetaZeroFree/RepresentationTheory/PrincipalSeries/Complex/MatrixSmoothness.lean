module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesMatrixSmooth
open KPCplxCharacterHaar
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable def upperTriangular (a d : ℂˣ) (b : ℂ) : ComplexGL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℂ), b; 0, (d : ℂ)] (by
    simpa [Matrix.det_fin_two] using mul_ne_zero a.ne_zero d.ne_zero)
noncomputable def inductionWeight (s : ℝ) (a d : ℂˣ) : ℝ :=
  Real.rpow (‖(a : ℂ) / (d : ℂ)‖ ^ 2) (1 / 2 + s)
noncomputable def openCoordinate (f : ComplexGL2 → ℂ) (x : ℂ) : ℂ :=
  f (weyl * upperUnipotent x)
noncomputable def infinityCoordinate (f : ComplexGL2 → ℂ) (u : ℂ) : ℂ :=
  f (lowerUnipotent u)
noncomputable def matrixFunction (f : ComplexGL2 → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  if h : g.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero g h) else 0
private lemma upperTriangular_coe_matrix (a d : ℂˣ) (b : ℂ) :
    (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := rfl
private lemma chart_formula (s : ℝ) (f : ComplexGL2 → ℂ)
    (hcov : ∀ (a d : ℂˣ) (b : ℂ) (g : ComplexGL2),
      f (upperTriangular a d b * g) = (inductionWeight s a d : ℂ) * f g)
    (hopen : ContDiff ℝ (⊤ : ℕ∞) (openCoordinate f))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate f)) (g : ComplexGL2)
    (north : Bool) (h : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1) ≠ 0) :
    f g = (Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)‖ ^ 2) (1 + 2*s) : ℂ) *
      (if north then openCoordinate f else infinityCoordinate f)
      ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 1 else 0) /
       (g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)) := by
  let d : ℂˣ := Units.mk0 ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)) h
  let a : ℂˣ := (if north then -Matrix.GeneralLinearGroup.det g else Matrix.GeneralLinearGroup.det g) / d
  have hg : g = upperTriangular a d
      ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 (if north then 0 else 1)) *
      (if north then weyl * upperUnipotent
        ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
       else lowerUnipotent
        ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    cases north <;> fin_cases i <;> fin_cases j <;>
      simp [upperTriangular_coe_matrix, weyl, upperUnipotent, lowerUnipotent,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        a, d, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    all_goals simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true] at h
    all_goals field_simp [h]
    all_goals ring
  conv_lhs => rw [hg, hcov]
  have hw : inductionWeight s a d =
      Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)‖ ^ 2) (1 + 2*s) := by
    unfold inductionWeight
    have he : ‖(a : ℂ) / (d : ℂ)‖ = ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)‖ ^ 2 := by
      cases north <;> simp [a, d, norm_div, norm_neg, div_div, sq]
    rw [he]
    calc
      _ = Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
          ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)‖ ^ 2)
          ((2 : ℕ) * (1/2+s)) :=
        (Real.rpow_natCast_mul (show 0 ≤ ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
          ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)‖ ^ 2 by positivity) 2 (1/2+s)).symm
      _ = _ := by congr 1; norm_num; ring
  rw [hw]
  cases north <;> rfl

private lemma matrix_chart_smooth (s : ℝ) (f : ComplexGL2 → ℂ)
    (hcov : ∀ (a d : ℂˣ) (b : ℂ) (g : ComplexGL2),
      f (upperTriangular a d b * g) = (inductionWeight s a d : ℂ) * f g)
    (hopen : ContDiff ℝ (⊤ : ℕ∞) (openCoordinate f))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate f))
    (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.det ≠ 0)
    (north : Bool) (hc : m 1 (if north then 0 else 1) ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (matrixFunction f) m := by
  let c : Fin 2 := if north then 0 else 1
  let d : Fin 2 := if north then 1 else 0
  have hdet : ContDiff ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ => g 1 c) := by fun_prop
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ =>
      ‖g.det‖ / ‖g 1 c‖ ^ 2) m :=
    ((contDiffAt_norm ℝ hm).comp m hdet.contDiffAt).div
      (((contDiffAt_norm ℝ hc).comp m he.contDiffAt).pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  have hp : ‖m.det‖ / ‖m 1 c‖ ^ 2 ≠ 0 :=
    div_ne_zero (norm_ne_zero_iff.mpr hm) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  have hw : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ =>
      (Real.rpow (‖g.det‖ / ‖g 1 c‖ ^ 2) (1+2*s) : ℂ)) m :=
    by
      have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ =>
          Real.rpow (‖g.det‖ / ‖g 1 c‖ ^ 2) (1+2*s)) m :=
        by
          have hr0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.rpow t (1+2*s))
              (‖m.det‖ / ‖m 1 c‖ ^ 2) := Real.contDiffAt_rpow_const_of_ne hp
          have hcomp := hr0.comp m hn
          simpa only [Function.comp_def] using hcomp
      have hcomp := Complex.ofRealCLM.contDiff.contDiffAt.comp m hr
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using hcomp
  have hratio : ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ =>
      g 1 d / g 1 c) m := by
    simp only [div_eq_mul_inv]
    exact (show ContDiffAt ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ => g 1 d) m by
      fun_prop).mul (he.contDiffAt.inv hc)
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (if north then openCoordinate f else infinityCoordinate f) := by
    cases north
    · exact hinf
    · exact hopen
  apply (hw.mul (hf.contDiffAt.comp m hratio)).congr_of_eventuallyEq
  have hmd : ∀ᶠ g : Matrix (Fin 2) (Fin 2) ℂ in nhds m, g.det ≠ 0 :=
    hdet.continuous.continuousAt (isOpen_ne.mem_nhds hm)
  have hmc : ∀ᶠ g : Matrix (Fin 2) (Fin 2) ℂ in nhds m, g 1 c ≠ 0 :=
    he.continuous.continuousAt (isOpen_ne.mem_nhds hc)
  filter_upwards [hmd, hmc] with g hg hg'
  rw [matrixFunction, dif_pos hg]
  exact chart_formula s f hcov hopen hinf (Matrix.GeneralLinearGroup.mkOfDetNeZero g hg) north hg'

theorem covariant_matrix_smooth (s : ℝ) (f : ComplexGL2 → ℂ)
    (hcov : ∀ (a d : ℂˣ) (b : ℂ) (g : ComplexGL2),
      f (upperTriangular a d b * g) = (inductionWeight s a d : ℂ) * f g)
    (hopen : ContDiff ℝ (⊤ : ℕ∞) (openCoordinate f))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate f)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matrixFunction f)
      {g : Matrix (Fin 2) (Fin 2) ℂ | g.det ≠ 0} := by
  intro m hm
  by_cases h : m 1 0 = 0
  · have h' : m 1 1 ≠ 0 := by
      intro hz
      apply hm
      simp [Matrix.det_fin_two, h, hz]
    exact (matrix_chart_smooth s f hcov hopen hinf m hm false h').contDiffWithinAt
  · exact (matrix_chart_smooth s f hcov hopen hinf m hm true h).contDiffWithinAt

lemma matrixFunction_coe (f : ComplexGL2 → ℂ) (g : ComplexGL2) : matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  unfold matrixFunction
  split_ifs with h
  · exact congrArg f (Units.ext rfl)
  · exact False.elim (h (Matrix.GeneralLinearGroup.det_ne_zero g))
lemma matrix_smooth_charts (f : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (matrixFunction f)
      {g : Matrix (Fin 2) (Fin 2) ℂ | g.det ≠ 0}) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate f) ∧
      ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate f) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (upperUnipotent z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change ContDiff ℝ (⊤ : ℕ∞) ((Matrix.ofLinearEquiv ℝ : (Fin 2 → Fin 2 → ℂ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) ∘
      (fun z : ℂ => fun i j => !![1, z; 0, 1] i j))
    apply ((Matrix.ofLinearEquiv ℝ : (Fin 2 → Fin 2 → ℂ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ).toLinearMap.toContinuousLinearMap.contDiff).comp
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;> simp
    all_goals first | exact contDiff_const | exact contDiff_id
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (lowerUnipotent z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change ContDiff ℝ (⊤ : ℕ∞) ((Matrix.ofLinearEquiv ℝ : (Fin 2 → Fin 2 → ℂ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) ∘
      (fun z : ℂ => fun i j => !![1, 0; z, 1] i j))
    apply ((Matrix.ofLinearEquiv ℝ : (Fin 2 → Fin 2 → ℂ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ).toLinearMap.toContinuousLinearMap.contDiff).comp
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;> simp
    all_goals first | exact contDiff_const | exact contDiff_id
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (weyl * upperUnipotent z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    exact (LinearMap.mulLeft ℝ (weyl : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap.contDiff.comp hu
  constructor
  · have h := hf.comp ho.contDiffOn (s := Set.univ) (by intro z hz; exact Matrix.GeneralLinearGroup.det_ne_zero (weyl * upperUnipotent z))
    apply contDiffOn_univ.mp
    convert h using 1
    funext z
    exact (matrixFunction_coe f _).symm
  · have h := hf.comp hi.contDiffOn (s := Set.univ) (by intro z hz; exact Matrix.GeneralLinearGroup.det_ne_zero (lowerUnipotent z))
    apply contDiffOn_univ.mp
    convert h using 1
    funext z
    exact (matrixFunction_coe f _).symm
end DedekindZetaZeroFree.KPCplxPrincipalSeriesMatrixSmooth
