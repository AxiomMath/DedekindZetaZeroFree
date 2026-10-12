module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.KPArch

noncomputable section

open scoped Matrix

open MeasureTheory

abbrev H3 := ℂ × ℝ

def height (z : H3) : ℝ := Real.exp z.2

def actionDenominator (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) : ℝ :=
  ‖g 1 0 * z.1 + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * height z ^ 2

def action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) : H3 :=
  (((g 0 0 * z.1 + g 0 1) * star (g 1 0 * z.1 + g 1 1) +
      g 0 0 * star (g 1 0) * (height z ^ 2 : ℝ)) /
      (actionDenominator g z : ℂ),
    Real.log (‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * height z /
      actionDenominator g z))

abbrev Space (d : ℕ) := Fin d → H3

def productAction (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z : Space d) : Space d := fun i => action (g i) (z i)

theorem actionDenominator_pos (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    0 < actionDenominator g z := by
  have hy : 0 < height z := Real.exp_pos _
  have hd := g.det_ne_zero
  by_cases hc : g 1 0 = 0
  · have hd' : g 1 1 ≠ 0 := by
      intro h
      apply hd
      simp [Matrix.det_fin_two, hc, h]
    simpa [actionDenominator, hc] using sq_pos_of_pos (norm_pos_iff.mpr hd')
  · unfold actionDenominator
    exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hc)) (sq_pos_of_pos hy))

theorem action_height (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    height (action g z) =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * height z /
        (‖g 1 0 * z.1 + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * height z ^ 2) := by
  change Real.exp (Real.log _) = _
  apply Real.exp_log
  exact div_pos (mul_pos (norm_pos_iff.mpr g.det_ne_zero) (Real.exp_pos _))
    (actionDenominator_pos g z)

def den (a b : ℂ) (x : ℂ) (Y : ℝ) : ℂ :=
  (a*x+b)*star (a*x+b)+a*star a*(Y:ℂ)

def num (a b c d : ℂ) (x : ℂ) (Y : ℝ) : ℂ :=
  (a*x+b)*star (c*x+d)+a*star c*(Y:ℂ)

private lemma den_comp (a b c d C D x : ℂ) (Y : ℝ) :
    (C*num a b c d x Y+D*den c d x Y)*star (C*num a b c d x Y+D*den c d x Y)+
      C*star C*((a*d-b*c)*star (a*d-b*c)*(Y:ℂ)) =
        den (C*a+D*c) (C*b+D*d) x Y * den c d x Y := by
  simp only [num, den, star_add, star_mul, star_sub, star_star, Complex.star_def,
    Complex.conj_ofReal]
  simp only [Complex.conj_conj]
  ring

private lemma num_comp (a b c d A B C D x : ℂ) (Y : ℝ) :
    (A*num a b c d x Y+B*den c d x Y)*star (C*num a b c d x Y+D*den c d x Y)+
      A*star C*((a*d-b*c)*star (a*d-b*c)*(Y:ℂ)) =
        num (A*a+B*c) (A*b+B*d) (C*a+D*c) (C*b+D*d) x Y * den c d x Y := by
  simp only [num, den, star_add, star_mul, star_sub, star_star, Complex.star_def,
    Complex.conj_ofReal]
  simp only [Complex.conj_conj]
  ring

private lemma norm_cast (a : ℂ) : (‖a‖ ^ 2 : ℝ) = (a*star a : ℂ) := by
  simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj a).symm

private lemma den_eq (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    (actionDenominator g z : ℂ) = den (g 1 0) (g 1 1) z.1 (height z ^ 2) := by
  simp only [actionDenominator, Complex.ofReal_add, Complex.ofReal_mul, norm_cast, den]

private lemma fst_eq (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    (action g z).1 = num (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.1 (height z ^ 2) /
      den (g 1 0) (g 1 1) z.1 (height z ^ 2) := by
  simp [action, num, ← den_eq]

private lemma height_sq (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    ((height (action g z) ^ 2 : ℝ) : ℂ) =
      ((g : Matrix (Fin 2) (Fin 2) ℂ).det * star ((g : Matrix (Fin 2) (Fin 2) ℂ).det) *
      ((height z ^ 2 : ℝ) : ℂ)) / (actionDenominator g z : ℂ)^2 := by
  rw [action_height]
  change (( (‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * height z / actionDenominator g z)^2 : ℝ) : ℂ) = _
  simp only [div_pow, mul_pow, Complex.ofReal_div, Complex.ofReal_mul, norm_cast,
    Complex.ofReal_pow]
  rw [← Complex.ofReal_pow, norm_cast]

private lemma den_mul (g h : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    (actionDenominator g (action h z) : ℂ) * (actionDenominator h z : ℂ) =
      (actionDenominator (g*h) z : ℂ) := by
  have hd : (actionDenominator h z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (actionDenominator_pos h z)
  rw [den_eq, den, fst_eq, height_sq]
  simp only [star_add, star_mul, star_div]
  rw [← den_eq h z]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [den_eq (g*h) z]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two]
  have hc := den_comp (h 0 0) (h 0 1) (h 1 0) (h 1 1) (g 1 0) (g 1 1) z.1 (height z ^ 2)
  rw [← den_eq h z] at hc
  simp only [map_div₀, Complex.conj_ofReal]
  simp only [star_add, star_mul, Complex.star_def] at hc
  simp only [Complex.conj_ofReal] at hc
  field_simp
  linear_combination hc

private lemma fst_mul (g h : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    (action g (action h z)).1 = (action (g*h) z).1 := by
  have hd : (actionDenominator h z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (actionDenominator_pos h z)
  have hg : (actionDenominator g (action h z) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (actionDenominator_pos g (action h z))
  rw [fst_eq g, ← den_eq g, num, fst_eq h, height_sq, fst_eq (g*h)]
  rw [← den_eq h, ← den_eq (g*h), ← den_mul g h z]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two, star_add, star_mul, Complex.star_def]
  simp only [map_div₀, Complex.conj_ofReal]
  have hc := num_comp (h 0 0) (h 0 1) (h 1 0) (h 1 1)
    (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.1 (height z ^ 2)
  rw [← den_eq h z] at hc
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal] at hc
  simp only [num, star_add, star_mul, star_star, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_conj] at hc ⊢
  field_simp
  linear_combination hc

theorem action_laws (g h : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    action 1 z = z ∧ action (g * h) z = action g (action h z) := by
  constructor
  · apply Prod.ext
    · simp [action, actionDenominator]
    · simp [action, actionDenominator, height]
  · apply Prod.ext
    · exact (fst_mul g h z).symm
    · apply Real.exp_injective
      change height (action (g*h) z) = height (action g (action h z))
      have hd : actionDenominator h z ≠ 0 := ne_of_gt (actionDenominator_pos h z)
      have hg : actionDenominator g (action h z) ≠ 0 :=
        ne_of_gt (actionDenominator_pos g (action h z))
      have hm : actionDenominator g (action h z) * actionDenominator h z =
          actionDenominator (g*h) z := by exact_mod_cast den_mul g h z
      rw [action_height (g*h), action_height g]
      change ‖((g*h) : Matrix.GeneralLinearGroup (Fin 2) ℂ).val.det‖ * height z /
          actionDenominator (g*h) z =
        ‖g.val.det‖ * height (action h z) / actionDenominator g (action h z)
      rw [action_height h]
      change ‖((g*h) : Matrix.GeneralLinearGroup (Fin 2) ℂ).val.det‖ * height z /
          actionDenominator (g*h) z =
        ‖g.val.det‖ * (‖h.val.det‖ * height z / actionDenominator h z) /
          actionDenominator g (action h z)
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, ← hm]
      field_simp

theorem scalar_action (a : ℂˣ) (z : H3) :
    action (Matrix.GeneralLinearGroup.scalar (Fin 2) a) z = z := by
  have ha : ‖(a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr a.ne_zero
  have hac : ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 ha
  have hc : (a : ℂ) * star (a : ℂ) = (‖(a : ℂ)‖ ^ 2 : ℝ) := by
    simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (a : ℂ)
  apply Prod.ext
  · simp only [action, actionDenominator, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, Fin.reduceEq, if_true, if_false,
      zero_mul, zero_add, norm_zero, zero_pow, mul_zero, add_zero, star_zero]
    norm_num only [OfNat.ofNat_ne_zero, zero_pow, zero_mul, add_zero]
    rw [show (a : ℂ) * z.1 * star (a : ℂ) =
      z.1 * ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ) by rw [← hc]; ring]
    exact mul_div_cancel_right₀ _ hac
  · simp only [action, actionDenominator, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, Fin.reduceEq, if_true, if_false,
      zero_mul, zero_add, norm_zero, zero_pow, mul_zero, add_zero, star_zero,
      Matrix.det_fin_two, norm_mul, sub_zero]
    norm_num only [OfNat.ofNat_ne_zero, zero_pow, zero_mul, add_zero]
    rw [show ‖(a : ℂ)‖ * ‖(a : ℂ)‖ = ‖(a : ℂ)‖ ^ 2 by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 ha)]
    exact Real.log_exp _

private lemma actionDenominator_contDiff (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    ContDiff ℝ ⊤ (actionDenominator g) := by
  unfold actionDenominator height
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  change ContDiff ℝ ⊤ (fun z : H3 =>
    Complex.reCLM (g 1 0 * z.1 + g 1 1) * Complex.reCLM (g 1 0 * z.1 + g 1 1) +
    Complex.imCLM (g 1 0 * z.1 + g 1 1) * Complex.imCLM (g 1 0 * z.1 + g 1 1) +
    _)
  fun_prop

 lemma action_contDiff (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    ContDiff ℝ ⊤ (action g) := by
  have hd := actionDenominator_contDiff g
  unfold action
  apply ContDiff.prodMk
  · simp only [div_eq_mul_inv]
    apply ContDiff.mul
    · unfold height
      change ContDiff ℝ ⊤ (fun x : H3 =>
        (g 0 0 * x.1 + g 0 1) * Complex.conjCLE (g 1 0 * x.1 + g 1 1) +
        g 0 0 * star (g 1 0) * Complex.ofRealCLM (Real.exp x.2 ^ 2))
      fun_prop
    · simpa only [Function.comp_def, Pi.inv_apply, Complex.ofRealCLM_apply,
        Complex.ofReal_inv] using
        Complex.ofRealCLM.contDiff.comp
          (hd.inv (fun z => ne_of_gt (actionDenominator_pos g z)))
  · apply ContDiff.log
    · apply ContDiff.div
      · unfold height
        fun_prop
      · exact hd
      · intro z
        exact ne_of_gt (actionDenominator_pos g z)
    · intro z
      exact ne_of_gt (div_pos (mul_pos (norm_pos_iff.mpr g.det_ne_zero)
        (Real.exp_pos _)) (actionDenominator_pos g z))

theorem productAction_contDiff (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    ContDiff ℝ ⊤ (productAction d g) := by
  apply contDiff_pi.mpr
  intro i
  exact (action_contDiff (g i)).comp (contDiff_apply ℝ H3 i)

end

end DedekindZetaZeroFree.KPArch

section

namespace DedekindZetaZeroFree.KPArch

noncomputable section
open scoped Matrix
open MeasureTheory

def metric (d : ℕ) (z v : Space d) : ℝ :=
  ∑ i, ((height (z i))⁻¹ ^ 2 * ‖(v i).1‖ ^ 2 + (v i).2 ^ 2)

def volumeDensity (d : ℕ) (z : Space d) : ℝ :=
  ∏ i, (height (z i))⁻¹ ^ 2

def hyperbolicVolume (d : ℕ) : Measure (Space d) :=
  volume.withDensity (fun z => ENNReal.ofReal (volumeDensity d z))

abbrev SplitSpace (d : ℕ) := (Fin (d + 1) → ℂ) × ℝ × (Fin d → ℝ)

def shape (d : ℕ) (b : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc b (-∑ i, b i)

def splitCoordinates (d : ℕ) (p : SplitSpace d) : Space (d + 1) :=
  fun i => (p.1 i, p.2.1 + shape d p.2.2 i)

theorem complex_places_of_primitive_twelfth_root (F : Type) [Field F]
    [NumberField F] (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) :
    NumberField.InfinitePlace.nrRealPlaces F = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces F = Module.finrank ℚ F / 2 ∧
      0 < NumberField.InfinitePlace.nrComplexPlaces F := by
  have hr := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
    (by norm_num : 2 < 12) hζ12
  have hn := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hp := Module.finrank_pos (R := ℚ) (M := F)
  refine ⟨hr, ?_, ?_⟩
  · omega
  · omega

private def norm2 (a : ℂ) : ℂ := a*star a
private def N (a b c d x : ℂ) (Y : ℝ) : ℂ :=
  (a*x+b)*star (c*x+d)+a*star c*(Y:ℂ)
private def D (c d x : ℂ) (Y : ℝ) : ℂ :=
  norm2 (c*x+d)+norm2 c*(Y:ℂ)
private def dN (a b c d x v : ℂ) (Y w : ℝ) : ℂ :=
  a*v*star (c*x+d)+(a*x+b)*star (c*v)+a*star c*(2*(Y:ℂ)*(w:ℂ))
private def dD (c d x v : ℂ) (Y w : ℝ) : ℂ :=
  c*v*star (c*x+d)+(c*x+d)*star (c*v)+c*star c*(2*(Y:ℂ)*(w:ℂ))
private lemma metric_alg (a b c d x v : ℂ) (Y w : ℝ) :
    norm2 (dN a b c d x v Y w * D c d x Y - N a b c d x Y*dD c d x v Y w) +
      norm2 (a*d-b*c)*(Y:ℂ)*((w:ℂ)*D c d x Y-dD c d x v Y w)^2 =
      norm2 (a*d-b*c)*D c d x Y^2*(norm2 v+(Y:ℂ)*(w:ℂ)^2) := by
  simp only [norm2, N, D, dN, dD, star_mul, star_add, star_sub, star_star,
    Complex.star_def, Complex.conj_ofReal]
  simp only [map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj]
  ring

private def path (z v : H3) (t : ℝ) : H3 := z + t • v
private lemma path_deriv (z v : H3) : HasDerivAt (path z v) v 0 := by
  exact ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z |>.congr_deriv (by simp)
private lemma norm2_cast (a : ℂ) : norm2 a = (‖a‖^2 : ℝ) := by
  simpa [norm2, Complex.normSq_eq_norm_sq] using Complex.mul_conj a
private lemma D_cast (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : H3) :
    D (g 1 0) (g 1 1) z.1 (height z ^ 2) = (actionDenominator g z : ℂ) := by
  simp [D, norm2_cast, actionDenominator]
private lemma dD_real (c d x v : ℂ) (Y w : ℝ) :
    (Complex.re (dD c d x v Y w) : ℂ) = dD c d x v Y w := by
  apply Complex.ext <;> simp [dD, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring
private lemma path_x (z v : H3) : HasDerivAt (fun t => (path z v t).1) v.1 0 :=
  (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt _ (path_deriv z v)
private lemma path_u (z v : H3) : HasDerivAt (fun t => (path z v t).2) v.2 0 :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt _ (path_deriv z v)
private lemma path_Y (z v : H3) :
    HasDerivAt (fun t => height (path z v t)^2) (2 * height z^2 * v.2) 0 := by
  convert ((path_u z v).exp.pow 2) using 1
  · rfl
  · simp [path, height]
    ring
private lemma path_N (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) :
    HasDerivAt (fun t => N (g 0 0) (g 0 1) (g 1 0) (g 1 1) (path z v t).1
      (height (path z v t)^2))
      (dN (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2) 0 := by
  have hx := path_x z v
  have hy := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ (path_Y z v)
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _
    ((hx.const_mul (g 1 0)).add_const (g 1 1))
  convert (((hx.const_mul (g 0 0)).add_const (g 0 1)).mul hc).add
    (hy.const_mul (g 0 0 * star (g 1 0))) using 1
  · rfl
  · simp [N, dN, path, Complex.star_def]
private lemma path_D (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) :
    HasDerivAt (fun t => D (g 1 0) (g 1 1) (path z v t).1 (height (path z v t)^2))
      (dD (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2) 0 := by
  have hx := (path_x z v).const_mul (g 1 0) |>.add_const (g 1 1)
  have hy := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ (path_Y z v)
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ hx
  convert (hx.mul hc).add (hy.const_mul (g 1 0 * star (g 1 0))) using 1
  · rfl
  · simp [D, norm2, dD, path, Complex.star_def]
private lemma path_R (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) :
    HasDerivAt (fun t => actionDenominator g (path z v t))
      (Complex.re (dD (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2)) 0 := by
  simpa only [Function.comp_def, Complex.reCLM_apply, D_cast, Complex.ofReal_re] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ (path_D g z v)
private def diffX (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) : ℂ :=
  (dN (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2 *
      (actionDenominator g z : ℂ) -
    N (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.1 (height z^2) *
      dD (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2) /
      (actionDenominator g z : ℂ)^2
private def diffU (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) : ℝ :=
  v.2 - Complex.re (dD (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2) / actionDenominator g z
private lemma path_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) :
    HasDerivAt (fun t => action g (path z v t)) (diffX g z v, diffU g z v) 0 := by
  have hr := path_R g z v
  have hy := (path_u z v).exp
  have hn : actionDenominator g z ≠ 0 := ne_of_gt (actionDenominator_pos g z)
  have hc : (actionDenominator g z : ℂ) ≠ 0 := by exact_mod_cast hn
  have hdet : ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ ≠ 0 := norm_ne_zero_iff.mpr g.det_ne_zero
  have hx := (path_N g z v).div (path_D g z v) (by simpa [path, D_cast] using hc)
  have hu := ((hy.const_mul ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖).div hr
    (by simpa [path] using hn)).log (by
      simpa [path, height] using
        div_ne_zero (mul_ne_zero hdet (ne_of_gt (Real.exp_pos z.2))) hn)
  convert hx.prodMk hu using 1
  · funext t
    apply Prod.ext
    · simp [action, N, D_cast]
    · rfl
  · apply Prod.ext
    · simp [diffX, path, D_cast]
    · simp only [diffU, path, zero_smul, add_zero, height, Real.exp_pos,
        Pi.div_apply, ne_eq, Real.exp_ne_zero, not_false_eq_true, mul_one, Prod.snd_add,
        Prod.snd_smul, Prod.snd_zero]
      field_simp
private lemma action_diff (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3)
    (hg : DifferentiableAt ℝ (action g) z) :
    fderiv ℝ (action g) z v = (diffX g z v, diffU g z v) := by
  have hp := path_deriv z v
  have hg' : HasFDerivAt (action g) (fderiv ℝ (action g) z) (path z v 0) := by
    simpa [path] using hg.hasFDerivAt
  have hcomp := hg'.comp_hasDerivAt 0 hp
  have h := (path_action g z v).deriv.symm.trans hcomp.deriv
  simpa [Function.comp_def, path] using h.symm
private lemma rankOne_metric (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z v : H3) :
    (height (action g z))⁻¹ ^ 2 * ‖diffX g z v‖^2 + (diffU g z v)^2 =
      (height z)⁻¹ ^ 2 * ‖v.1‖^2 + v.2^2 := by
  have hy : height z ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hdet : ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ ≠ 0 := norm_ne_zero_iff.mpr g.det_ne_zero
  have hd : actionDenominator g z ≠ 0 := ne_of_gt (actionDenominator_pos g z)
  have hyc : (height z : ℂ) ≠ 0 := by exact_mod_cast hy
  have hdc : (actionDenominator g z : ℂ) ≠ 0 := by exact_mod_cast hd
  have hdetc : (‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ : ℂ) ≠ 0 := by exact_mod_cast hdet
  have h := metric_alg (g 0 0) (g 0 1) (g 1 0) (g 1 1) z.1 v.1 (height z^2) v.2
  rw [D_cast] at h
  have ht : norm2 (g 0 0*g 1 1-g 0 1*g 1 0) =
      (‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ : ℂ)^2 := by
    rw [norm2_cast, Matrix.det_fin_two, Complex.ofReal_pow]
  rw [ht, Complex.ofReal_pow] at h
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv]
  rw [← Complex.ofReal_pow ‖diffX g z v‖, ← Complex.ofReal_pow ‖v.1‖,
    ← norm2_cast, ← norm2_cast]
  rw [action_height]
  change (↑(‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * height z / actionDenominator g z) : ℂ)⁻¹ ^ 2 * _ + _ = _
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv]
  unfold diffX diffU
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
    dD_real, norm2, star_div, star_sub, star_mul, Complex.star_def,
    Complex.conj_ofReal, map_pow]
  simp only [norm2, star_mul, Complex.star_def] at h
  simp only [map_div₀, map_pow, Complex.conj_ofReal]
  field_simp
  simp only [map_sub, map_mul, Complex.conj_ofReal] at h ⊢
  linear_combination h

theorem metric_invariant (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z v : Space d) :
    metric d (productAction d g z) (fderiv ℝ (productAction d g) z v) =
      metric d z v := by
  have ha (i : Fin d) : DifferentiableAt ℝ (action (g i)) (z i) :=
    (action_contDiff (g i)).differentiable (by simp) (z i)
  have hp : fderiv ℝ (productAction d g) z =
      ContinuousLinearMap.pi (fun i =>
        (fderiv ℝ (action (g i)) (z i)).comp (ContinuousLinearMap.proj i)) := by
    unfold productAction
    change fderiv ℝ (fun z : Space d => fun i => (action (g i) ∘ (fun z : Space d => z i)) z) z = _
    rw [fderiv_pi (fun i => (ha i).comp z (differentiableAt_apply i z))]
    congr 1
    funext i
    rw [fderiv_comp z (ha i) (differentiableAt_apply i z)]
    congr 1
    change fderiv ℝ (ContinuousLinearMap.proj i : Space d →L[ℝ] H3) z = _
    exact (ContinuousLinearMap.proj i : Space d →L[ℝ] H3).hasFDerivAt.fderiv
  unfold metric
  rw [hp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, action_diff (g i) (z i) (v i) (ha i)]
  exact rankOne_metric (g i) (z i) (v i)

private abbrev Idx (d : ℕ) := (i : Fin d) × (Fin 2 ⊕ Unit)
private def B (d : ℕ) : Module.Basis (Idx d) ℝ (Space d) :=
  Pi.basis (fun _ => Complex.basisOneI.prod (Module.Basis.singleton Unit ℝ))
private def weights (d : ℕ) (z : Space d) (i : Idx d) : ℝ :=
  match i.2 with
  | Sum.inl _ => (height (z i.1))⁻¹ ^ 2
  | Sum.inr _ => 1
private def Q (d : ℕ) (z : Space d) : QuadraticForm ℝ (Space d) :=
  (QuadraticMap.weightedSumSquares ℝ (weights d z)).comp (B d).equivFun.toLinearMap
private lemma Q_eq (d : ℕ) (z v : Space d) : Q d z v = metric d z v := by
  simp only [Q, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.equivFun_apply, QuadraticMap.weightedSumSquares_apply,
    Fintype.sum_sigma, Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_unique,
    weights, B, Pi.basis_repr, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
    Complex.coe_basisOneI_repr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Module.Basis.singleton_repr, smul_eq_mul, one_mul, metric]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring
private lemma w_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) :
    QuadraticForm.discr' (QuadraticMap.weightedSumSquares ℝ w) = ∏ i, w i := by
  have hm : QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares ℝ w) = Matrix.diagonal w := by
    ext i j
    simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
      QuadraticMap.associated_apply, QuadraticMap.weightedSumSquares_apply,
      Pi.add_apply, smul_eq_mul]
    have hsum : (∑ x, w x * (((Pi.single i 1 : ι → ℝ) x + (Pi.single j 1 : ι → ℝ) x) *
        ((Pi.single i 1 : ι → ℝ) x + (Pi.single j 1 : ι → ℝ) x))) =
        w i + w j + (if i = j then 2 * w i else 0) := by
      simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
      simp [Pi.single_apply, Finset.sum_ite_irrel, mul_ite, ite_mul]
      split_ifs <;> simp_all <;> ring
    rw [hsum]
    simp [Pi.single_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [QuadraticForm.discr', hm, Matrix.det_diagonal]
private lemma Q_discr (d : ℕ) (z : Space d) :
    (Q d z).discr (B d) = volumeDensity d z ^ 2 := by
  have hm : (Q d z).toMatrix (B d) =
      QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares ℝ (weights d z)) := by
    ext i j
    simp [Q, QuadraticForm.toMatrix, QuadraticForm.toMatrix',
      LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂'_apply,
      QuadraticMap.associated_comp]
    congr 2 <;> ext k <;> simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [QuadraticForm.discr, hm, ← QuadraticForm.discr', w_discr]
  simp only [Fintype.prod_sigma, Fintype.prod_sum_type, Fin.prod_univ_two,
    Fintype.prod_unique, weights, mul_one, volumeDensity, ← Finset.prod_mul_distrib]
  simp only [← pow_two, Finset.prod_pow, ← pow_mul]
private lemma density_pos (d : ℕ) (z : Space d) : 0 < volumeDensity d z := by
  unfold volumeDensity
  apply Finset.prod_pos
  intro i _
  exact sq_pos_of_pos (inv_pos.mpr (Real.exp_pos _))
private lemma jacobian_metric (d : ℕ) (f : Space d → Space d) (z : Space d)
    (hm : ∀ v, metric d (f z) (fderiv ℝ f z v) = metric d z v) :
    |(fderiv ℝ f z).det| * volumeDensity d (f z) = volumeDensity d z := by
  have hq : (Q d (f z)).comp (fderiv ℝ f z).toLinearMap = Q d z := by
    ext v
    simpa only [QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe, Q_eq] using hm v
  have hh := QuadraticForm.discr_comp (b := B d) (B d) (Q d (f z)) (fderiv ℝ f z).toLinearMap
  rw [hq, Q_discr, Q_discr, LinearMap.det_toMatrix] at hh
  change volumeDensity d z ^ 2 =
    (fderiv ℝ f z).det * (fderiv ℝ f z).det * volumeDensity d (f z) ^ 2 at hh
  have ha : (|(fderiv ℝ f z).det| * volumeDensity d (f z)) ^ 2 = volumeDensity d z ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith [hh]
  exact (sq_eq_sq₀ (mul_nonneg (abs_nonneg _) (le_of_lt (density_pos d (f z))))
    (le_of_lt (density_pos d z))).mp ha
private lemma action_inv (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Function.LeftInverse (action g⁻¹) (action g) := by
  intro z
  rw [← (action_laws g⁻¹ g z).2, inv_mul_cancel, (action_laws g g z).1]
private lemma product_bij (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Function.Bijective (productAction d g) := by
  have h : Function.LeftInverse (productAction d (fun i => (g i)⁻¹)) (productAction d g) := by
    intro z
    funext i
    exact action_inv (g i) (z i)
  have h' : Function.RightInverse (productAction d (fun i => (g i)⁻¹)) (productAction d g) := by
    intro z
    funext i
    simpa only [productAction, inv_inv] using action_inv ((g i)⁻¹) (z i)
  exact ⟨h.injective, h'.surjective⟩
theorem hyperbolicVolume_invariant (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Measure.map (productAction d g) (hyperbolicVolume d) = hyperbolicVolume d := by
  letI : (volume : Measure H3).IsAddHaarMeasure := by
    change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
    infer_instance
  letI : (volume : Measure (Space d)).IsAddHaarMeasure := by
    change (Measure.pi (fun _ : Fin d => (volume : Measure H3))).IsAddHaarMeasure
    exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hc := (productAction_contDiff d g).continuous
  have hb := product_bij d g
  have hd : ∀ z, DifferentiableAt ℝ (productAction d g) z :=
    fun z => (productAction_contDiff d g).differentiable (by simp) z
  have hj (z : Space d) := jacobian_metric d (productAction d g) z (metric_invariant d g z)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hc.measurable hs]
  unfold hyperbolicVolume
  rw [withDensity_apply _ (hc.measurable hs), withDensity_apply _ hs]
  have hi : productAction d g '' (productAction d g ⁻¹' s) = s :=
    Set.image_preimage_eq s hb.surjective
  conv_rhs => rw [← hi]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (Space d)) (hc.measurable hs)
    (fun z _ => (hd z).hasFDerivAt.hasFDerivWithinAt) hb.injective.injOn]
  apply setLIntegral_congr_fun (hc.measurable hs)
  intro z _
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg _), hj]

theorem volumeDensity_split (d : ℕ) (p : SplitSpace d) :
    volumeDensity (d + 1) (splitCoordinates d p) =
      Real.exp (-2 * (d + 1 : ℝ) * p.2.1) := by
  have hs : ∑ i, shape d p.2.2 i = 0 := by
    simp [shape, Fin.sum_univ_succAbove, Fin.sum_univ_castSucc]
  have he (u : ℝ) : (Real.exp u)⁻¹ ^ 2 = Real.exp (-2 * u) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [volumeDensity, height, splitCoordinates, he]
  rw [← Real.exp_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

private def shearB (d : ℕ) (p : ℝ × (Fin d → ℝ)) : ℝ × (Fin d → ℝ) :=
  (p.1, fun i => p.2 i + p.1)
private lemma shearB_mp (d : ℕ) : MeasurePreserving (shearB d) := by
  change MeasurePreserving (fun p : ℝ × (Fin d → ℝ) => (id p.1, fun i => p.2 i + p.1))
    (volume.prod volume) (volume.prod volume)
  apply MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure ℝ))
    (g := fun (t : ℝ) (b : Fin d → ℝ) => fun i => b i + t)
  ·
    fun_prop
  · filter_upwards [] with t
    exact (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) (fun _ => t)).map_eq
private def shearT (d : ℕ) (p : ℝ × (Fin d → ℝ)) : ℝ × (Fin d → ℝ) :=
  (p.1 - ∑ i, p.2 i, p.2)
private lemma shearT_mp (d : ℕ) : MeasurePreserving (shearT d) := by
  have h := MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure (Fin d → ℝ)))
    (g := fun b t => t + (-∑ i, b i)) (by fun_prop)
    (Filter.Eventually.of_forall (fun b => (measurePreserving_add_right volume (-∑ i, b i)).map_eq))
  change MeasurePreserving (fun p : ℝ × (Fin d → ℝ) => (p.1 - ∑ i, p.2 i, p.2))
    (volume.prod volume) (volume.prod volume)
  simpa only [Function.comp_def, sub_eq_add_neg, Prod.swap_prod_mk,
    Prod.fst_swap, Prod.snd_swap, id_eq] using
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
      (h.comp (Measure.measurePreserving_swap (μ := volume) (ν := volume)))
private lemma scaleT_mp (d : ℕ) : MeasurePreserving
    (fun p : ℝ × (Fin d → ℝ) => ((d+1 : ℝ)*p.1, p.2))
    (ENNReal.ofReal (d+1 : ℝ) • volume) volume := by
  have hn : (d+1 : ℝ) ≠ 0 := by positivity
  have h : MeasurePreserving (fun t : ℝ => (d+1 : ℝ)*t)
      (ENNReal.ofReal (d+1 : ℝ) • volume) volume := by
    constructor
    · fun_prop
    · rw [Measure.map_smul _ (by fun_prop)]
      simpa [abs_of_pos (show 0 < (d+1 : ℝ) by positivity)] using Real.smul_map_volume_mul_left hn
  have hh := h.prod (MeasurePreserving.id (volume : Measure (Fin d → ℝ)))
  change MeasurePreserving (Prod.map (fun t : ℝ => (d+1 : ℝ)*t) id)
    (ENNReal.ofReal (d+1 : ℝ) • volume.prod volume) (volume.prod volume)
  simpa only [Measure.prod_smul_left] using hh

private lemma shape_mp (d : ℕ) : MeasurePreserving
    (fun p : ℝ × (Fin d → ℝ) => fun i => p.1 + shape d p.2 i)
    (ENNReal.ofReal (d+1 : ℝ) • volume) volume := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)).symm
  have hh := he.comp ((shearT_mp d).comp ((scaleT_mp d).comp
    ((shearB_mp d).smul_measure (ENNReal.ofReal (d+1 : ℝ)))))
  convert hh using 1
  funext p i
  simp only [Function.comp_def, shearB, shearT, Prod.map_apply, id_eq]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [shape, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  · simp [shape, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth,
      add_comm]
private lemma split_mp (d : ℕ) : MeasurePreserving (splitCoordinates d)
    (ENNReal.ofReal (d+1 : ℝ) • volume) volume := by
  have hh := (MeasurePreserving.id (volume : Measure (Fin (d+1) → ℂ))).prod (shape_mp d)
  have he := (volume_measurePreserving_arrowProdEquivProdArrow ℂ ℝ (Fin (d+1))).symm
  have hc := he.comp hh
  change MeasurePreserving (splitCoordinates d)
    (ENNReal.ofReal (d+1 : ℝ) • volume.prod volume) volume
  rw [Measure.prod_smul_right] at hc
  convert hc using 1
  funext p i
  rfl

private lemma weighted_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    (ρ : B → ENNReal) (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = ν.withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  rw [← hf.map_eq]
  rw [← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs,
    lintegral_map (hρ.indicator hs) hf.measurable]
  congr 1

theorem hyperbolicVolume_split (d : ℕ) :
    Measure.map (splitCoordinates d)
      (volume.withDensity (fun p : SplitSpace d =>
        ENNReal.ofReal ((d + 1 : ℝ) * Real.exp (-2 * (d + 1 : ℝ) * p.2.1)))) =
      hyperbolicVolume (d + 1) := by
  have hr : Measurable (fun z : Space (d+1) => ENNReal.ofReal (volumeDensity (d+1) z)) := by
    unfold volumeDensity height
    fun_prop
  have h := weighted_map (split_mp d) _ hr
  unfold hyperbolicVolume
  rw [← h]
  congr 1
  rw [withDensity_smul_measure]
  rw [← withDensity_smul _ (hr.comp (split_mp d).measurable)]
  congr 1
  ext p
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_def, volumeDensity_split]
  rw [ENNReal.ofReal_mul (by positivity)]

end
end DedekindZetaZeroFree.KPArch

end
