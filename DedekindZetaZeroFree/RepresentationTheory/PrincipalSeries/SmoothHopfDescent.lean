module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HopfMatrixCoordinates

@[expose] public section

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped Matrix Matrix.Norms.Elementwise

private lemma chart_formula (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2)
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
  conv_lhs => rw [hg, f.property.1]
  have hw : inductionWeight s a d =
      Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 (if north then 0 else 1)‖ ^ 2) (1 + 2*s) := by
    unfold inductionWeight complexAbs
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

private lemma matrix_chart_smooth (s : ℝ) (f : PrincipalSeries s)
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
    · exact f.property.2.2
    · exact f.property.2.1
  apply (hw.mul (hf.contDiffAt.comp m hratio)).congr_of_eventuallyEq
  have hmd : ∀ᶠ g : Matrix (Fin 2) (Fin 2) ℂ in nhds m, g.det ≠ 0 :=
    hdet.continuous.continuousAt (isOpen_ne.mem_nhds hm)
  have hmc : ∀ᶠ g : Matrix (Fin 2) (Fin 2) ℂ in nhds m, g 1 c ≠ 0 :=
    he.continuous.continuousAt (isOpen_ne.mem_nhds hc)
  filter_upwards [hmd, hmc] with g hg hg'
  rw [matrixFunction, dif_pos hg]
  exact chart_formula s f (Matrix.GeneralLinearGroup.mkOfDetNeZero g hg) north hg'

theorem principalSeries_matrix_smooth (s : ℝ) (f : PrincipalSeries s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matrixFunction f)
      {g : Matrix (Fin 2) (Fin 2) ℂ | g.det ≠ 0} := by
  intro m hm
  by_cases h : m 1 0 = 0
  · have h' : m 1 1 ≠ 0 := by
      intro hz
      apply hm
      simp [Matrix.det_fin_two, h, hz]
    exact (matrix_chart_smooth s f m hm false h').contDiffWithinAt
  · exact (matrix_chart_smooth s f m hm true h).contDiffWithinAt

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Matrix Matrix.Norms.Elementwise

def rowMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star b, -star a; a, b]

def hopfChartSU2OfUnitBottomRow (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
  ⟨rowMatrix a b, by
    have h' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rowMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, h, h', mul_comm]
    · simp [rowMatrix, Matrix.det_fin_two, Complex.star_def, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, h, h']⟩

private lemma sphere_equation (x : Sphere) :
    (x : Ambient) 0 ^ 2 + (x : Ambient) 1 ^ 2 + (x : Ambient) 2 ^ 2 = 1 := by
  have hx : ‖(x : Ambient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have := congrArg (fun r : ℝ => r ^ 2) hx
  simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs,
    sq_abs, one_pow] using this

noncomputable def southA (x : Ambient) : ℂ :=
  ⟨x 0 / (2 * Real.sqrt ((1 - x 2) / 2)), x 1 / (2 * Real.sqrt ((1 - x 2) / 2))⟩
noncomputable def southB (x : Ambient) : ℂ := Real.sqrt ((1 - x 2) / 2)
noncomputable def northA (x : Ambient) : ℂ := Real.sqrt ((1 + x 2) / 2)
noncomputable def northB (x : Ambient) : ℂ :=
  ⟨x 0 / (2 * Real.sqrt ((1 + x 2) / 2)), -x 1 / (2 * Real.sqrt ((1 + x 2) / 2))⟩

private lemma south_lift (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (x : Sphere) (hx : (x : Ambient) 2 < 1) :
    ∃ k : ComplexSU2, H k = x ∧ (k : Matrix (Fin 2) (Fin 2) ℂ) =
      rowMatrix (southA x) (southB x) := by
  let r : ℝ := Real.sqrt ((1 - (x : Ambient) 2) / 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = (1 - (x : Ambient) 2) / 2 := Real.sq_sqrt (by linarith)
  have hs := sphere_equation x
  have ha : ‖southA x‖ ^ 2 = (1 + (x : Ambient) 2) / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, ← sq]
    change ((x : Ambient) 0 / (2*r)) ^ 2 + ((x : Ambient) 1 / (2*r)) ^ 2 = _
    field_simp [ne_of_gt hr]
    nlinarith [hr2]
  have hb : ‖southB x‖ ^ 2 = (1 - (x : Ambient) 2) / 2 := by
    change ‖(r : ℂ)‖ ^ 2 = _
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hr2
  refine ⟨hopfChartSU2OfUnitBottomRow (southA x) (southB x) (by rw [ha, hb]; ring), ?_, rfl⟩
  apply Subtype.ext
  rw [hH]
  apply PiLp.ext
  intro i
  fin_cases i
  · change 2 * ((southA x) * star (southB x)).re = (x : Ambient) 0
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, southA, southB, Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    change 2 * ((x : Ambient) 0 / (2*r) * r) = _
    field_simp [ne_of_gt hr]
  · change 2 * ((southA x) * star (southB x)).im = (x : Ambient) 1
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, southA, southB, Complex.star_def, Complex.conj_ofReal, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    change 2 * ((x : Ambient) 1 / (2*r) * r) = _
    field_simp [ne_of_gt hr]
  · change ‖southA x‖ ^ 2 - ‖southB x‖ ^ 2 = (x : Ambient) 2
    rw [ha, hb]; ring

private lemma north_lift (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (x : Sphere) (hx : -1 < (x : Ambient) 2) :
    ∃ k : ComplexSU2, H k = x ∧ (k : Matrix (Fin 2) (Fin 2) ℂ) =
      rowMatrix (northA x) (northB x) := by
  let r : ℝ := Real.sqrt ((1 + (x : Ambient) 2) / 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = (1 + (x : Ambient) 2) / 2 := Real.sq_sqrt (by linarith)
  have hs := sphere_equation x
  have ha : ‖northA x‖ ^ 2 = (1 + (x : Ambient) 2) / 2 := by
    change ‖(r : ℂ)‖ ^ 2 = _
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hr2
  have hb : ‖northB x‖ ^ 2 = (1 - (x : Ambient) 2) / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, ← sq]
    change ((x : Ambient) 0 / (2*r)) ^ 2 + (-(x : Ambient) 1 / (2*r)) ^ 2 = _
    field_simp [ne_of_gt hr]
    nlinarith [hr2]
  refine ⟨hopfChartSU2OfUnitBottomRow (northA x) (northB x) (by rw [ha, hb]; ring), ?_, rfl⟩
  apply Subtype.ext
  rw [hH]
  apply PiLp.ext
  intro i
  fin_cases i
  · change 2 * ((northA x) * star (northB x)).re = (x : Ambient) 0
    simp only [northA, northB, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change 2 * (r * ((x : Ambient) 0 / (2*r))) = _
    field_simp [ne_of_gt hr]
  · change 2 * ((northA x) * star (northB x)).im = (x : Ambient) 1
    simp only [northA, northB, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, neg_div, neg_neg]
    change 2 * (r * ((x : Ambient) 1 / (2*r))) = _
    field_simp [ne_of_gt hr]
  · change ‖northA x‖ ^ 2 - ‖northB x‖ ^ 2 = (x : Ambient) 2
    rw [ha, hb]; ring

private lemma rowMatrix_smooth {a b : Ambient → ℂ} {x : Ambient}
    (ha : ContDiffAt ℝ (⊤ : ℕ∞) a x) (hb : ContDiffAt ℝ (⊤ : ℕ∞) b x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => rowMatrix (a y) (b y)) x := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (star : ℂ → ℂ) := Complex.conjCLE.contDiff
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hc.contDiffAt.comp x hb
  · exact (hc.contDiffAt.comp x ha).neg
  · exact ha
  · exact hb

private lemma south_smooth (x : Ambient) (hx : x 2 < 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => rowMatrix (southA y) (southB y)) x := by
  have hp : 0 < (1 - x 2) / 2 := by linarith
  have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => Real.sqrt ((1 - y 2) / 2)) x := by
    have ht : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => (1 - y 2) / 2) x := by fun_prop
    exact ht.sqrt (ne_of_gt hp)
  have hn : Real.sqrt ((1 - x 2) / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have h0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => y 0 / (2 * Real.sqrt ((1 - y 2) / 2))) x := by
    apply ContDiffAt.div
    · fun_prop
    · exact contDiffAt_const.mul hr
    · exact mul_ne_zero (by norm_num) hn
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => y 1 / (2 * Real.sqrt ((1 - y 2) / 2))) x := by
    apply ContDiffAt.div
    · fun_prop
    · exact contDiffAt_const.mul hr
    · exact mul_ne_zero (by norm_num) hn
  apply rowMatrix_smooth
  · convert (Complex.ofRealCLM.contDiff.contDiffAt.comp x h0).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x h1).mul (contDiffAt_const (c := Complex.I))) using 1
    funext y
    apply Complex.ext <;> simp only [Function.comp_apply, Complex.ofRealCLM_apply, southA, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hr

private lemma north_smooth (x : Ambient) (hx : -1 < x 2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => rowMatrix (northA y) (northB y)) x := by
  have hp : 0 < (1 + x 2) / 2 := by linarith
  have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => Real.sqrt ((1 + y 2) / 2)) x := by
    have ht : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => (1 + y 2) / 2) x := by fun_prop
    exact ht.sqrt (ne_of_gt hp)
  have hn : Real.sqrt ((1 + x 2) / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have h0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => y 0 / (2 * Real.sqrt ((1 + y 2) / 2))) x := by
    apply ContDiffAt.div
    · fun_prop
    · exact contDiffAt_const.mul hr
    · exact mul_ne_zero (by norm_num) hn
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Ambient => -y 1 / (2 * Real.sqrt ((1 + y 2) / 2))) x := by
    apply ContDiffAt.div
    · fun_prop
    · exact contDiffAt_const.mul hr
    · exact mul_ne_zero (by norm_num) hn
  apply rowMatrix_smooth
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
  · convert (Complex.ofRealCLM.contDiff.contDiffAt.comp x h0).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x h1).mul (contDiffAt_const (c := Complex.I))) using 1
    funext y
    apply Complex.ext <;> simp only [Function.comp_apply, Complex.ofRealCLM_apply, northB, ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]

private lemma local_lifts (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (p : Sphere) :
    ∃ (M : Ambient → Matrix (Fin 2) (Fin 2) ℂ) (V : Set Ambient),
      IsOpen V ∧ (p : Ambient) ∈ V ∧ ContDiffAt ℝ (⊤ : ℕ∞) M p ∧
      ∀ q : Sphere, (q : Ambient) ∈ V →
        ∃ k : ComplexSU2, H k = q ∧ (k : Matrix (Fin 2) (Fin 2) ℂ) = M q := by
  by_cases hp : (p : Ambient) 2 < 1
  · refine ⟨fun y => rowMatrix (southA y) (southB y), {y | y 2 < 1}, ?_, hp,
      south_smooth p hp, fun q hq => south_lift H hH q hq⟩
    exact isOpen_lt (by fun_prop) continuous_const
  · have hp' : -1 < (p : Ambient) 2 := by linarith
    refine ⟨fun y => rowMatrix (northA y) (northB y), {y | -1 < y 2}, ?_, hp',
      north_smooth p hp', fun q hq => north_lift H hH q hq⟩
    exact isOpen_lt continuous_const (by fun_prop)

private lemma matrixFunction_compact (f : ComplexGL2 → ℂ) (k : ComplexSU2) :
    matrixFunction f (k : Matrix (Fin 2) (Fin 2) ℂ) = f (complexSU2Embedding k) := by
  have hd : (k : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp k.property).2]
    exact one_ne_zero
  rw [matrixFunction, dif_pos hd]
  congr 1

theorem smooth_hopf_descent (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (s : ℝ) (f : PrincipalSeries s)
    (hf : ∀ k l : ComplexSU2, H k = H l →
      compactRestriction s f k = compactRestriction s f l) :
    ∃ F : Sphere → ℂ, IsSphereSmooth F ∧
      ∀ k : ComplexSU2, compactRestriction s f k = F (H k) := by
  classical
  have hsurj : Function.Surjective H := by
    intro p
    obtain ⟨M, V, hV, hp, hM, hl⟩ := local_lifts H hH p
    obtain ⟨k, hk, _⟩ := hl p hp
    exact ⟨k, hk⟩
  let F : Sphere → ℂ := fun p => compactRestriction s f (Classical.choose (hsurj p))
  have hF : ∀ k : ComplexSU2, compactRestriction s f k = F (H k) := by
    intro k
    exact hf k _ (Classical.choose_spec (hsurj (H k))).symm
  refine ⟨F, ?_, hF⟩
  have hmat := principalSeries_matrix_smooth s f
  have hopen : IsOpen {g : Matrix (Fin 2) (Fin 2) ℂ | g.det ≠ 0} := by
    exact isOpen_ne.preimage (show Continuous (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) by
      simp only [Matrix.det_fin_two]; fun_prop)
  intro x hx
  let N : Ambient → Ambient := fun y => ‖y‖⁻¹ • y
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) N x :=
    ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
  have hnorm : ∀ (y : Ambient), y ≠ 0 → ‖N y‖ = 1 := by
    intro y hy
    simp only [N, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  let p : Sphere := ⟨N x, by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm x hx⟩
  obtain ⟨M, V, hV, hp, hM, hl⟩ := local_lifts H hH p
  obtain ⟨k, hk, hMk⟩ := hl p hp
  have hd : (M (N x)).det ≠ 0 := by
    change (M (p : Ambient)).det ≠ 0
    rw [← hMk, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2]
    exact one_ne_zero
  have hmAt : ContDiffAt ℝ (⊤ : ℕ∞) (matrixFunction f) (M (N x)) :=
    hmat.contDiffAt (hopen.mem_nhds hd)
  have hMN : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => M (N y)) x := by
    exact hM.comp x hN
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => matrixFunction f (M (N y))) x :=
    by simpa only [Function.comp_def] using hmAt.comp x hMN
  apply (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  have heV : ∀ᶠ y in nhds x, N y ∈ V := hN.continuousAt (hV.mem_nhds hp)
  have hne : ∀ᶠ y in nhds x, y ≠ 0 := isOpen_ne.mem_nhds hx
  filter_upwards [heV, hne] with y hyV hy
  let q : Sphere := ⟨N y, by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm y hy⟩
  obtain ⟨l, hlq, hMl⟩ := hl q hyV
  change radialExtension F y = matrixFunction f (M (N y))
  rw [radialExtension, dif_pos hy]
  change F q = matrixFunction f (M (q : Ambient))
  rw [← hMl, matrixFunction_compact]
  exact (hlq ▸ hF l).symm

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end
