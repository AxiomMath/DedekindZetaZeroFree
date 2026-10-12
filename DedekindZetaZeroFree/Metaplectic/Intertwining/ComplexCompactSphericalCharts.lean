module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SmoothHopfDescent
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HopfChartRotationBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.InverseHopfJetBounds
public import DedekindZetaZeroFree.Metaplectic.Intertwining.StereographicHaarIntegral
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SphericalSectionCovariance

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped NNReal BigOperators Matrix Matrix.Norms.Elementwise

noncomputable def hopfVector (k : ComplexSU2) : Ambient :=
  WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re)

theorem hopfVector_norm (k : ComplexSU2) : ‖hopfVector k‖ = 1 := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hu : m * star m = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hr := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hr
  simp only [Complex.star_def, Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.one_re] at hr
  have hprod : (m 1 0 * star (m 1 1)).re ^ 2 +
      (m 1 0 * star (m 1 1)).im ^ 2 = ‖m 1 0‖ ^ 2 * ‖m 1 1‖ ^ 2 := by
    calc
      _ = Complex.normSq (m 1 0 * star (m 1 1)) := by
        simp only [Complex.normSq_apply, sq]
      _ = _ := by rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_star]
  have hs : ‖hopfVector k‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hopfVector, compactSphereCoordinate, Fin.sum_univ_three,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Complex.ofReal_re, Real.norm_eq_abs, sq_abs,
      ← Complex.ofReal_pow, Complex.sub_re]
    change (2 * (m 1 0 * star (m 1 1)).re) ^ 2 +
      (2 * (m 1 0 * star (m 1 1)).im) ^ 2 +
      (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2) ^ 2 = 1
    nlinarith [hprod, sq_nonneg (‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2 - 1)]
  nlinarith [norm_nonneg (hopfVector k)]

noncomputable def hopf (k : ComplexSU2) : Sphere :=
  ⟨hopfVector k, by simpa only [Metric.mem_sphere, dist_zero_right] using hopfVector_norm k⟩

private theorem hopf_coordinates : CompactCharts.HasHopfCoordinates hopf := by
  intro k
  rfl

def rowSU2 (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
  ⟨!![star b, -star a; a, b], by
    have h' : ‖b‖ ^ 2 + ‖a‖ ^ 2 = 1 := by linarith
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
          ← Complex.ofReal_add, h, h', mul_comm]
    · simp [Matrix.det_fin_two, Complex.star_def, Complex.mul_conj',
        mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_add, h, h']⟩

theorem hopf_surjective : Function.Surjective hopf := by
  intro x
  have hs : (x : Ambient) 0 ^ 2 + (x : Ambient) 1 ^ 2 + (x : Ambient) 2 ^ 2 = 1 := by
    have hx : ‖(x : Ambient)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have := congrArg (fun r : ℝ => r ^ 2) hx
    simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs,
      sq_abs, one_pow] using this
  have hz : (x : Ambient) 2 ≤ 1 := by
    nlinarith [sq_nonneg ((x : Ambient) 0), sq_nonneg ((x : Ambient) 1)]
  by_cases he : (x : Ambient) 2 = 1
  · have h0 : (x : Ambient) 0 = 0 := by nlinarith [sq_nonneg ((x : Ambient) 1)]
    have h1 : (x : Ambient) 1 = 0 := by nlinarith [sq_nonneg ((x : Ambient) 0)]
    refine ⟨rowSU2 1 0 (by simp), ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, rowSU2, h0, h1, he]
  · let r : ℝ := Real.sqrt ((1 - (x : Ambient) 2) / 2)
    have hr : 0 < r := Real.sqrt_pos.2 (by have hz' : (x : Ambient) 2 < 1 := lt_of_le_of_ne hz he; linarith)
    have hr2 : r ^ 2 = (1 - (x : Ambient) 2) / 2 :=
      Real.sq_sqrt (by linarith)
    let a : ℂ := ⟨(x : Ambient) 0 / (2*r), (x : Ambient) 1 / (2*r)⟩
    let b : ℂ := r
    have ha : ‖a‖ ^ 2 = (1 + (x : Ambient) 2) / 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [a]
      field_simp
      nlinarith [hr2]
    have hb : ‖b‖ ^ 2 = (1 - (x : Ambient) 2) / 2 := by
      simpa [b, Complex.norm_real, sq_abs] using hr2
    refine ⟨rowSU2 a b (by rw [ha, hb]; ring), ?_⟩
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hopf, hopfVector, compactSphereCoordinate, rowSU2,
      ha, hb, a, b, Complex.mul_re, Complex.mul_im, ne_of_gt hr,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, hr2]
    all_goals field_simp
    all_goals ring

theorem principalSeries_open_bruhat (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2)
    (ha : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0) :
    f g = (Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) (1 + 2*s) : ℂ) *
      openCoordinate f ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  let d : ℂˣ := Units.mk0 ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ha
  let a : ℂˣ := -(Matrix.GeneralLinearGroup.det g) / d
  have hg : g = upperTriangular a d ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) *
      (weyl * upperUnipotent ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [CompactCharts.upperTriangular_coe_matrix, weyl, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, a, d, Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.det_fin_two]
    all_goals field_simp
    all_goals ring
  conv_lhs => rw [hg, f.property.1]
  congr 1
  unfold inductionWeight complexAbs
  have he : ‖(a : ℂ) / (d : ℂ)‖ = ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 := by
    simp [a, d, norm_div, norm_neg, div_div, sq]
  rw [he]
  apply congrArg Complex.ofReal
  calc
    _ = Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) ((2 : ℕ) * (1/2+s)) :=
      (Real.rpow_natCast_mul (show 0 ≤ ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 by positivity) 2 (1/2+s)).symm
    _ = _ := by congr 1; norm_num; ring

theorem su2_bottomRow_norm_sq (k : ComplexSU2) :
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hr := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.star_def,
    Complex.mul_conj', ← Complex.ofReal_pow] using hr
theorem hopf_fiber_row_data (k l : ComplexSU2) (h : hopf k = hopf l) :
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 ∧
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 ∧
    (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
      (l : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((l : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  have hv := congrArg Subtype.val h
  have h0 := congrArg (fun x : Ambient => x 0) hv
  have h1 := congrArg (fun x : Ambient => x 1) hv
  have h2 := congrArg (fun x : Ambient => x 2) hv
  simp only [hopf, hopfVector, compactSphereCoordinate, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Complex.ofReal_re, Complex.sub_re, ← Complex.ofReal_pow] at h0 h1 h2
  change (‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 - ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 : ℝ) =
    ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 - ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 at h2
  have hk := su2_bottomRow_norm_sq k
  have hl := su2_bottomRow_norm_sq l
  refine ⟨by linarith, by linarith, ?_⟩
  apply Complex.ext <;> linarith
private lemma ratio_of_product (a b : ℂ) (ha : a ≠ 0) :
    b / a = star (a * star b) / (‖a‖ ^ 2 : ℂ) := by
  have hn : (‖a‖ ^ 2 : ℂ) = a * star a := by
    simp [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [hn, star_mul, star_star]
  field_simp [ha, star_ne_zero.mpr ha]
theorem principalSeries_infinity_bruhat (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2)
    (ha : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    f g = (Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) (1 + 2*s) : ℂ) *
      infinityCoordinate f ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  let d : ℂˣ := Units.mk0 ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ha
  let a : ℂˣ := Matrix.GeneralLinearGroup.det g / d
  have hg : g = upperTriangular a d ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) *
      (lowerUnipotent ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [CompactCharts.upperTriangular_coe_matrix, lowerUnipotent, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, a, d, Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.det_fin_two]
    all_goals field_simp
    all_goals ring
  conv_lhs => rw [hg, f.property.1]
  congr 1
  unfold inductionWeight complexAbs
  have he : ‖(a : ℂ) / (d : ℂ)‖ = ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
    simp [a, d, norm_div, norm_neg, div_div, sq]
  rw [he]
  apply congrArg Complex.ofReal
  calc
    _ = Real.rpow (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) ((2 : ℕ) * (1/2+s)) :=
      (Real.rpow_natCast_mul (show 0 ≤ ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 by positivity) 2 (1/2+s)).symm
    _ = _ := by congr 1; norm_num; ring

theorem compactRestriction_hopf_fiber (s : ℝ) (f : PrincipalSeries s)
    (k l : ComplexSU2) (h : hopf k = hopf l) :
    compactRestriction s f k = compactRestriction s f l := by
  obtain ⟨h0, h1, hp⟩ := hopf_fiber_row_data k l h
  have hdetk : (Matrix.GeneralLinearGroup.det (complexSU2Embedding k) : ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have hdetl : (Matrix.GeneralLinearGroup.det (complexSU2Embedding l) : ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp l.property).2
  change f (complexSU2Embedding k) = f (complexSU2Embedding l)
  by_cases ha : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · have hl : (l : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      have hn : ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ = 0 := by
        rw [ha, norm_zero, zero_pow (by decide)] at h0
        nlinarith [norm_nonneg ((l : Matrix (Fin 2) (Fin 2) ℂ) 1 0)]
      exact norm_eq_zero.mp hn
    have hbk : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      have := su2_bottomRow_norm_sq k
      intro hb
      simp [ha, hb] at this
    have hbl : (l : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      have := su2_bottomRow_norm_sq l
      intro hb
      simp [hl, hb] at this
    rw [principalSeries_infinity_bruhat s f _ hbk, principalSeries_infinity_bruhat s f _ hbl]
    simp only [hdetk, hdetl]
    change (Real.rpow (‖(1:ℂ)‖ / ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) (1+2*s):ℂ) *
      infinityCoordinate f ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
      (Real.rpow (‖(1:ℂ)‖ / ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) (1+2*s):ℂ) *
      infinityCoordinate f ((l : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (l : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
    simp only [ha, hl, zero_div]
    rw [h1]
  · have hl : (l : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := by
      intro hl
      rw [hl, norm_zero, zero_pow (by decide)] at h0
      have hn : ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ = 0 := by
        nlinarith [norm_nonneg ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)]
      exact ha (norm_eq_zero.mp hn)
    rw [principalSeries_open_bruhat s f _ ha, principalSeries_open_bruhat s f _ hl]
    simp only [hdetk, hdetl]
    change (Real.rpow (‖(1:ℂ)‖ / ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) (1+2*s):ℂ) *
      openCoordinate f ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0) =
      (Real.rpow (‖(1:ℂ)‖ / ‖(l : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) (1+2*s):ℂ) *
      openCoordinate f ((l : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (l : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    rw [ratio_of_product _ _ ha, ratio_of_product _ _ hl, hp, h0]
    simp only [← Complex.ofReal_pow, h0]

 theorem hopf_open_ratio (k : ComplexSU2)
    (ha : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0) :
    (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      ((hopfVector k 0 : ℂ) - Complex.I * (hopfVector k 1 : ℂ)) / (1 + (hopfVector k 2 : ℂ)) := by
  let a := (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let b := (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  have hn : 1 + (hopfVector k 2 : ℂ) = 2 * (‖a‖ ^ 2 : ℂ) := by
    have hs := su2_bottomRow_norm_sq k
    change 1 + ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) = _
    have hs' : 1 + (‖a‖ ^ 2 - ‖b‖ ^ 2) = 2 * ‖a‖ ^ 2 := by
      change ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 at hs
      linarith
    exact_mod_cast hs'
  have hp : (hopfVector k 0 : ℂ) - Complex.I * (hopfVector k 1 : ℂ) =
      2 * star (a * star b) := by
    change ((2 * (a * star b).re : ℝ) : ℂ) - Complex.I * ((2 * (a * star b).im : ℝ) : ℂ) = _
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring
  rw [hn, hp]
  have hn' : (‖a‖ ^ 2 : ℂ) = a * star a := by
    simp [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [hn', star_mul, star_star]
  change b / a = _
  field_simp [show a ≠ 0 from ha, star_ne_zero.mpr (show a ≠ 0 from ha)]

theorem hopf_infinity_ratio (k : ComplexSU2)
    (hb : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      ((hopfVector k 0 : ℂ) + Complex.I * (hopfVector k 1 : ℂ)) / (1 - (hopfVector k 2 : ℂ)) := by
  let a := (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let b := (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  have hn : 1 - (hopfVector k 2 : ℂ) = 2 * (‖b‖ ^ 2 : ℂ) := by
    have hs := su2_bottomRow_norm_sq k
    change 1 - ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) = _
    have hs' : 1 - (‖a‖ ^ 2 - ‖b‖ ^ 2) = 2 * ‖b‖ ^ 2 := by
      change ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 at hs
      linarith
    exact_mod_cast hs'
  have hp : (hopfVector k 0 : ℂ) + Complex.I * (hopfVector k 1 : ℂ) =
      2 * (a * star b) := by
    change ((2 * (a * star b).re : ℝ) : ℂ) + Complex.I * ((2 * (a * star b).im : ℝ) : ℂ) = _
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring
  rw [hn, hp]
  have hn' : (‖b‖ ^ 2 : ℂ) = b * star b := by
    simp [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [hn']
  change a / b = _
  field_simp [show b ≠ 0 from hb, star_ne_zero.mpr (show b ≠ 0 from hb)]

theorem hopf_bottomRow_coordinates (k : ComplexSU2) :
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = (1 + hopfVector k 2) / 2 ∧
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = (1 - hopfVector k 2) / 2 := by
  have hs := su2_bottomRow_norm_sq k
  change ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 =
    (1 + (‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 - ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) / 2 ∧
    ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
    (1 - (‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 - ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) / 2
  constructor <;> linarith
 theorem compactRestriction_open_hopf (s : ℝ) (f : PrincipalSeries s) (k : ComplexSU2)
    (ha : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0) :
    compactRestriction s f k =
      (Real.rpow (2 / (1 + hopfVector k 2)) (1+2*s) : ℂ) *
      openCoordinate f (((hopfVector k 0 : ℂ) - Complex.I * (hopfVector k 1 : ℂ)) / (1 + (hopfVector k 2 : ℂ))) := by
  have hd : (Matrix.GeneralLinearGroup.det (complexSU2Embedding k) : ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  change f (complexSU2Embedding k) = _
  rw [principalSeries_open_bruhat s f _ ha, hd]
  change (Real.rpow (‖(1:ℂ)‖ / ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2) (1+2*s):ℂ) *
      openCoordinate f ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = _
  rw [hopf_open_ratio k ha, (hopf_bottomRow_coordinates k).1, norm_one]
  congr 3
  simp [div_div]
 theorem compactRestriction_infinity_hopf (s : ℝ) (f : PrincipalSeries s) (k : ComplexSU2)
    (hb : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    compactRestriction s f k =
      (Real.rpow (2 / (1 - hopfVector k 2)) (1+2*s) : ℂ) *
      infinityCoordinate f (((hopfVector k 0 : ℂ) + Complex.I * (hopfVector k 1 : ℂ)) / (1 - (hopfVector k 2 : ℂ))) := by
  have hd : (Matrix.GeneralLinearGroup.det (complexSU2Embedding k) : ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  change f (complexSU2Embedding k) = _
  rw [principalSeries_infinity_bruhat s f _ hb, hd]
  change (Real.rpow (‖(1:ℂ)‖ / ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) (1+2*s):ℂ) *
      infinityCoordinate f ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 / (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = _
  rw [hopf_infinity_ratio k hb, (hopf_bottomRow_coordinates k).2, norm_one]
  congr 3
  simp [div_div]

theorem existsUnique_sphereProfile (s : ℝ) (f : PrincipalSeries s) :
    ∃! F : Sphere → ℂ, IsSphereSmooth F ∧
      ∀ k : ComplexSU2, compactRestriction s f k = F (hopf k) := by
  obtain ⟨F, hF, hf⟩ := CompactCharts.smooth_hopf_descent hopf hopf_coordinates s f
    (compactRestriction_hopf_fiber s f)
  refine ⟨F, ⟨hF, hf⟩, ?_⟩
  intro G hG
  funext x
  obtain ⟨k, rfl⟩ := hopf_surjective x
  exact (hG.2 k).symm.trans (hf k)

noncomputable def sphereProfile (s : ℝ) (f : PrincipalSeries s) : Sphere → ℂ :=
  Classical.choose (existsUnique_sphereProfile s f).exists

theorem sphereProfile_spec (s : ℝ) (f : PrincipalSeries s) :
    IsSphereSmooth (sphereProfile s f) ∧
      ∀ k : ComplexSU2, compactRestriction s f k = sphereProfile s f (hopf k) :=
  Classical.choose_spec (existsUnique_sphereProfile s f).exists

noncomputable def bottomHopf (m : Matrix (Fin 2) (Fin 2) ℂ) : Ambient :=
  WithLp.toLp 2 ![2 * (m 1 0 * star (m 1 1)).re,
    2 * (m 1 0 * star (m 1 1)).im, Complex.normSq (m 1 0) - Complex.normSq (m 1 1)]
private lemma bottomHopf_norm (m : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖bottomHopf m‖ = Complex.normSq (m 1 0) + Complex.normSq (m 1 1) := by
  have hprod : (m 1 0 * star (m 1 1)).re ^ 2 +
      (m 1 0 * star (m 1 1)).im ^ 2 = Complex.normSq (m 1 0) * Complex.normSq (m 1 1) := by
    calc
      _ = Complex.normSq (m 1 0 * star (m 1 1)) := by simp only [Complex.normSq_apply, sq]
      _ = _ := by rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_star, Complex.normSq_eq_norm_sq]
  have hs : ‖bottomHopf m‖ ^ 2 = (Complex.normSq (m 1 0) + Complex.normSq (m 1 1)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [bottomHopf, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Real.norm_eq_abs, sq_abs]
    change (2 * (m 1 0 * star (m 1 1)).re) ^ 2 +
      (2 * (m 1 0 * star (m 1 1)).im) ^ 2 +
      (Complex.normSq (m 1 0) - Complex.normSq (m 1 1)) ^ 2 = _
    nlinarith
  nlinarith [norm_nonneg (bottomHopf m), Complex.normSq_nonneg (m 1 0),
    Complex.normSq_nonneg (m 1 1)]
private lemma bottomHopf_ne_zero (g : ComplexGL2) :
    bottomHopf (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  intro he
  have h := bottomHopf_norm (g : Matrix (Fin 2) (Fin 2) ℂ)
  rw [he, norm_zero] at h
  have h0 : Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 0 := by
    nlinarith [Complex.normSq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0),
      Complex.normSq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)]
  have h1 : Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = 0 := by
    nlinarith [Complex.normSq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0),
      Complex.normSq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)]
  have hd := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Complex.normSq_eq_zero] at h0 h1
  apply hd
  simp [Matrix.det_fin_two, h0, h1]
private lemma bottomHopf_smooth : ContDiff ℝ (⊤ : ℕ∞) bottomHopf := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  have hre : ContDiff ℝ (⊤ : ℕ∞) Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ (⊤ : ℕ∞) Complex.im := Complex.imCLM.contDiff
  have hconj : ContDiff ℝ (⊤ : ℕ∞) (star : ℂ → ℂ) := Complex.conjCLE.contDiff
  fin_cases i
  · change ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => 2 * (m 1 0 * star (m 1 1)).re)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => 2 * (m 1 0 * star (m 1 1)).im)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => Complex.normSq (m 1 0) - Complex.normSq (m 1 1))
    simp only [Complex.normSq_apply]
    fun_prop
lemma radialExtension_pos_smul (F : Sphere → ℂ) (x : Ambient) (t : ℝ) (ht : 0 < t) :
    radialExtension F (t • x) = radialExtension F x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  · have htx : t • x ≠ 0 := smul_ne_zero (ne_of_gt ht) hx
    simp only [radialExtension, dif_pos hx, dif_pos htx]
    congr 1
    apply Subtype.ext
    change ‖t • x‖⁻¹ • (t • x) = ‖x‖⁻¹ • x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv, smul_smul]
    rw [mul_assoc, mul_comm (‖x‖⁻¹), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), one_mul]
lemma bottomHopf_upper (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    bottomHopf (↑(upperTriangular a d b * g)) =
      (‖(d : ℂ)‖ ^ 2) • bottomHopf (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [bottomHopf, CompactCharts.upperTriangular_coe_matrix, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply,
      Fin.sum_univ_two, PiLp.smul_apply, Complex.normSq_mul, Complex.normSq_eq_norm_sq,
      star_mul, Complex.star_def, mul_assoc, mul_left_comm, mul_comm,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
  all_goals simp only [mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at *
  all_goals ring
lemma spherePullback_chart_smooth (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (q : ℂ → ComplexGL2)
    (hq : ContDiff ℝ (⊤ : ℕ∞) (fun z => (q z : Matrix (Fin 2) (Fin 2) ℂ))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => radialExtension F (bottomHopf ↑(q z))) := by
  rw [← contDiffOn_univ]
  exact hF.comp (bottomHopf_smooth.comp hq).contDiffOn
    (fun z _ => bottomHopf_ne_zero (q z))

noncomputable def normalizedSection (s : ℝ) : PrincipalSeries s :=
  ⟨sphericalFunction s, CompactCharts.sphericalFunction_covariance s,
    (CompactCharts.sphericalFunction_charts s).1,
    (CompactCharts.sphericalFunction_charts s).2⟩

noncomputable def rawSphereSection (s : ℝ) (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    PrincipalSeries s :=
  ⟨fun g => normalizedSection s g * radialExtension F (bottomHopf ↑g), by
    change HasCovariance s _ ∧ ContDiff ℝ (⊤ : ℕ∞) _ ∧ ContDiff ℝ (⊤ : ℕ∞) _
    refine ⟨?_, ?_, ?_⟩
    · intro a d b g
      have hs : HasCovariance s (normalizedSection s) := (normalizedSection s).property.1
      dsimp only
      rw [hs, bottomHopf_upper, radialExtension_pos_smul F _ _ (by
        exact sq_pos_of_pos (norm_pos_iff.mpr d.ne_zero))]
      ring
    · have hs : ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (normalizedSection s)) :=
        (normalizedSection s).property.2.1
      apply hs.mul
      apply spherePullback_chart_smooth F hF
      simp only [weyl, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul]
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
    · have hs : ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (normalizedSection s)) :=
        (normalizedSection s).property.2.2
      apply hs.mul
      apply spherePullback_chart_smooth F hF
      simp only [lowerUnipotent]
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop⟩
private lemma bottomHopf_su2 (k : ComplexSU2) : bottomHopf (k : Matrix (Fin 2) (Fin 2) ℂ) = hopfVector k := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [bottomHopf, hopfVector, compactSphereCoordinate,
    ← Complex.ofReal_pow, Complex.normSq_eq_norm_sq]
private lemma normalizedSection_su2 (s : ℝ) (k : ComplexSU2) :
    normalizedSection s (complexSU2Embedding k) = 1 := by
  have hdet : (Matrix.GeneralLinearGroup.det (complexSU2Embedding k) : ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have hn : bottomRowNormSq (complexSU2Embedding k) = 1 := by
    rw [bottomRowNormSq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact (bottomHopf_norm (k : Matrix (Fin 2) (Fin 2) ℂ)).symm.trans
      (by rw [bottomHopf_su2, hopfVector_norm])
  change (Real.rpow _ _ : ℂ) = 1
  rw [hdet, hn]
  simp

private lemma rawSphereSection_compact (s : ℝ) (F : Sphere → ℂ) (hF : IsSphereSmooth F) (k : ComplexSU2) :
    compactRestriction s (rawSphereSection s F hF) k = F (hopf k) := by
  change normalizedSection s (complexSU2Embedding k) *
    radialExtension F (bottomHopf (k : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [normalizedSection_su2, one_mul, bottomHopf_su2]
  have hn : hopfVector k ≠ 0 := by intro he; have := hopfVector_norm k; simpa [he] using this
  simp only [radialExtension, dif_pos hn]
  congr 1
  apply Subtype.ext
  change ‖hopfVector k‖⁻¹ • hopfVector k = hopfVector k
  rw [hopfVector_norm, inv_one, one_smul]

theorem sphereProfile_surjective (s : ℝ) (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    ∃ f : PrincipalSeries s, sphereProfile s f = F := by
  refine ⟨rawSphereSection s F hF, ?_⟩
  funext x
  obtain ⟨k, rfl⟩ := hopf_surjective x
  rw [← (sphereProfile_spec s (rawSphereSection s F hF)).2 k, rawSphereSection_compact]

open CompactCharts.RotationToChartsSteps

private lemma inverse_profile_pointwise (s : ℝ) (f : PrincipalSeries s)
    (north : Bool) (y : Ambient) (hy : y ≠ 0)
    (hd : 0 < ‖y‖ + hemisphereSign north * y 2) :
    radialExtension (sphereProfile s f) y = inverseHopfWeight s north y *
      (if north then openCoordinate f else infinityCoordinate f) (inverseHopfCoordinate north y) := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let p : Sphere := ⟨‖y‖⁻¹ • y, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ (ne_of_gt hn)]⟩
  obtain ⟨k, hk⟩ := hopf_surjective p
  have hcoord (i : Fin 3) : hopfVector k i = ‖y‖⁻¹ * y i := by
    have h := congrArg (fun q : Sphere => (q : Ambient) i) hk
    simpa only [hopf, p, PiLp.smul_apply, smul_eq_mul] using h
  have hr : radialExtension (sphereProfile s f) y = compactRestriction s f k := by
    rw [radialExtension, dif_pos hy]
    change sphereProfile s f p = compactRestriction s f k
    rw [← hk, (sphereProfile_spec s f).2]
  rw [hr]
  cases north
  · have hh : 0 < 1 - hopfVector k 2 := by
      rw [hcoord]; simp only [hemisphereSign, Bool.false_eq_true, if_false, neg_one_mul] at hd
      nlinarith [inv_mul_cancel₀ (ne_of_gt hn)]
    have hb : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      intro hb
      have h := (hopf_bottomRow_coordinates k).2
      rw [hb, norm_zero, zero_pow (by decide)] at h
      linarith
    rw [compactRestriction_infinity_hopf s f k hb]
    simp only [Bool.false_eq_true, if_false, inverseHopfWeight, inverseHopfCoordinate,
      hemisphereSign, neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul,
      one_mul, sub_neg_eq_add]
    rw [hcoord 0, hcoord 1, hcoord 2]
    congr 1
    · congr 2
      simp only [← sub_eq_add_neg]
      field_simp
    · congr 1
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hn)]
      <;> ring
  · have hh : 0 < 1 + hopfVector k 2 := by
      rw [hcoord]; simp only [hemisphereSign, if_true, one_mul] at hd
      nlinarith [inv_mul_cancel₀ (ne_of_gt hn)]
    have ha : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := by
      intro ha
      have h := (hopf_bottomRow_coordinates k).1
      rw [ha, norm_zero, zero_pow (by decide)] at h
      linarith
    rw [compactRestriction_open_hopf s f k ha]
    simp only [if_true, inverseHopfWeight, inverseHopfCoordinate, hemisphereSign,
      one_mul, Complex.ofReal_one]
    rw [hcoord 0, hcoord 1, hcoord 2]
    congr 1
    · congr 2
      simp only [← sub_eq_add_neg]
      field_simp
    · congr 1
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hn)]
      <;> ring

theorem chart_rotation_comparison (s : ℝ) (n : ℕ) :
    ∃ (C D : ℝ≥0), C ≠ 0 ∧ D ≠ 0 ∧
      (∀ f : PrincipalSeries s,
        chartSeminorm s n f ≤ (C : ℝ) * rotationSup n (sphereProfile s f)) ∧
      (∀ f : PrincipalSeries s,
        rotationSup n (sphereProfile s f) ≤
          (D • (Finset.range (n + 1)).sup (chartSeminorm s)) f) := by
  obtain ⟨C, hC, hc⟩ := CompactCharts.chart_le_rotation_raw hopf hopf_coordinates s n
  obtain ⟨A, hA, ha⟩ := CompactCharts.inverse_hopf_jet_bound s n
  have hrad : ∀ (f : PrincipalSeries s), ∀ j ≤ n, ∀ p : Sphere,
      ‖iteratedFDeriv ℝ j (radialExtension (sphereProfile s f)) p‖ ≤
        A * (((Finset.range (n+1)).sup (chartSeminorm s)) f) := by
    intro f j hj p
    obtain ⟨north, hside, hp, hden, hz⟩ := CompactCharts.inverse_hopf_disc_cover p
    have he : radialExtension (sphereProfile s f) =ᶠ[nhds (p : Ambient)]
        (fun y => inverseHopfWeight s north y *
          (if north then openCoordinate f else infinityCoordinate f) (inverseHopfCoordinate north y)) := by
      have hn : ∀ᶠ y in nhds (p : Ambient), y ≠ 0 := isOpen_ne.mem_nhds hp
      have hd : ∀ᶠ y in nhds (p : Ambient), 0 < ‖y‖ + hemisphereSign north * y 2 :=
        (isOpen_lt continuous_const
          (show Continuous (fun y : Ambient => ‖y‖ + hemisphereSign north * y 2) by fun_prop)).mem_nhds hden
      filter_upwards [hn, hd] with y hy hyden
      exact inverse_profile_pointwise s f north y hy hyden
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    apply ha north (if north then openCoordinate f else infinityCoordinate f) ?_
      (((Finset.range (n+1)).sup (chartSeminorm s)) f) (apply_nonneg _ _) p hside ?_ j hj
    · cases north
      · exact f.property.2.2.of_le (by simp)
      · exact f.property.2.1.of_le (by simp)
    · intro k hk
      have hjet := CompactCharts.actual_chart_jet_le_range_sup s n k hk f
        (inverseHopfCoordinate north p) hz
      cases north
      · exact hjet.2
      · exact hjet.1
  obtain ⟨D, hD, hd⟩ := CompactCharts.rotation_le_charts_of_radial_jet_bounds hopf s n A hA
    (fun f F hF hf j hj p => by
      have he : F = sphereProfile s f := by
        funext x
        obtain ⟨k, rfl⟩ := hopf_surjective x
        exact (hf k).symm.trans ((sphereProfile_spec s f).2 k)
      rw [he]
      exact hrad f j hj p)
  refine ⟨C, D, hC, hD, ?_, ?_⟩
  · intro f
    exact hc f (sphereProfile s f) (sphereProfile_spec s f).1 (sphereProfile_spec s f).2
  · intro f
    exact hd f (sphereProfile s f) (sphereProfile_spec s f).1 (sphereProfile_spec s f).2

theorem standardIntertwiner_sphereProfile (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    sphereProfile negativeParameter (standardIntertwiner β f) =
      fun x => (sphericalScalar β : ℂ) *
        fractionalIntegral (1 / 3) (sphereProfile positiveParameter f) x := by
  funext x
  obtain ⟨k, rfl⟩ := hopf_surjective x
  rw [← (sphereProfile_spec negativeParameter (standardIntertwiner β f)).2 k]
  change standardIntertwiner β f (complexSU2Embedding k) = _
  rw [standardIntertwiner_apply]
  exact CompactCharts.intertwiner_hopf_integral hopf hopf_coordinates β f
    (sphereProfile positiveParameter f) (sphereProfile_spec positiveParameter f).1
    (sphereProfile_spec positiveParameter f).2 k

end DedekindZetaZeroFree.ComplexFractionalInverse

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped NNReal BigOperators Matrix Matrix.Norms.Elementwise

theorem existsUnique_hopf_descent (s : ℝ) (f : PrincipalSeries s) :
    ∃! F : Sphere → ℂ, ∀ k : ComplexSU2, compactRestriction s f k = F (hopf k) := by
  let F : Sphere → ℂ := fun x => compactRestriction s f (Classical.choose (hopf_surjective x))
  have hF : ∀ k : ComplexSU2, compactRestriction s f k = F (hopf k) := by
    intro k
    exact compactRestriction_hopf_fiber s f k _ (Classical.choose_spec (hopf_surjective (hopf k))).symm
  refine ⟨F, hF, ?_⟩
  intro G hG
  funext x
  obtain ⟨k, rfl⟩ := hopf_surjective x
  exact (hG k).symm.trans (hF k)

open CompactCharts.RotationToChartsSteps

end DedekindZetaZeroFree.ComplexFractionalInverse

end
