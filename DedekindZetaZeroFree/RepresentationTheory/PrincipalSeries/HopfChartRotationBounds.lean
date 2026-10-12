module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HopfMatrixCoordinates

@[expose] public section

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open scoped BigOperators

private lemma radial_pos_smul (F : Sphere → ℂ) (t : ℝ) (ht : 0 < t) (x : Ambient) :
    radialExtension F (t • x) = radialExtension F x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  have htx : t • x ≠ 0 := smul_ne_zero (ne_of_gt ht) hx
  simp only [radialExtension, dif_pos hx, dif_pos htx]
  congr 1
  apply Subtype.ext
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), mul_one]

private lemma radial_diff {F : Sphere → ℂ} (hF : IsSphereSmooth F)
    {x : Ambient} (hx : x ≠ 0) : DifferentiableAt ℝ (radialExtension F) x :=
  (hF.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt (by simp)

private lemma radial_diff_smul (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (t : ℝ) (ht : 0 < t) (x : Ambient) (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension F) (t • x) (t • v) =
      fderiv ℝ (radialExtension F) x v := by
  have he : (fun y : Ambient => radialExtension F (t • y)) = radialExtension F :=
    funext (radial_pos_smul F t ht)
  have h := (radial_diff hF (smul_ne_zero (ne_of_gt ht) hx)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul t)
  change HasFDerivAt (fun y : Ambient => radialExtension F (t • y)) _ x at h
  rw [he] at h
  have hh := congrArg (fun L : Ambient →L[ℝ] ℂ => L v) h.fderiv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] using hh.symm

private lemma radial_diff_self (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (x : Ambient) (hx : x ≠ 0) : fderiv ℝ (radialExtension F) x x = 0 := by
  have hx' : HasFDerivAt (radialExtension F) (fderiv ℝ (radialExtension F) x)
      ((1 : ℝ) • x) := by simpa using (radial_diff hF hx).hasFDerivAt
  have h := hx'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun t : ℝ => radialExtension F (t • x)) =ᶠ[nhds 1]
      (fun _ => radialExtension F x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact radial_pos_smul F t ht x
  have hz := (hasDerivAt_const (1 : ℝ) (radialExtension F x)).congr_of_eventuallyEq he
  simpa only [one_smul] using h.unique hz

private lemma rotation_scale (i : Fin 3) (t : ℝ) (x : Ambient) :
    rotationVector i (t • x) = t • rotationVector i x := by
  apply PiLp.ext
  intro j
  simp only [rotationVector, PiLp.smul_apply, WithLp.toLp]
  split_ifs <;> simp

private lemma radial_rotation (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (x : Ambient) (hx : x ≠ 0) (i : Fin 3) :
    radialExtension (rotationDeriv i F) x =
      fderiv ℝ (radialExtension F) x (rotationVector i x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [radialExtension, dif_pos hx, rotationDeriv]
  rw [rotation_scale]
  exact radial_diff_smul F hF _ (inv_pos.mpr hn) x hx _

private lemma frame_sum (x v : Ambient) :
    ∑ i : Fin 3, (inner ℝ (rotationVector i x) v) • rotationVector i x =
      ‖x‖ ^ 2 • v - (inner ℝ x v) • x := by
  apply PiLp.ext
  intro j
  fin_cases j <;>
    simp [Fin.sum_univ_three, rotationVector, PiLp.inner_apply,
      Fin.isValue, PiLp.sub_apply, PiLp.smul_apply,
      EuclideanSpace.norm_sq_eq] <;> ring

theorem radial_fderiv_rotation_frame (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (x : Ambient) (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension F) x v =
      ∑ i : Fin 3, (inner ℝ (rotationVector i x) v / ‖x‖ ^ 2) •
        radialExtension (rotationDeriv i F) x := by
  simp_rw [radial_rotation F hF x hx, div_eq_mul_inv, mul_comm _ (‖x‖ ^ 2)⁻¹,
    mul_smul]
  simp_rw [← map_smul]
  rw [← map_sum]
  rw [← Finset.smul_sum, frame_sum, map_smul, map_sub, map_smul, map_smul,
    radial_diff_self F hF x hx]
  simp only [smul_zero, sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)), one_smul]

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end

section
namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open scoped BigOperators

noncomputable def frameCoeff (i : Fin 3) (x : Ambient) : Ambient →L[ℝ] ℂ :=
  (‖x‖ ^ 2)⁻¹ • Complex.ofRealCLM.comp (innerSL ℝ (rotationVector i x))

private lemma frameCoeff_smooth (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (frameCoeff i) {x : Ambient | x ≠ 0} := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Ambient =>
      Complex.ofRealCLM.comp (innerSL ℝ (rotationVector i x))) :=
    contDiff_const.clm_comp ((innerSL ℝ).contDiff.comp (rotationVector_smooth i))
  exact ((contDiff_norm_sq ℝ).contDiffOn.inv (fun x hx =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul hs.contDiffOn

private lemma sphere_ne (p : Sphere) : (p : Ambient) ≠ 0 := by
  have hn : ‖(p : Ambient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  intro hz
  simp [hz] at hn

private lemma toWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Ambient → E} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {x : Ambient | x ≠ 0})
    (n : ℕ) {x : Ambient} (hx : x ≠ 0) :
    iteratedFDerivWithin ℝ n f {x : Ambient | x ≠ 0} x = iteratedFDeriv ℝ n f x :=
  iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ne.uniqueDiffOn
    ((hf.contDiffAt (isOpen_ne.mem_nhds hx)).of_le (by simp)) hx

private lemma frameCoeff_bound (n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i : Fin 3, ∀ j ≤ n, ∀ p : Sphere,
      ‖iteratedFDeriv ℝ j (frameCoeff i) (p : Ambient)‖ ≤ D := by
  classical
  have hb : ∀ ij : Fin 3 × Fin (n + 1), ∃ D : ℝ, 0 ≤ D ∧ ∀ p : Sphere,
      ‖iteratedFDeriv ℝ ij.2.val (frameCoeff ij.1) (p : Ambient)‖ ≤ D := by
    intro ij
    have hcont : ContinuousOn (fun x : Ambient =>
        ‖iteratedFDeriv ℝ ij.2.val (frameCoeff ij.1) x‖) {x | x ≠ 0} := by
      have h := (frameCoeff_smooth ij.1).continuousOn_iteratedFDerivWithin
        (m := ij.2.val) (by simp) isOpen_ne.uniqueDiffOn
      apply h.norm.congr
      intro x hx
      exact congrArg norm (toWithin (frameCoeff_smooth ij.1) _ hx).symm
    obtain ⟨D, hD⟩ := (isCompact_sphere (0 : Ambient) 1).bddAbove_image
      (hcont.mono (fun x hx => sphere_ne ⟨x, hx⟩))
    exact ⟨max 0 D, le_max_left _ _, fun p =>
      (hD (Set.mem_image_of_mem _ p.property)).trans (le_max_right _ _)⟩
  choose D hD0 hD using hb
  refine ⟨∑ ij, D ij, Finset.sum_nonneg (fun ij _ => hD0 ij), ?_⟩
  intro i j hj p
  let ij : Fin 3 × Fin (n + 1) := ⟨i, ⟨j, by omega⟩⟩
  exact (hD ij p).trans (Finset.single_le_sum (fun k _ => hD0 k) (Finset.mem_univ ij))

private lemma fderiv_frame (F : Sphere → ℂ) (hF : IsSphereSmooth F)
    (x : Ambient) (hx : x ≠ 0) :
    fderiv ℝ (radialExtension F) x =
      ∑ i : Fin 3, radialExtension (rotationDeriv i F) x • frameCoeff i x := by
  ext v
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, frameCoeff, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [radial_fderiv_rotation_frame F hF x hx v]
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_eq_mul, div_eq_mul_inv, Complex.ofReal_mul]
  ring

private lemma rotationSup_deriv (i : Fin 3) (n : ℕ) (F : Sphere → ℂ)
    (hF : IsSphereSmooth F) : rotationSup n (rotationDeriv i F) ≤ rotationSup (n + 1) F := by
  apply Real.sSup_le _ (rotationSup_nonneg _ _)
  rintro r ⟨w, hw, p, rfl⟩
  have h := rotationWord_norm_le_rotationSup hF (w ++ [i]) (n := n + 1)
    (by simp; omega) p
  simpa only [rotationWord_append, rotationWord] using h

theorem radial_jet_bound_direct (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ F : Sphere → ℂ, IsSphereSmooth F → ∀ p : Sphere,
      ‖iteratedFDeriv ℝ n (radialExtension F) p‖ ≤ A * rotationSup n F := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro F hF p
      simpa only [norm_iteratedFDeriv_zero, radialExtension_sphere, one_mul, rotationWord] using
        rotationWord_norm_le_rotationSup hF [] (n := 0) (by simp) p
    | succ n =>
      have hb : ∀ j : Fin (n + 1), ∃ A : ℝ, 0 ≤ A ∧ ∀ F : Sphere → ℂ,
          IsSphereSmooth F → ∀ p : Sphere,
          ‖iteratedFDeriv ℝ j.val (radialExtension F) p‖ ≤ A * rotationSup j.val F :=
        fun j => ih j.val j.isLt
      choose A hA0 hA using hb
      obtain ⟨D, hD0, hD⟩ := frameCoeff_bound n
      let B := ∑ j : Fin (n + 1), A j
      have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => hA0 j)
      have hBj (j : Fin (n + 1)) : A j ≤ B :=
        Finset.single_le_sum (fun k _ => hA0 k) (Finset.mem_univ j)
      let C := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * B * D
      have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => by positivity)
      refine ⟨3 * C, by positivity, ?_⟩
      intro F hF p
      have hne := sphere_ne p
      let S : Set Ambient := {x | x ≠ 0}
      have hprod (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => radialExtension (rotationDeriv i F) x • frameCoeff i x) S :=
        (rotationDeriv_smooth i hF).smul (frameCoeff_smooth i)
      have he : fderiv ℝ (radialExtension F) =ᶠ[nhds (p : Ambient)]
          (fun x => ∑ i : Fin 3,
            radialExtension (rotationDeriv i F) x • frameCoeff i x) := by
        filter_upwards [isOpen_ne.mem_nhds hne] with x hx
        exact fderiv_frame F hF x hx
      rw [← norm_iteratedFDeriv_fderiv]
      rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
      rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
        ((hprod i).contDiffAt (isOpen_ne.mem_nhds hne)).of_le (by simp))]
      calc
        ‖∑ i : Fin 3, iteratedFDeriv ℝ n
            (fun x => radialExtension (rotationDeriv i F) x • frameCoeff i x) p‖
            ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ n
              (fun x => radialExtension (rotationDeriv i F) x • frameCoeff i x) p‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i : Fin 3, C * rotationSup (n + 1) F := by
          apply Finset.sum_le_sum
          intro i _
          rw [← toWithin (hprod i) n hne]
          have h := norm_iteratedFDerivWithin_smul_le (rotationDeriv_smooth i hF)
            (frameCoeff_smooth i) isOpen_ne.uniqueDiffOn hne (n := n) (by simp)
          simp_rw [toWithin (rotationDeriv_smooth i hF) _ hne,
            toWithin (frameCoeff_smooth i) _ hne] at h
          apply h.trans
          calc
            _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
                (B * rotationSup (n + 1) F) * D := by
              apply Finset.sum_le_sum
              intro j hj
              have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
              have hrad := hA ⟨j, by omega⟩ (rotationDeriv i F) (rotationDeriv_smooth i hF) p
              have hrot := (rotationSup_mono hjn (rotationDeriv_smooth i hF)).trans
                (rotationSup_deriv i n F hF)
              have hbnd : ‖iteratedFDeriv ℝ j (radialExtension (rotationDeriv i F)) p‖ ≤
                  B * rotationSup (n + 1) F := hrad.trans
                (mul_le_mul (hBj _) hrot (rotationSup_nonneg _ _) hB0)
              exact mul_le_mul (mul_le_mul_of_nonneg_left hbnd (Nat.cast_nonneg _))
                (hD i (n-j) (Nat.sub_le _ _) p) (norm_nonneg _)
                  (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB0 (rotationSup_nonneg _ _)))
            _ = C * rotationSup (n + 1) F := by
              simp only [C, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (3 * C) * rotationSup (n + 1) F := by simp [mul_assoc]

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped NNReal Matrix Matrix.Norms.Elementwise
noncomputable def chartToRotationSU2OfUnitRow (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ComplexSU2 :=
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
noncomputable def rowScale (x : ℂ) : ℝ := (Real.sqrt (1 + Complex.normSq x))⁻¹
lemma rowScale_pos (x : ℂ) : 0 < rowScale x := by
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  have := Complex.normSq_nonneg x
  linarith
private lemma rowScale_sq (x : ℂ) : rowScale x ^ 2 * (1 + ‖x‖ ^ 2) = 1 := by
  have hp : 0 < 1 + Complex.normSq x := by have := Complex.normSq_nonneg x; linarith
  simp only [rowScale, Complex.normSq_eq_norm_sq, inv_pow, Real.sq_sqrt (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity)]
  exact inv_mul_cancel₀ (ne_of_gt (show 0 < 1 + ‖x‖ ^ 2 by positivity))
lemma rowScale_row (x : ℂ) :
    ‖(rowScale x : ℂ)‖ ^ 2 + ‖(rowScale x : ℂ) * x‖ ^ 2 = 1 := by
  have hs := rowScale_sq x
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rowScale_pos x)]
  nlinarith
noncomputable def openSU2 (x : ℂ) : ComplexSU2 :=
  chartToRotationSU2OfUnitRow (rowScale x) ((rowScale x : ℂ) * x) (rowScale_row x)
noncomputable def infinitySU2 (x : ℂ) : ComplexSU2 :=
  chartToRotationSU2OfUnitRow ((rowScale x : ℂ) * x) (rowScale x) (by linarith [rowScale_row x])
noncomputable def rowUnit (x : ℂ) : ℂˣ := Units.mk0 (rowScale x : ℂ)
  (by exact_mod_cast ne_of_gt (rowScale_pos x))

private lemma upperTriangular_matrix (a d : ℂˣ) (b : ℂ) :
    ((upperTriangular a d b : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(a : ℂ), b; 0, (d : ℂ)] := by
  rfl
private lemma open_decomposition (x : ℂ) :
    weyl * upperUnipotent x =
      upperTriangular (-(rowUnit x)) (rowUnit x)⁻¹
        ((rowScale x : ℂ) * star x) * complexSU2Embedding (openSU2 x) := by
  have hr : (rowScale x : ℂ) ^ 2 * (1 + (‖x‖ ^ 2 : ℂ)) = 1 := by
    exact_mod_cast rowScale_sq x
  have hx : x * star x = (‖x‖ ^ 2 : ℂ) := by
    simp [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  have hn : (rowScale x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (rowScale_pos x)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul, upperTriangular_matrix, complexSU2Embedding, openSU2, chartToRotationSU2OfUnitRow,
      rowUnit, Matrix.mul_apply, Fin.sum_univ_two, star_mul, Complex.star_def, hn]
  · ring
  · rw [← hx] at hr
    simp only [Complex.star_def] at hr
    linear_combination -hr
private lemma infinity_decomposition (x : ℂ) :
    lowerUnipotent x =
      upperTriangular (rowUnit x) (rowUnit x)⁻¹
        ((rowScale x : ℂ) * star x) * complexSU2Embedding (infinitySU2 x) := by
  have hr : (rowScale x : ℂ) ^ 2 * (1 + (‖x‖ ^ 2 : ℂ)) = 1 := by
    exact_mod_cast rowScale_sq x
  have hx : x * star x = (‖x‖ ^ 2 : ℂ) := by
    simp [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  have hn : (rowScale x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (rowScale_pos x)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, Matrix.GeneralLinearGroup.coe_mul, upperTriangular_matrix, complexSU2Embedding, infinitySU2, chartToRotationSU2OfUnitRow,
      rowUnit, Matrix.mul_apply, Fin.sum_univ_two, star_mul, Complex.star_def, hn]
  · rw [← hx] at hr
    simp only [Complex.star_def] at hr
    linear_combination -hr
  · ring

private lemma open_weight (s : ℝ) (x : ℂ) :
    inductionWeight s (-(rowUnit x)) (rowUnit x)⁻¹ =
      inductionWeight s (rowUnit x) (rowUnit x)⁻¹ := by
  simp [inductionWeight, complexAbs, rowUnit, norm_div]

noncomputable def openHopfChart (z : ℂ) : Ambient :=
  WithLp.toLp 2 ![2 * rowScale z ^ 2 * z.re,
    -(2 * rowScale z ^ 2 * z.im), rowScale z ^ 2 * (1 - ‖z‖ ^ 2)]

noncomputable def infinityHopfChart (z : ℂ) : Ambient :=
  WithLp.toLp 2 ![2 * rowScale z ^ 2 * z.re,
    2 * rowScale z ^ 2 * z.im, rowScale z ^ 2 * (‖z‖ ^ 2 - 1)]

private lemma open_hopf_chart (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (z : ℂ) : (H (openSU2 z) : Ambient) = openHopfChart z := by
  rw [hH]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [compactSphereCoordinate, openSU2, chartToRotationSU2OfUnitRow, openHopfChart,
      Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.norm_real,
      norm_mul, mul_pow, sq_abs, ← Complex.ofReal_pow] <;> ring

private lemma infinity_hopf_chart (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (z : ℂ) : (H (infinitySU2 z) : Ambient) = infinityHopfChart z := by
  rw [hH]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [compactSphereCoordinate, infinitySU2, chartToRotationSU2OfUnitRow, infinityHopfChart,
      Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.norm_real,
      norm_mul, mul_pow, sq_abs, ← Complex.ofReal_pow] <;> ring

private lemma rowScale_smooth : ContDiff ℝ (⊤ : ℕ∞) rowScale := by
  have hp (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have he : rowScale = fun z : ℂ => (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ := by
    funext z
    simp [rowScale, Complex.normSq_eq_norm_sq]
  rw [he]
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun z => ne_of_gt (hp z)) |>.inv
    (fun z => ne_of_gt (Real.sqrt_pos.mpr (hp z)))

theorem hopfCharts_smooth : ContDiff ℝ (⊤ : ℕ∞) openHopfChart ∧
    ContDiff ℝ (⊤ : ℕ∞) infinityHopfChart := by
  have hs := rowScale_smooth
  have hn := contDiff_norm_sq (n := (⊤ : ℕ∞)) ℝ (E := ℂ)
  have hr := Complex.reCLM.contDiff (n := (⊤ : ℕ∞))
  have hi := Complex.imCLM.contDiff (n := (⊤ : ℕ∞))
  constructor
  all_goals
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
  · exact (contDiff_const.mul (hs.pow 2)).mul hr
  · exact ((contDiff_const.mul (hs.pow 2)).mul hi).neg
  · exact (hs.pow 2).mul (contDiff_const.sub hn)
  · exact (contDiff_const.mul (hs.pow 2)).mul hr
  · exact (contDiff_const.mul (hs.pow 2)).mul hi
  · exact (hs.pow 2).mul (hn.sub contDiff_const)

noncomputable def chartInductionMultiplier (s : ℝ) (z : ℂ) : ℂ :=
  (inductionWeight s (rowUnit z) (rowUnit z)⁻¹ : ℂ)

theorem chartInductionMultiplier_smooth (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (chartInductionMultiplier s) := by
  have he : chartInductionMultiplier s = fun z : ℂ =>
      (Real.rpow ((rowScale z * rowScale z) ^ 2) (1/2+s) : ℂ) := by
    funext z
    simp [chartInductionMultiplier, inductionWeight, complexAbs, rowUnit, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rowScale_pos z), div_inv_eq_mul]
  rw [he]
  apply Complex.ofRealCLM.contDiff.comp
  exact ((rowScale_smooth.mul rowScale_smooth).pow 2).rpow_const_of_ne
    (fun z => pow_ne_zero 2 (mul_ne_zero (ne_of_gt (rowScale_pos z))
      (ne_of_gt (rowScale_pos z))))

theorem chart_profile_formula (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (s : ℝ) (f : PrincipalSeries s) (F : Sphere → ℂ)
    (hf : ∀ k : ComplexSU2, compactRestriction s f k = F (H k)) :
    openCoordinate f = (fun z => chartInductionMultiplier s z *
      radialExtension F (openHopfChart z)) ∧
    infinityCoordinate f = (fun z => chartInductionMultiplier s z *
      radialExtension F (infinityHopfChart z)) := by
  constructor
  · funext z
    change f (weyl * upperUnipotent z) = _
    rw [open_decomposition, f.property.1, open_weight]
    rw [← open_hopf_chart H hH, radialExtension_sphere]
    exact congrArg (fun v => chartInductionMultiplier s z * v) (hf (openSU2 z))
  · funext z
    change f (lowerUnipotent z) = _
    rw [infinity_decomposition, f.property.1]
    rw [← infinity_hopf_chart H hH, radialExtension_sphere]
    exact congrArg (fun v => chartInductionMultiplier s z * v) (hf (infinitySU2 z))

private lemma compact_jet_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ℂ → V) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ i g z‖ ≤ D := by
  classical
  have hb : ∀ i : Fin (n + 1), ∃ B : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ (i : ℕ) g z‖ ≤ max 1 B := by
    intro i
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
      ((ContDiff.continuous_iteratedFDeriv (m := (i : ℕ)) (by simp) hg).norm.continuousOn)
    exact ⟨B, fun z hz => (hB (Set.mem_image_of_mem _ hz)).trans (le_max_right _ _)⟩
  choose B hB using hb
  let D := ∑ i : Fin (n + 1), max 1 (B i)
  have hle (i : Fin (n + 1)) : max 1 (B i) ≤ D :=
    Finset.single_le_sum (fun j _ => le_trans zero_le_one (le_max_left _ _))
      (Finset.mem_univ i)
  refine ⟨D, (le_max_left 1 (B ⟨0, by omega⟩)).trans (hle _), ?_⟩
  intro i hi z hz
  exact (hB ⟨i, by omega⟩ z hz).trans (hle _)

private lemma weighted_pullback_bound (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (φ : ℂ → Ambient) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : ∀ z, ∃ p : Sphere, φ z = (p : Ambient))
    (s : ℝ) (n : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Sphere → ℂ, IsSphereSmooth F →
      (∀ i ≤ n, ∀ p : Sphere, ‖iteratedFDeriv ℝ i (radialExtension F) p‖ ≤
        A * rotationSup n F) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ n (fun z => chartInductionMultiplier s z *
          radialExtension F (φ z)) z‖ ≤ C * rotationSup n F := by
  obtain ⟨D, hD1, hD⟩ := compact_jet_bound φ hφ n
  obtain ⟨W, hW1, hW⟩ := compact_jet_bound (chartInductionMultiplier s)
    (chartInductionMultiplier_smooth s) n
  let C := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * W * ((n - i).factorial * A * D ^ (n - i))
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  refine ⟨C, Finset.sum_nonneg (fun i _ => by positivity), ?_⟩
  intro F hF hrad z hz
  have hne (z : ℂ) : φ z ≠ 0 := by
    obtain ⟨p, hp⟩ := hφs z
    rw [hp]
    have hn : ‖(p : Ambient)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.property
    intro hzero
    simp [hzero] at hn
  have hpull : ContDiff ℝ (⊤ : ℕ∞) (radialExtension F ∘ φ) :=
    hF.comp_contDiff hφ hne
  have hcomp (m : ℕ) (hm : m ≤ n) :
      ‖iteratedFDeriv ℝ m (radialExtension F ∘ φ) z‖ ≤
        (m.factorial * A * D ^ m) * rotationSup n F := by
    have h := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (n := m)
      (t := {x : Ambient | x ≠ 0})
      (by rintro _ ⟨y, rfl⟩; exact hne y)
      isOpen_ne.uniqueDiffOn hF hφ (by simp) z
      (C := A * rotationSup n F) (D := D) ?_ ?_
    · convert h using 1 <;> ring
    · intro i hi
      rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ne.uniqueDiffOn
        ((hF.contDiffAt (isOpen_ne.mem_nhds (hne z))).of_le (by simp)) (hne z)]
      obtain ⟨p, hp⟩ := hφs z
      rw [hp]
      exact hrad i (hi.trans hm) p
    · intro i hi him
      exact (hD i (him.trans hm) z hz).trans (le_self_pow₀ hD1 (by omega))
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (chartInductionMultiplier s) z‖ *
        ‖iteratedFDeriv ℝ (n - i) (radialExtension F ∘ φ) z‖ :=
      norm_iteratedFDeriv_mul_le (chartInductionMultiplier_smooth s) hpull z (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * W *
        (((n-i).factorial * A * D ^ (n-i)) * rotationSup n F) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hW i hin z hz) (Nat.cast_nonneg _))
        (hcomp (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = C * rotationSup n F := by
      simp only [C, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem chart_le_rotation_of_radial_jet_bounds (H : ComplexSU2 → Sphere)
    (hH : HasHopfCoordinates H) (s : ℝ) (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hrad : ∀ F : Sphere → ℂ, IsSphereSmooth F → ∀ i ≤ n, ∀ p : Sphere,
      ‖iteratedFDeriv ℝ i (radialExtension F) p‖ ≤ A * rotationSup n F) :
    ∃ C : ℝ≥0, C ≠ 0 ∧ ∀ (f : PrincipalSeries s) (F : Sphere → ℂ),
      IsSphereSmooth F → (∀ k, compactRestriction s f k = F (H k)) →
      chartSeminorm s n f ≤ (C : ℝ) * rotationSup n F := by
  have ho (z : ℂ) : ∃ p : Sphere, openHopfChart z = (p : Ambient) :=
    ⟨H (openSU2 z), (open_hopf_chart H hH z).symm⟩
  have hi (z : ℂ) : ∃ p : Sphere, infinityHopfChart z = (p : Ambient) :=
    ⟨H (infinitySU2 z), (infinity_hopf_chart H hH z).symm⟩
  obtain ⟨B, hB0, hB⟩ := weighted_pullback_bound H hH _ hopfCharts_smooth.1 ho s n A hA
  obtain ⟨D, hD0, hD⟩ := weighted_pullback_bound H hH _ hopfCharts_smooth.2 hi s n A hA
  let C : ℝ≥0 := ⟨1 + B + D, by positivity⟩
  have hCpos : 0 < (C : ℝ) := by change 0 < 1 + B + D; positivity
  refine ⟨C, ne_of_gt hCpos, ?_⟩
  intro f F hF hf
  obtain ⟨hopen, hinf⟩ := chart_profile_formula H hH s f F hf
  have hR := rotationSup_nonneg n F
  change max _ _ ≤ _
  apply max_le
  · apply Real.sSup_le _ (mul_nonneg hCpos.le hR)
    rintro r ⟨z, hz, rfl⟩
    rw [hopen]
    exact (hB F hF (hrad F hF) z hz).trans
      (mul_le_mul_of_nonneg_right (by change B ≤ 1 + B + D; linarith) hR)
  · apply Real.sSup_le _ (mul_nonneg hCpos.le hR)
    rintro r ⟨z, hz, rfl⟩
    rw [hinf]
    exact (hD F hF (hrad F hF) z hz).trans
      (mul_le_mul_of_nonneg_right (by change D ≤ 1 + B + D; linarith) hR)

private theorem radial_all_orders_bound (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ F : Sphere → ℂ, IsSphereSmooth F →
      ∀ i ≤ n, ∀ p : Sphere,
        ‖iteratedFDeriv ℝ i (radialExtension F) p‖ ≤ A * rotationSup n F := by
  classical
  have hb : ∀ i : Fin (n + 1), ∃ A : ℝ, 0 ≤ A ∧
      ∀ F : Sphere → ℂ, IsSphereSmooth F → ∀ p : Sphere,
        ‖iteratedFDeriv ℝ i.val (radialExtension F) p‖ ≤ A * rotationSup i.val F :=
    fun i => radial_jet_bound_direct i.val
  choose A hA hbound using hb
  refine ⟨∑ i : Fin (n + 1), A i, Finset.sum_nonneg (fun i _ => hA i), ?_⟩
  intro F hF i hi p
  let j : Fin (n + 1) := ⟨i, by omega⟩
  have hle : A j ≤ ∑ j : Fin (n + 1), A j :=
    Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j)
  exact (hbound j F hF p).trans
    ((mul_le_mul_of_nonneg_left (rotationSup_mono hi hF) (hA j)).trans
      (mul_le_mul_of_nonneg_right hle (rotationSup_nonneg n F)))

theorem chart_le_rotation_raw (H : ComplexSU2 → Sphere) (hH : HasHopfCoordinates H)
    (s : ℝ) (n : ℕ) :
    ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (f : PrincipalSeries s) (F : Sphere → ℂ), IsSphereSmooth F →
        (∀ k : ComplexSU2, compactRestriction s f k = F (H k)) →
        chartSeminorm s n f ≤ (C : ℝ) * rotationSup n F := by
  obtain ⟨A, hA, hrad⟩ := radial_all_orders_bound n
  exact chart_le_rotation_of_radial_jet_bounds H hH s n A hA hrad

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

end
