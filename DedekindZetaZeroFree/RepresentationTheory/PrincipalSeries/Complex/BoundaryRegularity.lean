module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryPairing

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxPrincipalSeriesJets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
private theorem open_le (s : ℝ) (f : PrincipalSeries s) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖openCoordinate f z‖ ≤ chartSeminorm s 0 f := by
  have h := (jetLe 0 _ f.property.2.1 z (by simpa using hz)).trans
    (le_max_left (jetSup 0 (openCoordinate f)) (jetSup 0 (infinityCoordinate f)))
  change ‖iteratedFDeriv ℝ 0 (openCoordinate f) z‖ ≤ chartSeminorm s 0 f at h
  simpa only [norm_iteratedFDeriv_zero] using h
private theorem infinity_le (s : ℝ) (f : PrincipalSeries s) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖infinityCoordinate f z‖ ≤ chartSeminorm s 0 f := by
  have h := (jetLe 0 _ f.property.2.2 z (by simpa using hz)).trans
    (le_max_right (jetSup 0 (openCoordinate f)) (jetSup 0 (infinityCoordinate f)))
  change ‖iteratedFDeriv ℝ 0 (infinityCoordinate f) z‖ ≤ chartSeminorm s 0 f at h
  simpa only [norm_iteratedFDeriv_zero] using h

theorem complementary_transition (s : ℝ) (z : ℂ) (hz : z ≠ 0) :
    transitionWeight s z * transitionWeight (-s) z = ‖z‖ ^ (-4 : ℝ) := by
  simp only [transitionWeight, Real.rpow_eq_pow]
  rw [← Real.rpow_add (norm_pos_iff.mpr hz)]
  congr 1
  ring

theorem product_transition (s : ℝ) (f : PrincipalSeries s) (g : PrincipalSeries (-s))
    (z : ℂ) (hz : z ≠ 0) :
    star (infinityCoordinate f z) * infinityCoordinate g z =
      ((‖z‖ ^ (-4 : ℝ) : ℝ) : ℂ) * (star (openCoordinate f z⁻¹) * openCoordinate g z⁻¹) := by
  rw [coordinate_transition s f z hz, coordinate_transition (-s) g z hz]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((transitionWeight s z : ℂ) * (transitionWeight (-s) z : ℂ)) *
        ((starRingEnd ℂ) (openCoordinate f z⁻¹) * openCoordinate g z⁻¹) := by ring
    _ = _ := by rw [← Complex.ofReal_mul, complementary_transition s z hz]

theorem boundary_product_bound (s : ℝ) (f : PrincipalSeries s) (g : PrincipalSeries (-s))
    (z : ℂ) :
    ‖star (openCoordinate f z) * openCoordinate g z‖ ≤
      (4 * chartSeminorm s 0 f * chartSeminorm (-s) 0 g) *
        (1 + ‖z‖ ^ 2) ^ (-2 : ℝ) := by
  let p := chartSeminorm s 0 f
  let q := chartSeminorm (-s) 0 g
  have hp : 0 ≤ p := (norm_nonneg _).trans (open_le s f 0 (by simp))
  have hq : 0 ≤ q := (norm_nonneg _).trans (open_le (-s) g 0 (by simp))
  have hd : 0 < (1 + ‖z‖ ^ 2)^2 := by positivity
  have hbd : ‖star (openCoordinate f z) * openCoordinate g z‖ * (1 + ‖z‖^2)^2 ≤ 4*p*q := by
    by_cases hz : ‖z‖ ≤ 1
    · have hb : ‖star (openCoordinate f z) * openCoordinate g z‖ ≤ p*q := by
        rw [norm_mul, norm_star]
        exact mul_le_mul (open_le s f z hz) (open_le (-s) g z hz) (norm_nonneg _) hp
      have hr : (1 + ‖z‖^2)^2 ≤ (4:ℝ) := by
        have hsq : ‖z‖^2 ≤ (1:ℝ) := by nlinarith [norm_nonneg z]
        nlinarith [sq_nonneg (1-‖z‖^2)]
      calc
        _ ≤ p*q*4 := mul_le_mul hb hr (sq_nonneg _) (mul_nonneg hp hq)
        _ = _ := by ring
    · have hr : 1 < ‖z‖ := lt_of_not_ge hz
      have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hr))
      have hz' : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hr.le
      have hi : ‖star (infinityCoordinate f z⁻¹) * infinityCoordinate g z⁻¹‖ ≤ p*q := by
        rw [norm_mul, norm_star]
        exact mul_le_mul (infinity_le s f _ hz') (infinity_le (-s) g _ hz') (norm_nonneg _) hp
      have he := congrArg norm (product_transition s f g z⁻¹ (inv_ne_zero hz0))
      simp only [inv_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), norm_inv,
        Real.inv_rpow (norm_nonneg z), Real.rpow_neg (norm_nonneg z),
        inv_inv, Real.rpow_natCast] at he
      have hfour : ‖star (openCoordinate f z) * openCoordinate g z‖ * ‖z‖^4 ≤ p*q := by
        simp only [norm_mul] at hi ⊢
        rw [he] at hi
        convert hi using 1 <;> norm_num [mul_comm]
      have hs : (1 + ‖z‖^2)^2 ≤ 4*‖z‖^4 := by nlinarith [sq_nonneg (‖z‖^2-1)]
      calc
        _ ≤ ‖star (openCoordinate f z) * openCoordinate g z‖ * (4*‖z‖^4) :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg _)
        _ = 4*(‖star (openCoordinate f z) * openCoordinate g z‖ * ‖z‖^4) := by ring
        _ ≤ 4*(p*q) := mul_le_mul_of_nonneg_left hfour (by norm_num)
        _ = _ := by ring
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  change _ ≤ (4*p*q) * ((1+‖z‖^2)^2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ hd]
  exact hbd

theorem pairing_integrable (β : ℂˣ) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    Integrable (fun z => star (openCoordinate f z) * openCoordinate g z) (characterHaar β) := by
  letI := characterHaar_isAddHaarMeasure β
  have hi : Integrable (fun z : ℂ => (1 + ‖z‖^2)^(-2:ℝ)) (characterHaar β) := by
    convert integrable_rpow_neg_one_add_norm_sq (μ := characterHaar β) (r := 4)
      (by norm_num [Complex.finrank_real_complex]) using 1 <;> norm_num
  exact (hi.const_mul (4 * chartSeminorm s 0 f * chartSeminorm (-s) 0 g)).mono'
    ((f.property.2.1.continuous.star.mul g.property.2.1.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall (boundary_product_bound s f g))
end DedekindZetaZeroFree.CurrentComplexBoundary

end
