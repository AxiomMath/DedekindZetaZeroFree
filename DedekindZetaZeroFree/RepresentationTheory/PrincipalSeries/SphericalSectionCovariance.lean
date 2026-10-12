module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HopfMatrixCoordinates

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped Matrix Matrix.Norms.Elementwise
private lemma row_norm_upper (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    bottomRowNormSq (upperTriangular a d b * g) = ‖(d : ℂ)‖ ^ 2 * bottomRowNormSq g := by
  simp [bottomRowNormSq, Matrix.GeneralLinearGroup.coe_mul, upperTriangular_coe_matrix,
    Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow]
  ring
private lemma det_norm_upper (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    ‖(Matrix.GeneralLinearGroup.det (upperTriangular a d b * g) : ℂ)‖ =
      ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ := by
  rw [map_mul, Units.val_mul, norm_mul]
  congr 1
  change ‖(↑(upperTriangular a d b) : Matrix (Fin 2) (Fin 2) ℂ).det‖ = _
  simp [upperTriangular_coe_matrix, Matrix.det_fin_two, norm_mul]
theorem sphericalFunction_covariance (s : ℝ) : HasCovariance s (sphericalFunction s) := by
  intro a d b g
  have hd : ‖(d : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr d.ne_zero
  have hw : inductionWeight s a d = Real.rpow (‖(a : ℂ)‖ / ‖(d : ℂ)‖) (1 + 2*s) := by
    simp only [inductionWeight, complexAbs, norm_div]
    calc
      _ = Real.rpow (‖(a : ℂ)‖ / ‖(d : ℂ)‖) ((2 : ℕ) * (1/2+s)) :=
        (Real.rpow_natCast_mul (by positivity) 2 (1/2+s)).symm
      _ = _ := by congr 1; norm_num; ring
  unfold sphericalFunction
  rw [row_norm_upper, det_norm_upper, hw]
  have he : ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ /
      (‖(d : ℂ)‖ ^ 2 * bottomRowNormSq g) =
      (‖(a : ℂ)‖ / ‖(d : ℂ)‖) *
      (‖(Matrix.GeneralLinearGroup.det g : ℂ)‖ / bottomRowNormSq g) := by
    simp only [div_mul_eq_div_div, sq]
    field_simp
    <;> ring
  rw [he, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  exact Real.mul_rpow (by positivity) (by unfold bottomRowNormSq; positivity)
theorem sphericalFunction_charts (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (sphericalFunction s)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (sphericalFunction s)) := by
  have h0 (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (Real.rpow (1 / (1 + ‖z‖ ^ 2)) (1+2*s) : ℂ)) := by
    apply Complex.ofRealCLM.contDiff.comp
    apply ContDiff.rpow_const_of_ne
    · exact contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ)) (fun z => ne_of_gt (h0 z))
    · exact fun z => ne_of_gt (one_div_pos.mpr (h0 z))
  have ho : openCoordinate (sphericalFunction s) = fun z : ℂ =>
      (Real.rpow (1 / (1 + ‖z‖ ^ 2)) (1+2*s) : ℂ) := by
    funext z
    simp [openCoordinate, sphericalFunction, bottomRowNormSq,
      Matrix.GeneralLinearGroup.val_det_apply, weyl, upperUnipotent,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hi : infinityCoordinate (sphericalFunction s) = fun z : ℂ =>
      (Real.rpow (1 / (1 + ‖z‖ ^ 2)) (1+2*s) : ℂ) := by
    funext z
    simp [infinityCoordinate, sphericalFunction, bottomRowNormSq,
      Matrix.GeneralLinearGroup.val_det_apply, lowerUnipotent, Matrix.det_fin_two, add_comm]
  exact ⟨ho ▸ hc, hi ▸ hc⟩
end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
