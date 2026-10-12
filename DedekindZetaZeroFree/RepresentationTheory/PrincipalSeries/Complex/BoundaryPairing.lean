module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def pairing (β : ℂˣ) (s : ℝ) (f : PrincipalSeries s) (g : PrincipalSeries (-s)) : ℂ :=
  ∫ z, star (openCoordinate f z) * openCoordinate g z ∂characterHaar β

private theorem integral_dilation (β c : ℂˣ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f ((c : ℂ) * x) ∂characterHaar β) =
      ((‖(c : ℂ)‖ ^ 2)⁻¹ : ℝ) • ∫ x : ℂ, f x ∂characterHaar β := by
  letI := characterHaar_isAddHaarMeasure β
  let r : ℝ := ‖(c : ℂ)‖
  have hr : 0 < r := norm_pos_iff.mpr c.ne_zero
  let u : Circle := ⟨(c : ℂ) / (r : ℂ), by
    change (c : ℂ) / (r : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    exact div_self hr.ne'⟩
  have hrot : MeasurePreserving (rotation u) (characterHaar β) (characterHaar β) := by
    refine ⟨(rotation u).continuous.measurable, ?_⟩
    unfold characterHaar euclideanArea
    rw [Measure.map_smul _ (rotation u).continuous.measurable.aemeasurable,
      (rotation u).measurePreserving.map_eq]
  have he (x : ℂ) : (c : ℂ) * x = r • (rotation u x) := by
    change (c : ℂ) * x = (r : ℂ) * (((c : ℂ) / (r : ℂ)) * x)
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    field_simp
    <;> ring
  simp_rw [he]
  calc
    (∫ x : ℂ, f (r • rotation u x) ∂characterHaar β) =
        ∫ x : ℂ, f (r • x) ∂characterHaar β :=
      hrot.integral_comp (rotation u).toHomeomorph.measurableEmbedding (fun x => f (r • x))
    _ = _ := by
      simpa only [Complex.finrank_real_complex] using
        Measure.integral_comp_smul_of_nonneg (characterHaar β) f r (hR := hr.le)

private theorem integral_affine (β c : ℂˣ) (b : ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (b + (c : ℂ) * x) ∂characterHaar β) =
      ((‖(c : ℂ)‖ ^ 2)⁻¹ : ℝ) • ∫ x : ℂ, f x ∂characterHaar β := by
  letI := characterHaar_isAddHaarMeasure β
  rw [integral_dilation β c (fun x => f (b + x)), integral_add_left_eq_self f b]

private theorem weyl_upper (a d : ℂˣ) (b x : ℂ) :
    weyl * upperUnipotent x * upperTriangular a d b =
      upperTriangular d a 0 * (weyl * upperUnipotent ((b + x * (d : ℂ)) / (a : ℂ))) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (((!![0, 1; 1, 0] * !![1, x; 0, 1]) *
    !![(a : ℂ), b; 0, (d : ℂ)]) : Matrix (Fin 2) (Fin 2) ℂ) i j =
    ((!![(d : ℂ), 0; 0, (a : ℂ)] *
      (!![0, 1; 1, 0] * !![1, (b + x * (d : ℂ)) / (a : ℂ); 0, 1])) :
      Matrix (Fin 2) (Fin 2) ℂ) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  <;> field_simp
  <;> ring

theorem complementary_weights (s : ℝ) (a d : ℂˣ) :
    inductionWeight s a d * inductionWeight (-s) a d = ‖(a : ℂ) / (d : ℂ)‖ ^ 2 := by
  have hp : 0 < complexAbs ((a : ℂ) / (d : ℂ)) :=
    sq_pos_of_pos (norm_pos_iff.mpr (div_ne_zero a.ne_zero d.ne_zero))
  simp only [inductionWeight, Real.rpow_eq_pow]
  rw [← Real.rpow_add hp]
  rw [show (1 / 2 + s) + (1 / 2 + -s) = (1:ℝ) by ring, Real.rpow_one]
  rfl

theorem pairing_upper_invariant (β : ℂˣ) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) (a d : ℂˣ) (b : ℂ) :
    pairing β s (rightTranslate s (upperTriangular a d b) f)
      (rightTranslate (-s) (upperTriangular a d b) g) = pairing β s f g := by
  have hp (z : ℂ) :
      star (f (weyl * upperUnipotent z * upperTriangular a d b)) *
        g (weyl * upperUnipotent z * upperTriangular a d b) =
      ((‖(d : ℂ) / (a : ℂ)‖ ^ 2 : ℝ) : ℂ) *
        (star (openCoordinate f (b / (a : ℂ) + ((d / a : ℂˣ) : ℂ) * z)) *
          openCoordinate g (b / (a : ℂ) + ((d / a : ℂˣ) : ℂ) * z)) := by
    rw [weyl_upper, f.property.1, g.property.1]
    have hc := complementary_weights s d a
    have he : (b + z * (d : ℂ)) / (a : ℂ) =
        b / (a : ℂ) + ((d / a : ℂˣ) : ℂ) * z := by
      simp only [Units.val_div_eq_div_val]
      ring
    rw [he]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal, openCoordinate]
    calc
      _ = ((inductionWeight s d a : ℂ) * (inductionWeight (-s) d a : ℂ)) *
          ((starRingEnd ℂ) (f (weyl * upperUnipotent (b / (a : ℂ) + ((d / a : ℂˣ) : ℂ) * z))) *
            g (weyl * upperUnipotent (b / (a : ℂ) + ((d / a : ℂˣ) : ℂ) * z))) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, hc]
  change (∫ z, star (f (weyl * upperUnipotent z * upperTriangular a d b)) *
    g (weyl * upperUnipotent z * upperTriangular a d b) ∂characterHaar β) = _
  simp_rw [hp]
  rw [integral_const_mul, integral_affine β (d/a) (b/(a:ℂ))
    (fun z => star (openCoordinate f z) * openCoordinate g z)]
  have hn : ‖(d : ℂ) / (a : ℂ)‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (div_ne_zero d.ne_zero a.ne_zero))
  simp only [Complex.real_smul, Complex.ofReal_inv, Units.val_div_eq_div_val]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn), one_mul]
  rfl
end DedekindZetaZeroFree.CurrentComplexBoundary

end
