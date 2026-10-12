module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarGerms.CompactTaylorExpansion
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarGerms.CovarianceAndRegularity

@[expose] public section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.EisensteinSmoothGerms
open MomentSources Complex
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

def ScalarGerm.coefficients {C : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v) (n : ℕ) : Functions R := fun g =>
  (cauchyPowerSeries (fun z => H.cleared z g) 0 (H.radius / 2)).coeff n

theorem ScalarGerm.coefficients_eq_circle {C : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v)
    (t : ℝ) (ht : 0 < t) (htH : t < H.radius) (n : ℕ) (g : Group R) :
    H.coefficients n g = (cauchyPowerSeries (fun z => H.cleared z g) 0 t).coeff n :=
  scalar_cauchy_coefficients_radius_independent _ _ (H.analytic g) _ _
    (half_pos H.radius_pos) ht (by linarith [H.radius_pos]) htH n

private theorem coefficient_covariance (f h : ℂ → ℂ) (t : ℝ) (ht : 0 < t)
    (c : ℂ) (he : ∀ z ∈ Metric.sphere (0 : ℂ) t, f z = c * h z) (n : ℕ) :
    (cauchyPowerSeries f 0 t).coeff n = c * (cauchyPowerSeries h 0 t).coeff n := by
  change (cauchyPowerSeries f 0 t n) (fun _ => 1) =
    c * (cauchyPowerSeries h 0 t n) (fun _ => 1)
  simp only [cauchyPowerSeries_apply, one_div, smul_eq_mul]
  have hi : (∮ z in C(0, t), (z - 0)⁻¹ ^ n * ((z - 0)⁻¹ * f z)) =
      ∮ z in C(0, t), c * ((z - 0)⁻¹ ^ n * ((z - 0)⁻¹ * h z)) := by
    apply circleIntegral.integral_congr ht.le
    intro z hz
    dsimp only
    rw [he z hz]
    ring
  rw [hi, circleIntegral.integral_const_mul]
  ring

theorem ScalarGerm.coefficients_level {C : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v) (n : ℕ) (g u : Group R)
    (hu : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 Q.level) :
    H.coefficients n (g * u) = H.coefficients n g := by
  apply (show _ = (1 : ℂ) * _ from coefficient_covariance _ _ _
    (half_pos H.radius_pos) 1 ?_ n).trans (one_mul _)
  intro z hz
  have hb : z ∈ Metric.ball (0 : ℂ) H.radius :=
    Metric.closedBall_subset_ball (by linarith [H.radius_pos])
      (Metric.sphere_subset_closedBall hz)
  simpa using scalarGerm_level H hb g u hu

end DedekindZetaZeroFree.EisensteinSmoothGerms

end
