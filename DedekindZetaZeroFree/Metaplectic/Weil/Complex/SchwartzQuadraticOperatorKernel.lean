module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.SchwartzFourierModel
public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.DampedFourierComposition
public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.AbelKernelConvergence

@[expose] public section

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory Filter
open scoped Topology

private theorem psi_add (β t₁ t₂ : ℂ) : psi β (t₁ + t₂) = psi β t₁ * psi β t₂ := by
  have h : ((2 * Real.pi * (β * (t₁ + t₂)).re : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (β * t₁).re : ℝ) : ℂ) * Complex.I +
        ((2 * Real.pi * (β * t₂).re : ℝ) : ℂ) * Complex.I := by
    rw [mul_add, Complex.add_re]
    push_cast
    ring
  unfold psi
  rw [h, Complex.exp_add]

private theorem psi_quadratic_split (β a y z : ℂ) (ha : a ≠ 0) :
    psi β (-(y + z) ^ 2 / (4 * a)) =
      psi β (-y ^ 2 / (4 * a)) * psi β (-z ^ 2 / (4 * a)) *
        psi β (-z * (y / (2 * a))) := by
  have h : -(y + z) ^ 2 / (4 * a) =
      -y ^ 2 / (4 * a) + (-z ^ 2 / (4 * a) + -z * (y / (2 * a))) := by
    field_simp
    ring
  rw [h, psi_add, psi_add]
  ring

theorem FT_M_FT_schwartz (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (f : SchwartzMap ℂ ℂ) (y : ℂ) :
    FT β (fun x : ℂ => psi β (a * x ^ 2) * FT β (⇑f) x) y =
      (1 / (2 * ‖a‖) : ℝ) * psi β (-y ^ 2 / (4 * a)) *
        FT β (fun z : ℂ => psi β (-z ^ 2 / (4 * a)) * f z) (y / (2 * a)) := by

  have hA : FT β (fun x : ℂ => psi β (a * x ^ 2) * FT β (⇑f) x) y
      = F β (M β a (F β (⇑f))) y := by
    rw [FT_eq_F]
    congr 1
    funext x
    rw [FT_eq_F]
    rfl

  have hC : F β (M β a (F β (⇑f))) y
      = ∫ z : ℂ, f z * ((1 / (2 * ‖a‖) : ℝ) : ℂ) *
          psi β (-(y + z) ^ 2 / (4 * a)) ∂mu β := by
    have h1 : Tendsto (fun ε : ℝ => F β (fun x : ℂ =>
        Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
          F β (⇑f) x) y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (F β (M β a (F β (⇑f))) y)) :=
      tendsto_F_damped_M_F β a hβ ha f y
    have h2 : Tendsto (fun ε : ℝ => F β (fun x : ℂ =>
        Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
          F β (⇑f) x) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ z : ℂ, f z * ((1 / (2 * ‖a‖) : ℝ) : ℂ) *
          psi β (-(y + z) ^ 2 / (4 * a)) ∂mu β)) := by
      refine (tendsto_integral_schwartz_mul_K β a hβ ha f y).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (F_damped_M_F_eq_integral_K β a hβ ha ε hε f y).symm
    exact tendsto_nhds_unique h1 h2

  have hB : (1 / (2 * ‖a‖) : ℝ) * psi β (-y ^ 2 / (4 * a)) *
        FT β (fun z : ℂ => psi β (-z ^ 2 / (4 * a)) * f z) (y / (2 * a))
      = ∫ z : ℂ, f z * ((1 / (2 * ‖a‖) : ℝ) : ℂ) *
          psi β (-(y + z) ^ 2 / (4 * a)) ∂mu β := by
    have hinner : ∫ z : ℂ, f z * ((1 / (2 * ‖a‖) : ℝ) : ℂ) *
          psi β (-(y + z) ^ 2 / (4 * a)) ∂(volume : Measure ℂ)
        = ((1 / (2 * ‖a‖) : ℝ) : ℂ) * psi β (-y ^ 2 / (4 * a)) *
            ∫ z : ℂ, (psi β (-z ^ 2 / (4 * a)) * f z) *
              psi β (-z * (y / (2 * a))) ∂(volume : Measure ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      rw [psi_quadratic_split β a y z ha]
      ring
    simp only [FT]
    rw [mu, integral_smul_measure, ENNReal.toReal_ofReal (norm_nonneg β), hinner]
    simp only [Complex.real_smul]
    ring
  rw [hA, hC, hB]

end
end DedekindZetaZeroFree.ComplexWeil
