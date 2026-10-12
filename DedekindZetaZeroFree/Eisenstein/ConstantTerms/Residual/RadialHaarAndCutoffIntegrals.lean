module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.RadialCommutatorIntegral

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DedekindZetaZeroFree.KPCutoffSource
theorem radial_log_integral (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ) :
    (∫ r : ℝ in Set.Ioi 0, (r : ℂ) * f (Real.log r / k)
      ∂KPMsFixedHaarDisintegration.radialMeasure) = k • ∫ t, f t := by
  unfold KPMsFixedHaarDisintegration.radialMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (show Measurable (fun r : ℝ => ENNReal.ofReal (r ^ 2)⁻¹) by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Ioi]
  have he : (∫ r : ℝ in Set.Ioi 0,
      (ENNReal.ofReal (r ^ 2)⁻¹).toReal • ((r : ℂ) * f (Real.log r / k))) =
      ∫ r : ℝ in Set.Ioi 0, r⁻¹ • f (Real.log r / k) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg r))]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    field_simp
  rw [he, integral_comp_log_Ioi_zero (fun u => f (u / k))]
  simpa only [div_eq_mul_inv, mul_comm, abs_of_pos hk] using
    Measure.integral_comp_inv_mul_left f k
theorem incoming_commutator_radial (d : ℕ) (hd : 0 < d) {T : ℝ}
    (χ : SmoothCuspCutoff T) (s : ℂ) :
    (∫ r : ℝ in Set.Ioi 0, (r : ℂ) *
      incomingCommutatorMultiplier d χ.toFun s (Real.log r / (2*d))
      ∂KPMsFixedHaarDisintegration.radialMeasure) =
      (2*(d : ℂ)) * (-(2:ℂ)/3-4*s) := by
  rw [radial_log_integral (2*(d:ℝ)) (by positivity),
    incoming_commutator_integral_full]
  simp [Complex.real_smul]

theorem incoming_commutator_zero_below (d : ℕ) {T : ℝ} (χ : SmoothCuspCutoff T)
    (s : ℂ) (t : ℝ) (ht : t < T) :
    incomingCommutatorMultiplier d χ.toFun s t = 0 := by
  have he : χ.toFun =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact χ.zero_below x hx.le
  have h1 : deriv χ.toFun t = 0 := by simpa only [deriv_const] using he.deriv_eq
  have h2 : deriv (deriv χ.toFun) t = 0 := by
    simpa only [deriv_const',deriv_const] using he.deriv.deriv_eq
  simp [incomingCommutatorMultiplier,h1,h2]

theorem incoming_commutator_radial_above (d : ℕ) (hd : 0 < d) {T : ℝ}
    (χ : SmoothCuspCutoff T) (s : ℂ) (τ : ℝ) (hτ : τ < T) :
    (∫ r : ℝ in Set.Ioi (Real.exp (2*d*τ)), (r : ℂ) *
      incomingCommutatorMultiplier d χ.toFun s (Real.log r / (2*d))
      ∂KPMsFixedHaarDisintegration.radialMeasure) =
      (2*(d : ℂ)) * (-(2:ℂ)/3-4*s) := by
  rw [← incoming_commutator_radial d hd χ s]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ioi_subset_Ioi (Real.exp_pos _).le)
  intro r hr
  have hle : r ≤ Real.exp (2*(d:ℝ)*τ) := le_of_not_gt hr.2
  have hlog := Real.log_le_log hr.1 hle
  rw [Real.log_exp] at hlog
  have hdiv : Real.log r / (2*(d:ℝ)) < T := by
    have hlediv : Real.log r / (2*(d:ℝ)) ≤ τ := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    exact lt_of_le_of_lt hlediv hτ
  rw [incoming_commutator_zero_below d χ s _ hdiv,mul_zero]

theorem incoming_outgoing_height_product (d : ℕ) (t : ℝ) :
    KPIncomingCasimir.heightFactor d 0 t *
      star (Complex.exp ((d:ℂ)*(2/3)*(t:ℂ))) = Complex.exp (2*(d:ℂ)*(t:ℂ)) := by
  unfold KPIncomingCasimir.heightFactor
  have he : Complex.exp ((d:ℂ)*(2/3)*(t:ℂ)) =
      (Real.exp ((d:ℝ)*(2/3)*t) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem incoming_outgoing_radial_density (d : ℕ) (hd : 0 < d) (r : ℝ) (hr : 0 < r) :
    KPIncomingCasimir.heightFactor d 0 (Real.log r / (2*d)) *
      star (Complex.exp ((d:ℂ)*(2/3)*((Real.log r / (2*d):ℝ):ℂ))) = (r:ℂ) := by
  rw [incoming_outgoing_height_product]
  have hd' : (d:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have he : 2*(d:ℂ)*((Real.log r / (2*d):ℝ):ℂ) = (Real.log r : ℂ) := by
    push_cast
    field_simp
  rw [he, ← Complex.ofReal_exp, Real.exp_log hr]

end DedekindZetaZeroFree.KPCutoffSource

end
