module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspRadialIntegrationAndShellVolumes

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical ENNReal NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsOffsetRadialCoarea

theorem offset_radial_lintegral (d : ℕ) (hd : 0 < d) (c : ℝ) (hc : 0 < c)
    (Y : ℝ) (hY : 0 < Y) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Set.Ioi (Real.log (Y / c) / (2 * (d : ℝ))),
      f (c * Real.exp (2 * (d : ℝ) * t)) ∂KPCuspCharts.radialMeasure d) =
    ENNReal.ofReal (c / (2 * (d : ℝ))) *
      ∫⁻ r in Set.Ioi Y, f r ∂KPMsFixedHaar.radialMeasure := by
  let q : ℝ := 2 * d
  have hq : 0 < q := mul_pos (by norm_num) (by exact_mod_cast hd)
  let T := Set.Ioi (Real.log (Y / c) / q)
  have hi : Set.InjOn (fun t : ℝ => c * Real.exp (q*t)) T := by
    intro x hx y hy he
    exact mul_left_cancel₀ hq.ne' (Real.exp_injective (mul_left_cancel₀ hc.ne' he))
  have himage : (fun t : ℝ => c * Real.exp (q*t)) '' T = Set.Ioi Y := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hh : Real.log (Y/c) < q*t := by
        simpa only [mul_comm] using (div_lt_iff₀ hq).mp ht
      have he := Real.exp_lt_exp.mpr hh
      rw [Real.exp_log (div_pos hY hc)] at he
      simpa only [Set.mem_Ioi, mul_comm] using (div_lt_iff₀ hc).mp he
    · intro hr
      refine ⟨Real.log (r/c)/q, ?_, ?_⟩
      · exact (div_lt_div_iff_of_pos_right hq).mpr
          (Real.log_lt_log (div_pos hY hc) ((div_lt_div_iff_of_pos_right hc).mpr hr))
      · change c * Real.exp (q * (Real.log (r/c)/q)) = r
        rw [mul_div_cancel₀ _ hq.ne', Real.exp_log (div_pos (lt_trans hY hr) hc)]
        exact mul_div_cancel₀ r hc.ne'
  have hder : ∀ t ∈ T, HasDerivWithinAt (fun t : ℝ => c * Real.exp (q*t))
      (q * (c * Real.exp (q*t))) T t := by
    intro t ht
    convert (((Real.hasDerivAt_exp (q*t)).comp t
      ((hasDerivAt_id t).const_mul q)).const_mul c).hasDerivWithinAt using 1 <;> first | rfl | ring
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hi
    (fun r => ENNReal.ofReal (r^2)⁻¹ * f r)
  rw [himage] at hj
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x^2)⁻¹) :=
    (measurable_id.pow_const 2).inv.ennreal_ofReal
  have hm' : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-2*(d:ℝ)*x))) := by
    fun_prop
  have hfinite : ∀ᵐ x ∂volume.restrict (Set.Ioi Y), ENNReal.ofReal (x^2)⁻¹ < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hfinite' : ∀ᵐ x ∂volume.restrict T,
      ENNReal.ofReal (Real.exp (-2*(d:ℝ)*x)) < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have heq : (∫⁻ r in Set.Ioi Y, f r ∂KPMsFixedHaar.radialMeasure) =
      ENNReal.ofReal (q/c) * ∫⁻ t in T, f (c * Real.exp (q*t))
        ∂KPCuspCharts.radialMeasure d := by
    rw [KPMsFixedHaar.radialMeasure,
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume hm f
        measurableSet_Ioi hfinite]
    simp only [Pi.mul_apply]
    rw [hj]
    rw [KPCuspCharts.radialMeasure,
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume hm' _
        measurableSet_Ioi hfinite']
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    rw [abs_of_pos (mul_pos hq (mul_pos hc (Real.exp_pos _))), ← mul_assoc,
      ← ENNReal.ofReal_mul (le_of_lt (mul_pos hq (mul_pos hc (Real.exp_pos _))))]
    have hs : q * (c * Real.exp (q*t)) * ((c * Real.exp (q*t))^2)⁻¹ =
        (q/c) * Real.exp (-2*(d:ℝ)*t) := by
      rw [show -2*(d:ℝ) = -q by dsimp [q]; ring]
      rw [neg_mul, Real.exp_neg]
      field_simp
    rw [hs, ENNReal.ofReal_mul (div_pos hq hc).le, mul_assoc]
    rfl
  change _ = ENNReal.ofReal (c/q) * _
  rw [heq, ← mul_assoc, ← ENNReal.ofReal_mul (div_pos hc hq).le]
  have hcancel : c/q * (q/c) = 1 := by field_simp
  rw [hcancel, ENNReal.ofReal_one, one_mul]

end DedekindZetaZeroFree.KPMsOffsetRadialCoarea

end
