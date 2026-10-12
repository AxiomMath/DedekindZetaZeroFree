module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.RadialHaarAndCutoffIntegrals

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DedekindZetaZeroFree.KPCutoffSource
theorem incoming_commutator_integrable (d : ℕ) {T : ℝ} (χ : SmoothCuspCutoff T) (s : ℂ) :
    Integrable (incomingCommutatorMultiplier d χ.toFun s) := by
  have hc : Continuous (incomingCommutatorMultiplier d χ.toFun s) := by
    unfold incomingCommutatorMultiplier
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv χ.toFun) := χ.smooth.deriv'
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv χ.toFun)) := h1.deriv'
    fun_prop
  have he : incomingCommutatorMultiplier d χ.toFun s =
      fun t => (incomingCommutatorMultiplier d χ.toFun s t *
        (KPIncomingCasimir.heightFactor d s t * 1)) *
        (KPIncomingCasimir.heightFactor d s t)⁻¹ := by
    funext t
    simp [KPIncomingCasimir.heightFactor, Complex.exp_ne_zero]
  apply hc.integrable_of_hasCompactSupport
  apply IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
  rw [he]
  exact tsupport_mul_subset_left.trans (incoming_commutator_support d χ s 1)
theorem radial_log_integrable (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ) (hf : Integrable f) :
    IntegrableOn (fun r : ℝ => (r:ℂ)*f (Real.log r / k)) (Set.Ioi 0)
      KPMsFixedHaarDisintegration.radialMeasure := by
  unfold IntegrableOn KPMsFixedHaarDisintegration.radialMeasure
  rw [restrict_withDensity measurableSet_Ioi]
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun r : ℝ => ENNReal.ofReal (r^2)⁻¹) by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  have hs : Integrable (fun u : ℝ => f (u/k)) := by
    simpa only [div_eq_mul_inv,mul_comm] using hf.comp_mul_left' (inv_ne_zero hk.ne')
  have hl := (integrableOn_comp_log_Ioi_zero (fun u : ℝ => f (u/k))).mpr hs
  apply hl.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg r))]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  have hn : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  field_simp
theorem incoming_commutator_radial_integrable (d : ℕ) (hd : 0 < d) {T : ℝ}
    (χ : SmoothCuspCutoff T) (s : ℂ) (τ : ℝ) :
    IntegrableOn (fun r : ℝ => (r:ℂ)*
      incomingCommutatorMultiplier d χ.toFun s (Real.log r/(2*d)))
      (Set.Ioi (Real.exp (2*d*τ))) KPMsFixedHaarDisintegration.radialMeasure :=
  (radial_log_integrable (2*(d:ℝ)) (by positivity) _
    (incoming_commutator_integrable d χ s)).mono_set
      (Set.Ioi_subset_Ioi (Real.exp_pos _).le)

open scoped BigOperators
theorem finite_cusp_radial_cancellation {J : Type*} [Fintype J]
    (d : ℕ) (hd : 0 < d) {T : ℝ} (χ : J → SmoothCuspCutoff T)
    (τ : ℝ) (hτ : τ < T) (c : J → ℂ) :
    (∫ r : ℝ in Set.Ioi (Real.exp (2*d*τ)),
      ∑ j, c j * ((r:ℂ)*incomingCommutatorMultiplier d (χ j).toFun 0
        (Real.log r/(2*d))) ∂KPMsFixedHaarDisintegration.radialMeasure) =
      (-(4:ℂ)*(d:ℂ)/3) * ∑j,c j := by
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, incoming_commutator_radial_above d hd _ 0 τ hτ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact (incoming_commutator_radial_integrable d hd (χ j) 0 τ).const_mul (c j)

end DedekindZetaZeroFree.KPCutoffSource

end
