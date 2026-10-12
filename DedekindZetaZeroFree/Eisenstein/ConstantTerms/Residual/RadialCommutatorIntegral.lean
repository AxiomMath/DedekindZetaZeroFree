module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace DedekindZetaZeroFree.KPCutoffSource
theorem incoming_commutator_integral (d : ℕ) {T : ℝ} (χ : SmoothCuspCutoff T)
    (s : ℂ) :
    (∫ t in (T-1)..(T+2), incomingCommutatorMultiplier d χ.toFun s t) =
      -(2 : ℂ)/3 - 4*s := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv χ.toFun) := χ.smooth.deriv'
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv χ.toFun)) := h1.deriv'
  let p : ℝ → ℂ := fun t => -((d:ℂ)⁻¹) * ((deriv χ.toFun t:ℝ):ℂ) +
    (2-2*((4:ℂ)/3+2*s))*(χ.toFun t:ℂ)
  have hp (t : ℝ) : HasDerivAt p (incomingCommutatorMultiplier d χ.toFun s t) t := by
    have ha := ((h1.differentiable (by simp) t).hasDerivAt.ofReal_comp).const_mul (-((d:ℂ)⁻¹))
    have hb := ((χ.smooth.differentiable (by simp) t).hasDerivAt.ofReal_comp).const_mul
      (2-2*((4:ℂ)/3+2*s))
    convert ha.add hb using 1; dsimp [p, incomingCommutatorMultiplier]; ring
  have hi : IntervalIntegrable (fun t => incomingCommutatorMultiplier d χ.toFun s t)
      volume (T-1) (T+2) := by
    apply Continuous.intervalIntegrable
    unfold incomingCommutatorMultiplier
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hp t) hi]
  have hlo : χ.toFun =ᶠ[𝓝 (T-1)] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds (show T-1 < T by linarith)] with t ht
    exact χ.zero_below t ht.le
  have hhi : χ.toFun =ᶠ[𝓝 (T+2)] (fun _ => (1:ℝ)) := by
    filter_upwards [Ioi_mem_nhds (show T+1 < T+2 by linarith)] with t ht
    exact χ.one_above t ht.le
  have hlo' : deriv χ.toFun (T-1)=0 := by simpa using hlo.deriv_eq
  have hhi' : deriv χ.toFun (T+2)=0 := by simpa using hhi.deriv_eq
  simp only [p,hlo',hhi',χ.zero_below (T-1) (by linarith),
    χ.one_above (T+2) (by linarith),Complex.ofReal_zero,Complex.ofReal_one,mul_zero,mul_one,add_zero,zero_add,sub_zero]
  ring

theorem incoming_commutator_integral_full (d : ℕ) {T : ℝ} (χ : SmoothCuspCutoff T)
    (s : ℂ) :
    (∫ t, incomingCommutatorMultiplier d χ.toFun s t) = -(2:ℂ)/3 - 4*s := by
  have hsupport (t : ℝ) (ht : t ∉ Set.Ioc (T-1) (T+2)) :
      incomingCommutatorMultiplier d χ.toFun s t = 0 := by
    have hconst : ∃ c : ℝ, χ.toFun =ᶠ[𝓝 t] (fun _ => c) := by
      by_cases hlo : t < T
      · refine ⟨0, ?_⟩
        filter_upwards [Iio_mem_nhds hlo] with u hu
        exact χ.zero_below u hu.le
      · have hhi : T+1 < t := by
          have hnot : ¬(T-1 < t ∧ t ≤ T+2) := ht
          push Not at hnot
          have hlow : T-1 < t := by linarith
          have := hnot hlow
          linarith
        refine ⟨1, ?_⟩
        filter_upwards [Ioi_mem_nhds hhi] with u hu
        exact χ.one_above u hu.le
    obtain ⟨c,hc⟩ := hconst
    have hfirst : deriv χ.toFun t = 0 := by simpa only [deriv_const] using hc.deriv_eq
    have hsecond : deriv (deriv χ.toFun) t = 0 := by
      simpa only [deriv_const',deriv_const] using hc.deriv.deriv_eq
    simp [incomingCommutatorMultiplier,hfirst,hsecond]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
  rw [← intervalIntegral.integral_of_le (show T-1 ≤ T+2 by linarith)]
  exact incoming_commutator_integral d χ s
end DedekindZetaZeroFree.KPCutoffSource

end
