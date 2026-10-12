module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.CoprimeAndFiniteScaledSummation
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.NonprincipalHeckeSummation
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.SpectrumRecovery
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedCoprimeTruncation

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve

theorem bilinear_middle_double_reflection_bounds
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b) :
    (∀ (u v : ℝ) (n : ℕ), 0 < u → u ≤ v →
      ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc u v, ∀ t : ℝ,
        (1 + |t|) ^ n *
          ‖reflectedSquareSpectrum D r W ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) ∧
    (∀ c x : ℝ, 0 < c → 0 < x →
      Integrable (fun t : ℝ =>
        reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) ∧
      SquareSecondPass.reflectedTransform D r W x =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ,
          reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I) *
            (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) ∧
    ContDiffOn ℝ ∞ (SquareSecondPass.reflectedTransform D r W) (Set.Ioi 0) ∧
    (∀ (j : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ‖Vendor.EulerIter j (SquareSecondPass.reflectedTransform D r W) x‖ ≤
        C * Real.rpow x (-c)) ∧
    (∀ z : ℂ, 0 < z.re →
      MellinConvergent (SquareSecondPass.reflectedTransform D r W) z ∧
      mellin (SquareSecondPass.reflectedTransform D r W) z =
        reflectedSquareSpectrum D r W z) := by
  refine ⟨fun u v n hu huv =>
      reflectedSquareSpectrum_rapid_bound D r W a b u v n hD hr hW hsupp ha hab hu huv, ?_,
    reflectedSquareTransform_contDiffOn D r W a b hD hr hW hsupp ha hab, ?_, ?_⟩
  · intro c x hc hx
    have hK := ReflectedCoprimeTruncation.kernel_eq_mellinInv D r W a b hD hr hW hsupp ha hab
      c x hc hx
    have hvi : Complex.VerticalIntegrable (reflectedSquareSpectrum D r W) c := hK.1
    have htr : SquareSecondPass.reflectedTransform D r W x =
        mellinInv c (reflectedSquareSpectrum D r W) x := hK.2
    have hcont : Continuous (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) :=
      (by fun_prop : Continuous (fun t : ℝ => -((c : ℂ) + (t : ℂ) * Complex.I))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    have hint : Integrable (fun t : ℝ =>
        reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) := by
      refine Integrable.mono'
        (g := fun t : ℝ => x ^ (-c) *
          ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖)
        (hvi.norm.const_mul _) (hvi.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
      filter_upwards with t
      have hre : (-((c : ℂ) + (t : ℂ) * Complex.I)).re = -c := by
        simp [Complex.add_re, Complex.mul_re]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
      exact le_of_eq (mul_comm _ _)
    refine ⟨hint, ?_⟩
    rw [htr, Vendor.mellinInv_eq_verticalIntegral c (reflectedSquareSpectrum D r W) hx,
      Vendor.verticalIntegral]
    rw [show (1 / (2 * Real.pi) : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ by push_cast; ring]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    ring
  · intro j c hc
    obtain ⟨C, hC, h1, h2⟩ :=
      reflectedSquareTransform_euler_two_ended_bound D r W a b hD hr hW hsupp ha hab j
        (Nat.ceil c + 1) c hc
    refine ⟨C, hC, fun x hx => ?_⟩
    rcases le_total x 1 with hx1 | hx1
    · exact h1 x hx hx1
    · refine (h2 x hx1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC.le
      refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
      have : c ≤ (Nat.ceil c : ℝ) := Nat.le_ceil c
      push_cast
      linarith
  · intro z hz
    have hf_loc : LocallyIntegrableOn (SquareSecondPass.reflectedTransform D r W) (Set.Ioi 0) :=
      (reflectedSquareTransform_contDiffOn D r W a b hD hr hW hsupp ha hab).continuousOn.locallyIntegrableOn
        measurableSet_Ioi
    obtain ⟨C, _hC, hbot, htop⟩ :=
      reflectedSquareTransform_euler_two_ended_bound D r W a b hD hr hW hsupp ha hab
        0 (Nat.ceil z.re + 1) (z.re / 2) (by linarith)
    simp only [Vendor.EulerIter_zero] at hbot htop
    have hf : MellinConvergent (SquareSecondPass.reflectedTransform D r W) z := by
      refine mellinConvergent_of_isBigO_rpow (a := (Nat.ceil z.re + 1 : ℝ)) (b := z.re / 2)
        hf_loc ?_ ?_ ?_ ?_
      · refine Asymptotics.IsBigO.of_bound C ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx1
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
        simpa using htop x hx1
      · have h1 := Nat.le_ceil z.re
        have h2 : z.re < (Nat.ceil z.re : ℝ) + 1 := by linarith
        simpa using h2
      · refine Asymptotics.IsBigO.of_bound C ?_
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
          with x hx hx1
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
        exact hbot x hx hx1.le
      · linarith
    refine ⟨hf, ?_⟩
    apply Vendor.mellin_eq_of_eq_mellinInv (SquareSecondPass.reflectedTransform D r W)
      (reflectedSquareSpectrum D r W) z.re z rfl hf
    · exact (reflectedSquareSpectrum_differentiableOn D r W a b hD hr hW hsupp ha hab).continuousOn.comp_continuous
        (by fun_prop) (fun t => by simpa using hz)
    · exact (ReflectedCoprimeTruncation.kernel_eq_mellinInv D r W a b hD hr hW hsupp ha hab
        z.re 1 hz (by norm_num)).1
    · intro x hx
      exact (ReflectedCoprimeTruncation.kernel_eq_mellinInv D r W a b hD hr hW hsupp ha hab
        z.re x hz hx).2

end DedekindZetaZeroFree.LargeSieve

end
