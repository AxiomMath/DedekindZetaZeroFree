module

public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection

theorem strip_integrability (K : ℂ → ℂ) (a b : ℝ)
    (hhol : ∀ s : ℂ, a < s.re → s.re < b → DifferentiableAt ℂ K s)
    (hrapid : ∀ u v : ℝ, a < u → u ≤ v → v < b → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
        (1 + |t|) ^ N * ‖K ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (c : ℝ) (hac : a < c) (hcb : c < b) :
    Complex.VerticalIntegrable K c volume ∧
    ∀ x : ℝ, 0 < x →
      Integrable (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
        K ((c : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hline : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    intro t; simp
  have hcont : Continuous (fun t : ℝ => K ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hlin : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) t :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    exact ContinuousAt.comp (g := K)
      (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) (x := t)
      ((hhol _ (by rw [hline]; exact hac) (by rw [hline]; exact hcb)).continuousAt) hlin
  obtain ⟨C, hC0, hdec⟩ := hrapid c c hac le_rfl hcb 2
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hcont.continuousOn (s := Set.Icc (-1) 1))
  set K0 : ℝ := 4 * (C + max C1 0) with hK
  have hK0 : 0 ≤ K0 := by rw [hK]; positivity
  have hstep : ∀ t : ℝ, ((1 + |t|) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
    intro t
    have hle : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t]
    simpa only [one_div] using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1 + t ^ 2 by positivity) hle
  have hcase : ∀ t : ℝ,
      ‖K ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K0 * ((1 + |t|) ^ 2)⁻¹ := by
    intro t
    by_cases ht : 1 ≤ |t|
    · have hb := hdec c t le_rfl le_rfl ht
      have hpos : (0 : ℝ) < (1 + |t|) ^ 2 := by positivity
      have h2 : ‖K ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * ((1 + |t|) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith [hb]
      refine h2.trans ?_
      have hCK : C ≤ K0 := by rw [hK]; nlinarith [hC0, le_max_right C1 0]
      exact mul_le_mul_of_nonneg_right hCK (by positivity)
    · have ht' : |t| < 1 := not_le.mp ht
      have hb := hC1 t (by
        rw [Set.mem_Icc]
        exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
      refine hb.trans ?_
      have h4 : (1 + |t|) ^ 2 ≤ 4 := by
        nlinarith [abs_nonneg t, sq_abs t, sq_nonneg t, le_of_lt ht']
      have hinv : (4 : ℝ)⁻¹ ≤ ((1 + |t|) ^ 2)⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (show (0 : ℝ) < (1 + |t|) ^ 2 by positivity) h4
      have h1 : K0 * (4 : ℝ)⁻¹ ≤ K0 * ((1 + |t|) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hK0
      have h2 : K0 * (4 : ℝ)⁻¹ = C + max C1 0 := by rw [hK]; ring
      calc C1 ≤ max C1 0 := le_max_left _ _
        _ ≤ C + max C1 0 := by linarith [hC0]
        _ = K0 * (4 : ℝ)⁻¹ := h2.symm
        _ ≤ K0 * ((1 + |t|) ^ 2)⁻¹ := h1
  have hbound_all : ∀ t : ℝ,
      ‖K ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K0 * (1 + t ^ 2)⁻¹ :=
    fun t => (hcase t).trans (mul_le_mul_of_nonneg_left (hstep t) hK0)
  have hvert : Complex.VerticalIntegrable K c volume := by
    show Integrable (fun y : ℝ => K ((c : ℂ) + (y : ℂ) * Complex.I)) volume
    exact Integrable.mono' (integrable_inv_one_add_sq.const_mul K0) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound_all)
  refine ⟨hvert, fun x hx => ?_⟩
  haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (ne_of_gt hx)⟩
  have hcontx : Continuous (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))) :=
    (continuous_const_cpow (x : ℂ)).comp (by continuity)
  refine Integrable.bdd_mul (c := x ^ (-c)) hvert hcontx.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hre : (-((c : ℂ) + (t : ℂ) * Complex.I)).re = -c := by simp
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]

end DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection

end
