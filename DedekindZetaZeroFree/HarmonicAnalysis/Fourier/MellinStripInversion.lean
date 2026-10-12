module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.MellinStripIntegrability
public import DedekindZetaZeroFree.Analysis.ContourIntegration.ExponentialStripGrowth
public import DedekindZetaZeroFree.Analysis.VerticalStripBounds

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection

theorem strip_inverse_api (K : ℂ → ℂ) (a b : ℝ)
    (hhol : ∀ s : ℂ, a < s.re → s.re < b → DifferentiableAt ℂ K s)
    (hrapid : ∀ u v : ℝ, a < u → u ≤ v → v < b → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, u ≤ σ → σ ≤ v → 1 ≤ |t| →
        (1 + |t|) ^ N * ‖K ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) :
    (∀ c d x : ℝ, a < c → c < b → a < d → d < b → 0 < x →
      mellinInv c K x = mellinInv d K x) ∧
    (∀ c : ℝ, a < c → c < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
        ‖mellinInv c K x‖ ≤ C * Real.rpow x (-c)) := by
  open MeasureTheory in
  have hshift : ∀ c d x : ℝ, a < c → c ≤ d → d < b → 0 < x →
      mellinInv c K x = mellinInv d K x := by
    intro c d x hac hcd hdb hx
    have hcb : c < b := lt_of_le_of_lt hcd hdb
    have had : a < d := lt_of_lt_of_le hac hcd
    haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) :=
      (differentiable_const_cpow_of_neZero (x : ℂ)).comp differentiable_neg
    have hKcont : ContinuousOn K {s : ℂ | s.re ∈ Set.Icc c d} := by
      intro s hs
      exact (hhol s (lt_of_lt_of_le hac hs.1)
        (lt_of_le_of_lt hs.2 hdb)).continuousAt.continuousWithinAt
    obtain ⟨B, hB, hbound⟩ := Subquadratic.strip_bound_of_tail_bound K hKcont (by
      obtain ⟨C, hC, htail⟩ := hrapid c d hac hcd hdb 0
      exact ⟨C, hC, fun σ t hσ ht => by simpa using htail σ t hσ.1 hσ.2 ht⟩)
    have hrpow : ∀ σ : ℝ, c ≤ σ → σ ≤ d →
        Real.rpow x (-σ) ≤ max (Real.rpow x (-c)) (Real.rpow x (-d)) := by
      intro σ hcσ hσd
      rcases le_total 1 x with hx1 | hx1
      · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans
          (le_max_right _ _)
    rw [mellinInv_eq_verticalIntegral c K hx, mellinInv_eq_verticalIntegral d K hx]
    refine integral_eq_of_exponential_strip_growth hcd
      (fun s => (x : ℂ) ^ (-s) * K s) ?_ ?_ ?_ ?_
    · intro s hs1 hs2
      exact hpow.differentiableAt.mul
        (hhol s (lt_of_lt_of_le hac hs1) (lt_of_le_of_lt hs2 hdb))
    · exact (strip_integrability K a b hhol hrapid c hac hcb).2 x hx
    · exact (strip_integrability K a b hhol hrapid d had hdb).2 x hx
    · refine ⟨0, max (Real.rpow x (-c)) (Real.rpow x (-d)) * B, le_rfl,
        mul_nonneg ((Real.rpow_nonneg hx.le _).trans (le_max_left _ _)) hB, ?_⟩
      intro σ hσ t
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_self, add_zero, Real.exp_zero, one_mul, zero_mul, mul_one]
      exact mul_le_mul (hrpow σ hσ.1 hσ.2) (hbound σ t hσ) (norm_nonneg _)
        ((Real.rpow_nonneg hx.le _).trans (le_max_left _ _))
  constructor
  · intro c d x hac hcb had hdb hx
    rcases le_total c d with hcd | hdc
    · exact hshift c d x hac hcd hdb hx
    · exact (hshift d c x had hdc hcb hx).symm
  · intro c hac hcb
    let P : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖
    let L : ℝ := ∫ t : ℝ, ‖K ((c : ℂ) + (t : ℂ) * Complex.I)‖
    have hP : 0 ≤ P := norm_nonneg _
    have hL : 0 ≤ L := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    refine ⟨P * L, mul_nonneg hP hL, ?_⟩
    intro x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hnorm : (∫ t : ℝ, ‖(x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
        K ((c : ℂ) + (t : ℂ) * Complex.I)‖) = Real.rpow x (-c) * L := by
      simp_rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_self, add_zero]
      exact MeasureTheory.integral_const_mul _ _
    rw [mellinInv_eq_verticalIntegral c K hx, verticalIntegral, norm_mul]
    calc
      P * ‖∫ t : ℝ, (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
          K ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ P * (∫ t : ℝ, ‖(x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)) *
            K ((c : ℂ) + (t : ℂ) * Complex.I)‖) :=
        mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _) hP
      _ = (P * L) * Real.rpow x (-c) := by rw [hnorm]; ring

end DedekindZetaZeroFree.LargeSieve.Vendor.LogReflection

end
