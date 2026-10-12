module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.Definitions
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.FiniteLocalUnitsIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
noncomputable section
open MeasureTheory NumberField
open scoped Topology
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem weighted_finitePowerMajorant_integrable
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (ν : Measure (v.adicCompletion F)ˣ) [ν.IsHaarMeasure]
    (M s : ℝ) (hM : 0 < M) (hs : -(1 / 4 : ℝ) < s) :
    Integrable (fun z : (v.adicCompletion F)ˣ => (‖z.val‖ ^ s) *
      finitePowerMajorant M ‖z.val‖) ν := by
  classical

  set g : v.adicCompletion F → ℂ := fun x => if ‖x‖ ≤ M then 1 else 0 with hg
  have hglc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : ‖x‖ ≤ M
    · refine ⟨Metric.ball x M, Metric.isOpen_ball, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_self]
        exact hM
      · intro y hy
        have hy' : ‖y‖ ≤ M := by
          rw [Metric.mem_ball, dist_eq_norm] at hy
          calc ‖y‖ = ‖x + (y - x)‖ := by congr 1; ring
            _ ≤ max ‖x‖ ‖y - x‖ := IsUltrametricDist.norm_add_le_max x (y - x)
            _ ≤ M := max_le hx hy.le
        simp only [hg]
        rw [if_pos hy', if_pos hx]
    · refine ⟨{y | M < ‖y‖}, isOpen_lt continuous_const continuous_norm, ?_, ?_⟩
      · exact not_le.mp hx
      · intro y hy
        simp only [Set.mem_setOf_eq] at hy
        simp only [hg]
        rw [if_neg (not_le.mpr hy), if_neg hx]
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : v.adicCompletion F) M) ?_
    intro x hx
    simp only [hg]
    exact if_neg (by rw [Metric.mem_closedBall, dist_eq_norm] at hx; simpa using hx)
  have hz : 0 < (((s + 1 / 4 : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]; linarith
  have h := DedekindZetaZeroFree.ProbeSheetGlobalIntegrability.finiteUnitsMellin_integrable
    F v g hglc hgc ν (((s + 1 / 4 : ℝ) : ℂ)) hz
  refine h.norm.congr ?_
  filter_upwards with x
  simp only [hg]
  have hnpos : 0 < ‖x.val‖ := norm_pos_iff.mpr (Units.ne_zero x)
  have hnorm : ‖(((‖x.val‖ : ℝ)) : ℂ) ^ ((s + 1 / 4 : ℝ) : ℂ)‖
      = ‖x.val‖ ^ (s + 1 / 4) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.ofReal_re]
  by_cases h : ‖x.val‖ ≤ M
  · rw [if_pos h, one_mul, hnorm, finitePowerMajorant, if_pos h,
      Real.rpow_add hnpos s (1 / 4)]
    rfl
  · rw [if_neg h, zero_mul, norm_zero, finitePowerMajorant, if_neg h, mul_zero]

end
end DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
