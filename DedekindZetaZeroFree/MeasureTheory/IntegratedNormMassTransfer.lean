module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

namespace DedekindZetaZeroFree.ProbeJointNormMassTransfer
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

theorem norm_mass_transfer {T I O : Type*} [MeasurableSpace T]
    (μ : Measure T) (D : Set T) (f : I → T → ℂ) (g : O → T → ℂ)
    (hf : ∀ i, IntegrableOn (f i) D μ)
    (hg : ∀ o, Integrable (g o) μ)
    (hs : Summable (fun o => ∫ t, ‖g o t‖ ∂μ))
    (he : (∑' i, ∫⁻ t in D, ENNReal.ofReal ‖f i t‖ ∂μ) =
      ∑' o, ∫⁻ t, ENNReal.ofReal ‖g o t‖ ∂μ) :
    Summable (fun i => ∫ t in D, ‖f i t‖ ∂μ) ∧
      (∑' i, ∫ t in D, ‖f i t‖ ∂μ) = ∑' o, ∫ t, ‖g o t‖ ∂μ := by

  have hg_int : ∀ o, ∫⁻ t, ENNReal.ofReal ‖g o t‖ ∂μ
      = ENNReal.ofReal (∫ t, ‖g o t‖ ∂μ) := by
    intro o
    simpa only [ofReal_norm] using (ofReal_integral_norm_eq_lintegral_enorm (hg o)).symm
  have hb_nonneg : ∀ o, 0 ≤ ∫ t, ‖g o t‖ ∂μ :=
    fun o => integral_nonneg fun t => norm_nonneg _
  have hgsum : (∑' o, ∫⁻ t, ENNReal.ofReal ‖g o t‖ ∂μ)
      = ENNReal.ofReal (∑' o, ∫ t, ‖g o t‖ ∂μ) := by
    simp_rw [hg_int]
    exact (ENNReal.ofReal_tsum_of_nonneg hb_nonneg hs).symm
  have hf_int : ∀ i, ∫⁻ t in D, ENNReal.ofReal ‖f i t‖ ∂μ
      = ENNReal.ofReal (∫ t in D, ‖f i t‖ ∂μ) := by
    intro i
    simpa only [ofReal_norm] using (ofReal_integral_norm_eq_lintegral_enorm (hf i)).symm
  have ha_nonneg : ∀ i, 0 ≤ ∫ t in D, ‖f i t‖ ∂μ :=
    fun i => integral_nonneg fun t => norm_nonneg _

  have hA : (∑' i, ENNReal.ofReal (∫ t in D, ‖f i t‖ ∂μ))
      = ENNReal.ofReal (∑' o, ∫ t, ‖g o t‖ ∂μ) := by
    have h1 : (∑' i, ∫⁻ t in D, ENNReal.ofReal ‖f i t‖ ∂μ)
        = ∑' i, ENNReal.ofReal (∫ t in D, ‖f i t‖ ∂μ) := by
      simp_rw [hf_int]
    rw [← h1, he, hgsum]

  have hA_ne : (∑' i, ENNReal.ofReal (∫ t in D, ‖f i t‖ ∂μ)) ≠ ∞ := by
    rw [hA]; exact ENNReal.ofReal_ne_top

  let v : I → ℝ≥0 := fun i => (∫ t in D, ‖f i t‖ ∂μ).toNNReal
  have hv : Summable v := by
    refine ENNReal.tsum_coe_ne_top_iff_summable.1 ?_
    rw [show (∑' i, (v i : ℝ≥0∞)) = ∑' i, ENNReal.ofReal (∫ t in D, ‖f i t‖ ∂μ) from rfl]
    exact hA_ne
  have ha : Summable (fun i => ∫ t in D, ‖f i t‖ ∂μ) :=
    (NNReal.summable_coe.2 hv).congr (fun i => Real.coe_toNNReal _ (ha_nonneg i))

  have hfin : ENNReal.ofReal (∑' i, ∫ t in D, ‖f i t‖ ∂μ)
      = ENNReal.ofReal (∑' o, ∫ t, ‖g o t‖ ∂μ) := by
    rw [ENNReal.ofReal_tsum_of_nonneg ha_nonneg ha, hA]
  exact ⟨ha, (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha_nonneg)
    (tsum_nonneg hb_nonneg)).1 hfin⟩

end
end DedekindZetaZeroFree.ProbeJointNormMassTransfer
