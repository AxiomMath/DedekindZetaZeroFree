module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization

@[expose] public section

namespace DedekindZetaZeroFree.TateSLocalMeasurability
noncomputable section
open scoped Classical NumberField ENNReal
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem pi_measure_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  letI : ∀ i, SigmaFinite (c i • μ i) := fun i => by
    rw [← ENNReal.coe_toNNReal (hc i)]
    exact SMul.sigmaFinite _
  apply Measure.pi_eq
  intro t _
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

theorem finite_map_mul (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ((v : S) → v.val.adicCompletion F)ˣ) :
    Measure.map (fun x : ((v : S) → v.val.adicCompletion F) => g.val * x)
        (Measure.pi (fun v : S => localNormalizedHaar F v.val)) =
      (ENNReal.ofReal (∏ v : S, ‖g.val v‖))⁻¹ •
        Measure.pi (fun v : S => localNormalizedHaar F v.val) := by
  have hgv (v : S) : g.val v * (↑g⁻¹ : (v : S) → v.val.adicCompletion F) v = 1 := by
    have h := congr_fun (Units.mul_inv g) v
    simpa using h
  have hne (v : S) : g.val v ≠ 0 := fun h0 => by
    have := hgv v
    rw [h0, zero_mul] at this
    exact one_ne_zero this.symm
  let c : (v : S) → (v.val.adicCompletion F)ˣ := fun v => Units.mk0 (g.val v) (hne v)
  haveI : ∀ v : S, SigmaFinite
      ((localNormalizedHaar F v.val).map (fun x => g.val v * x)) :=
    fun v => (Homeomorph.mulLeft₀ (g.val v) (hne v)).toMeasurableEquiv.sigmaFinite_map
  rw [show (fun x : ((v : S) → v.val.adicCompletion F) => g.val * x)
        = (fun x v => g.val v * x v) from rfl]
  rw [Measure.pi_map_pi
    (μ := fun v : S => localNormalizedHaar F v.val)
    (f := fun v x => g.val v * x)
    (fun v => (continuous_const.mul continuous_id).measurable.aemeasurable)]
  simp_rw [show ∀ v : S, (localNormalizedHaar F v.val).map (fun x => g.val v * x) =
      (ENNReal.ofReal ‖g.val v‖)⁻¹ • localNormalizedHaar F v.val from fun v =>
    CompletionHaarModule.map_mul F v.val (localNormalizedHaar F v.val) (c v)]
  rw [pi_measure_smul (fun v : S => localNormalizedHaar F v.val)
    (fun v : S => (ENNReal.ofReal ‖g.val v‖)⁻¹) (fun v => ENNReal.inv_ne_top.mpr (by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact norm_pos_iff.mpr (hne v)))]
  have hinv : (∏ v : S, (ENNReal.ofReal ‖g.val v‖)⁻¹) =
      (∏ v : S, ENNReal.ofReal ‖g.val v‖)⁻¹ := by
    simpa using (ENNReal.prod_inv_distrib (s := Finset.univ)
      (f := fun v : S => ENNReal.ofReal ‖g.val v‖)
      (fun i _ j _ _ => Or.inl (ENNReal.ofReal_ne_zero_iff.mpr
        (norm_pos_iff.mpr (hne i))))).symm
  have hscalar : (∏ v : S, (ENNReal.ofReal ‖g.val v‖)⁻¹) =
      (ENNReal.ofReal (∏ v : S, ‖g.val v‖))⁻¹ := by
    rw [hinv, ← ENNReal.ofReal_prod_of_nonneg (fun v _ => norm_nonneg (g.val v))]
  rw [hscalar]

end
end DedekindZetaZeroFree.TateSLocalMeasurability
