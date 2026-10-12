module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetContinuityAndDifferentiation

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

theorem sheet_log_derivative_bounds
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (w : InfinitePlace F)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    (σ : ℝ) (k : ℕ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      Integrable (fun t => logDerivativeRaw A w k
        (ProbeWeight.fourier F A.Sf e μ W0) (sheetPointRaw A T t).val) dt ∧
      (∫ t, ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val‖ ∂dt) ≤ C * T ^ (-σ) := by
  letI : MeasurableSpace A.G1 := borel _
  letI : BorelSpace A.G1 := ⟨rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_gt σ
  obtain ⟨M, R, hM, hR, hbound⟩ :=
    raw_fourier_log_derivative_envelope A e he hne μ hμ w k N W0 hW0 hcompact
  obtain ⟨C, hC, hsheet⟩ := raw_radial_envelope_sheet_bounds A dt hdt σ N R hσ hN hR
  have hcontinuous := raw_fourier_log_derivative_continuous A e he μ hμ w k W0 hW0 hcompact
  refine ⟨M * C, mul_nonneg hM hC, ?_⟩
  intro T hT
  obtain ⟨hB, hBbound⟩ := hsheet T hT
  have hmeas : AEStronglyMeasurable (fun t => logDerivativeRaw A w k
      (ProbeWeight.fourier F A.Sf e μ W0) (sheetPointRaw A T t).val) dt := by
    apply Continuous.aestronglyMeasurable
    have hparam : Continuous (fun t : A.G1 =>
        ((⟨T, hT⟩ : {T : ℝ // 0 < T}), t)) :=
      continuous_const.prodMk continuous_id
    have hs : Continuous (fun t : A.G1 => (sheetPointRaw A T t).val) :=
      Continuous.comp
        (g := fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val)
        (f := fun t : A.G1 => ((⟨T, hT⟩ : {T : ℝ // 0 < T}), t))
        (raw_sheet_continuous A) hparam
    exact Continuous.comp
      (g := logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0))
      (f := fun t : A.G1 => (sheetPointRaw A T t).val) hcontinuous hs
  have hmajorant := hB.const_mul M
  have hbound_ae : ∀ᵐ t ∂dt,
      ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val‖ ≤
      M * radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val :=
    Filter.Eventually.of_forall fun t => hbound (sheetPointRaw A T t).val
  have hint := hmajorant.mono' hmeas hbound_ae
  refine ⟨hint, ?_⟩
  calc
    (∫ t, ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val‖ ∂dt) ≤
        ∫ t, M * radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val ∂dt :=
      integral_mono_ae hint.norm hmajorant hbound_ae
    _ = M * (∫ t, radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val ∂dt) :=
      integral_const_mul _ _
    _ ≤ M * (C * T ^ (-σ)) := mul_le_mul_of_nonneg_left hBbound hM
    _ = (M * C) * T ^ (-σ) := (mul_assoc _ _ _).symm

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
