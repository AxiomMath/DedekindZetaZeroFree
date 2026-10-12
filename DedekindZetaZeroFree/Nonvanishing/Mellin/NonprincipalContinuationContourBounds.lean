module

public import DedekindZetaZeroFree.Moments.Comparison.NonprincipalFrequencySum
public import DedekindZetaZeroFree.LFunctions.Hecke.RightCorridorAndCorrectionBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.LeftNumeratorAndUniformStripBounds
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.PrimitiveDenominatorRectanglesAndDyadicCounts
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalFarContourBounds

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.ContinuationSteps

open Filter Asymptotics MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem rapid_of_vertical (f : ℂ → ℂ) (a b : ℝ)
    (h : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B)) :
    comparisonRapidStripDecay f a b := by
  intro B hB
  obtain ⟨C, hC, hbound⟩ := h B hB
  refine ⟨C + 1, by linarith, ?_⟩
  intro s hs
  have hp := hbound s.re hs s.im
  rw [Complex.re_add_im] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))

theorem actual_mellin_weight_contour_inputs (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.W.M {z : ℂ | 2 / 5 - 1 / 100000 < z.re} ∧
    DifferentiableOn ℂ R.W.W1Hat {w : ℂ | 3 / 1000 - 1 / 100000 < w.re} ∧
    comparisonRapidStripDecay R.W.M (2 / 5) 2 ∧
    comparisonRapidStripDecay R.W.W1Hat (3 / 1000) 4 := by
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar w
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, hM, hMd, hW, hWd, _⟩
  change DifferentiableOn ℂ R.W.M {z : ℂ | 0 < z.re} at hM
  change Differentiable ℂ R.W.W1Hat at hW
  refine ⟨hM.mono (fun z hz => by dsimp at hz ⊢; linarith), hW.differentiableOn, ?_, ?_⟩
  · apply rapid_of_vertical
    intro B hB
    exact hMd (2 / 5) 2 B (by norm_num) (by norm_num) hB
  · apply rapid_of_vertical
    intro B hB
    exact hWd (3 / 1000) 4 B (by norm_num) hB

theorem actual_mellin_weight_far_inputs (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.W.M {z : ℂ | 0 < z.re} ∧
    Continuous (fun t : ℝ => R.W.W1Hat ((4 : ℂ) + (t : ℂ) * Complex.I)) ∧
    (∀ N : ℕ, ∃ A : ℝ, 0 < A ∧
      (∀ z : ℂ, z.re ∈ Set.Icc 2 comparisonR₀ →
        ‖R.W.M z‖ ≤ A * (1 + |z.im|) ^ (-(N : ℝ))) ∧
      (∀ t : ℝ, ‖R.W.W1Hat ((4 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (1 + |t|) ^ (-(N : ℝ)))) := by
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar w
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, hM, hMd, hW, hWd, _⟩
  change DifferentiableOn ℂ R.W.M {z : ℂ | 0 < z.re} at hM
  change Differentiable ℂ R.W.W1Hat at hW
  refine ⟨hM, hW.continuous.comp (by fun_prop), ?_⟩
  intro N
  obtain ⟨CM, hCM, hMb⟩ := hMd 2 comparisonR₀ N (by norm_num)
    (by norm_num [comparisonR₀]) (by positivity)
  obtain ⟨CW, hCW, hWb⟩ := hWd 4 4 N (by norm_num) (by positivity)
  refine ⟨CM + CW + 1, by positivity, ?_, ?_⟩
  · intro z hz
    have hb := hMb z.re hz z.im
    rw [Complex.re_add_im] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (by positivity) _))
  · intro t
    have hb := hWb 4 (by simp) t
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (by positivity) _))

theorem nonprincipal_continued_contour_inputs
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (E P : Frequency R → ℂ → ℂ → ℂ → ℂ) (L : Frequency R → ℂ → ℂ)
      (good : ℝ → Frequency R → Prop)
      (Ω Ωleft : Set (ℂ × ℂ × ℂ)) (A_F ρ K : ℝ)
      (D : ℕ → Finset (Frequency R)),
      (∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
        ξ.re = 4 → w.re = 4 → z.re = 2 →
        separatedSeries R u ξ w z = E u ξ w z) ∧
      IsOpen Ω ∧
      (∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
        w ∈ comparisonClosedStrip (3 / 1000) 4 →
        z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R →
        DifferentiableOn ℂ
          (fun p : ℂ × ℂ × ℂ => E u p.1 p.2.1 p.2.2) Ω) ∧
      DifferentiableOn ℂ R.W.M {z : ℂ | 2 / 5 - 1 / 100000 < z.re} ∧
      DifferentiableOn ℂ R.W.W1Hat {w : ℂ | 3 / 1000 - 1 / 100000 < w.re} ∧
      comparisonRapidStripDecay R.W.M (2 / 5) 2 ∧
      comparisonRapidStripDecay R.W.W1Hat (3 / 1000) 4 ∧
      (∃ d : ℝ, 0 ≤ d ∧ ∀ δ : ℝ, 0 < δ →
        ∃ B : ℝ, 0 < B ∧ ∀ u : Frequency R, u ≠ principalFrequency R →
          1 ≤ frequencyNorm R u → ∀ ξ w z : ℂ,
          ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
          w ∈ comparisonClosedStrip (3 / 1000) 4 →
          z ∈ comparisonClosedStrip (2 / 5) 2 →
          ‖E u ξ w z‖ ≤
            B * (frequencyNorm R u) ^ (1 / 2 + δ) * (2 + |w.im|) ^ d) ∧
      IsOpen Ωleft ∧
      (∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
        w.re = 3 / 1000 → z.re = 2 / 5 → (ξ, w, z) ∈ Ωleft) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R →
        DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => P u p.1 p.2.1 p.2.2) Ωleft) ∧
      (∀ (U : ℝ) (u : Frequency R), 1 ≤ U → good U u →
        DifferentiableOn ℂ (L u) {ξ : ℂ | 0 < ξ.re}) ∧
      (∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
        (ξ, w, z) ∈ Ωleft → L u ξ ≠ 0 →
        E u ξ w z = P u ξ w z / L u ξ) ∧
      0 ≤ A_F ∧
      (∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
        ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
          1 ≤ frequencyNorm R u →
          ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
          w.re = 3 / 1000 → z.re = 2 / 5 →
          ‖P u ξ w z‖ ≤ B * (frequencyNorm R u) ^ (1 / 2 + δ) *
            (2 + |ξ.im|) ^ A_F * (2 + |w.im|) ^ A_F * (2 + |z.im|) ^ A_F) ∧
      0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
        ∀ (U : ℝ) (u : Frequency R), Udet ≤ U → good U u →
          U ≤ frequencyNorm R u → frequencyNorm R u < 2 * U →
          ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
            L u ξ ≠ 0 ∧ ‖(L u ξ)⁻¹‖ ≤ B * U ^ δ) ∧
      0 < K ∧
      comparisonFarContourInput (frequencyNorm R) (principalFrequency R) R.W.M
        R.W.W1Hat (E) ∧
      (∀ j : ℕ, comparisonFrequencyDyad (frequencyNorm R) (principalFrequency R) K
        ((2 : ℝ) ^ j) (D j)) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R → ∃ j : ℕ, u ∈ D j) ∧
      (∃ B Uexc : ℝ, 0 < B ∧ 1 ≤ Uexc ∧ ∀ j : ℕ, Uexc ≤ (2 : ℝ) ^ j →
        (((D j).filter (fun u => ¬ good ((2 : ℝ) ^ j) u)).card : ℝ) ≤
          B * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, U, plus, minus, hC, hU, hplus, hminus, hplusSeries, hminusSeries⟩ :=
    NonprincipalContinuation.actual_raw_hecke_rows R
  obtain ⟨Ω, Ωleft, hinitial, hΩ, hstrip, hE, hΩleft, hleftStrip, hP⟩ :=
    NonprincipalContinuation.actual_quotient_corridors R C U plus minus
      hC hU hplus hminus hplusSeries hminusSeries
  obtain ⟨A_F, hA_F, hPbound⟩ :=
    NonprincipalContinuation.actual_left_numerator_bound R C U plus minus
         hC hU hplus hminus hplusSeries hminusSeries
  obtain ⟨good, ρ, K, D, hL, hρ, hρmax, hdet, hK, hD, hcover, hexc⟩ :=
    NonprincipalContinuation.actual_denominator_detector_dyads R U minus
      hU hminus hminusSeries A_F hA_F
  have hEbound := NonprincipalContinuation.actual_right_corridor_bound
    R C U plus minus hC hU hplus hminus hplusSeries hminusSeries
  obtain ⟨hM, hW, hMrapid, hWrapid⟩ := actual_mellin_weight_contour_inputs R
  obtain ⟨hMfar, hWfar, hdecayFar⟩ := actual_mellin_weight_far_inputs R
  obtain ⟨hEcontFar, hEholoFar, hEboundFar⟩ :=
    NonprincipalContinuation.actual_far_euler_inputs R C U plus minus
         hC hU hplus hminus hplusSeries hminusSeries
  refine ⟨NonprincipalContinuation.euler R C U plus minus,
    NonprincipalContinuation.numerator R C U plus, minus, good,
    Ω, Ωleft, A_F, ρ, K, D, hinitial, hΩ, hstrip, hE,
    hM, hW, hMrapid, hWrapid, hEbound, hΩleft, hleftStrip, hP, hL, ?_,
    hA_F, hPbound, hρ, hρmax, hdet, hK, ?_, hD, hcover, hexc⟩
  · intro u ξ w z _ _ _
    rfl
  · exact ⟨hMfar, hWfar, hdecayFar, hEcontFar, hEholoFar, hEboundFar⟩

end DedekindZetaZeroFree.PrincipalMellinComparison.ContinuationSteps
