module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexExceptionalFunctional
public import DedekindZetaZeroFree.Adeles.Characters.StandardComplexCharacter
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.Definitions
public import DedekindZetaZeroFree.Analysis.Complex.LogarithmicRadialDerivatives
import DedekindZetaZeroFree.Theta.Whittaker.InducedAmplitudePowerBounds
import DedekindZetaZeroFree.Theta.Profiles.MixedAmplitudeJetBounds
import DedekindZetaZeroFree.Theta.Whittaker.RotatedFirstRootRapidDecay

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCplxJacquetFunctional

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPCplxRotatedRapidDecay KPCplxRotatedKernelEstimates MeasureTheory
open TraceHaarTransport ThetaArchInducedMajorant
open ThetaRawSheetEnvelope.WeightedWhittakerSheets

public def standardWeylJacquet (κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (y : ℂˣ) : ℂ :=
  (κ : ℂ) * KPCplxJacquetFunctional.jacquetIntegral standardComplexParameter
    (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk (diagonal y * weyl)) f)

private lemma third_min_le_quarter_min (r A : ℝ) (hr : 0 < r) (hA : 0 < A) :
    min (r ^ (1 / 3 : ℝ)) (r ^ (-A)) ≤ min (r ^ (1 / 4 : ℝ)) (r ^ (-A)) := by
  by_cases h : r ≤ 1
  · exact min_le_min_right _ (Real.rpow_le_rpow_of_exponent_ge hr h (by norm_num))
  · have h1 : 1 ≤ r := le_of_lt (lt_of_not_ge h)
    have hp : r ^ (-A) ≤ r ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    rw [min_eq_right hp]
    exact min_le_right _ _

public theorem exists_norm_iterate_logarithmicDerivative_standardWeylJacquet_le (κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (j : ℕ), j ≤ 2 → ∀ y : ℂˣ,
      ‖((logarithmicDerivative^[j]) (standardWeylJacquet κ f)) y‖ ≤
        D * archPowerMajorant A (‖(y : ℂ)‖ ^ 2) := by
  have hf := hasInducedAmplitudeEstimates_of_pointwise_bounds standardComplexParameter κ f
    (ThetaArchInducedMajorant.norm_amplitudeDerivative_le _ _ _)
  have hF : ∀ (u : ℂˣ) (ρ : ℝ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      standardWeylJacquet κ f (radialUnit ρ u) = ∫ x : ℂ,
        Complex.exp (-Complex.I * ((characterScale standardComplexParameter * x.re : ℝ) : ℂ)) *
          rotatedAmplitude standardComplexParameter κ f u ρ x ∂euclideanArea := by
    intro u ρ _ _
    exact rotated_jacquet_integral standardComplexParameter κ f u ρ
  have hb : ∀ j : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂˣ,
      ‖((logarithmicDerivative^[j.val]) (standardWeylJacquet κ f)) y‖ ≤
        C * archPowerMajorant A (‖(y : ℂ)‖ ^ 2) := by
    intro j
    obtain ⟨C, hC, hb⟩ := radial_min_bound_of_power_bounds
      (fun _ : Unit => ((logarithmicDerivative^[j.val]) (standardWeylJacquet κ f))) A hA
      (fun h => by
        obtain ⟨D, hD, hd⟩ := ThetaArchInducedMajorant.exists_norm_iterate_logarithmicDerivative_le
          standardComplexParameter κ f hf (standardWeylJacquet κ f) hF j.val h (by omega)
        exact ⟨D, hD, fun _ y => hd y⟩)
    refine ⟨C, hC, fun y => (hb () y).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (third_min_le_quarter_min _ A
        (pow_pos (norm_pos_iff.mpr y.ne_zero) 2) hA) hC
  choose C hC hb using hb
  refine ⟨∑ j : Fin 3, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j hj y
  let i : Fin 3 := ⟨j, by omega⟩
  have hle : C i ≤ ∑ k : Fin 3, C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ i)
  exact (hb i y).trans (mul_le_mul_of_nonneg_right hle
    (archPowerMajorant_nonneg A _ (sq_nonneg _)))

end DedekindZetaZeroFree.KPCplxJacquetFunctional

end
