module

public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.FrequencyCount

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDetector31

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detector_exists (D : FixedData S η) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ RawConvexityExponent D A ∧ HeightSpec D A ρ ∧
      ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (FixedData.rawExceptionalSet D ρ U).Finite ∧
          ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α := by
  obtain ⟨A, ρ, hA, hc, hρ⟩ := height_exists D
  exact ⟨A, ρ, hA, hc, hρ, DedekindZetaZeroFree.Quantitative.RawDetectorCount31.rawExceptionalSet_card D A ρ hA hρ⟩

theorem detector_exists_prefix (D : FixedData S η) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ RawConvexityExponent D A ∧ HeightSpec D A ρ ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        ∀ u ∈ FixedData.rawExceptionalSet D ρ U, ∀ s : ℂ,
          DetectorDef.IsLZero (FixedData.primMinus D u) s → DetectorDef.σ₀ ≤ s.re → s.re ≤ 1 →
          |s.im| ≤ 4 * U ^ ρ →
          ∃ N y : ℝ, U ^ DetectorDef.qExp / 2 < N ∧ N ≤ U ^ DetectorDef.r' ∧ N ≤ y ∧
            y ≤ 2 * N ∧
            c₁ / Real.log U ≤ ‖DetectorPrefix.prefixSum F U (FixedData.primMinus D u).character
              s.im N y‖) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (FixedData.rawExceptionalSet D ρ U).Finite ∧
          ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α := by
  obtain ⟨A, ρ, hA, hc, hρ⟩ := height_exists D
  exact ⟨A, ρ, hA, hc, hρ, detector_prefix D A ρ hρ,
    DedekindZetaZeroFree.Quantitative.RawDetectorCount31.rawExceptionalSet_card D A ρ hA hρ⟩

end DedekindZetaZeroFree.Quantitative.RawDetector31
