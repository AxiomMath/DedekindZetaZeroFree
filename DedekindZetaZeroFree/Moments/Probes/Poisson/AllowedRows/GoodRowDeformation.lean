module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.RectangleDeformation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowGoodDeform

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Jtail (C : Set D.Row) (x y v T Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in {t : ℝ | T < |t|}, wzIntegral D u ((x : ℂ) + (t : ℂ) * Complex.I) y v Z

theorem row_good_deform (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ C : Set D.Row, C.Finite →
      (∀ u ∈ C, u.toFrequency.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧ u ∉ exceptionalSet D ρ U) →
      ∀ Z : ℝ, 0 < Z →

        (∀ u ∈ C, ∀ ξ : ℂ, Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine →
          (|ξ.im| ≤ U ^ ρ ∨ ξ.re = Scales.rightLine) →
            (∀ w : ℂ, w.re = Scales.wLine →
              MeasureTheory.Integrable
                (fun τ : ℝ => K D u ξ w ((Scales.zLine : ℂ) + (τ : ℂ) * Complex.I) Z)) ∧
            MeasureTheory.Integrable (fun τ : ℝ =>
              comparisonVerticalIntegral Scales.zLine
                (fun z => K D u ξ ((Scales.wLine : ℂ) + (τ : ℂ) * Complex.I) z Z))) ∧

        (∀ u ∈ C, MeasureTheory.Integrable (fun t : ℝ =>
          wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z)) ∧

        J D C Scales.rightLine Scales.wLine Scales.zLine Z =
          Jcentral D C Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z +
          Jhoriz D C 1 Scales.goodLine Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z +
          Jhoriz D C (-1) Scales.rightLine Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z +
          Jtail D C Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z := by
  obtain ⟨U₁, hU₁, hrect⟩ := DedekindZetaZeroFree.Quantitative.RowRectangleDeformation.row_rectangle_deformation_decomp D A_F ρ hA hconv hρ
  obtain ⟨U₂, hU₂, hpw⟩ :=
    DedekindZetaZeroFree.Quantitative.RowRectangleDeformation.row_pointwise_integrable D A_F ρ hA hconv hρ
  refine ⟨max (max 2 U₁) U₂, le_trans (le_max_left 2 U₁) (le_max_left _ _), ?_⟩
  intro U hU C hC hCmem Z hZ
  have hU1 : U₁ ≤ U := le_trans (le_max_right 2 U₁) (le_trans (le_max_left _ _) hU)
  have hU2 : U₂ ≤ U := le_trans (le_max_right _ _) hU
  have hU2' : 2 ≤ U := le_trans (le_trans (le_max_left 2 U₁) (le_max_left _ _)) hU
  refine ⟨?_, ?_, ?_⟩
  · intro u hu ξ hξ1 hξ2 hξ3
    obtain ⟨h1, h2, h3, h4⟩ := hCmem u hu
    exact hpw U hU2 u h1 h2 h3 h4 Z hZ ξ hξ1 hξ2 hξ3
  · intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := hCmem u hu
    exact DedekindZetaZeroFree.Quantitative.RowRectangleDeformation.row_right_integrable D A_F hconv U hU2' u
      h1 h2 h3 Z hZ
  · have key : ∀ u ∈ C,
        comparisonVerticalIntegral Scales.rightLine (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) =
          (2 * (Real.pi : ℂ))⁻¹ *
              (∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
                wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∫ σ in Scales.goodLine..Scales.rightLine,
                wzIntegral D u ((σ : ℂ) + ((1 * U ^ ρ : ℝ) : ℂ) * Complex.I)
                  Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∫ σ in Scales.rightLine..Scales.goodLine,
                wzIntegral D u ((σ : ℂ) + (((-1) * U ^ ρ : ℝ) : ℂ) * Complex.I)
                  Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ))⁻¹ *
              (∫ t in {t : ℝ | U ^ ρ < |t|},
                wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) := by
      intro u hu
      obtain ⟨h1, h2, h3, h4⟩ := hCmem u hu
      exact hrect U hU1 u h1 h2 h3 h4 Z hZ
    unfold J Jcentral Jhoriz Jtail
    rw [finsum_mem_congr rfl key]
    all_goals simp only [finsum_mem_add_distrib hC]

end

end DedekindZetaZeroFree.Quantitative.RowGoodDeform
