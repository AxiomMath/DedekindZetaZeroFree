module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowContourRow

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowLowContour

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowCont (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

def JCont (C : Set D.Row) (x y v Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, comparisonVerticalIntegral x (fun ξ =>
    comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => kernelWith D (rowCont D) u ξ w z Z)))

theorem E_relative :
    Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine - Scales.mainExponent = -2552 / 10000 + Scales.contourOffset := by
  unfold Scales.kernelExponent Scales.rightLine Scales.contourOffset Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.mainExponent Scales.wLine Scales.zLine
  norm_num

theorem J_initial_eq (U Z : ℝ) (hU : 2 ≤ U) (hZ : 2 ≤ Z) (C : Set D.Row)
    (hC : C ⊆ {u : D.Row | u.u ≠ 1} ∩ dyadRows D U) (hfin : C.Finite) :
    J D C 4 4 2 Z = JCont D C Scales.rightLine Scales.wLine Scales.zLine Z := by
  unfold J JCont
  refine finsum_mem_congr rfl ?_
  intro u hu
  exact DedekindZetaZeroFree.Quantitative.RowLowContourRow.row_initial_eq D u (hC hu).1 U Z hU hZ (hC hu).2

theorem JCont_bound (Ccount β : ℝ) (hCcount : 0 < Ccount) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ (U Z : ℝ), 2 ≤ U → 2 ≤ Z → ∀ C : Set D.Row,
      C ⊆ {u : D.Row | u.u ≠ 1} ∩ dyadRows D U → C.Finite →
      (C.ncard : ℝ) ≤ Ccount * U ^ β →
        ‖JCont D C Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
          Cε * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (β + 1 / 25 + ε) := by
  obtain ⟨C₀, hC₀, h⟩ := DedekindZetaZeroFree.Quantitative.RowLowContourRow.row_bound D ε hε
  refine ⟨Ccount * C₀, mul_pos hCcount hC₀, ?_⟩
  intro U Z hU hZ C hC hfin hcard
  have hU0 : 0 < U := by linarith
  have hZ0 : 0 < Z := by linarith
  have hB0 : 0 ≤ C₀ * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 25 + ε) := by
    positivity
  unfold JCont
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _
    (C₀ * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 25 + ε)) ?_) ?_
  · intro u hu
    have hu' : u ∈ C := hfin.mem_toFinset.mp hu
    obtain ⟨h1, h2⟩ : U ≤ D.q u ∧ D.q u < 2 * U := (hC hu').2
    exact h u (hC hu').1 U Z hU hZ h1 h2
  · rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card C hfin]
    calc (C.ncard : ℝ) * (C₀ * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 25 + ε))
        ≤ (Ccount * U ^ β) *
          (C₀ * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (1 / 25 + ε)) :=
          mul_le_mul_of_nonneg_right hcard hB0
      _ = Ccount * C₀ * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
          U ^ (β + 1 / 25 + ε) := by
          have e : U ^ (β + 1 / 25 + ε) = U ^ β * U ^ (1 / 25 + ε) := by
            rw [← Real.rpow_add hU0]; congr 1; ring
          rw [e]; ring

end

end DedekindZetaZeroFree.Quantitative.RowLowContour
