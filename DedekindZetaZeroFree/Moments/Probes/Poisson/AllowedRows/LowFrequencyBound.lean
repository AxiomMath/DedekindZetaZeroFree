module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.FixedLowContour

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowNormRowBound

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.RowLowContour
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def lowNormRows : Set D.Row := dyadRows D 1 \ principalRows D

theorem lowNormRows_finite : (lowNormRows D).Finite :=
  (ActualRowCount.dyadRows_finite D 1).subset Set.diff_subset

theorem lowNorm_initial_eq (Z : ℝ) (hZ : 2 ≤ Z) :
    J D (lowNormRows D) 4 4 2 Z = JCont D (lowNormRows D) Scales.rightLine Scales.wLine Scales.zLine Z := by
  unfold J JCont
  refine finsum_mem_congr rfl ?_
  intro u hu
  have hne : u.u ≠ 1 := fun h => hu.2 h
  have h1 := FixedLowRowContour.fixedRow_initial_eq D u hne Z hZ
  rw [FixedLowRowContour.J_singleton] at h1
  exact h1

theorem lowNorm_row_bound_exists (u : D.Row) :
    ∃ Cu : ℝ, 0 < Cu ∧ (u ∈ lowNormRows D → ∀ Z : ℝ, 2 ≤ Z →
      ‖FixedLowRowContour.rowIntegral D (FixedLowRowContour.lowRowFactor D) u
          Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
        Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine)) := by
  by_cases hu : u ∈ lowNormRows D
  · have hne : u.u ≠ 1 := fun h => hu.2 h
    obtain ⟨Cu, hC, h⟩ := FixedLowRowContour.fixedRow_low_bound D u hne
    exact ⟨Cu, hC, fun _ => h⟩
  · exact ⟨1, one_pos, fun h => absurd h hu⟩

theorem lowNorm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖J D (lowNormRows D) 4 4 2 Z‖ ≤ C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
  choose c hc0 hc using lowNorm_row_bound_exists D
  have hfin := lowNormRows_finite D
  refine ⟨1 + ∑ u ∈ hfin.toFinset, c u, ?_, ?_⟩
  · have : 0 ≤ ∑ u ∈ hfin.toFinset, c u :=
      Finset.sum_nonneg (fun u _ => (hc0 u).le)
    linarith
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZE : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := Real.rpow_nonneg hZ0.le _
  rw [lowNorm_initial_eq D Z hZ]
  unfold JCont
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine le_trans (norm_sum_le _ _) ?_
  have hsum : ∑ u ∈ hfin.toFinset, c u * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) ≤
      (1 + ∑ u ∈ hfin.toFinset, c u) * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hZE
  refine le_trans (Finset.sum_le_sum (fun u hu => ?_)) hsum
  exact (hc u) ((hfin.mem_toFinset).mp hu) Z hZ

theorem lowNorm_rows_small_k0 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖J D (dyadRows D ((2 : ℝ) ^ (0 : ℕ)) \ principalRows D) 4 4 2 Z‖ ≤
        C * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε) := by
  obtain ⟨C, hC, h⟩ := lowNorm_bound D
  refine ⟨C, hC, fun Z hZ => ?_⟩
  rw [pow_zero]
  refine (h Z hZ).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  have h1 := E_relative
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  linarith

end

end DedekindZetaZeroFree.Quantitative.LowNormRowBound
