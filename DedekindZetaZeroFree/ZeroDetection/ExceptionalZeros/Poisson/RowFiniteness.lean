module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRowCount
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.MaximalSieve

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectRows

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem heightMax_nonneg (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) :
    0 ≤ detectorHeightPrefixMaximum F b ω N T := by
  unfold detectorHeightPrefixMaximum
  apply Real.sSup_nonneg
  rintro v ⟨t, _, rfl⟩
  unfold detectorPrefixMaximum
  apply Real.sSup_nonneg
  rintro v ⟨y, _, rfl⟩
  positivity

open DedekindZetaZeroFree.Quantitative.DetectorSieve in

theorem card_dyad (U M T δ : ℝ) (b : Ideal (𝓞 F) → ℂ) :
    {u : D.Row | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T}.Finite ∧
    (({u : D.Row | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T}.ncard : ℕ) : ℝ)
      * δ ≤ rowMaximalSum D U M T b := by
  have hdy : ∀ u : D.Row, U ≤ D.q u → D.q u < 2 * U →
      u ∈ PoissonKernel.dyadRows D U := fun u h1 h2 => ⟨h1, h2⟩
  have hfin : {u : D.Row | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T}.Finite :=
    (ActualRowCount.dyadRows_finite D U).subset (fun u hu => hdy u hu.2.1 hu.2.2.1)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hsum : rowMaximalSum D U M T b = ∑ u ∈ (ActualRowCount.dyadRows_finite D U).toFinset,
      (if FixedData.Row.u u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
        detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T else 0) := by
    unfold rowMaximalSum
    apply finsum_eq_sum_of_support_subset
    intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    split_ifs at hu with hc
    · exact hdy u hc.2.1 hc.2.2
    · exact absurd rfl hu
  rw [hsum]
  calc ((hfin.toFinset.card : ℕ) : ℝ) * δ = ∑ u ∈ hfin.toFinset, δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ hfin.toFinset,
        (if FixedData.Row.u u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
          detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T else 0) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Set.Finite.mem_toFinset] at hu
        split_ifs with hc
        · exact hu.2.2.2
        · exact absurd ⟨hu.1, hu.2.1, hu.2.2.1⟩ hc
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          rw [Set.Finite.mem_toFinset] at hu
          exact (ActualRowCount.dyadRows_finite D U).mem_toFinset.mpr (hdy u hu.2.1 hu.2.2.1)
        · intro u _ _
          split_ifs
          · exact heightMax_nonneg _ _ _ _
          · exact le_rfl

theorem dyadRows_finite (U : ℝ) : (PoissonKernel.dyadRows D U).Finite :=
  ActualRowCount.dyadRows_finite D U

end

end DedekindZetaZeroFree.Quantitative.DetectRows
