module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowZControls
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowWControls
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowContourBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLowRowContour31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem initialRowIntegral_eq_triple (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) :
    initialRowIntegral D u Z = triple D u Scales.rightLine Scales.wLine Scales.zLine Z := by
  rw [← RawLowXiControls31.triple_xi_shift D u hu Z hZ]
  unfold initialRowIntegral triple comparisonVerticalIntegral
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have hξ : (((4 : ℝ) : ℂ) + (t : ℂ) * I).re = 4 := by simp
  rw [← RawLowWControls31.Iwz_w_shift D u hu Z hZ _ hξ]
  unfold Iwz comparisonVerticalIntegral
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  have hw : Scales.wLine ≤ (((4 : ℝ) : ℂ) + (s : ℂ) * I).re ∧
      (((4 : ℝ) : ℂ) + (s : ℂ) * I).re ≤ 4 := by
    simp [Scales.wLine]
    norm_num
  rw [RawLowZControls31.Iz_z_shift D u hu Z hZ _ _ hξ hw]

theorem initialRowIntegral_dyad_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
      ∀ Z : ℝ, 2 ≤ Z →
        ‖initialRowIntegral D u Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 : ℝ) / 25 + ε) := by
  obtain ⟨C, hC, h⟩ := RawLowRowBound31.raw_low_dyad_bound D ε hε
  refine ⟨C, hC, fun u hu U hU h1 h2 Z hZ => ?_⟩
  rw [initialRowIntegral_eq_triple D u hu Z (by linarith)]
  exact h u hu U hU h1 h2 Z hZ

theorem initialRowIntegral_fixed_bound (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖initialRowIntegral D u Z‖ ≤ Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
  obtain ⟨Cu, hC, h⟩ := RawLowRowBound31.raw_low_fixed_row_bound D u hu
  refine ⟨Cu, hC, fun Z hZ => ?_⟩
  rw [initialRowIntegral_eq_triple D u hu Z (by linarith)]
  exact h Z hZ

end

end DedekindZetaZeroFree.Quantitative.RawLowRowContour31
