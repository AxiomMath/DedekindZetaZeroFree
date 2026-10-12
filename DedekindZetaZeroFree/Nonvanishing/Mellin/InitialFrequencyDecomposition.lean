module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

noncomputable section
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev Frequency (R : PrincipalMellin.ActualRecipe S η) :=
  {u // u ∈ R.probe.frequencies.reps}

def principalFrequency (R : PrincipalMellin.ActualRecipe S η) : Frequency R :=
  ⟨⟨1, one_ne_zero⟩, R.probe.frequencies.containsOne⟩

def frequencyNorm (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) : ℝ :=
  (FiniteTransform.exteriorNorm R.A.R.toSubring u.val.val : ℝ)

def separatedSeries (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) (ξ w z : ℂ) : ℂ :=
  NormalizedProbe.principalSeparatedMellinSeries R.A R.σ R.target R.traceBad
    R.probe u ξ w z

def initialFrequencyIntegral (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) (Z : ℝ) : ℂ :=
  comparisonFrequencyIntegral (frequencyNorm R) R.W.M R.W.W1Hat
    (separatedSeries R) {u} Z 4 4 2

def principalInitialIntegral (R : PrincipalMellin.ActualRecipe S η)
    (Z : ℝ) : ℂ :=
  initialFrequencyIntegral R (principalFrequency R) Z

def nonprincipalInitialIntegral (R : PrincipalMellin.ActualRecipe S η)
    (Z : ℝ) : ℂ :=
  ∑' u : {u : Frequency R // u ≠ principalFrequency R},
    initialFrequencyIntegral R u.val Z

open MeasureTheory

private lemma weight_eq (R : PrincipalMellin.ActualRecipe S η) (Z : ℝ) (hZ : 0 < Z)
    (ξ w z : ℂ) :
    NormalizedProbe.tripleMellinWeight R.probe (Z ^ (9 / 10 : ℝ))
      (Z ^ (133 / 1000 : ℝ)) Z ξ w z =
    comparisonRealPower Z ((comparisonA : ℂ) / 2 + ξ - 1 +
      (comparisonH₀ : ℂ) * z + (comparisonB : ℂ) * (w - 1)) *
      Complex.exp ((ξ + z - 1)^2) * R.W.M z * R.W.W1Hat w := by
  simp only [NormalizedProbe.tripleMellinWeight, PrincipalMellin.ActualRecipe.W,
    NormalizedProbe.principalMellinWeights, comparisonMellinWeightsFromProbe]
  unfold comparisonRealPower
  rw [Real.log_rpow hZ, Real.log_rpow hZ]
  simp only [Complex.ofReal_mul]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 4
  norm_num [comparisonA, comparisonH₀, comparisonB]
  ring
private lemma exterior_countable (R : PrincipalMellin.ActualRecipe S η) :
    Countable R.A.Exterior := by
  have he := (ProbeExteriorIdealCount.ideal_norm_summable F R.A.cS 2 (by norm_num)).countable_support
  have hall : Function.support (fun I : R.A.Exterior => (idealNorm I.val) ^ (-(2 : ℝ))) =
      Set.univ := by
    ext I
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (R.A.exteriorNorm_pos I) _).ne'
  rw [hall] at he
  exact Set.countable_univ_iff.mp he

private lemma integral_three {f : (ℝ × ℝ × ℝ) → ℂ} (hf : Integrable f) :
    (∫ t : ℝ × ℝ × ℝ, f t) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x, y, z) := by
  rw [MeasureTheory.Measure.volume_eq_prod] at hf
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_right_ae] with x hx
  rw [MeasureTheory.Measure.volume_eq_prod] at hx
  exact integral_prod _ hx

theorem initial_frequency_decomposition (R : PrincipalMellin.ActualRecipe S η)
    (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun u : {u : Frequency R // u ≠ principalFrequency R} =>
      ‖initialFrequencyIntegral R u.val Z‖) ∧
    R.I Z = principalInitialIntegral R Z + nonprincipalInitialIntegral R Z := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable R.A.Exterior := exterior_countable R
  letI : Countable (ExteriorSquarefreeIdeal R.A.cS) := by
    change Countable {I : R.A.Exterior // Squarefree I.val}
    infer_instance
  let X := Z ^ (9 / 10 : ℝ)
  let Y := Z ^ (133 / 1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  let f := NormalizedProbe.initialTripleMellinSummand R.probe X Y Z
  obtain ⟨_, hint, hsum⟩ :=
    NormalizedProbe.tripleMellin_integrable_majorant R.probe X Y Z hX hY hZ
  obtain ⟨hwhole, hinter⟩ :=
    NormalizedProbe.tripleMellin_sum_integral_interchange R.probe X Y Z hX hY hZ
  have hsint : Summable (fun i : NormalizedProbe.MellinSeriesIndex R.probe =>
      ∫ t : ℝ × ℝ × ℝ, f i t) :=
    hsum.of_norm_bounded (fun i => norm_integral_le_integral_norm _)
  have hrow (u : Frequency R) (t : ℝ × ℝ × ℝ) :
      (∑' a, f (u, a) t) =
        comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat
          (separatedSeries R) Z u (NormalizedProbe.initialMellinPoint t).1
          (NormalizedProbe.initialMellinPoint t).2.1
          (NormalizedProbe.initialMellinPoint t).2.2 := by
    dsimp [f, NormalizedProbe.initialTripleMellinSummand]
    simp only [NormalizedProbe.weightedSeparatedSummand, tsum_mul_left]
    rw [weight_eq R Z hZ]
    simp only [comparisonFrequencyKernel, frequencyNorm, separatedSeries,
      NormalizedProbe.principalSeparatedMellinSeries, NormalizedProbe.separatedMellinSeries,
      comparisonEulerPoissonSeries, tsum_mul_left, mul_assoc]
  have hrowint (u : Frequency R) : initialFrequencyIntegral R u Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∑' a, ∫ t : ℝ × ℝ × ℝ, f (u, a) t := by
    simp only [initialFrequencyIntegral, comparisonFrequencyIntegral, Finset.sum_singleton,
      comparisonTripleVerticalIntegral]
    congr 1
    change (∫ t : ℝ × ℝ × ℝ,
      comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat
        (separatedSeries R) Z u (NormalizedProbe.initialMellinPoint t).1
        (NormalizedProbe.initialMellinPoint t).2.1
        (NormalizedProbe.initialMellinPoint t).2.2) = _
    simp_rw [← hrow]
    exact (integral_tsum_of_summable_integral_norm
      (fun a => hint (u, a)) (hsum.prod_factor u)).symm
  have hsrows : Summable (fun u : Frequency R => initialFrequencyIntegral R u Z) := by
    simp_rw [hrowint]
    exact hsint.prod.mul_left _
  refine ⟨hsrows.norm.subtype (fun u => u ≠ principalFrequency R), ?_⟩
  have hpoint (t : ℝ × ℝ × ℝ) :
      (∑' i : NormalizedProbe.MellinSeriesIndex R.probe, f i t) =
        NormalizedProbe.principalTripleMellinKernel R.A R.σ R.target R.traceBad
          R.probe X Y Z (NormalizedProbe.initialMellinPoint t).1
          (NormalizedProbe.initialMellinPoint t).2.1
          (NormalizedProbe.initialMellinPoint t).2.2 := by
    dsimp [f, NormalizedProbe.initialTripleMellinSummand]
    rw [tsum_mul_left, NormalizedProbe.separatedSeries_eq_grouped R.probe]
    · rfl
    all_goals norm_num [NormalizedProbe.initialMellinPoint, Complex.mul_re]
  have hI : R.I Z = ∑' u : Frequency R, initialFrequencyIntegral R u Z := by
    have hexact := NormalizedProbe.ExactTripleMellin.initial_order R.A R.σ R.target
      R.traceBad R.probe (NormalizedProbe.probe_exact_triple_mellin R.A R.σ R.target
        R.traceBad R.probe R.normalization) ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩
    change R.I Z = _ at hexact
    rw [hexact]
    simp_rw [hrowint]
    rw [tsum_mul_left, ← hsint.tsum_prod' (fun u => hsint.prod_factor u), ← hinter]
    have hi := integral_three hwhole
    rw [hi]
    congr 1
    · simp [NormalizedProbe.tripleMellinNormalization]
    · change _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        ∑' i : NormalizedProbe.MellinSeriesIndex R.probe, f i (x, y, z)
      simp_rw [hpoint]
      rfl
  rw [hI]
  symm
  have heq : (fun u : Frequency R => u ∉ ({principalFrequency R} : Finset (Frequency R))) =
      (fun u => u ≠ principalFrequency R) := by
    funext u
    simp
  have hsplit := hsrows.sum_add_tsum_subtype_compl {principalFrequency R}
  simp only [Finset.sum_singleton] at hsplit
  rw [heq] at hsplit
  exact hsplit

end
end DedekindZetaZeroFree.PrincipalMellinComparison
