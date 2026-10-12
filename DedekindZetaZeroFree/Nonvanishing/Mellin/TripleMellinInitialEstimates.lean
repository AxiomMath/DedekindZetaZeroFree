module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSpectralResidueEstimate

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.ContinuationSteps

open MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private lemma integrable_tsum_of_summable_integral_norm
    {ι α E : Type*} [Countable ι] [MeasurableSpace α] [NormedAddCommGroup E] [CompleteSpace E]
    {μ : Measure α} {F : ι → α → E} (hint : ∀ i, Integrable (F i) μ)
    (hsum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  refine ⟨AEStronglyMeasurable.tsum fun i => (hint i).1, ?_⟩
  refine HasFiniteIntegral.mono'_enorm (g := fun a => ∑' i, ‖F i a‖ₑ) ?_ ?_
  · simp only [hasFiniteIntegral_iff_enorm, enorm_eq_self]
    rw [lintegral_tsum (fun i => (hint i).1.enorm)]
    have hstep : (∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ) =
        ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖ ∂μ) := by
      rw [tsum_congr fun i => (ofReal_integral_norm_eq_lintegral_enorm (hint i)).symm]
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun i => integral_nonneg fun a => norm_nonneg _) hsum]
    rw [hstep]
    exact ENNReal.ofReal_lt_top
  · filter_upwards with a using enorm_tsum_le_tsum_enorm

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

theorem nonprincipal_initial_absolute_of_initial_lines
    (R : PrincipalMellin.ActualRecipe S η)
    (E : Frequency R → ℂ → ℂ → ℂ → ℂ)
    (hinitial : ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
      ξ.re = 4 → w.re = 4 → z.re = 2 →
      separatedSeries R u ξ w z = E u ξ w z) :
    ∀ Z : ℝ, 1 ≤ Z →
        (∀ u : Frequency R, u ≠ principalFrequency R →
          Integrable (fun t : ℝ × ℝ × ℝ =>
            comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat
              E Z u
              ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
              ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
              ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I))) ∧
        Summable (fun u : {u : Frequency R // u ≠ principalFrequency R} =>
          ∫ t : ℝ × ℝ × ℝ,
            ‖comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat
              E Z u.val
              ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
              ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
              ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)‖) := by
  intro Z hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable R.A.Exterior := exterior_countable R
  letI : Countable (ExteriorSquarefreeIdeal R.A.cS) := by
    change Countable {I : R.A.Exterior // Squarefree I.val}
    infer_instance
  obtain ⟨hmajorant, hint, hsum⟩ :=
    NormalizedProbe.tripleMellin_integrable_majorant R.probe
      (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _) hZpos

  have hrow : ∀ (u : Frequency R) (t : ℝ × ℝ × ℝ),
      (∑' a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior,
        NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t) =
      comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat (separatedSeries R) Z u
        ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
        ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I) := by
    intro u t
    dsimp only [NormalizedProbe.initialTripleMellinSummand, NormalizedProbe.initialMellinPoint]
    simp only [NormalizedProbe.weightedSeparatedSummand, tsum_mul_left]
    rw [weight_eq R Z hZpos]
    simp only [comparisonFrequencyKernel, frequencyNorm, separatedSeries,
      NormalizedProbe.principalSeparatedMellinSeries, NormalizedProbe.separatedMellinSeries,
      comparisonEulerPoissonSeries, tsum_mul_left, mul_assoc]

  have hfibsum (u : Frequency R) : Summable (fun a :
      ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior =>
        ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖) :=
    hsum.prod_factor u
  have hfibsum' (u : Frequency R) : Summable (fun a :
      ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior =>
        ∫ t : ℝ × ℝ × ℝ, ‖‖NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfibsum u
  have hGint (u : Frequency R) : Integrable (fun t : ℝ × ℝ × ℝ =>
      ∑' a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior,
        NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t) :=
    integrable_tsum_of_summable_integral_norm (fun a => hint (u, a)) (hfibsum u)
  have hGnint (u : Frequency R) : Integrable (fun t : ℝ × ℝ × ℝ =>
      ∑' a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior,
        ‖NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖) :=
    integrable_tsum_of_summable_integral_norm
      (F := fun a (t : ℝ × ℝ × ℝ) => ‖NormalizedProbe.initialTripleMellinSummand R.probe
        (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖)
      (fun a => (hint (u, a)).norm) (hfibsum' u)

  have htn : ∀ (u : Frequency R) (t : ℝ × ℝ × ℝ),
      Summable (fun a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior =>
        ‖NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖) := by
    intro u t
    have hd : NormalizedProbe.initialMellinPoint t ∈ NormalizedProbe.separatedSeriesDomain := by
      norm_num [NormalizedProbe.initialMellinPoint, NormalizedProbe.separatedSeriesDomain,
        Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    have hn := (NormalizedProbe.separatedSeries_absolute_locallyUniform R.probe).1
      (NormalizedProbe.initialMellinPoint t) hd
    simpa only [NormalizedProbe.initialTripleMellinSummand, norm_mul] using
      (hn.prod_factor u).mul_left (‖NormalizedProbe.tripleMellinWeight R.probe
        (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z
        (NormalizedProbe.initialMellinPoint t).1
        (NormalizedProbe.initialMellinPoint t).2.1
        (NormalizedProbe.initialMellinPoint t).2.2‖)

  have hsep_int : ∀ u : Frequency R, Integrable (fun t : ℝ × ℝ × ℝ =>
      comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat (separatedSeries R) Z u
        ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
        ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)) := by
    intro u
    refine (hGint u).congr ?_
    filter_upwards with t
    exact hrow u t

  have hbound : ∀ u : Frequency R, u ≠ principalFrequency R →
      ∫ t : ℝ × ℝ × ℝ,
        ‖comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat E Z u
          ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤
      ∑' a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior,
        ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand R.probe
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖ := by
    intro u hu
    have hEe : (fun t : ℝ × ℝ × ℝ =>
        ‖comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat E Z u
          ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)‖) =ᵐ[volume]
        (fun t : ℝ × ℝ × ℝ =>
        ‖comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat (separatedSeries R) Z u
          ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)‖) := by
      filter_upwards with t
      simp only [comparisonFrequencyKernel]
      rw [hinitial u _ _ _ hu (by simp) (by simp) (by simp)]
    rw [integral_congr_ae hEe]
    refine (integral_mono_ae (hsep_int u).norm (hGnint u) ?_).trans_eq ?_
    · filter_upwards with t
      rw [← hrow u t]
      exact norm_tsum_le_tsum_norm (htn u t)
    · exact (integral_tsum_of_summable_integral_norm
        (fun a => (hint (u, a)).norm) (hfibsum' u)).symm
  constructor
  · intro u hu
    refine (hsep_int u).congr ?_
    filter_upwards with t
    simp only [comparisonFrequencyKernel]
    rw [hinitial u _ _ _ hu (by simp) (by simp) (by simp)]
  · have hH : Summable (fun u : Frequency R =>
        ∑' a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior,
          ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand R.probe
            (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u, a) t‖) :=
      hsum.prod
    have hHs : Summable (fun u : {u : Frequency R // u ≠ principalFrequency R} =>
        ∑' a : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior × R.A.Exterior × R.A.Exterior,
          ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand R.probe
            (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (u.val, a) t‖) :=
      hH.subtype (fun u => u ≠ principalFrequency R)
    exact Summable.of_nonneg_of_le (fun u => integral_nonneg fun t => norm_nonneg _)
      (fun u => hbound u.val u.property) hHs

end DedekindZetaZeroFree.PrincipalMellinComparison.ContinuationSteps

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

open Filter Asymptotics MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem initialFrequencyIntegral_eq_of_initial_lines
    (R : PrincipalMellin.ActualRecipe S η)
    (E : Frequency R → ℂ → ℂ → ℂ → ℂ)
    (hinitial : ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
      ξ.re = 4 → w.re = 4 → z.re = 2 →
      separatedSeries R u ξ w z = E u ξ w z)
    (u : Frequency R) (hu : u ≠ principalFrequency R) (Z : ℝ) :
    initialFrequencyIntegral R u Z =
      comparisonFrequencyIntegral (frequencyNorm R) R.W.M R.W.W1Hat E {u} Z 4 4 2 := by
  classical
  unfold initialFrequencyIntegral comparisonFrequencyIntegral comparisonTripleVerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Finset.sum_singleton, comparisonFrequencyKernel]
  rw [hinitial u _ _ _ hu (by simp) (by simp) (by simp)]

theorem nonprincipal_initial_estimate_of_contour_inputs
    (R : PrincipalMellin.ActualRecipe S η)
    (E P : Frequency R → ℂ → ℂ → ℂ → ℂ) (L : Frequency R → ℂ → ℂ)
    (good : ℝ → Frequency R → Prop)
    (hinitial : ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
      ξ.re = 4 → w.re = 4 → z.re = 2 →
      separatedSeries R u ξ w z = E u ξ w z)
    (Ω : Set (ℂ × ℂ × ℂ)) (hΩ : IsOpen Ω)
  (hbox : ∀ ξ w z : ℂ,
    ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
    w ∈ comparisonClosedStrip (3 / 1000) 4 →
    z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω)
  (hE : ∀ u : Frequency R, u ≠ principalFrequency R →
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => E u p.1 p.2.1 p.2.2) Ω)
  (hM : DifferentiableOn ℂ R.W.M {z : ℂ | 2 / 5 - 1 / 100000 < z.re})
  (hW : DifferentiableOn ℂ R.W.W1Hat {w : ℂ | 3 / 1000 - 1 / 100000 < w.re})
  (hMdecay : comparisonRapidStripDecay R.W.M (2 / 5) 2)
  (hWdecay : comparisonRapidStripDecay R.W.W1Hat (3 / 1000) 4)
  (hEBound : ∃ d : ℝ, 0 ≤ d ∧ ∀ δ : ℝ, 0 < δ →
    ∃ B : ℝ, 0 < B ∧ ∀ u : Frequency R, u ≠ principalFrequency R → 1 ≤ frequencyNorm R u →
      ∀ ξ w z : ℂ,
        ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
        w ∈ comparisonClosedStrip (3 / 1000) 4 →
        z ∈ comparisonClosedStrip (2 / 5) 2 →
        ‖E u ξ w z‖ ≤ B * (frequencyNorm R u) ^ (1 / 2 + δ) * (2 + |w.im|) ^ d)
  (Ωleft : Set (ℂ × ℂ × ℂ)) (hΩleft : IsOpen Ωleft)
  (hleft : ∀ ξ w z : ℂ,
    ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
    w.re = 3 / 1000 → z.re = 2 / 5 → (ξ, w, z) ∈ Ωleft)
  (hP : ∀ u : Frequency R, u ≠ principalFrequency R →
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => P u p.1 p.2.1 p.2.2) Ωleft)
  (hL : ∀ (U : ℝ) (u : Frequency R), 1 ≤ U → good U u →
    DifferentiableOn ℂ (L u) {ξ : ℂ | 0 < ξ.re})
  (hfactor : ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
    (ξ, w, z) ∈ Ωleft → L u ξ ≠ 0 → E u ξ w z = P u ξ w z / L u ξ)
  (A_F : ℝ) (hAF : 0 ≤ A_F)
  (hPBound : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
    ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R → 1 ≤ frequencyNorm R u →
      ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
      w.re = 3 / 1000 → z.re = 2 / 5 →
      ‖P u ξ w z‖ ≤ B * (frequencyNorm R u) ^ (1 / 2 + δ) *
        (2 + |ξ.im|) ^ A_F * (2 + |w.im|) ^ A_F * (2 + |z.im|) ^ A_F)
  (ρ : ℝ) (hρ : 0 < ρ)
  (hρsmall : ρ < min (1 / 10) (1 / (A_F + 1)))
  (hdetector : ∀ δ : ℝ, 0 < δ → ∃ B Udet : ℝ, 0 < B ∧ 1 ≤ Udet ∧
    ∀ (U : ℝ) (u : Frequency R), Udet ≤ U → good U u → U ≤ frequencyNorm R u → frequencyNorm R u < 2 * U →
      ∀ ξ : ℂ, 499 / 500 ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
        L u ξ ≠ 0 ∧ ‖(L u ξ)⁻¹‖ ≤ B * U ^ δ)
  (K : ℝ) (hK : 0 < K)
  (hFar : comparisonFarContourInput (frequencyNorm R) (principalFrequency R) R.W.M R.W.W1Hat E)
  (D : ℕ → Finset (Frequency R))
  (hDyads : ∀ j : ℕ,
    comparisonFrequencyDyad (frequencyNorm R) (principalFrequency R) K ((2 : ℝ) ^ j) (D j))
  (hCover : ∀ u : Frequency R, u ≠ principalFrequency R → ∃ j : ℕ, u ∈ D j)
  (hExceptional : ∃ B Uexc : ℝ, 0 < B ∧ 1 ≤ Uexc ∧
    ∀ j : ℕ, Uexc ≤ (2 : ℝ) ^ j →
      (((D j).filter (fun u => ¬ good ((2 : ℝ) ^ j) u)).card : ℝ) ≤
        B * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ))
  (hInitialAbsolute : ∀ Z : ℝ, 1 ≤ Z →
    (∀ u : Frequency R, u ≠ principalFrequency R →
      Integrable (fun t : ℝ × ℝ × ℝ =>
        comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat E Z u
          ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I))) ∧
    Summable (fun u : {u : Frequency R // u ≠ principalFrequency R} =>
      ∫ t : ℝ × ℝ × ℝ,
        ‖comparisonFrequencyKernel (frequencyNorm R) R.W.M R.W.W1Hat E Z u.val
          ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I)‖)) :
    nonprincipalInitialIntegral R =O[atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500)) := by
  classical
  obtain ⟨C, Z₀, hC, hZ₀, hbound⟩ :=
    comparison_nonprincipal_sum_analytic (principalFrequency R) (frequencyNorm R)
      R.W.M R.W.W1Hat E P L good Ω hΩ hbox hE
      hM hW hMdecay hWdecay hEBound Ωleft hΩleft hleft hP hL hfactor A_F hAF hPBound
      ρ hρ hρsmall hdetector K hK hFar D hDyads hCover hExceptional hInitialAbsolute
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hsum : nonprincipalInitialIntegral R Z =
      ∑' u : {u : Frequency R // u ≠ principalFrequency R},
        comparisonFrequencyIntegral (frequencyNorm R) R.W.M R.W.W1Hat E {u.val} Z 4 4 2 := by
    apply tsum_congr
    intro u
    exact initialFrequencyIntegral_eq_of_initial_lines R E hinitial u.val u.property Z
  rw [hsum]
  have hZpos : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hZpos _)]
    using (hbound Z hZ).2.2.2.2.2

theorem nonprincipal_initial_estimate
    (R : PrincipalMellin.ActualRecipe S η) :
    nonprincipalInitialIntegral R =O[atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500)) := by
  obtain ⟨E, P, L, good, Ω, Ωleft, A_F, ρ, K, D, hinitial, hΩ, hbox, hE,
    hM, hW, hMdecay, hWdecay, hEBound, hΩleft, hleft, hP, hL, hfactor, hAF,
    hPBound, hρ, hρsmall, hdetector, hK, hFar, hDyads, hCover, hExceptional⟩ :=
    ContinuationSteps.nonprincipal_continued_contour_inputs R
  have hInitialAbsolute :=
    ContinuationSteps.nonprincipal_initial_absolute_of_initial_lines R E hinitial
  exact nonprincipal_initial_estimate_of_contour_inputs R E P L good hinitial
    Ω hΩ hbox hE hM hW hMdecay hWdecay hEBound Ωleft hΩleft hleft hP hL hfactor
    A_F hAF hPBound ρ hρ hρsmall hdetector K hK hFar D hDyads hCover hExceptional
    hInitialAbsolute

end DedekindZetaZeroFree.PrincipalMellinComparison

end

section

namespace DedekindZetaZeroFree.PrincipalMellin

open Filter Asymptotics

variable {F : Type} [Field F] [NumberField F]

namespace ActualRecipe

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem mellinWeight_ne_zero (R : ActualRecipe S η) : R.W.M (1 / 6) ≠ 0 :=
  R.probe.nonzeroMellin

theorem realMellinWeight_ne_zero (R : ActualRecipe S η) : R.W.W1Hat 1 ≠ 0 :=
  probeRealWeightMellin_one_ne_zero R.probe.W1

theorem c_ne_zero_iff (R : ActualRecipe S η) : R.c ≠ 0 ↔ R.continuation.R 1 ≠ 0 := by
  have hmask := MellinZeroFree.comparisonPrincipalIncompleteL_eulerFactors_ne_zero
    F R.A R.target (1 : ℂ) (by norm_num)
  have hres : comparisonPrincipalResidue F R.A R.target R.probe.principal
      R.continuation ≠ 0 ↔ R.continuation.R 1 ≠ 0 := by
    unfold comparisonPrincipalResidue
    constructor
    · exact fun h => (mul_ne_zero_iff.mp h).1
    · exact fun h => mul_ne_zero h hmask
  constructor
  · intro hc
    apply hres.mp
    intro hzero
    apply hc
    simp [ActualRecipe.c, comparisonPrincipalConstant, hzero]
  · intro hR
    exact comparisonPrincipalConstant_ne_zero F R.A R.target R.probe.principal
      R.continuation R.W (hres.mpr hR) R.mellinWeight_ne_zero
      R.realMellinWeight_ne_zero

end ActualRecipe

theorem actual_principal_comparison
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (R : ActualRecipe S η) :
    R.c ≠ 0 ∧ (fun x : ℝ => R.I x - R.c * R.f x) =O[atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500)) := by
  have hres : R.continuation.R 1 ≠ 0 :=
    PrincipalMellinComparison.principal_regularization_ne_zero F R.A.modulus
      R.A.modulus_ne_zero R.target R.probe.principal R.continuation
  refine ⟨R.c_ne_zero_iff.mpr hres, ?_⟩
  have hprincipal := PrincipalMellinComparison.principal_initial_residue_estimate
      R
  have hnonprincipal := PrincipalMellinComparison.nonprincipal_initial_estimate
       R
  have hpower : (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2000)) =O[atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500)) := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  apply ((hprincipal.trans hpower).add hnonprincipal).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hdecomp := (PrincipalMellinComparison.initial_frequency_decomposition R x
    (by linarith)).2
  rw [hdecomp]
  ring

end DedekindZetaZeroFree.PrincipalMellin

end
