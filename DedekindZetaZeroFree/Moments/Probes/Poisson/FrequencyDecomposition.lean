module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PoissonFrequencyDecomposition

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory PoissonKernel PoissonInitialBridge
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowIntegral (u : D.Row) (Z : ℝ) : ℂ :=
  comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 2 Z)

def allowedIndices : Set (NormalizedProbe.MellinSeriesIndex D.recipe.probe) :=
  {i | ∃ u : D.Row, toProbeFrequency D u = i.1}

def omittedSum (Z : ℝ) : ℂ :=
  ∑' i : ↥(allowedIndices D)ᶜ, (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
    ∫ t : ℝ × ℝ × ℝ, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
      (Scales.xScale Z) (Scales.yScale Z) Z i.val t

private theorem exterior_countable'' : Countable D.recipe.A.Exterior := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have he := (DedekindZetaZeroFree.ProbeExteriorIdealCount.ideal_norm_summable F
    D.recipe.A.cS 2 (by norm_num)).countable_support
  have hall : Function.support (fun I : D.recipe.A.Exterior => (idealNorm I.val) ^ (-(2 : ℝ))) =
      Set.univ := by
    ext I
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (D.recipe.A.exteriorNorm_pos I) _).ne'
  rw [hall] at he
  exact Set.countable_univ_iff.mp he

private theorem aIndex_countable'' :
    Countable (ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior ×
      D.recipe.A.Exterior × D.recipe.A.Exterior) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI := exterior_countable'' D
  letI : Countable (ExteriorSquarefreeIdeal D.recipe.A.cS) := by
    change Countable {I : D.recipe.A.Exterior // Squarefree I.val}
    infer_instance
  infer_instance

private theorem integral_three'' {f : (ℝ × ℝ × ℝ) → ℂ} (hf : Integrable f) :
    (∫ t : ℝ × ℝ × ℝ, f t) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x, y, z) := by
  rw [MeasureTheory.Measure.volume_eq_prod] at hf
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_right_ae] with x hx
  rw [MeasureTheory.Measure.volume_eq_prod] at hx
  exact integral_prod _ hx

private theorem kernel_eq_sum' (Z : ℝ) (t : ℝ × ℝ × ℝ) :
    ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
        NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i t =
      NormalizedProbe.principalTripleMellinKernel D.recipe.A D.recipe.σ D.recipe.target
        D.recipe.traceBad D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
        (NormalizedProbe.initialMellinPoint t).1 (NormalizedProbe.initialMellinPoint t).2.1
        (NormalizedProbe.initialMellinPoint t).2.2 := by
  dsimp [NormalizedProbe.initialTripleMellinSummand]
  rw [tsum_mul_left, NormalizedProbe.separatedSeries_eq_grouped D.recipe.probe]
  · rfl
  all_goals norm_num [NormalizedProbe.initialMellinPoint, Complex.mul_re]

private theorem Iscale_eq_whole' (Z : ℝ) (hZ : 0 < Z) :
    D.Iscale Z = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ,
      ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
        NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i t := by
  have hX := Scales.xScale_pos Z hZ
  have hY := Scales.yScale_pos Z hZ
  have hwhole := (NormalizedProbe.tripleMellin_sum_integral_interchange D.recipe.probe
    (Scales.xScale Z) (Scales.yScale Z) Z hX hY hZ).1
  have hexact := NormalizedProbe.ExactTripleMellin.initial_order D.recipe.A D.recipe.σ
    D.recipe.target D.recipe.traceBad D.recipe.probe
    (NormalizedProbe.probe_exact_triple_mellin D.recipe.A D.recipe.σ D.recipe.target
      D.recipe.traceBad D.recipe.probe D.recipe.normalization)
    ⟨Scales.xScale Z, hX⟩ ⟨Scales.yScale Z, hY⟩ ⟨Z, hZ⟩
  change D.Iscale Z = _ at hexact
  rw [hexact, integral_three'' hwhole]
  congr 1
  · simp [NormalizedProbe.tripleMellinNormalization]
  · simp_rw [kernel_eq_sum' D Z]
    rfl

private theorem countable_mellin : Countable (NormalizedProbe.MellinSeriesIndex D.recipe.probe) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable D.recipe.A.R := by infer_instance
  letI := aIndex_countable'' D
  infer_instance

private theorem countable_row' : Countable D.Row := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable D.recipe.A.R := by infer_instance
  exact (ActualRowCount.row_u_injective D).countable

private theorem norm_summable_pt (Z : ℝ) (t : ℝ × ℝ × ℝ) :
    Summable (fun i : NormalizedProbe.MellinSeriesIndex D.recipe.probe =>
      ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i t‖) := by
  have hd : NormalizedProbe.initialMellinPoint t ∈ NormalizedProbe.separatedSeriesDomain := by
    norm_num [NormalizedProbe.initialMellinPoint, NormalizedProbe.separatedSeriesDomain,
      Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  have hn := (NormalizedProbe.separatedSeries_absolute_locallyUniform D.recipe.probe).1
    (NormalizedProbe.initialMellinPoint t) hd
  simpa only [NormalizedProbe.initialTripleMellinSummand, norm_mul] using
    hn.mul_left (‖NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
      (NormalizedProbe.initialMellinPoint t).1
      (NormalizedProbe.initialMellinPoint t).2.1 (NormalizedProbe.initialMellinPoint t).2.2‖)

private theorem whole_integrable' (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun t : ℝ × ℝ × ℝ => ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i t) :=
  (NormalizedProbe.tripleMellin_sum_integral_interchange D.recipe.probe (Scales.xScale Z)
    (Scales.yScale Z) Z (Scales.xScale_pos Z hZ) (Scales.yScale_pos Z hZ) hZ).1

private theorem allowed_pt (Z : ℝ) (hZ : 0 < Z) (t : ℝ × ℝ × ℝ) :
    ∑' i : ↥(allowedIndices D), NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t = ∑' u : D.Row, initialRowIntegrand D u Z t := by
  have hs : Summable (fun i : NormalizedProbe.MellinSeriesIndex D.recipe.probe =>
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t) :=
    (norm_summable_pt D Z t).of_norm
  let g : D.Row × (ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior ×
      D.recipe.A.Exterior × D.recipe.A.Exterior) → NormalizedProbe.MellinSeriesIndex D.recipe.probe :=
    fun p => (toProbeFrequency D p.1, p.2)
  have hg : Function.Injective g := by
    intro a b h
    have h' : (toProbeFrequency D a.1, a.2) = (toProbeFrequency D b.1, b.2) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (toProbeFrequency_injective D h1) h2
  have hsupp : Function.support ((allowedIndices D).indicator fun i =>
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t) ⊆
      Set.range g := by
    intro i hi
    have hmem : i ∈ allowedIndices D := by
      by_contra h
      exact hi (Set.indicator_of_notMem h _)
    obtain ⟨u, hu⟩ := hmem
    exact ⟨(u, i.2), Prod.ext hu rfl⟩
  have hsum2 : Summable (fun p => (allowedIndices D).indicator (fun i =>
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t)
      (g p)) :=
    (hs.indicator _).comp_injective hg
  rw [tsum_subtype (allowedIndices D) (fun i =>
    NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t)]
  rw [← hg.tsum_eq hsupp, hsum2.tsum_prod' (fun u => hsum2.prod_factor u)]
  refine tsum_congr fun u => ?_
  rw [rowIntegrand_eq_tsum D u Z hZ t]
  refine tsum_congr fun a => ?_
  rw [Set.indicator_of_mem (show g (u, a) ∈ allowedIndices D from ⟨u, rfl⟩)]

private theorem split_pt (Z : ℝ) (hZ : 0 < Z) (t : ℝ × ℝ × ℝ) :
    ∑' i : ↥(allowedIndices D), NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t +
      ∑' i : ↥(allowedIndices D)ᶜ, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t =
    ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t := by
  have hs : Summable (fun i : NormalizedProbe.MellinSeriesIndex D.recipe.probe =>
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t) :=
    (norm_summable_pt D Z t).of_norm
  exact (hs.subtype _).tsum_add_tsum_compl (hs.subtype _)

theorem Iscale_eq_rows_add_omitted (Z : ℝ) (hZ : 0 < Z) :
    (∀ u : D.Row, Integrable (initialRowIntegrand D u Z)) ∧
    Summable (fun u : D.Row => ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖) ∧
    (∀ u : D.Row, rowIntegral D u Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, initialRowIntegrand D u Z t) ∧
    Summable (fun u : D.Row => rowIntegral D u Z) ∧
    Summable (fun i : ↥(allowedIndices D)ᶜ => ∫ t : ℝ × ℝ × ℝ,
      ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t‖) ∧
    Summable (fun i : ↥(allowedIndices D)ᶜ => (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
      ∫ t : ℝ × ℝ × ℝ, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t) ∧
    Integrable (fun t : ℝ × ℝ × ℝ => ∑' i : ↥(allowedIndices D)ᶜ,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t) ∧
    omittedSum D Z = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, ∑' i : ↥(allowedIndices D)ᶜ,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t ∧
    D.Iscale Z = ∑' u : D.Row, rowIntegral D u Z + omittedSum D Z := by
  letI := countable_mellin D
  letI := countable_row' D
  have hint : ∀ u : D.Row, Integrable (initialRowIntegrand D u Z) :=
    fun u => rowIntegrand_integrable D u Z hZ
  have hnorm : Summable (fun u : D.Row => ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖) :=
    rowIntegrand_norm_summable D Z hZ
  obtain ⟨-, hmint, hmsum⟩ := initial_majorant D Z hZ
  have hwhole := whole_integrable' D Z hZ
  have hA : Integrable (fun t : ℝ × ℝ × ℝ => ∑' u : D.Row, initialRowIntegrand D u Z t) :=
    (integrable_tsum_norm_bound (fun u => initialRowIntegrand D u Z) hint hnorm).1
  have hO : Integrable (fun t : ℝ × ℝ × ℝ => ∑' i : ↥(allowedIndices D)ᶜ,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t) := by
    have hfun : (fun t : ℝ × ℝ × ℝ => ∑' i : ↥(allowedIndices D)ᶜ,
        NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i.val t) =
        fun t => (∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
          NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t)
          - ∑' u : D.Row, initialRowIntegrand D u Z t := by
      funext t
      have h1 := split_pt D Z hZ t
      rw [allowed_pt D Z hZ t] at h1
      linear_combination h1
    rw [hfun]
    exact hwhole.sub hA
  have hGO : ∀ t : ℝ × ℝ × ℝ, (∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t) =
      (∑' u : D.Row, initialRowIntegrand D u Z t) + ∑' i : ↥(allowedIndices D)ᶜ,
        NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i.val t := fun t => by
    have h1 := split_pt D Z hZ t
    rw [allowed_pt D Z hZ t] at h1
    exact h1.symm
  have hIsplit : ∫ t : ℝ × ℝ × ℝ, ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z i t =
      (∫ t : ℝ × ℝ × ℝ, ∑' u : D.Row, initialRowIntegrand D u Z t) +
        ∫ t : ℝ × ℝ × ℝ, ∑' i : ↥(allowedIndices D)ᶜ,
          NormalizedProbe.initialTripleMellinSummand D.recipe.probe
            (Scales.xScale Z) (Scales.yScale Z) Z i.val t := by
    rw [← integral_add hA hO]
    exact integral_congr_ae (Filter.Eventually.of_forall hGO)
  have h3 : ∀ u : D.Row, rowIntegral D u Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, initialRowIntegrand D u Z t := by
    intro u
    rw [integral_three'' (hint u)]
    simp only [rowIntegral, comparisonVerticalIntegral, wzIntegral, initialRowIntegrand,
      integral_const_mul, Complex.ofReal_ofNat]
    ring
  have hsumrow : Summable (fun u : D.Row => rowIntegral D u Z) := by
    have h1 : Summable (fun u : D.Row => (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
        ∫ t : ℝ × ℝ × ℝ, initialRowIntegrand D u Z t) := by
      refine (hnorm.mul_left ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖).of_norm_bounded (fun u => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    have hfun : (fun u : D.Row => rowIntegral D u Z) = fun u : D.Row =>
        (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, initialRowIntegrand D u Z t := funext h3
    rw [hfun]
    exact h1
  have hOsum : Summable (fun i : ↥(allowedIndices D)ᶜ => ∫ t : ℝ × ℝ × ℝ,
      ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t‖) := hmsum.subtype _
  have hOsum' : Summable (fun i : ↥(allowedIndices D)ᶜ => (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
      ∫ t : ℝ × ℝ × ℝ, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t) := by
    refine (hOsum.mul_left ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖).of_norm_bounded (fun i => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  have hOmit : omittedSum D Z = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ,
      ∑' i : ↥(allowedIndices D)ᶜ, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t := by
    unfold omittedSum
    rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
      (fun i : ↥(allowedIndices D)ᶜ => hmint i.val) hOsum]
  have hsumU : ∑' u : D.Row, rowIntegral D u Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, ∑' u : D.Row, initialRowIntegrand D u Z t := by
    rw [tsum_congr h3, tsum_mul_left, integral_tsum_of_summable_integral_norm hint hnorm]
  refine ⟨hint, hnorm, h3, hsumrow, hOsum, hOsum', hO, hOmit, ?_⟩
  rw [Iscale_eq_whole' D Z hZ, hsumU, hOmit, hIsplit]
  ring

end

end DedekindZetaZeroFree.Quantitative.PoissonFrequencyDecomposition
