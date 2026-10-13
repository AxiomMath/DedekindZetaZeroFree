module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.MeromorphicFactorization

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PoissonInitialBridge

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory PoissonKernel
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem X_eq (Z : ℝ) : Scales.xScale Z = Z ^ (67 / 100 : ℝ) := by
  unfold Scales.xScale Scales.xExponent; norm_num

theorem Y_eq (Z : ℝ) : Scales.yScale Z = Z ^ (151 / 400 : ℝ) := by
  unfold Scales.yScale Scales.yExponent; norm_num

def initialRowIntegrand (u : D.Row) (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
    ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I) Z

theorem row_mem_reps (u : D.Row) :
    ∃ h : u.toFrequency.u ≠ 0,
      (⟨u.toFrequency.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈ D.recipe.probe.frequencies.reps :=
  FixedData.Row.u_mem_reps u

def toProbeFrequency (u : D.Row) : PrincipalMellinComparison.Frequency D.recipe :=
  ⟨⟨u.toFrequency.u, (FixedData.Row.u_mem_reps u).choose⟩,
    (FixedData.Row.u_mem_reps u).choose_spec⟩

theorem toProbeFrequency_injective : Function.Injective (toProbeFrequency D) := by
  intro u v h
  apply FixedData.Row.u_unique
  have h2 := congrArg
    (fun f : PrincipalMellinComparison.Frequency D.recipe => (f.val.val : D.recipe.A.R)) h
  exact h2

theorem repRows_eq_univ :
    {u : D.Row | ∃ h : u.toFrequency.u ≠ 0,
      (⟨u.toFrequency.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈
        D.recipe.probe.frequencies.reps} = Set.univ :=
  Set.eq_univ_of_forall fun u => FixedData.Row.u_mem_reps u

theorem q_eq_frequencyNorm (u : D.Row) :
    D.q u = PrincipalMellinComparison.frequencyNorm D.recipe (toProbeFrequency D u) := rfl

theorem principalRows_subsingleton : (principalRows D).Subsingleton := by
  intro u hu v hv
  have hu' : u.toFrequency.u = 1 := hu
  have hv' : v.toFrequency.u = 1 := hv
  exact FixedData.Row.u_unique (hu'.trans hv'.symm)

theorem initial_majorant (Z : ℝ) (hZ : 0 < Z) :
    Integrable (NormalizedProbe.initialAbsoluteMellinMajorant D.recipe.probe
      (Scales.xScale Z) (Scales.yScale Z) Z) ∧
    (∀ i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
      Integrable (NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i)) ∧
    Summable (fun i : NormalizedProbe.MellinSeriesIndex D.recipe.probe =>
      ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i t‖) :=
  NormalizedProbe.tripleMellin_integrable_majorant D.recipe.probe _ _ _
    (Scales.xScale_pos Z hZ) (Scales.yScale_pos Z hZ) hZ

theorem tripleMellinWeight_eq (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ) :
    NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z ξ w z =
      (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
        (Scales.yExponent : ℂ) * (w - 1)) *
        Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w := by
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have key : ∀ s : ℂ, (Z : ℂ) ^ s = comparisonRealPower Z s := by
    intro s
    unfold comparisonRealPower
    rw [Complex.cpow_def_of_ne_zero hZc, Complex.ofReal_log hZ.le]
    congr 1
    ring
  have hX : comparisonRealPower (Scales.xScale Z) (1 / 2 - z) =
      (Z : ℂ) ^ ((Scales.xExponent : ℂ) * (1 / 2 - z)) := by
    rw [key]
    unfold comparisonRealPower Scales.xScale
    rw [Real.log_rpow hZ]
    congr 1
    push_cast
    ring
  have hY : comparisonRealPower (Scales.yScale Z) (w - 1) =
      (Z : ℂ) ^ ((Scales.yExponent : ℂ) * (w - 1)) := by
    rw [key]
    unfold comparisonRealPower Scales.yScale
    rw [Real.log_rpow hZ]
    congr 1
    push_cast
    ring
  have hZ1 : comparisonRealPower Z (ξ + z - 1) = (Z : ℂ) ^ (ξ + z - 1) := (key _).symm
  have hh : (Scales.smoothingExponent : ℂ) = 1 - (Scales.xExponent : ℂ) := by
    unfold Scales.smoothingExponent Scales.xExponent
    push_cast
    ring
  have hexp : ((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
      (Scales.yExponent : ℂ) * (w - 1) =
      (Scales.xExponent : ℂ) * (1 / 2 - z) + (ξ + z - 1) + (Scales.yExponent : ℂ) * (w - 1) := by
    rw [hh]
    push_cast
    ring
  unfold NormalizedProbe.tripleMellinWeight
  rw [hX, hY, hZ1, hexp, Complex.cpow_add _ _ hZc, Complex.cpow_add _ _ hZc]
  rfl

theorem q_pos (u : D.Row) : 0 < D.q u := by
  letI := D.recipe.probe.coefficients.finiteResidue u.toFrequency.u (FixedData.Row.u_ne_zero u)
  unfold FixedData.q
  exact_mod_cast (show 0 < FiniteTransform.exteriorNorm D.recipe.A.R.toSubring u.toFrequency.u from by
    simp only [FiniteTransform.exteriorNorm, Nat.card_eq_fintype_card]
    exact Fintype.card_pos)

theorem cpow_eq_comparisonRealPower {q : ℝ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s = comparisonRealPower q s := by
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold comparisonRealPower
  rw [Complex.cpow_def_of_ne_zero hqc, Complex.ofReal_log hq.le]
  congr 1
  ring

def strictRegion : Set (ℂ × ℂ × ℂ) := {p | 4 < p.1.re ∧ 4 < p.2.1.re ∧ 2 < p.2.2.re}

def closedRegion : Set (ℂ × ℂ × ℂ) := {p | 4 ≤ p.1.re ∧ 4 ≤ p.2.1.re ∧ 2 ≤ p.2.2.re}

theorem strictRegion_subset : strictRegion ⊆ closedRegion :=
  fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

theorem closedRegion_subset_closure : closedRegion ⊆ closure strictRegion := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hcont : Continuous (fun ε : ℝ => ((p.1 + (ε : ℂ), p.2.1 + (ε : ℂ), p.2.2 + (ε : ℂ)) :
      ℂ × ℂ × ℂ)) := by fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ => ((p.1 + (ε : ℂ), p.2.1 + (ε : ℂ), p.2.2 + (ε : ℂ)) :
      ℂ × ℂ × ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
    have h0 := hcont.tendsto 0
    have e : ((p.1 + ((0 : ℝ) : ℂ), p.2.1 + ((0 : ℝ) : ℂ), p.2.2 + ((0 : ℝ) : ℂ)) :
      ℂ × ℂ × ℂ) = p := by simp
    rw [e] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  refine Filter.eventually_of_mem (self_mem_nhdsWithin) (fun ε hε => ?_)
  have hε' : 0 < ε := hε
  simp only [strictRegion, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem crp_aux (q : ℝ) (z : ℂ) (s : ℂ) :
    s = comparisonRealPower q z * (comparisonRealPower q (-z) * s) := by
  rw [← mul_assoc]
  have : comparisonRealPower q z * comparisonRealPower q (-z) = 1 := by
    unfold comparisonRealPower
    rw [← Complex.exp_add, ← add_mul, add_neg_cancel, zero_mul, Complex.exp_zero]
  rw [this, one_mul]

private theorem majorant_antitone' (i : NormalizedProbe.MellinSeriesIndex D.recipe.probe)
    {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    NormalizedProbe.separatedSeriesMajorant D.recipe.probe i a' b' c' ≤
      NormalizedProbe.separatedSeriesMajorant D.recipe.probe i a b c := by
  have hn : ∀ I : D.recipe.A.Exterior, 1 ≤ D.recipe.A.exteriorNorm I := by
    intro I
    have hpos := D.recipe.A.exteriorNorm_pos I
    change 0 < (Ideal.absNorm I.val : ℝ) at hpos
    change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (show Ideal.absNorm I.val ≠ 0 by exact_mod_cast ne_of_gt hpos))
  letI := D.recipe.probe.coefficients.finiteResidue i.1.val.val i.1.val.property
  have hu : (1 : ℝ) ≤ (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring i.1.val.val : ℝ) := by
    simp only [FiniteTransform.exteriorNorm, Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty
      (FiniteTransform.Residue D.recipe.A.R.toSubring i.1.val.val))
  unfold NormalizedProbe.separatedSeriesMajorant
  apply mul_le_mul
  · apply mul_le_mul
    · apply mul_le_mul
      · apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
        · exact Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _
        · exact Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _
      · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
      · exact Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _
      · exact mul_nonneg (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _)
          (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _)
    · exact Real.rpow_le_rpow_of_exponent_le (hn _) (by linarith)
    · exact Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _)
        (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _))
        (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _)
  · exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _)
      (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _))
      (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _))
      (Real.rpow_nonneg (D.recipe.A.exteriorNorm_pos _).le _)

theorem rawRowFactor_continuousOn (u : D.Row) :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => rawRowFactor D u p.1 p.2.1 p.2.2) closedRegion := by
  have hinj : Function.Injective (fun a : ExteriorSquarefreeIdeal D.recipe.A.cS ×
      D.recipe.A.Exterior × D.recipe.A.Exterior × D.recipe.A.Exterior =>
      ((toProbeFrequency D u, a) : NormalizedProbe.MellinSeriesIndex D.recipe.probe)) :=
    fun a b h => (Prod.mk.inj h).2
  have hsum : Summable (fun a : ExteriorSquarefreeIdeal D.recipe.A.cS ×
      D.recipe.A.Exterior × D.recipe.A.Exterior × D.recipe.A.Exterior =>
      NormalizedProbe.separatedSeriesMajorant D.recipe.probe (toProbeFrequency D u, a) 4 4 2) :=
    (NormalizedProbe.separatedSeriesMajorant_summable D.recipe.probe 4 4 2 (by norm_num)
      (by norm_num) (by norm_num)).comp_injective hinj
  have hG : ContinuousOn (fun p : ℂ × ℂ × ℂ => ∑' a : ExteriorSquarefreeIdeal D.recipe.A.cS ×
      D.recipe.A.Exterior × D.recipe.A.Exterior × D.recipe.A.Exterior,
      NormalizedProbe.weightedSeparatedSummand D.recipe.probe (toProbeFrequency D u, a)
        p.1 p.2.1 p.2.2) closedRegion := by
    refine continuousOn_tsum (fun a => ?_) hsum (fun a p hp => ?_)
    · exact (NormalizedProbe.weightedSeparatedSummand_continuous D.recipe.probe
        (toProbeFrequency D u, a)).continuousOn
    · refine (NormalizedProbe.weightedSeparatedSummand_norm_le D.recipe.probe
        (toProbeFrequency D u, a) p.1 p.2.1 p.2.2).trans ?_
      exact majorant_antitone' D (toProbeFrequency D u, a) hp.1 hp.2.1 hp.2.2
  have hraw : (fun p : ℂ × ℂ × ℂ => rawRowFactor D u p.1 p.2.1 p.2.2) = fun p =>
      comparisonRealPower (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring
        u.toFrequency.u : ℝ) p.2.2 * ∑' a : ExteriorSquarefreeIdeal D.recipe.A.cS ×
        D.recipe.A.Exterior × D.recipe.A.Exterior × D.recipe.A.Exterior,
      NormalizedProbe.weightedSeparatedSummand D.recipe.probe (toProbeFrequency D u, a)
        p.1 p.2.1 p.2.2 := by
    funext p
    rw [← tsum_mul_left]
    unfold rawRowFactor comparisonEulerPoissonSeries
    refine tsum_congr (fun a => ?_)
    show _ = comparisonRealPower (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring
        u.toFrequency.u : ℝ) p.2.2 *
      NormalizedProbe.weightedSeparatedSummand D.recipe.probe (toProbeFrequency D u, a)
        p.1 p.2.1 p.2.2
    unfold NormalizedProbe.weightedSeparatedSummand
    exact crp_aux _ _ _
  rw [hraw]
  have hc : Continuous (fun p : ℂ × ℂ × ℂ => comparisonRealPower
      (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring u.toFrequency.u : ℝ) p.2.2) := by
    unfold comparisonRealPower
    fun_prop
  exact hc.continuousOn.mul hG

theorem rowFactor_continuousOn (u : D.Row) :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => rowFactor D u p.1 p.2.1 p.2.2) closedRegion := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  apply ContinuousAt.continuousWithinAt
  unfold rowFactor
  have hne1 : ∀ s : ℂ, 4 ≤ s.re → s ≠ 1 := by
    intro s hs h
    rw [h] at hs
    simp at hs
  have hz6 : (6 * p.2.2).re = 6 * p.2.2.re := by simp
  have hZ : ContinuousAt (fun p : ℂ × ℂ × ℂ => D.zetaSCont (6 * p.2.2)) p := by
    have hg : ContinuousAt D.zetaSCont (6 * p.2.2) :=
      (RightHeckeBounds.zetaSCont_analyticOnNhd D (6 * p.2.2)
        ⟨by simp only [Set.mem_setOf_eq]; rw [hz6]; linarith,
         hne1 _ (by rw [hz6]; linarith)⟩).continuousAt
    have hf : ContinuousAt (fun p : ℂ × ℂ × ℂ => 6 * p.2.2) p := by fun_prop
    exact ContinuousAt.comp (g := D.zetaSCont) (f := fun p : ℂ × ℂ × ℂ => 6 * p.2.2) hg hf
  have hP : ContinuousAt (fun p : ℂ × ℂ × ℂ => D.Lpsi u p.2.1) p := by
    have hg : ContinuousAt (D.Lpsi u) p.2.1 :=
      (D.Lpsi_analyticOnNhd u p.2.1
        ⟨by simp only [Set.mem_setOf_eq]; linarith, hne1 _ h2⟩).continuousAt
    have hf : ContinuousAt (fun p : ℂ × ℂ × ℂ => p.2.1) p := by fun_prop
    exact ContinuousAt.comp (g := D.Lpsi u) (f := fun p : ℂ × ℂ × ℂ => p.2.1) hg hf
  have hL : ContinuousAt (fun p : ℂ × ℂ × ℂ => D.Llam u p.1) p := by
    have hg : ContinuousAt (D.Llam u) p.1 :=
      (D.Llam_analyticOnNhd u p.1
        ⟨by simp only [Set.mem_setOf_eq]; linarith, hne1 _ h1⟩).continuousAt
    have hf : ContinuousAt (fun p : ℂ × ℂ × ℂ => p.1) p := by fun_prop
    exact ContinuousAt.comp (g := D.Llam u) (f := fun p : ℂ × ℂ × ℂ => p.1) hg hf
  have hLne : D.Llam u p.1 ≠ 0 := RightHeckeBounds.Llam_ne_zero_of_one_lt D u p.1 (by linarith)
  have hH : ContinuousAt (fun p : ℂ × ℂ × ℂ => EulerDomain.Hu D u p.1 p.2.1 p.2.2) p := by
    have hmem : p ∈ EulerDomain.OmegaStar := by
      simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    exact (EulerContinuation.Hu_differentiableOn D u).continuousOn.continuousAt
      (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
  exact ((hZ.mul hP).div hL hLne).mul hH

theorem rowFactor_eq_raw_initial (u : D.Row) (ξ w z : ℂ) (hξ : 4 ≤ ξ.re) (hw : 4 ≤ w.re)
    (hz : 2 ≤ z.re) : rowFactor D u ξ w z = rawRowFactor D u ξ w z := by
  have hEq : Set.EqOn (fun p : ℂ × ℂ × ℂ => rowFactor D u p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℂ × ℂ => rawRowFactor D u p.1 p.2.1 p.2.2) strictRegion :=
    fun p hp => rowFactor_eq_raw D u p.1 p.2.1 p.2.2 hp.1 hp.2.1 hp.2.2
  have h := Set.EqOn.of_subset_closure hEq (rowFactor_continuousOn D u)
    (rawRowFactor_continuousOn D u) strictRegion_subset closedRegion_subset_closure
  have hmem : ((ξ, w, z) : ℂ × ℂ × ℂ) ∈ closedRegion := ⟨hξ, hw, hz⟩
  have h2 := h hmem
  simp only at h2
  exact h2

private theorem exterior_countable' : Countable D.recipe.A.Exterior := by
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

private theorem aIndex_countable' :
    Countable (ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior ×
      D.recipe.A.Exterior × D.recipe.A.Exterior) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI := exterior_countable' D
  letI : Countable (ExteriorSquarefreeIdeal D.recipe.A.cS) := by
    change Countable {I : D.recipe.A.Exterior // Squarefree I.val}
    infer_instance
  infer_instance

theorem K_eq_tsum_aux (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ)
    (hξ : (4 : ℝ) ≤ ξ.re) (hw : (4 : ℝ) ≤ w.re) (hz : (2 : ℝ) ≤ z.re) :
    K D u ξ w z Z = ∑' a : ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior ×
        D.recipe.A.Exterior × D.recipe.A.Exterior,
      NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z ξ w z *
        NormalizedProbe.weightedSeparatedSummand D.recipe.probe (toProbeFrequency D u, a) ξ w z := by
  have hc : comparisonRealPower (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring
      u.toFrequency.u : ℝ) (-z) = (D.q u : ℂ) ^ (-z) := by
    rw [cpow_eq_comparisonRealPower (q_pos D u)] <;> rfl
  have hfreq : (toProbeFrequency D u).val.val = u.toFrequency.u := rfl
  simp only [PoissonKernel.K, PoissonKernel.kernelWith]
  rw [rowFactor_eq_raw_initial D u ξ w z hξ hw hz]
  simp only [PoissonKernel.rawRowFactor, DedekindZetaZeroFree.comparisonEulerPoissonSeries,
    NormalizedProbe.weightedSeparatedSummand, tsum_mul_left, hfreq, FixedData.Row.u]
  rw [hc, tripleMellinWeight_eq D Z hZ ξ w z]
  ring

theorem rowIntegrand_eq_tsum (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (t : ℝ × ℝ × ℝ) :
    initialRowIntegrand D u Z t =
      ∑' a, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (toProbeFrequency D u, a) t := by
  have h1 : (NormalizedProbe.initialMellinPoint t).1.re = 4 := by
    simp [NormalizedProbe.initialMellinPoint]
  have h2 : (NormalizedProbe.initialMellinPoint t).2.1.re = 4 := by
    simp [NormalizedProbe.initialMellinPoint]
  have h3 : (NormalizedProbe.initialMellinPoint t).2.2.re = 2 := by
    simp [NormalizedProbe.initialMellinPoint]
  show K D u (NormalizedProbe.initialMellinPoint t).1 (NormalizedProbe.initialMellinPoint t).2.1
    (NormalizedProbe.initialMellinPoint t).2.2 Z = _
  exact K_eq_tsum_aux D u Z hZ _ _ _ h1.ge h2.ge h3.ge

theorem rowIntegrand_integrable (u : D.Row) (Z : ℝ) (hZ : 0 < Z) :
    Integrable (initialRowIntegrand D u Z) := by
  obtain ⟨hmaj, hint, hsum⟩ := initial_majorant D Z hZ
  letI := aIndex_countable' D
  have heq : initialRowIntegrand D u Z = fun t => ∑' a,
      NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (toProbeFrequency D u, a) t :=
    funext fun t => rowIntegrand_eq_tsum D u Z hZ t
  rw [heq]
  refine hmaj.mono' (AEStronglyMeasurable.tsum (fun a => (hint (toProbeFrequency D u, a)).1)) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have hd : NormalizedProbe.initialMellinPoint t ∈ NormalizedProbe.separatedSeriesDomain := by
    norm_num [NormalizedProbe.initialMellinPoint, NormalizedProbe.separatedSeriesDomain,
      Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  have hn := (NormalizedProbe.separatedSeries_absolute_locallyUniform D.recipe.probe).1
    (NormalizedProbe.initialMellinPoint t) hd
  have htn : Summable (fun i : NormalizedProbe.MellinSeriesIndex D.recipe.probe =>
      ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i t‖) := by
    simpa only [NormalizedProbe.initialTripleMellinSummand, norm_mul] using
      hn.mul_left (‖NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z
        (NormalizedProbe.initialMellinPoint t).1
        (NormalizedProbe.initialMellinPoint t).2.1 (NormalizedProbe.initialMellinPoint t).2.2‖)
  have hinj : Function.Injective (fun a : ExteriorSquarefreeIdeal D.recipe.A.cS ×
      D.recipe.A.Exterior × D.recipe.A.Exterior × D.recipe.A.Exterior =>
      ((toProbeFrequency D u, a) : NormalizedProbe.MellinSeriesIndex D.recipe.probe)) :=
    fun a b h => (Prod.mk.inj h).2
  calc ‖∑' a, NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z (toProbeFrequency D u, a) t‖
      ≤ ∑' a, ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z (toProbeFrequency D u, a) t‖ :=
        norm_tsum_le_tsum_norm (htn.comp_injective hinj)
    _ ≤ ∑' i : NormalizedProbe.MellinSeriesIndex D.recipe.probe,
          ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z i t‖ :=
        (htn.comp_injective hinj).tsum_le_tsum_of_inj _ hinj (fun _ _ => norm_nonneg _)
          (fun _ => le_rfl) htn
    _ = NormalizedProbe.initialAbsoluteMellinMajorant D.recipe.probe
          (Scales.xScale Z) (Scales.yScale Z) Z t := by
      simp only [NormalizedProbe.initialTripleMellinSummand,
        NormalizedProbe.initialAbsoluteMellinMajorant, norm_mul, tsum_mul_left]

theorem integrable_tsum_norm_bound {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} (F : ι → α → ℂ) (hint : ∀ i, Integrable (F i) μ)
    (hsum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ ∧
      ∫ a, ‖∑' i, F i a‖ ∂μ ≤ ∑' i, ∫ a, ‖F i a‖ ∂μ := by
  have hl : ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := by
    calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
          lintegral_tsum (fun i => (hint i).aestronglyMeasurable.enorm)
      _ = _ := by
          congr 1
          ext i
          exact (ofReal_integral_norm_eq_lintegral_enorm (hint i)).symm
  have hfin : ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) =
      ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖ ∂μ) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hsum).symm
  have hm : AEStronglyMeasurable (fun a => ∑' i, F i a) μ :=
    AEStronglyMeasurable.tsum (fun i => (hint i).1)
  have hlt : ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ < ⊤ :=
    lt_of_le_of_lt hl (by rw [hfin]; exact ENNReal.ofReal_lt_top)
  refine ⟨⟨hm, hlt⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hm]
  have h0 : (0 : ℝ) ≤ ∑' i, ∫ a, ‖F i a‖ ∂μ :=
    tsum_nonneg fun i => integral_nonneg fun a => norm_nonneg _
  calc (∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ).toReal
      ≤ (ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖ ∂μ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hl.trans_eq hfin)
    _ = _ := ENNReal.toReal_ofReal h0

theorem rowIntegrand_norm_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun u : D.Row => ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖) := by
  obtain ⟨hmaj, hint, hsum⟩ := initial_majorant D Z hZ
  letI := aIndex_countable' D
  have hfib : ∀ u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ ≤
      ∑' a, ∫ t : ℝ × ℝ × ℝ, ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (toProbeFrequency D u, a) t‖ := by
    intro u
    simp_rw [rowIntegrand_eq_tsum D u Z hZ]
    exact (integrable_tsum_norm_bound
      (fun a => NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z (toProbeFrequency D u, a))
      (fun a => hint _) (hsum.prod_factor _)).2
  have hs := hsum.prod
  have hs2 := hs.comp_injective (toProbeFrequency_injective D)
  exact Summable.of_nonneg_of_le (fun u => integral_nonneg fun t => norm_nonneg _) hfib hs2

end

end DedekindZetaZeroFree.Quantitative.PoissonInitialBridge
