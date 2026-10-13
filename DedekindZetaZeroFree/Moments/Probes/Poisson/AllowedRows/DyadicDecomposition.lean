module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.SmallFrequencySum
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.HorizontalAndTailBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LargeFrequencySum
public import DedekindZetaZeroFree.Moments.Probes.Poisson.TripleMellinIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowDyadDecomposition

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.RowsGoodCentral
  DedekindZetaZeroFree.Quantitative.RowsExceptional DedekindZetaZeroFree.Quantitative.RowsHeightErrors DedekindZetaZeroFree.Quantitative.RowsSmall
  DedekindZetaZeroFree.Quantitative.RowsLarge
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem dyadNP_eq_union (ρ U : ℝ) :
    dyadRows D U \ principalRows D = exceptionalSet D ρ U ∪ goodRows D ρ U := by
  ext u
  constructor
  · intro hu
    by_cases he : u ∈ exceptionalSet D ρ U
    · exact Or.inl he
    · exact Or.inr ⟨hu.1, hu.2, he⟩
  · rintro (he | hg)
    · refine ⟨⟨he.2.1, he.2.2.1⟩, ?_⟩
      intro h1
      exact he.1 h1
    · exact ⟨hg.1, hg.2.1⟩

theorem exceptional_disjoint_good (ρ U : ℝ) :
    Disjoint (exceptionalSet D ρ U) (goodRows D ρ U) := by
  rw [Set.disjoint_left]
  intro u hu hg
  exact hg.2.2 hu

theorem exceptionalSet_finite (ρ U : ℝ) : (exceptionalSet D ρ U).Finite :=
  (ActualRowCount.dyadRows_finite D U).subset fun u hu => ⟨hu.2.1, hu.2.2.1⟩

theorem goodRows_finite (ρ U : ℝ) : (goodRows D ρ U).Finite :=
  (ActualRowCount.dyadRows_finite D U).subset fun u hu => hu.1

theorem J_dyadNP_split (ρ U Z : ℝ) :
    J D (dyadRows D U \ principalRows D) 4 4 2 Z =
      J D (exceptionalSet D ρ U) 4 4 2 Z + J D (goodRows D ρ U) 4 4 2 Z := by
  rw [dyadNP_eq_union D ρ U]
  unfold J
  exact finsum_mem_union (exceptional_disjoint_good D ρ U) (exceptionalSet_finite D ρ U)
    (goodRows_finite D ρ U)

private def scaleExp : ℝ := Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * 2 + Scales.yExponent * (4 - 1)

private theorem K_norm_scale (u : D.Row) (ξ w z : ℂ) (Z : ℝ) (hZ : 0 < Z) :
    ‖K D u ξ w z Z‖ =
      Z ^ ((Scales.xExponent / 2 : ℝ) + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1)) *
        ‖K D u ξ w z 1‖ := by
  have h1 : K D u ξ w z 1 = Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w *
      (D.q u : ℂ) ^ (-z) * rowFactor D u ξ w z := by
    unfold K kernelWith
    simp
  have h2 : K D u ξ w z Z =
      (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) *
        (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w *
          (D.q u : ℂ) ^ (-z) * rowFactor D u ξ w z) := by
    unfold K kernelWith
    ring
  rw [h2, norm_mul, ← h1, Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  congr 2
  simp

private theorem rowIntegrand_norm_scale (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (t : ℝ × ℝ × ℝ) :
    ‖PoissonIdentity.rowIntegrand D u Z t‖ =
      Z ^ scaleExp * ‖PoissonIdentity.rowIntegrand D u 1 t‖ := by
  unfold PoissonIdentity.rowIntegrand
  rw [K_norm_scale D u _ _ _ Z hZ]
  congr 2
  simp [scaleExp]

private theorem tsum_scale (Z : ℝ) (hZ : 0 < Z) :
    ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ =
      Z ^ scaleExp * ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u 1 t‖ := by
  rw [← tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [← integral_const_mul]
  congr 1
  funext t
  exact rowIntegrand_norm_scale D u Z hZ t

private theorem J_norm_le_finset (A : Set D.Row) (hA : A.Finite) (s : Finset D.Row)
    (hs : A ⊆ ↑s) (Z : ℝ) (hZ : 0 < Z) :
    ‖J D A 4 4 2 Z‖ ≤ ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
      ∑ u ∈ s, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ := by
  have hJ : J D A 4 4 2 Z = ∑ᶠ u ∈ A, PoissonIdentity.rowIntegral D u Z := rfl
  have hu : ∀ u : D.Row, ‖PoissonIdentity.rowIntegral D u Z‖ ≤
      ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
        ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ := by
    intro u
    obtain ⟨-, -, heq, -⟩ := PoissonIdentity.Iscale_eq_sum_rowIntegral D Z hZ
    rw [heq u (PoissonInitialBridge.row_mem_reps D u), norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  rw [hJ, finsum_mem_eq_finite_toFinset_sum _ hA]
  calc ‖∑ u ∈ hA.toFinset, PoissonIdentity.rowIntegral D u Z‖
      ≤ ∑ u ∈ hA.toFinset, ‖PoissonIdentity.rowIntegral D u Z‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ hA.toFinset, ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
          ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ :=
        Finset.sum_le_sum fun u _ => hu u
    _ = ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
          ∑ u ∈ hA.toFinset, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ := by
        rw [Finset.mul_sum]
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
          ∑ u ∈ s, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun u _ _ => integral_nonneg fun t => norm_nonneg _)
        intro u hu'
        exact hs (hA.mem_toFinset.mp hu')

private theorem lt_floor_iff {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    k < ⌊Real.logb 2 x⌋₊ + 1 ↔ (2 : ℝ) ^ k ≤ x := by
  have hpos : 0 < x := by linarith
  rw [Nat.lt_succ_iff, Nat.le_floor_iff (Real.logb_nonneg (by norm_num) hx),
    Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos]
  simp

private theorem mem_intermediate_iff {Z : ℝ} (hZ : 1 ≤ Z) (k : ℕ) :
    k ∈ intermediateDyads Z ↔
      Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ Z ^ Scales.largeCutoffExponent := by
  have h1 : (1 : ℝ) ≤ Z ^ Scales.largeCutoffExponent := Real.one_le_rpow hZ (by unfold Scales.largeCutoffExponent; norm_num)
  unfold intermediateDyads
  rw [Finset.mem_filter, Finset.mem_range, lt_floor_iff h1]
  exact and_comm

private theorem dyad_disjoint (k l : ℕ) (hkl : k ≠ l) :
    Disjoint (dyadRows D ((2 : ℝ) ^ k)) (dyadRows D ((2 : ℝ) ^ l)) := by
  rw [Set.disjoint_left]
  intro u hk hl
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · have h1 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt h)
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h3 : D.q u < 2 * (2 : ℝ) ^ k := hk.2
    have h4 : (2 : ℝ) ^ l ≤ D.q u := hl.1
    linarith
  · have h1 : (2 : ℝ) ^ (l + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt h)
    have h2 : (2 : ℝ) ^ (l + 1) = 2 * 2 ^ l := by ring
    have h3 : D.q u < 2 * (2 : ℝ) ^ l := hl.2
    have h4 : (2 : ℝ) ^ k ≤ D.q u := hk.1
    linarith

private theorem dyad_bound_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun k : ℕ => ∑ u ∈ (ActualRowCount.dyadRows_finite D ((2 : ℝ) ^ k)).toFinset,
      ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖) := by
  have hsum := PoissonInitialBridge.rowIntegrand_norm_summable D Z hZ
  refine summable_of_sum_range_le
    (c := ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖)
    (fun k => Finset.sum_nonneg fun u _ => integral_nonneg fun t => norm_nonneg _)
    (fun n => ?_)
  have hd : Set.PairwiseDisjoint (↑(Finset.range n : Finset ℕ))
      (fun k : ℕ => (ActualRowCount.dyadRows_finite D ((2 : ℝ) ^ k)).toFinset) := by
    intro k _ l _ hkl
    refine Finset.disjoint_left.mpr ?_
    intro u hu hu'
    exact Set.disjoint_left.mp (dyad_disjoint D k l hkl)
      ((Set.Finite.mem_toFinset _).mp hu) ((Set.Finite.mem_toFinset _).mp hu')
  refine le_of_eq_of_le (Finset.sum_biUnion
    (f := fun u => ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖) hd).symm ?_
  exact hsum.sum_le_tsum _ (fun u _ => integral_nonneg fun t => norm_nonneg _)

private theorem dyad_norm_le (Z : ℝ) (hZ : 0 < Z) (k : ℕ) :
    ‖J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z‖ ≤
      ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
        ∑ u ∈ (ActualRowCount.dyadRows_finite D ((2 : ℝ) ^ k)).toFinset,
          ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ := by
  have hfin := ActualRowCount.dyadRows_finite D ((2 : ℝ) ^ k)
  exact J_norm_le_finset D _ (hfin.subset Set.diff_subset) hfin.toFinset
    (fun u hu => hfin.mem_toFinset.mpr hu.1) Z hZ

private theorem dyad_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun k : ℕ => J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z) :=
  Summable.of_norm_bounded
    ((dyad_bound_summable D Z hZ).mul_left ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖)
    (fun k => dyad_norm_le D Z hZ k)

theorem good_initial_eq (ρ U Z : ℝ) (hU : 2 ≤ U) (hZ : 2 ≤ Z) :
    J D (goodRows D ρ U) 4 4 2 Z =
      RowLowContour.JCont D (goodRows D ρ U) Scales.rightLine Scales.wLine Scales.zLine Z := by
  refine RowLowContour.J_initial_eq D U Z hU hZ _ ?_ (goodRows_finite D ρ U)
  intro u hu
  exact ⟨hu.2.1, hu.1⟩

theorem J_eq_JCont (C : Set D.Row) (x y v Z : ℝ) :
    J D C x y v Z = RowLowContour.JCont D C x y v Z := by
  have h : ∀ u ξ w z, K D u ξ w z Z =
      kernelWith D (RowLowContour.rowCont D) u ξ w z Z := by
    intro u ξ w z
    unfold K kernelWith RowLowContour.rowCont rowFactor
    rw [mul_div_right_comm (D.zetaSCont (6 * z) * D.Lpsi u w)]
  unfold J RowLowContour.JCont wzIntegral
  simp only [h]

theorem good_dyad_split (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U Z : ℝ, U₀ ≤ U → 2 ≤ Z →
      J D (goodRows D ρ U) 4 4 2 Z =
        Jcentral D (goodRows D ρ U) Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z +
          heightErrors D ρ U Z := by
  obtain ⟨U₀, hU₀, hdeform⟩ := RowGoodDeform.row_good_deform D A_F ρ hA hconv hρ
  refine ⟨U₀, hU₀, fun U Z hU hZ => ?_⟩
  have hU2 : 2 ≤ U := le_trans hU₀ hU
  have hZ0 : 0 < Z := by linarith
  have hC : ∀ u ∈ goodRows D ρ U, FixedData.Row.u u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      u ∉ exceptionalSet D ρ U := by
    intro u hu
    exact ⟨hu.2.1, hu.1.1, hu.1.2, hu.2.2⟩
  have hdef := (hdeform U hU (goodRows D ρ U) (goodRows_finite D ρ U) hC Z hZ0).2.2
  rw [good_initial_eq D ρ U Z hU2 hZ, ← J_eq_JCont D (goodRows D ρ U) Scales.rightLine Scales.wLine
    Scales.zLine Z, hdef]
  unfold heightErrors
  ring

theorem dyad_five_piece (ρ Z : ℝ) (hZ : 2 ≤ Z) :
    Summable (fun k : ℕ => J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z) ∧
    ∑' k : ℕ, J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z =
      smallDyadSum D Z + exceptionalDyadSum D ρ Z +
        ∑ k ∈ intermediateDyads Z, J D (goodRows D ρ ((2 : ℝ) ^ k)) 4 4 2 Z +
        ∑' k : ℕ, (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then dyadNP D ((2 : ℝ) ^ k) 2 Z else 0) := by
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  refine ⟨dyad_summable D Z hZ0, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℂ, ∀ k : ℕ,
      T k = J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z :=
    ⟨fun k => J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z, fun k => rfl⟩
  have hTf : T = fun k : ℕ => J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z :=
    funext hT
  have hTs : Summable T := by rw [hTf]; exact dyad_summable D Z hZ0
  rw [← hTf]
  have hN : ∀ k : ℕ, dyadNP D ((2 : ℝ) ^ k) 2 Z = T k := fun k => (hT k).symm
  simp only [hN]
  have hs0 : (1 : ℝ) ≤ Z ^ Scales.smallCutoffExponent := Real.one_le_rpow hZ1 (by unfold Scales.smallCutoffExponent; norm_num)
  have hsl : Z ^ Scales.smallCutoffExponent ≤ Z ^ Scales.largeCutoffExponent :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by unfold Scales.smallCutoffExponent Scales.largeCutoffExponent; norm_num)
  have hdec : ∀ k : ℕ, T k = (if (2 : ℝ) ^ k ≤ Z ^ Scales.smallCutoffExponent then T k else 0) +
      (if k ∈ intermediateDyads Z then T k else 0) +
      (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then T k else 0) := by
    intro k
    by_cases h1 : (2 : ℝ) ^ k ≤ Z ^ Scales.smallCutoffExponent
    · have h2 : k ∉ intermediateDyads Z := by
        rw [mem_intermediate_iff hZ1]
        exact fun h => absurd h.1 (not_lt.mpr h1)
      have h3 : ¬ Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k := by
        rw [not_lt]; linarith
      rw [if_pos h1, if_neg h2, if_neg h3, add_zero, add_zero]
    · have h1' : Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k := not_le.mp h1
      by_cases h4 : (2 : ℝ) ^ k ≤ Z ^ Scales.largeCutoffExponent
      · have h2 : k ∈ intermediateDyads Z := (mem_intermediate_iff hZ1 k).mpr ⟨h1', h4⟩
        have h3 : ¬ Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k := not_lt.mpr h4
        rw [if_neg h1, if_pos h2, if_neg h3, zero_add, add_zero]
      · have h4' : Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k := not_le.mp h4
        have h2 : k ∉ intermediateDyads Z := by
          rw [mem_intermediate_iff hZ1]
          exact fun h => h4 h.2
        rw [if_neg h1, if_neg h2, if_pos h4', zero_add, zero_add]
  have hite : ∀ (p : ℕ → Prop) [DecidablePred p], Summable (fun k : ℕ => if p k then T k else 0) := by
    intro p
    refine Summable.of_norm_bounded
      ((dyad_bound_summable D Z hZ0).mul_left ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖) (fun k => ?_)
    by_cases h : p k
    · rw [if_pos h, hT k]; exact dyad_norm_le D Z hZ0 k
    · rw [if_neg h, norm_zero]
      exact mul_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun u _ => integral_nonneg fun t => norm_nonneg _)
  have hss := hite (fun k => (2 : ℝ) ^ k ≤ Z ^ Scales.smallCutoffExponent)
  have hse := hite (fun k => k ∈ intermediateDyads Z)
  have hsL := hite (fun k => Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k)
  have hS : ∑' k : ℕ, (if (2 : ℝ) ^ k ≤ Z ^ Scales.smallCutoffExponent then T k else 0) = smallDyadSum D Z := by
    rw [tsum_eq_sum (s := Finset.range (⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1))]
    · unfold smallDyadSum
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range, lt_floor_iff hs0] at hk
      rw [if_pos hk, hT k]
    · intro k hk
      rw [Finset.mem_range, lt_floor_iff hs0] at hk
      exact if_neg hk
  have hE : ∑' k : ℕ, (if k ∈ intermediateDyads Z then T k else 0) =
      exceptionalDyadSum D ρ Z +
        ∑ k ∈ intermediateDyads Z, J D (goodRows D ρ ((2 : ℝ) ^ k)) 4 4 2 Z := by
    rw [tsum_eq_sum (s := intermediateDyads Z) (fun k hk => if_neg hk)]
    have hc : ∀ k ∈ intermediateDyads Z,
        (if k ∈ intermediateDyads Z then T k else 0) =
          J D (exceptionalSet D ρ ((2 : ℝ) ^ k)) 4 4 2 Z +
            J D (goodRows D ρ ((2 : ℝ) ^ k)) 4 4 2 Z := by
      intro k hk
      rw [if_pos hk, hT k]
      exact J_dyadNP_split D ρ _ Z
    rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
    rfl
  have h1 := Summable.tsum_add (hss.add hse) hsL
  have h2 := Summable.tsum_add hss hse
  rw [tsum_congr hdec, h1, h2, hS, hE]
  ring

theorem rowIntegrand_norm_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun u : D.Row => ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖) :=
  PoissonInitialBridge.rowIntegrand_norm_summable D Z hZ

theorem rowIntegrand_norm_summable_dyad (U Z : ℝ) (hZ : 0 < Z) :
    Summable (fun u : dyadRows D U =>
      ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖) :=
  (rowIntegrand_norm_summable D Z hZ).comp_injective Subtype.val_injective

theorem rowIntegrand_norm_tsum_locally_bounded (Z₀ : ℝ) :
    ∃ C : ℝ, ∀ Z ∈ Set.Icc (2 : ℝ) Z₀,
      ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u Z t‖ ≤ C := by
  have he : 0 ≤ scaleExp := by
    unfold scaleExp Scales.xExponent Scales.smoothingExponent Scales.yExponent; norm_num
  have hT0 : 0 ≤ ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u 1 t‖ :=
    tsum_nonneg fun u => integral_nonneg fun t => norm_nonneg _
  refine ⟨Z₀ ^ scaleExp *
    ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖PoissonIdentity.rowIntegrand D u 1 t‖, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith [hZ.1]
  rw [tsum_scale D Z hZ0]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hZ0.le hZ.2 he) hT0

theorem Jdyad_locally_bounded (Z₀ : ℝ) :
    ∃ C : ℝ, ∀ Z ∈ Set.Icc (2 : ℝ) Z₀, ∀ U : ℝ,
      ‖J D (dyadRows D U \ principalRows D) 4 4 2 Z‖ ≤ C := by
  obtain ⟨C, hC⟩ := rowIntegrand_norm_tsum_locally_bounded D Z₀
  refine ⟨‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ * C, fun Z hZ U => ?_⟩
  have hZ0 : 0 < Z := by linarith [hZ.1]
  have hfin := ActualRowCount.dyadRows_finite D U
  refine le_trans (J_norm_le_finset D _ (hfin.subset Set.diff_subset) hfin.toFinset
    (fun u hu => hfin.mem_toFinset.mpr hu.1) Z hZ0) ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact le_trans ((rowIntegrand_norm_summable D Z hZ0).sum_le_tsum _
    (fun u _ => integral_nonneg fun t => norm_nonneg _)) (hC Z hZ)

end

end DedekindZetaZeroFree.Quantitative.RowDyadDecomposition
