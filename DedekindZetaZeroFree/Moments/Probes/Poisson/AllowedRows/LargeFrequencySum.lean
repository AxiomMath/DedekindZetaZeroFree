module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LargeFrequencyShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowsLarge

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

noncomputable def dyadNP (U : ℝ) (v Z : ℝ) : ℂ :=
  J D (dyadRows D U \ principalRows D) 4 4 v Z

private lemma iter_triple (g : ℝ → ℝ → ℝ → ℂ)
    (hg : MeasureTheory.Integrable (fun t : ℝ × ℝ × ℝ => g t.1 t.2.1 t.2.2)) :
    ∫ a : ℝ, ∫ b : ℝ, ∫ c : ℝ, g a b c = ∫ t : ℝ × ℝ × ℝ, g t.1 t.2.1 t.2.2 := by
  have h1 : ∀ᵐ a : ℝ ∂MeasureTheory.volume,
      MeasureTheory.Integrable (fun y : ℝ × ℝ => g a y.1 y.2) MeasureTheory.volume :=
    MeasureTheory.Integrable.prod_right_ae hg
  calc ∫ a : ℝ, ∫ b : ℝ, ∫ c : ℝ, g a b c
      = ∫ a : ℝ, ∫ y : ℝ × ℝ, g a y.1 y.2 := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [h1] with a ha
        exact (MeasureTheory.integral_prod (fun y : ℝ × ℝ => g a y.1 y.2) ha).symm
    _ = ∫ t : ℝ × ℝ × ℝ, g t.1 t.2.1 t.2.2 :=
        (MeasureTheory.integral_prod (fun t : ℝ × ℝ × ℝ => g t.1 t.2.1 t.2.2) hg).symm

private lemma cvi_congr {σ : ℝ} {f g : ℂ → ℂ}
    (h : ∀ t : ℝ, f ((σ : ℂ) + (t : ℂ) * Complex.I) = g ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    comparisonVerticalIntegral σ f = comparisonVerticalIntegral σ g := by
  unfold comparisonVerticalIntegral
  simp only [h]

private lemma wz_shift (u : D.Row) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    wzIntegral D u ξ 4 2 Z = wzIntegral D u ξ 4 Scales.tailShift Z := by
  unfold wzIntegral
  refine cvi_congr (fun t => ?_)
  exact LargeRowShift.large_row_z_shift D u Z hZ ξ _ hξ (by simp)

private lemma row_val (u : D.Row) (Z : ℝ)
    (hint : MeasureTheory.Integrable (fun t : ℝ × ℝ × ℝ =>
      K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z)) :
    comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 Scales.tailShift Z) =
      (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ × ℝ × ℝ,
          K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z)) := by
  have h := iter_triple (fun a b c => K D u ((4 : ℂ) + (a : ℂ) * Complex.I)
    ((4 : ℂ) + (b : ℂ) * Complex.I) (((Scales.tailShift : ℝ) : ℂ) + (c : ℂ) * Complex.I) Z) hint
  rw [← h]
  simp only [comparisonVerticalIntegral, wzIntegral, MeasureTheory.integral_const_mul,
    Complex.ofReal_ofNat]

theorem rows_large_shift :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ U : ℝ, Z ^ Scales.largeCutoffExponent < U →
        dyadNP D U 2 Z = dyadNP D U Scales.tailShift Z ∧
        ‖dyadNP D U Scales.tailShift Z‖ ≤
          C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * U ^ (1 - Scales.tailShift + ε) := by
  classical
  refine ⟨1, one_pos, fun ε hε hε1 => ?_⟩
  obtain ⟨C0, hC0, hK⟩ := LargeRowShift.large_row_triple_bound D ε hε
  obtain ⟨Cc, hCc, hcnt⟩ := ActualRowCount.dyadRows_nonprincipal_count D
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ‖(2 * (Real.pi : ℂ))⁻¹‖ *
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖(2 * (Real.pi : ℂ))⁻¹‖) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨(A + 1) * C0 * Cc, by positivity, fun Z hZ U hU => ⟨?_, ?_⟩⟩
  · unfold dyadNP J
    refine finsum_mem_congr rfl (fun u _ => ?_)
    refine cvi_congr (fun t => ?_)
    exact wz_shift D u Z hZ _ (by simp)
  · have hZpos : 0 < Z := by linarith
    have hκ : (0 : ℝ) ≤ Scales.largeCutoffExponent := by unfold Scales.largeCutoffExponent; norm_num
    have h1Z : (1 : ℝ) ≤ Z := by linarith
    have hU1' : (1 : ℝ) ≤ Z ^ Scales.largeCutoffExponent := Real.one_le_rpow h1Z hκ
    have hU1 : 1 ≤ U := hU1'.trans hU.le
    have hUpos : 0 < U := by linarith
    obtain ⟨hfin, hcard⟩ := hcnt U hU1
    have hexp : -Scales.tailShift + ε ≤ 0 := by unfold Scales.tailShift; linarith
    have hZe : 0 ≤ Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) :=
      Real.rpow_nonneg hZpos.le _
    have hUe : 0 ≤ U ^ (-Scales.tailShift + ε) := Real.rpow_nonneg hUpos.le _
    have hrow : ∀ u ∈ (dyadRows D U \ principalRows D),
        ‖comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 Scales.tailShift Z)‖ ≤
          A * (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * U ^ (-Scales.tailShift + ε)) := by
      intro u hu
      obtain ⟨hint, hb⟩ := hK u Z hZ
      rw [row_val D u Z hint]
      simp only [norm_mul]
      have h1 : ‖∫ t : ℝ × ℝ × ℝ,
          K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ ≤
          C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * U ^ (-Scales.tailShift + ε) := by
        refine (MeasureTheory.norm_integral_le_integral_norm _).trans (hb.trans ?_)
        have hq : D.q u ^ (-Scales.tailShift + ε) ≤ U ^ (-Scales.tailShift + ε) :=
          Real.rpow_le_rpow_of_nonpos hUpos hu.1.1 hexp
        exact mul_le_mul_of_nonneg_left hq (mul_nonneg hC0.le hZe)
      rw [hA]
      have hn : 0 ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ *
            ‖∫ t : ℝ × ℝ × ℝ,
          K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖))
          = (‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖(2 * (Real.pi : ℂ))⁻¹‖)) *
            ‖∫ t : ℝ × ℝ × ℝ,
          K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hmain : dyadNP D U Scales.tailShift Z =
        ∑ u ∈ hfin.toFinset,
          comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 Scales.tailShift Z) := by
      unfold dyadNP J
      exact finsum_mem_eq_finite_toFinset_sum _ hfin
    have hpow : U ^ (1 - Scales.tailShift + ε) = U ^ (-Scales.tailShift + ε) * U := by
      rw [show (1 - Scales.tailShift + ε) = (-Scales.tailShift + ε) + 1 by ring, Real.rpow_add_one hUpos.ne']
    rw [hmain, hpow]
    have hB : 0 ≤ C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * U ^ (-Scales.tailShift + ε) :=
      mul_nonneg (mul_nonneg hC0.le hZe) hUe
    have hextra : 0 ≤ C0 * Cc * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
        U ^ (-Scales.tailShift + ε) * U :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0.le hCc.le) hZe) hUe) hUpos.le
    calc ‖∑ u ∈ hfin.toFinset,
          comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 Scales.tailShift Z)‖
        ≤ ∑ u ∈ hfin.toFinset,
          ‖comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 Scales.tailShift Z)‖ :=
          norm_sum_le _ _
      _ ≤ hfin.toFinset.card • (A * (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            U ^ (-Scales.tailShift + ε))) :=
          Finset.sum_le_card_nsmul _ _ _ (fun u hu => hrow u ((Set.Finite.mem_toFinset hfin).1 hu))
      _ = (Set.ncard (dyadRows D U \ principalRows D) : ℝ) * (A * (C0 *
            Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * U ^ (-Scales.tailShift + ε))) := by
          rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin]
      _ ≤ (Cc * U) * (A * (C0 *
            Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * U ^ (-Scales.tailShift + ε))) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hA0 hB)
      _ ≤ (A + 1) * C0 * Cc * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            (U ^ (-Scales.tailShift + ε) * U) := by nlinarith [hextra]

private lemma tail_geom (X : ℝ) (hX : 0 < X) :
    Summable (fun k : ℕ => if X < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) ∧
    ∑' k : ℕ, (if X < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) ≤ 2 / X := by
  classical
  have hex : ∃ k : ℕ, X < (2 : ℝ) ^ k := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)
  have hk0 : X < (2 : ℝ) ^ (Nat.find hex) := Nat.find_spec hex
  have hfun : (fun k : ℕ => if X < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) =
      fun k : ℕ => if Nat.find hex ≤ k then ((1 : ℝ) / 2) ^ k else 0 := by
    funext k
    by_cases h : Nat.find hex ≤ k
    · have h' : X < (2 : ℝ) ^ k := lt_of_lt_of_le hk0 (pow_le_pow_right₀ (by norm_num) h)
      rw [if_pos h', if_pos h]
    · have h' : ¬ X < (2 : ℝ) ^ k := Nat.find_min hex (not_le.mp h)
      rw [if_neg h', if_neg h]
  have hsum : Summable (fun k : ℕ => if X < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> first | positivity | simp)
      (fun k => by split_ifs <;> first | positivity | simp | exact le_rfl) summable_geometric_two
  refine ⟨hsum, ?_⟩
  have hs : Summable (fun k : ℕ => if Nat.find hex ≤ k then ((1 : ℝ) / 2) ^ k else 0) := by
    rw [← hfun]; exact hsum
  rw [hfun]
  have h1 := hs.sum_add_tsum_nat_add (Nat.find hex)
  have h2 : ∑ i ∈ Finset.range (Nat.find hex),
      (if Nat.find hex ≤ i then ((1 : ℝ) / 2) ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (not_le.mpr (Finset.mem_range.mp hi))]
  have h3 : ∀ i : ℕ, (if Nat.find hex ≤ i + Nat.find hex then ((1 : ℝ) / 2) ^ (i + Nat.find hex)
      else 0) = ((1 : ℝ) / 2) ^ (Nat.find hex) * ((1 : ℝ) / 2) ^ i := by
    intro i
    rw [if_pos (Nat.le_add_left _ _), pow_add, mul_comm]
  rw [← h1, h2, zero_add, tsum_congr h3, tsum_mul_left, tsum_geometric_two]
  have h4 : ((1 : ℝ) / 2) ^ (Nat.find hex) = 1 / (2 : ℝ) ^ (Nat.find hex) := by
    rw [one_div_pow]
  have h5 : 1 / (2 : ℝ) ^ (Nat.find hex) < 1 / X := one_div_lt_one_div_of_lt hX hk0
  rw [h4]
  calc 1 / (2 : ℝ) ^ (Nat.find hex) * 2 ≤ 1 / X * 2 := by linarith
    _ = 2 / X := by ring

theorem rows_large (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Summable (fun k : ℕ =>
        if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ‖dyadNP D ((2 : ℝ) ^ k) 2 Z‖ else 0) ∧
      ‖∑' k : ℕ, (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then dyadNP D ((2 : ℝ) ^ k) 2 Z else 0)‖ ≤
        C * Z ^ (Scales.mainExponent - 1481 / 2500 + ε) := by
  classical
  obtain ⟨ε₀, hε₀, H⟩ := rows_large_shift D
  obtain ⟨ε₁, h1, h2, h3, h4⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < ε₀ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 :=
    ⟨min (min ε (ε₀ / 2)) 1, lt_min (lt_min hε (by linarith)) one_pos,
      lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith),
      (min_le_left _ _).trans (min_le_left _ _), min_le_right _ _⟩
  obtain ⟨C, hC, hCb⟩ := H ε₁ h1 h2
  have hθ : (1 - Scales.tailShift + ε₁) + 1 ≤ 0 := by simp only [Scales.tailShift]; linarith
  refine ⟨2 * C, by positivity, fun Z hZ => ?_⟩
  have hZpos : 0 < Z := by linarith
  have hX : 0 < Z ^ Scales.largeCutoffExponent := Real.rpow_pos_of_pos hZpos _
  obtain ⟨hsum, htail⟩ := tail_geom (Z ^ Scales.largeCutoffExponent) hX
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
      (Z ^ Scales.largeCutoffExponent) ^ ((1 - Scales.tailShift + ε₁) + 1) := ⟨_, rfl⟩
  have hcnn : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hZpos.le _))
      (Real.rpow_nonneg hX.le _)
  have hCZ : 0 ≤ C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) :=
    mul_nonneg hC.le (Real.rpow_nonneg hZpos.le _)
  have hpt : ∀ k : ℕ, (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ‖dyadNP D ((2 : ℝ) ^ k) 2 Z‖ else 0)
      ≤ c * (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) := by
    intro k
    by_cases h : Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k
    · rw [if_pos h, if_pos h]
      obtain ⟨heq, hb⟩ := hCb Z hZ ((2 : ℝ) ^ k) h
      have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hpow : ((2 : ℝ) ^ k) ^ (1 - Scales.tailShift + ε₁) =
          ((2 : ℝ) ^ k) ^ ((1 - Scales.tailShift + ε₁) + 1) * ((1 : ℝ) / 2) ^ k := by
        have h5 := Real.rpow_add h2k ((1 - Scales.tailShift + ε₁) + 1) (-1)
        rw [show (1 - Scales.tailShift + ε₁) + 1 + -1 = 1 - Scales.tailShift + ε₁ by ring,
          Real.rpow_neg_one] at h5
        rw [h5, one_div, inv_pow]
      have hmono : ((2 : ℝ) ^ k) ^ ((1 - Scales.tailShift + ε₁) + 1) ≤
          (Z ^ Scales.largeCutoffExponent) ^ ((1 - Scales.tailShift + ε₁) + 1) :=
        Real.rpow_le_rpow_of_nonpos hX h.le hθ
      calc ‖dyadNP D ((2 : ℝ) ^ k) 2 Z‖ = ‖dyadNP D ((2 : ℝ) ^ k) Scales.tailShift Z‖ := by rw [heq]
        _ ≤ C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            ((2 : ℝ) ^ k) ^ (1 - Scales.tailShift + ε₁) := hb
        _ = C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            (((2 : ℝ) ^ k) ^ ((1 - Scales.tailShift + ε₁) + 1) * ((1 : ℝ) / 2) ^ k) := by rw [hpow]
        _ ≤ C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            ((Z ^ Scales.largeCutoffExponent) ^ ((1 - Scales.tailShift + ε₁) + 1) * ((1 : ℝ) / 2) ^ k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono (by positivity)) hCZ
        _ = c * ((1 : ℝ) / 2) ^ k := by rw [hc]; ring
    · rw [if_neg h, if_neg h]; simp
  have hnorm : ∀ k : ℕ,
      ‖(if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then dyadNP D ((2 : ℝ) ^ k) 2 Z else 0)‖ =
      (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ‖dyadNP D ((2 : ℝ) ^ k) 2 Z‖ else 0) := by
    intro k; split_ifs <;> simp
  have hsumm : Summable (fun k : ℕ =>
      if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ‖dyadNP D ((2 : ℝ) ^ k) 2 Z‖ else 0) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> first | positivity | simp) hpt (hsum.mul_left c)
  refine ⟨hsumm, ?_⟩
  have e1 := Real.rpow_add hZpos ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift)
    (Scales.largeCutoffExponent * (1 - Scales.tailShift + ε₁))
  have e2 := Real.rpow_mul hZpos.le Scales.largeCutoffExponent (1 - Scales.tailShift + ε₁)
  have e3 := Real.rpow_add_one hX.ne' (1 - Scales.tailShift + ε₁)
  have hfin : c * (2 / Z ^ Scales.largeCutoffExponent) = 2 * C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift +
      Scales.largeCutoffExponent * (1 - Scales.tailShift + ε₁)) := by
    rw [hc, e3, e1, e2]
    have hXne := hX.ne'
    first | (field_simp; ring) | field_simp
  have hexp : (44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift + Scales.largeCutoffExponent * (1 - Scales.tailShift + ε₁) ≤
      Scales.mainExponent - 1481 / 2500 + ε := by
    simp only [Scales.tailShift, Scales.largeCutoffExponent, Scales.mainExponent]; linarith
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  calc ‖∑' k : ℕ, (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then dyadNP D ((2 : ℝ) ^ k) 2 Z else 0)‖
      ≤ ∑' k : ℕ, ‖(if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then dyadNP D ((2 : ℝ) ^ k) 2 Z else 0)‖ :=
        norm_tsum_le_tsum_norm (by simp only [hnorm]; exact hsumm)
    _ = ∑' k : ℕ, (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ‖dyadNP D ((2 : ℝ) ^ k) 2 Z‖ else 0) :=
        tsum_congr hnorm
    _ ≤ ∑' k : ℕ, c * (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) :=
        hsumm.tsum_le_tsum hpt (hsum.mul_left c)
    _ = c * ∑' k : ℕ, (if Z ^ Scales.largeCutoffExponent < (2 : ℝ) ^ k then ((1 : ℝ) / 2) ^ k else 0) :=
        tsum_mul_left
    _ ≤ c * (2 / Z ^ Scales.largeCutoffExponent) := mul_le_mul_of_nonneg_left htail hcnn
    _ = 2 * C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift +
      Scales.largeCutoffExponent * (1 - Scales.tailShift + ε₁)) := hfin
    _ ≤ 2 * C * Z ^ (Scales.mainExponent - 1481 / 2500 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 hexp) (by positivity)

end DedekindZetaZeroFree.Quantitative.RowsLarge
