module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.DyadicRows
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.GoodRectangle
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowContour
public import DedekindZetaZeroFree.Analysis.DyadicGeometricPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawGoodRowsSum31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem tsum_set_finite {α : Type*} (G : Set α) (hG : G.Finite) (f : α → ℝ) :
    Summable (fun u : G => f u) ∧ ∑' u : G, f u = ∑ u ∈ hG.toFinset, f u := by
  haveI : Fintype G := hG.fintype
  refine ⟨Summable.of_finite, ?_⟩
  rw [tsum_fintype]
  exact (Finset.sum_subtype (p := (· ∈ G)) hG.toFinset (fun x => hG.mem_toFinset) (fun x => f x)).symm

theorem norm_add_four (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  linarith

theorem good_row_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U →
      u ∉ DedekindZetaZeroFree.Quantitative.RawFixed.FixedData.rawExceptionalSet D ρ U →
      ∀ Z : ℝ, 1 ≤ Z →
        ‖initialRowIntegral D u Z‖ ≤
          C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-(10 : ℝ))) := by
  obtain ⟨C1, hC1, U1, hU1, h1⟩ :=
    DedekindZetaZeroFree.Quantitative.RawGoodRowRectangle31.rawGood_central_bound D A ρ hA hconv hρ ε hε
  obtain ⟨C2, hC2, U2, hU2, h2⟩ :=
    DedekindZetaZeroFree.Quantitative.RawGoodRowRectangle31.rawGood_horiz_bound D A ρ hA hconv hρ 10 (by norm_num)
  obtain ⟨C3, hC3, U3, hU3, h3⟩ :=
    DedekindZetaZeroFree.Quantitative.RawGoodRowRectangle31.rawGood_tail_bound D A ρ hA hconv hρ 10 (by norm_num)
  obtain ⟨U4, hU4, h4⟩ :=
    DedekindZetaZeroFree.Quantitative.RawGoodRowRectangle31.rawGood_rectangle_decomp D A ρ hA hconv hρ
  refine ⟨C1 + C2 + C2 + C3, by positivity, max (max U1 U2) (max U3 U4),
    le_max_of_le_left (le_max_of_le_left hU1), ?_⟩
  intro U hU u hu hq1 hq2 hexc Z hZ1
  have hZ0 : 0 < Z := by linarith
  have hUU1 : U1 ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hU
  have hUU2 : U2 ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hU
  have hUU3 : U3 ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
  have hUU4 : U4 ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
  have hc := h1 U hUU1 u hu hq1 hq2 hexc Z hZ0
  obtain ⟨hup, hlow⟩ := h2 U hUU2 u hu hq1 hq2 hexc Z hZ1
  have ht := h3 U hUU3 u hu hq1 hq2 Z hZ0
  have hdec := h4 U hUU4 u hu hq1 hq2 hexc Z hZ0
  rw [DedekindZetaZeroFree.Quantitative.RawLowRowContour31.initialRowIntegral_eq_triple D u hu Z hZ0, hdec]
  refine le_trans (norm_add_four _ _ _ _) ?_
  have hU0 : 0 < U := by linarith
  have hP : 0 ≤ Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) := by
    positivity
  have hQ : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-(10 : ℝ)) := by
    positivity
  nlinarith [mul_nonneg hC1.le hQ, mul_nonneg hC2.le hP, mul_nonneg hC3.le hP,
    mul_nonneg hC2.le hQ, mul_nonneg hC3.le hQ, mul_nonneg hC1.le hP]

theorem raw_good_rows_sum_abs (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Summable (fun u : ↥(goodMedium D ρ Z) => ‖initialRowIntegral D u.1 Z‖) ∧
      ∑' u : ↥(goodMedium D ρ Z), ‖initialRowIntegral D u.1 Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) := by
  obtain ⟨C, hC, U₀, hU₀, hrow⟩ :=
    good_row_bound D A ρ hA hconv hρ (1 / 10000 : ℝ) (by norm_num)
  obtain ⟨K, hK, hKcard⟩ := rawDyad_finite_card D
  obtain ⟨Ca, hCa, hCaB⟩ :=
    DedekindZetaZeroFree.Quantitative.DyadicPowerSums.sum_dyadic_pos_interval ((1 : ℝ) + (1 / 25 + 1 / 10000))
      (by norm_num)
  obtain ⟨Cn, hCn, hCnB⟩ :=
    DedekindZetaZeroFree.Quantitative.DyadicPowerSums.sum_dyadic_neg_interval ((1 : ℝ) + -10) (by norm_num)
  refine ⟨K * C * Ca + K * C * Cn, by positivity, max 2 ((2 * U₀) ^ (5 : ℝ)),
    le_max_left _ _, fun Z hZ => ?_⟩
  have hZ2 : 2 ≤ Z := le_trans (le_max_left _ _) hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hXU : U₀ ≤ Z ^ Scales.smallCutoffExponent / 2 := by
    have h1 : (2 * U₀) ^ (5 : ℝ) ≤ Z := le_trans (le_max_right _ _) hZ
    have h2 : ((2 * U₀) ^ (5 : ℝ)) ^ Scales.smallCutoffExponent ≤ Z ^ Scales.smallCutoffExponent :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1
        (by unfold Scales.smallCutoffExponent; norm_num)
    rw [← Real.rpow_mul (x := 2 * U₀) (by linarith)] at h2
    have h3 : (5 : ℝ) * Scales.smallCutoffExponent = 1 := by unfold Scales.smallCutoffExponent; norm_num
    rw [h3, Real.rpow_one] at h2
    linarith
  have hX1 : 1 ≤ Z ^ Scales.smallCutoffExponent / 2 := by linarith
  have hY : 1 ≤ Z ^ Scales.largeCutoffExponent :=
    Real.one_le_rpow hZ1 (by unfold Scales.largeCutoffExponent; norm_num)
  have hfin := goodMedium_finite D ρ Z
  obtain ⟨hsum, htsum⟩ := tsum_set_finite (goodMedium D ρ Z) hfin
    (fun u => ‖initialRowIntegral D u Z‖)
  refine ⟨hsum, le_trans (le_of_eq htsum) ?_⟩
  have hmaps : ∀ u ∈ hfin.toFinset,
      dyadIndex D u ∈ Finset.range (Nat.log 2 ⌊Z ^ Scales.largeCutoffExponent⌋₊ + 1) := by
    intro u hu
    have huG := hfin.mem_toFinset.1 hu
    rw [DedekindZetaZeroFree.Quantitative.DyadicPowerSums.mem_dyadicRange_iff hY]
    exact le_trans (dyadIndex_spec D u).1 huG.1.2.2
  have key : ∑ u ∈ hfin.toFinset, ‖initialRowIntegral D u Z‖ ≤
      ∑ k ∈ Finset.range (Nat.log 2 ⌊Z ^ Scales.largeCutoffExponent⌋₊ + 1),
        (if Z ^ Scales.smallCutoffExponent / 2 ≤ (2 : ℝ) ^ k then
          K * (2 : ℝ) ^ k * (C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ))))
         else 0) := by
    refine le_trans (le_of_eq (Finset.sum_fiberwise_of_maps_to hmaps _).symm) ?_
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hXk : Z ^ Scales.smallCutoffExponent / 2 ≤ (2 : ℝ) ^ k
    · rw [if_pos hXk]
      have hrowk : ∀ u ∈ hfin.toFinset.filter (fun u => dyadIndex D u = k),
          ‖initialRowIntegral D u Z‖ ≤
            C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ))) := by
        intro u hu
        obtain ⟨huT, huk⟩ := Finset.mem_filter.1 hu
        have huG := hfin.mem_toFinset.1 huT
        have hspec := dyadIndex_spec' D u
        rw [huk] at hspec
        have hexc : u ∉ DedekindZetaZeroFree.Quantitative.RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ k) := by
          have h := huG.2
          rw [huk] at h
          exact h
        exact hrow ((2 : ℝ) ^ k) (le_trans hXU hXk) u huG.1.1 hspec.1 hspec.2 hexc Z hZ1
      have hcard : ((hfin.toFinset.filter (fun u => dyadIndex D u = k)).card : ℝ) ≤
          K * (2 : ℝ) ^ k := by
        have hsub : ((hfin.toFinset.filter (fun u => dyadIndex D u = k) : Finset _) :
            Set (Frequency D.recipe)) ⊆ rawDyad D k := by
          intro u hu
          have hu' := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
          exact hu'.2
        have h1 := Set.ncard_le_ncard hsub (hKcard k).1
        rw [Set.ncard_coe_finset] at h1
        exact le_trans (Nat.cast_le.mpr h1) (hKcard k).2
      have hbk : 0 ≤ C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ))) := by
        positivity
      calc ∑ u ∈ hfin.toFinset.filter (fun u => dyadIndex D u = k), ‖initialRowIntegral D u Z‖
          ≤ ∑ u ∈ hfin.toFinset.filter (fun u => dyadIndex D u = k),
            C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ))) :=
            Finset.sum_le_sum hrowk
        _ = ((hfin.toFinset.filter (fun u => dyadIndex D u = k)).card : ℝ) *
            (C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ K * (2 : ℝ) ^ k * (C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ)))) :=
            mul_le_mul_of_nonneg_right hcard hbk
    · rw [if_neg hXk]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro u hu
      exfalso
      obtain ⟨huT, huk⟩ := Finset.mem_filter.1 hu
      have huG := hfin.mem_toFinset.1 huT
      have hspec := dyadIndex_spec' D u
      rw [huk] at hspec
      have hq : Z ^ Scales.smallCutoffExponent < q D u := huG.1.2.1
      have hlt := not_le.mp hXk
      linarith [hspec.2]
  have h1 := hCaB (Z ^ Scales.smallCutoffExponent / 2) (Z ^ Scales.largeCutoffExponent) hY
  have h2 := hCnB (Z ^ Scales.smallCutoffExponent / 2) (Z ^ Scales.largeCutoffExponent) hX1
  rw [Finset.sum_filter] at h1 h2
  have hrhs : ∑ k ∈ Finset.range (Nat.log 2 ⌊Z ^ Scales.largeCutoffExponent⌋₊ + 1),
        (if Z ^ Scales.smallCutoffExponent / 2 ≤ (2 : ℝ) ^ k then
          K * (2 : ℝ) ^ k * (C * (Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
              ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) +
            Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (-(10 : ℝ))))
         else 0) =
      K * C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
        ∑ k ∈ Finset.range (Nat.log 2 ⌊Z ^ Scales.largeCutoffExponent⌋₊ + 1),
          (if Z ^ Scales.smallCutoffExponent / 2 ≤ (2 : ℝ) ^ k then
            ((2 : ℝ) ^ k) ^ ((1 : ℝ) + (1 / 25 + 1 / 10000)) else 0) +
      K * C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
        ∑ k ∈ Finset.range (Nat.log 2 ⌊Z ^ Scales.largeCutoffExponent⌋₊ + 1),
          (if Z ^ Scales.smallCutoffExponent / 2 ≤ (2 : ℝ) ^ k then
            ((2 : ℝ) ^ k) ^ ((1 : ℝ) + -10) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have e1 : ((2 : ℝ) ^ k) ^ ((1 : ℝ) + (1 / 25 + 1 / 10000)) =
        (2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ ((1 / 25 : ℝ) + 1 / 10000) := by
      rw [Real.rpow_add hp (1 : ℝ) ((1 / 25 : ℝ) + 1 / 10000), Real.rpow_one]
    have e2 : ((2 : ℝ) ^ k) ^ ((1 : ℝ) + -10) =
        (2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ (-(10 : ℝ)) := by
      rw [Real.rpow_add hp (1 : ℝ) (-10), Real.rpow_one]
    split_ifs
    · rw [e1, e2]; ring
    · ring
  have hA1 : Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
      (Z ^ Scales.largeCutoffExponent) ^ ((1 : ℝ) + (1 / 25 + 1 / 10000)) ≤ Z ^ (717 / 2000 : ℝ) := by
    rw [← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
    refine Real.rpow_le_rpow_of_exponent_le hZ1 ?_
    norm_num [Scales.kernelExponent, Scales.xExponent, Scales.goodLine, Scales.wLine, Scales.zLine, Scales.smoothingExponent, Scales.yExponent,
      Scales.largeCutoffExponent]
  have hZ1W : Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) ≤ Z ^ (717 / 2000 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hZ1 ?_
    norm_num [Scales.kernelExponent, Scales.xExponent, Scales.rightLine, Scales.contourOffset, Scales.wLine, Scales.zLine, Scales.smoothingExponent,
      Scales.yExponent]
  have hXp : (Z ^ Scales.smallCutoffExponent / 2) ^ ((1 : ℝ) + -10) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have hB1 : Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
      (Z ^ Scales.smallCutoffExponent / 2) ^ ((1 : ℝ) + -10) ≤ Z ^ (717 / 2000 : ℝ) := by
    have := mul_le_mul hZ1W hXp (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hZ0.le _)
    linarith
  have t1 := mul_le_mul_of_nonneg_left hA1 (by positivity : 0 ≤ K * C * Ca)
  have t2 := mul_le_mul_of_nonneg_left hB1 (by positivity : 0 ≤ K * C * Cn)
  calc ∑ u ∈ hfin.toFinset, ‖initialRowIntegral D u Z‖
      ≤ _ := key
    _ = _ := hrhs
    _ ≤ K * C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
          (Ca * (Z ^ Scales.largeCutoffExponent) ^ ((1 : ℝ) + (1 / 25 + 1 / 10000))) +
        K * C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
          (Cn * (Z ^ Scales.smallCutoffExponent / 2) ^ ((1 : ℝ) + -10)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ ≤ (K * C * Ca + K * C * Cn) * Z ^ (717 / 2000 : ℝ) := by nlinarith [t1, t2]

end

end DedekindZetaZeroFree.Quantitative.RawGoodRowsSum31
