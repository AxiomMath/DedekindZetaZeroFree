module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowContour
public import DedekindZetaZeroFree.Moments.Probes.Poisson.DyadicRows
public import DedekindZetaZeroFree.Analysis.DyadicGeometricPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawSmallRowsSum31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem finset_norm_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ G : Finset (Frequency D.recipe),
      (↑G : Set (Frequency D.recipe)) ⊆ smallSet D Z →
        ∑ u ∈ G, ‖initialRowIntegral D u Z‖ ≤ C * Z ^ ((717 : ℝ) / 2000) := by
  classical
  have hEnum : DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
      DedekindZetaZeroFree.Quantitative.Scales.zLine + DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent * (1 + ((1:ℝ)/25 + 1/4000))
      ≤ (717:ℝ)/2000 := by
    simp only [DedekindZetaZeroFree.Quantitative.Scales.kernelExponent, DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent, DedekindZetaZeroFree.Quantitative.Scales.xExponent,
      DedekindZetaZeroFree.Quantitative.Scales.yExponent, DedekindZetaZeroFree.Quantitative.Scales.smoothingExponent, DedekindZetaZeroFree.Quantitative.Scales.rightLine,
      DedekindZetaZeroFree.Quantitative.Scales.contourOffset, DedekindZetaZeroFree.Quantitative.Scales.wLine, DedekindZetaZeroFree.Quantitative.Scales.zLine]
    norm_num
  have hκab : (0:ℝ) ≤ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent * (1 + ((1:ℝ)/25 + 1/4000)) := by
    simp only [DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent]; norm_num
  have hfix : ∀ u : Frequency D.recipe, ∃ Cu : ℝ, 0 ≤ Cu ∧ (u ≠ principalFrequency D.recipe →
      ∀ Z : ℝ, 2 ≤ Z → ‖initialRowIntegral D u Z‖ ≤
        Cu * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
          DedekindZetaZeroFree.Quantitative.Scales.zLine)) := by
    intro u
    by_cases hu : u = principalFrequency D.recipe
    · exact ⟨0, le_rfl, fun h => absurd hu h⟩
    · obtain ⟨Cu, hC, h⟩ := RawLowRowContour31.initialRowIntegral_fixed_bound D u hu
      exact ⟨Cu, hC, fun _ Z hZ => h Z hZ⟩
  choose c hc0 hc using hfix
  obtain ⟨K, hK, hKcount⟩ := RawRowSumDefinitions31.rawDyad_finite_card D
  obtain ⟨Kf, hKf, hfc⟩ := RawFrequencyCount.fixedData_frequency_count_lt D
  obtain ⟨C1, hC1, hdy⟩ :=
    RawLowRowContour31.initialRowIntegral_dyad_bound D (1/4000) (by norm_num)
  obtain ⟨C2, hC2, hsum⟩ :=
    DyadicPowerSums.sum_dyadic_pos (1 + ((1:ℝ)/25 + 1/4000)) (by norm_num)
  have hF0 := (hfc 2 (by norm_num)).1
  have hM0 : 0 ≤ ∑ u ∈ hF0.toFinset, c u := Finset.sum_nonneg (fun u _ => hc0 u)
  refine ⟨(∑ u ∈ hF0.toFinset, c u) + C1 * K * C2,
    add_pos_of_nonneg_of_pos hM0 (mul_pos (mul_pos hC1 hK) hC2), fun Z hZ G hG => ?_⟩
  have hZ0 : (0:ℝ) < Z := by linarith
  have hZ1 : (1:ℝ) ≤ Z := by linarith
  have hκ1 : (1:ℝ) ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent :=
    Real.one_le_rpow hZ1 (by simp only [DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent]; norm_num)
  have hsmall : ∀ u ∈ G, u ≠ principalFrequency D.recipe ∧
      q D u ≤ Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent := fun u hu =>
    (mem_small_iff D Z u).1 (hG (Finset.mem_coe.2 hu))
  have hZE : 0 < Z ^ DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
      DedekindZetaZeroFree.Quantitative.Scales.zLine := Real.rpow_pos_of_pos hZ0 _
  have hEle : DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
      DedekindZetaZeroFree.Quantitative.Scales.zLine ≤ (717:ℝ)/2000 := by linarith
  have hZEle : Z ^ DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
      DedekindZetaZeroFree.Quantitative.Scales.zLine ≤ Z ^ ((717:ℝ)/2000) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hEle
  rw [← Finset.sum_filter_add_sum_filter_not G (fun u => (2:ℝ) ≤ q D u)]

  have hlow : ∑ u ∈ G.filter (fun u => ¬ (2:ℝ) ≤ q D u), ‖initialRowIntegral D u Z‖ ≤
      (∑ u ∈ hF0.toFinset, c u) * Z ^ ((717:ℝ)/2000) := by
    calc ∑ u ∈ G.filter (fun u => ¬ (2:ℝ) ≤ q D u), ‖initialRowIntegral D u Z‖
        ≤ ∑ u ∈ G.filter (fun u => ¬ (2:ℝ) ≤ q D u), c u * Z ^
            (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
              DedekindZetaZeroFree.Quantitative.Scales.zLine) := by
          apply Finset.sum_le_sum
          intro u hu
          exact hc u (hsmall u (Finset.mem_filter.1 hu).1).1 Z hZ
      _ = (∑ u ∈ G.filter (fun u => ¬ (2:ℝ) ≤ q D u), c u) * Z ^
            (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
              DedekindZetaZeroFree.Quantitative.Scales.zLine) := by rw [Finset.sum_mul]
      _ ≤ (∑ u ∈ hF0.toFinset, c u) * Z ^
            (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
              DedekindZetaZeroFree.Quantitative.Scales.zLine) := by
          apply mul_le_mul_of_nonneg_right _ hZE.le
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            obtain ⟨_, hnot⟩ := Finset.mem_filter.1 hu
            rw [Set.Finite.mem_toFinset]
            exact lt_of_not_ge hnot
          · intro u _ _
            exact hc0 u
      _ ≤ (∑ u ∈ hF0.toFinset, c u) * Z ^ ((717:ℝ)/2000) :=
          mul_le_mul_of_nonneg_left hZEle hM0

  set T := Finset.range (Nat.log 2 ⌊Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent⌋₊ + 1) with hTdef
  set G1 := G.filter (fun u => (2:ℝ) ≤ q D u) with hG1
  have hkey : ∀ u ∈ G1, 1 ≤ dyadIndex D u ∧ (2:ℝ) ^ dyadIndex D u ≤ frequencyNorm D.recipe u ∧
      frequencyNorm D.recipe u < 2 * (2:ℝ) ^ dyadIndex D u := by
    intro u hu
    have hu2 : (2:ℝ) ≤ frequencyNorm D.recipe u := (Finset.mem_filter.1 hu).2
    have hmem : u ∈ rawDyad D (dyadIndex D u) := rfl
    rw [rawDyad_eq, Set.mem_setOf_eq] at hmem
    obtain ⟨hlo, hhi⟩ := hmem
    refine ⟨?_, hlo, hhi⟩
    by_contra hk
    have h0 : dyadIndex D u = 0 := by omega
    rw [h0] at hhi
    norm_num at hhi
    linarith
  have hbd : ∀ u ∈ G1, ‖initialRowIntegral D u Z‖ ≤
      C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
        DedekindZetaZeroFree.Quantitative.Scales.zLine) * ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + 1/4000) := by
    intro u hu
    obtain ⟨hk1, hlo, hhi⟩ := hkey u hu
    have h2U : (2:ℝ) ≤ (2:ℝ) ^ dyadIndex D u := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ dyadIndex D u := pow_le_pow_right₀ (by norm_num) hk1
    have hne := (hsmall u (Finset.mem_filter.1 hu).1).1
    have := hdy u hne ((2:ℝ) ^ dyadIndex D u) h2U hlo hhi Z hZ
    exact this
  have hmaps : ∀ u ∈ G1, dyadIndex D u ∈ T := by
    intro u hu
    obtain ⟨hk1, hlo, _⟩ := hkey u hu
    have hq := (hsmall u (Finset.mem_filter.1 hu).1).2
    rw [hTdef, DyadicPowerSums.mem_dyadicRange_iff hκ1]
    exact le_trans hlo hq
  have hhigh : ∑ u ∈ G1, ‖initialRowIntegral D u Z‖ ≤
      C1 * K * C2 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
        DedekindZetaZeroFree.Quantitative.Scales.zLine + DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent * (1 + ((1:ℝ)/25 + 1/4000))) := by
    calc ∑ u ∈ G1, ‖initialRowIntegral D u Z‖
        ≤ ∑ u ∈ G1, C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine
            DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine) *
            ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + 1/4000) := Finset.sum_le_sum hbd
      _ = C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
            DedekindZetaZeroFree.Quantitative.Scales.zLine) * ∑ u ∈ G1, ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + 1/4000) := by
          rw [Finset.mul_sum]
      _ = C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
            DedekindZetaZeroFree.Quantitative.Scales.zLine) * ∑ j ∈ T, ∑ u ∈ G1 with dyadIndex D u = j,
              ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + 1/4000) := by
          rw [Finset.sum_fiberwise_of_maps_to hmaps]
      _ ≤ C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
            DedekindZetaZeroFree.Quantitative.Scales.zLine) * ∑ j ∈ T, K * ((2:ℝ) ^ j) ^ (1 + ((1:ℝ)/25 + 1/4000)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1.le hZE.le)
          apply Finset.sum_le_sum
          intro j _
          have hfib : ∑ u ∈ G1 with dyadIndex D u = j,
              ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + 1/4000) =
              ((G1.filter (fun u => dyadIndex D u = j)).card : ℝ) * ((2:ℝ) ^ j) ^ ((1:ℝ)/25 + 1/4000) := by
            have hconst : ∀ u ∈ G1.filter (fun u => dyadIndex D u = j),
                ((2:ℝ) ^ dyadIndex D u) ^ ((1:ℝ)/25 + 1/4000) = ((2:ℝ) ^ j) ^ ((1:ℝ)/25 + 1/4000) :=
              fun u hu => by rw [(Finset.mem_filter.1 hu).2]
            rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
          rw [hfib]
          have hsub : ((G1.filter (fun u => dyadIndex D u = j) : Finset _) : Set (Frequency D.recipe))
              ⊆ rawDyad D j := by
            intro u hu
            exact (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).2
          have hnc := Set.ncard_le_ncard hsub (hKcount j).1
          rw [Set.ncard_coe_finset] at hnc
          have hnc' : ((G1.filter (fun u => dyadIndex D u = j)).card : ℝ) ≤
              (Set.ncard (rawDyad D j) : ℝ) := by exact_mod_cast hnc
          have hcard : ((G1.filter (fun u => dyadIndex D u = j)).card : ℝ) ≤ K * (2:ℝ) ^ j :=
            le_trans hnc' (hKcount j).2
          have hpos : 0 ≤ ((2:ℝ) ^ j) ^ ((1:ℝ)/25 + 1/4000) := by positivity
          calc _ ≤ (K * (2:ℝ) ^ j) * ((2:ℝ) ^ j) ^ ((1:ℝ)/25 + 1/4000) :=
                mul_le_mul_of_nonneg_right hcard hpos
            _ = K * ((2:ℝ) ^ j) ^ (1 + ((1:ℝ)/25 + 1/4000)) := by
                rw [Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ) ^ j) 1 ((1:ℝ)/25 + 1/4000), Real.rpow_one]; ring
      _ = C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
            DedekindZetaZeroFree.Quantitative.Scales.zLine) * (K * ∑ j ∈ T, ((2:ℝ) ^ j) ^ (1 + ((1:ℝ)/25 + 1/4000))) := by
          simp only [Finset.mul_sum]
      _ ≤ C1 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine DedekindZetaZeroFree.Quantitative.Scales.wLine
            DedekindZetaZeroFree.Quantitative.Scales.zLine) * (K * (C2 * (Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent) ^
              (1 + ((1:ℝ)/25 + 1/4000)))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hsum (Z ^ DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent) hκ1) hK.le) (mul_nonneg hC1.le hZE.le)
      _ = C1 * K * C2 * Z ^ (DedekindZetaZeroFree.Quantitative.Scales.kernelExponent DedekindZetaZeroFree.Quantitative.Scales.rightLine
            DedekindZetaZeroFree.Quantitative.Scales.wLine DedekindZetaZeroFree.Quantitative.Scales.zLine +
            DedekindZetaZeroFree.Quantitative.Scales.smallCutoffExponent * (1 + ((1:ℝ)/25 + 1/4000))) := by
          rw [Real.rpow_add hZ0, ← Real.rpow_mul hZ0.le]; ring
  have hhigh' : ∑ u ∈ G1, ‖initialRowIntegral D u Z‖ ≤
      C1 * K * C2 * Z ^ ((717:ℝ)/2000) := by
    refine le_trans hhigh (mul_le_mul_of_nonneg_left ?_ (mul_pos (mul_pos hC1 hK) hC2).le)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hEnum
  rw [add_mul]
  linarith

theorem smallRows_norm_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Summable (fun u : smallSet D Z => ‖initialRowIntegral D u.1 Z‖) ∧
        ∑' u : smallSet D Z, ‖initialRowIntegral D u.1 Z‖ ≤ C * Z ^ ((717 : ℝ) / 2000) := by
  obtain ⟨C, hC, h⟩ := finset_norm_sum_le D
  refine ⟨C, hC, fun Z hZ => ?_⟩
  have hfin : (smallSet D Z).Finite := smallSet_finite D Z
  haveI : Finite (smallSet D Z) := hfin.to_subtype
  refine ⟨Summable.of_finite, ?_⟩
  refine Summable.tsum_le_of_sum_le Summable.of_finite (fun s => ?_)
  have key := h Z hZ (s.map (Function.Embedding.subtype _)) ?_
  · rwa [Finset.sum_map] at key
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2

end

end DedekindZetaZeroFree.Quantitative.RawSmallRowsSum31
