module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.DyadicDomination
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.DyadicDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Rows

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def nonprincipalDyad (k : ℕ) : Set D.Row :=
  {u | u.u ≠ 1} ∩ PoissonKernel.dyadRows D ((2 : ℝ) ^ k)

def dyadIntegral (k : ℕ) (Z : ℝ) : ℂ :=
  PoissonKernel.J D (nonprincipalDyad D k) 4 4 2 Z

def nonprincipalSum (Z : ℝ) : ℂ := ∑' k : ℕ, dyadIntegral D k Z

theorem dyadIntegral_summable (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun k : ℕ => ‖dyadIntegral D k Z‖) := by
  have hset : ∀ k : ℕ, nonprincipalDyad D k = InitialDyadDomination.nonprincipalDyad D k := by
    intro k
    ext u
    simp only [nonprincipalDyad, InitialDyadDomination.nonprincipalDyad, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_diff, PoissonKernel.principalRows]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h => h1 h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 h, h1⟩
  have key : ∀ k : ℕ, dyadIntegral D k Z = InitialDyadDomination.Jnp D k Z := by
    intro k
    unfold dyadIntegral InitialDyadDomination.Jnp
    rw [hset k]
  simp only [key]
  exact InitialDyadDomination.Jnp_norm_summable D Z hZ

private theorem dyadIntegral_eq (k : ℕ) (Z : ℝ) :
    dyadIntegral D k Z =
      PoissonKernel.J D (PoissonKernel.dyadRows D ((2 : ℝ) ^ k) \ PoissonKernel.principalRows D)
        4 4 2 Z := by
  have hset : nonprincipalDyad D k = InitialDyadDomination.nonprincipalDyad D k := by
    ext u
    simp only [nonprincipalDyad, InitialDyadDomination.nonprincipalDyad, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_diff, PoissonKernel.principalRows]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h => h1 h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 h, h1⟩
  unfold dyadIntegral
  rw [hset]
  try rfl

theorem nonprincipalSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖nonprincipalSum D Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) := by
  obtain ⟨A_F, ρ, hA, hconv, hρ⟩ := DetectorHeight.detector_height_exists D
  have hρpos : 0 < ρ := hρ.1
  obtain ⟨Cs, hCs, hS⟩ := RowsSmall.rows_small D (1 / 10000) (by norm_num)
  obtain ⟨Ce, hCe, Ze, hZe, hE⟩ :=
    RowsExceptional.rows_exceptional D A_F ρ hA hconv hρ (1 / 10000) (by norm_num)
  obtain ⟨Cg, hCg, Zg, hZg, hG⟩ :=
    RowsGoodCentral.rows_good_central D A_F ρ hA hconv hρ (1 / 10000) (by norm_num)
  obtain ⟨Ch, hCh, Zh, hZh, hH⟩ :=
    RowsHeightErrors.rows_height_errors D A_F ρ hA hconv hρ (10 / ρ + 1) (by linarith)
  obtain ⟨Cl, hCl, hL⟩ := RowsLarge.rows_large D (1 / 10000) (by norm_num)
  obtain ⟨U₀, hU₀, hsplit⟩ := RowDyadDecomposition.good_dyad_split D A_F ρ hA hconv hρ
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : ℝ, Z₀ = max (max (max Ze Zg) (max Zh (U₀ ^ 5))) 2 := ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ := InitialDyadDomination.Jnp_norm_tsum_bdd_on_compact D Z₀
  have hC1 : 1 ≤ max (Cs + Ce + Cg + Ch + Cl) (max Cc 1) :=
    le_max_of_le_right (le_max_right _ _)
  refine ⟨max (Cs + Ce + Cg + Ch + Cl) (max Cc 1), lt_of_lt_of_le one_pos hC1, fun Z hZ => ?_⟩
  have hZ1 : 1 ≤ Z := by linarith
  have hZpos : 0 < Z := by linarith
  have hpow1 : 1 ≤ Z ^ (717 / 2000 : ℝ) := Real.one_le_rpow hZ1 (by norm_num)
  have hCpos : 0 < max (Cs + Ce + Cg + Ch + Cl) (max Cc 1) := lt_of_lt_of_le one_pos hC1
  by_cases hbig : Z₀ ≤ Z
  ·
    have hZe' : Ze ≤ Z := le_trans (by rw [hZ₀]; simp [le_max_iff]) hbig
    have hZg' : Zg ≤ Z := le_trans (by rw [hZ₀]; simp [le_max_iff]) hbig
    have hZh' : Zh ≤ Z := le_trans (by rw [hZ₀]; simp [le_max_iff]) hbig
    have hZU : U₀ ^ 5 ≤ Z := le_trans (by rw [hZ₀]; simp [le_max_iff]) hbig
    have hU0nn : 0 ≤ U₀ := by linarith
    have hU : ∀ k ∈ RowsExceptional.intermediateDyads Z, U₀ ≤ (2 : ℝ) ^ k := by
      intro k hk
      obtain ⟨h1, h2⟩ := RowsGoodCentral.mem_intermediateDyads hZ1 hk
      have : U₀ ≤ Z ^ Scales.smallCutoffExponent := by
        calc U₀ = (U₀ ^ 5) ^ Scales.smallCutoffExponent := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hU0nn]
              unfold Scales.smallCutoffExponent; norm_num
          _ ≤ Z ^ Scales.smallCutoffExponent :=
              Real.rpow_le_rpow (pow_nonneg hU0nn 5) hZU (by unfold Scales.smallCutoffExponent; norm_num)
      exact this.trans h1.le
    have hgood : ∑ k ∈ RowsExceptional.intermediateDyads Z,
          PoissonKernel.J D (RowsGoodCentral.goodRows D ρ ((2 : ℝ) ^ k)) 4 4 2 Z =
        ∑ k ∈ RowsExceptional.intermediateDyads Z,
            PoissonKernel.Jcentral D (RowsGoodCentral.goodRows D ρ ((2 : ℝ) ^ k))
              Scales.goodLine Scales.wLine Scales.zLine (((2 : ℝ) ^ k) ^ ρ) Z +
          ∑ k ∈ RowsExceptional.intermediateDyads Z,
            RowsHeightErrors.heightErrors D ρ ((2 : ℝ) ^ k) Z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k hk => hsplit _ Z (hU k hk) hZ
    obtain ⟨_, heq⟩ := RowDyadDecomposition.dyad_five_piece D ρ Z hZ
    have hns : nonprincipalSum D Z = ∑' k : ℕ,
        PoissonKernel.J D (PoissonKernel.dyadRows D ((2 : ℝ) ^ k) \ PoissonKernel.principalRows D)
          4 4 2 Z := by
      unfold nonprincipalSum
      exact tsum_congr fun k => dyadIntegral_eq D k Z
    have key : ∀ a b c d e : ℂ, ‖a + b + (c + d) + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
      intro a b c d e
      have h1 := norm_add_le (a + b + (c + d)) e
      have h2 := norm_add_le (a + b) (c + d)
      have h3 := norm_add_le a b
      have h4 := norm_add_le c d
      linarith
    rw [hns, heq, hgood]
    have bs := hS Z hZ
    have be := hE Z hZe'
    have bg := hG Z hZg'
    have bh := hH Z hZh'
    have bl := (hL Z hZ).2
    have hp : ∀ e : ℝ, e ≤ 717 / 2000 → Z ^ e ≤ Z ^ (717 / 2000 : ℝ) :=
      fun e he => Real.rpow_le_rpow_of_exponent_le hZ1 he
    have e1 := mul_le_mul_of_nonneg_left
      (hp (Scales.mainExponent - 471999 / 10000000 + 1 / 10000) (by unfold Scales.mainExponent; norm_num)) hCs.le
    have e2 := mul_le_mul_of_nonneg_left
      (hp (Scales.mainExponent - 2617 / 80000 + 1 / 10000) (by unfold Scales.mainExponent; norm_num)) hCe.le
    have e3 := mul_le_mul_of_nonneg_left
      (hp (Scales.mainExponent - 7949 / 250000 + 1 / 10000) (by unfold Scales.mainExponent; norm_num)) hCg.le
    have e4 := mul_le_mul_of_nonneg_left
      (hp (Scales.mainExponent - 1) (by unfold Scales.mainExponent; norm_num)) hCh.le
    have e5 := mul_le_mul_of_nonneg_left
      (hp (Scales.mainExponent - 1481 / 2500 + 1 / 10000) (by unfold Scales.mainExponent; norm_num)) hCl.le
    have hfin : (Cs + Ce + Cg + Ch + Cl) * Z ^ (717 / 2000 : ℝ) ≤
        max (Cs + Ce + Cg + Ch + Cl) (max Cc 1) * Z ^ (717 / 2000 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    refine (key _ _ _ _ _).trans ?_
    linarith
  ·
    have hZc : Z ∈ Set.Icc (2 : ℝ) Z₀ := ⟨hZ, (not_le.mp hbig).le⟩
    have hb := hCc Z hZc
    have hsum := dyadIntegral_summable D Z hZpos
    calc ‖nonprincipalSum D Z‖ ≤ ∑' k : ℕ, ‖dyadIntegral D k Z‖ :=
          norm_tsum_le_tsum_norm hsum
      _ = ∑' k : ℕ, ‖InitialDyadDomination.Jnp D k Z‖ := by
          refine tsum_congr fun k => ?_
          exact congrArg norm (dyadIntegral_eq D k Z)
      _ ≤ Cc := hb
      _ ≤ max (Cs + Ce + Cg + Ch + Cl) (max Cc 1) :=
          (le_max_left _ _).trans (le_max_right _ _)
      _ ≤ _ := le_mul_of_one_le_right hCpos.le hpow1

end

end DedekindZetaZeroFree.Quantitative.Rows
