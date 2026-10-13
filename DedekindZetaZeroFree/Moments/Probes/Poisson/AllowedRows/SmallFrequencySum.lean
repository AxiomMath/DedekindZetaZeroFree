module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowFrequencyBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowsSmall

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

noncomputable def smallDyadSum (Z : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1),
    J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z

private lemma count_bound (ε : ℝ) (hε : 0 < ε) (Z : ℝ) (hZ : 2 ≤ Z) :
    ((⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1 : ℕ) : ℝ) ≤
      (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) + 1) * Z ^ (ε / 2) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  have hZ1 : (1:ℝ) ≤ Z := by linarith
  have hs : (0:ℝ) < ε / 2 := by linarith
  have hκ : (0:ℝ) < Scales.smallCutoffExponent := by unfold Scales.smallCutoffExponent; norm_num
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hpow : (0:ℝ) < Z ^ Scales.smallCutoffExponent := Real.rpow_pos_of_pos hZ0 _
  have hL0 : 0 ≤ Real.logb 2 (Z ^ Scales.smallCutoffExponent) := by
    apply Real.logb_nonneg (by norm_num)
    exact Real.one_le_rpow hZ1 (by unfold Scales.smallCutoffExponent; norm_num)
  have hfl : ((⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 (Z ^ Scales.smallCutoffExponent) :=
    Nat.floor_le hL0
  have hLeq : Real.logb 2 (Z ^ Scales.smallCutoffExponent) = Scales.smallCutoffExponent * Real.log Z / Real.log 2 := by
    unfold Real.logb
    rw [Real.log_rpow hZ0]
  have ht : Real.log Z ≤ Z ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hZ0.le hs
  have ht' : Real.log Z * (ε / 2) ≤ Z ^ (ε / 2) := by
    rwa [le_div_iff₀ hs] at ht
  have hcoef : 0 ≤ Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) :=
    div_nonneg hκ.le (mul_nonneg hl2.le hs.le)
  have key : Scales.smallCutoffExponent * Real.log Z / Real.log 2
      = (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2))) * (Real.log Z * (ε / 2)) := by
    have hl2' : Real.log 2 ≠ 0 := hl2.ne'
    have hε' : ε ≠ 0 := hε.ne'
    field_simp <;> ring
  have hLle : Real.logb 2 (Z ^ Scales.smallCutoffExponent)
      ≤ (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2))) * Z ^ (ε / 2) := by
    rw [hLeq, key]
    exact mul_le_mul_of_nonneg_left ht' hcoef
  push_cast
  calc ((⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ : ℕ) : ℝ) + 1
      ≤ (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2))) * Z ^ (ε / 2) + 1 * 1 := by
        have : (1:ℝ) ≤ Z ^ (ε / 2) := Real.one_le_rpow hZ1 hs.le
        linarith
    _ ≤ (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2))) * Z ^ (ε / 2) + Z ^ (ε / 2) := by
        have : (1:ℝ) ≤ Z ^ (ε / 2) := Real.one_le_rpow hZ1 hs.le
        linarith
    _ = (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) + 1) * Z ^ (ε / 2) := by ring

theorem rows_small (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖smallDyadSum D Z‖ ≤ C * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε) := by
  obtain ⟨A0, hA0, hk0⟩ := LowNormRowBound.lowNorm_rows_small_k0 D (ε / 2) (by linarith)
  obtain ⟨Cc, hCc, hcount⟩ := ActualRowCount.dyadRows_count D
  obtain ⟨Cε, hCε, hJ⟩ := RowLowContour.JCont_bound D Cc 1 hCc (ε / 2) (by linarith)
  have hs : (0:ℝ) < ε / 2 := by linarith
  have hκ : (0:ℝ) < Scales.smallCutoffExponent := by unfold Scales.smallCutoffExponent; norm_num
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (0:ℝ) < Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) + 1 := by
    have := div_nonneg hκ.le (mul_nonneg hl2.le hs.le)
    linarith
  have hd : Scales.contourOffset = 1 / 10000000 := by unfold Scales.contourOffset; norm_num
  have hE := RowLowContour.E_relative
  refine ⟨(A0 + Cε) * (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) + 1), mul_pos (by linarith) hK,
    ?_⟩
  intro Z hZ
  have hZ0 : (0:ℝ) < Z := by linarith
  have hZ1 : (1:ℝ) ≤ Z := by linarith
  have hpow : (0:ℝ) < Z ^ Scales.smallCutoffExponent := Real.rpow_pos_of_pos hZ0 _
  have hL0 : 0 ≤ Real.logb 2 (Z ^ Scales.smallCutoffExponent) := by
    apply Real.logb_nonneg (by norm_num)
    exact Real.one_le_rpow hZ1 (by unfold Scales.smallCutoffExponent; norm_num)
  have hfl : ((⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 (Z ^ Scales.smallCutoffExponent) :=
    Nat.floor_le hL0
  have hZθ : 0 ≤ Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2) := Real.rpow_nonneg hZ0.le _
  have hB0 : 0 ≤ (A0 + Cε) * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2) :=
    mul_nonneg (by linarith) hZθ
  have hterm : ∀ k ∈ Finset.range (⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1),
      ‖J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z‖
        ≤ (A0 + Cε) * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2) := by
    intro k hk
    have hkN : k ≤ ⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have h0 := hk0 Z hZ
      nlinarith [mul_nonneg hCε.le hZθ]
    · have hU2 : (2:ℝ) ≤ (2:ℝ) ^ k := by
        calc (2:ℝ) = (2:ℝ) ^ 1 := by norm_num
          _ ≤ (2:ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have hUZ : (2:ℝ) ^ k ≤ Z ^ Scales.smallCutoffExponent := by
        have hk' : (k:ℝ) ≤ Real.logb 2 (Z ^ Scales.smallCutoffExponent) :=
          le_trans (Nat.cast_le.mpr hkN) hfl
        have h2 : (2:ℝ) ^ (k:ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (Z ^ Scales.smallCutoffExponent)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hk'
        rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hpow] at h2
        exact h2
      have hUs : ((2:ℝ) ^ k) ^ (1 + 1 / 25 + ε / 2) ≤ (Z ^ Scales.smallCutoffExponent) ^ (1 + 1 / 25 + ε / 2) :=
        Real.rpow_le_rpow (by positivity) hUZ (by linarith)
      have hZs : (Z ^ Scales.smallCutoffExponent) ^ (1 + 1 / 25 + ε / 2)
          = Z ^ (Scales.smallCutoffExponent * (1 + 1 / 25 + ε / 2)) :=
        (Real.rpow_mul hZ0.le _ _).symm
      have hexp : Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine + Scales.smallCutoffExponent * (1 + 1 / 25 + ε / 2)
          ≤ Scales.mainExponent - 471999 / 10000000 + ε / 2 := by
        unfold Scales.smallCutoffExponent
        linarith
      have hCsub : (dyadRows D ((2 : ℝ) ^ k) \ principalRows D)
          ⊆ {u : D.Row | u.u ≠ (1 : ↥D.recipe.A.R)} ∩ dyadRows D ((2 : ℝ) ^ k) :=
        fun u hu => ⟨fun h1 => hu.2 h1, hu.1⟩
      obtain ⟨hfinU, hcardU⟩ := hcount ((2 : ℝ) ^ k) (by linarith)
      have hfin : (dyadRows D ((2 : ℝ) ^ k) \ principalRows D).Finite :=
        hfinU.subset (fun u hu => hu.1)
      have hcard : ((dyadRows D ((2 : ℝ) ^ k) \ principalRows D).ncard : ℝ)
          ≤ Cc * ((2 : ℝ) ^ k) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        have h1 : (dyadRows D ((2 : ℝ) ^ k) \ principalRows D).ncard
            ≤ (dyadRows D ((2 : ℝ) ^ k)).ncard :=
          Set.ncard_le_ncard (fun u hu => hu.1) hfinU
        have h1' : ((dyadRows D ((2 : ℝ) ^ k) \ principalRows D).ncard : ℝ)
            ≤ ((dyadRows D ((2 : ℝ) ^ k)).ncard : ℝ) := by exact_mod_cast h1
        linarith
      have hb := hJ ((2 : ℝ) ^ k) Z hU2 hZ _ hCsub hfin hcard
      have hJe := RowLowContour.J_initial_eq D ((2 : ℝ) ^ k) Z hU2 hZ _ hCsub hfin
      rw [hJe]
      have hEnn : 0 ≤ Cε * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) :=
        mul_nonneg hCε.le (Real.rpow_nonneg hZ0.le _)
      calc ‖RowLowContour.JCont D _ Scales.rightLine Scales.wLine Scales.zLine Z‖
          ≤ Cε * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (1 + 1 / 25 + ε / 2) := hb
        _ ≤ Cε * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * (Z ^ Scales.smallCutoffExponent) ^ (1 + 1 / 25 + ε / 2) :=
            mul_le_mul_of_nonneg_left hUs hEnn
        _ = Cε * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine + Scales.smallCutoffExponent * (1 + 1 / 25 + ε / 2)) := by
            rw [hZs, Real.rpow_add hZ0, mul_assoc]
        _ ≤ Cε * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 hexp) hCε.le
        _ ≤ (A0 + Cε) * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hZθ
  unfold smallDyadSum
  calc ‖∑ k ∈ Finset.range (⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1),
        J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z‖
      ≤ ∑ k ∈ Finset.range (⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1),
          ‖J D (dyadRows D ((2 : ℝ) ^ k) \ principalRows D) 4 4 2 Z‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1),
          (A0 + Cε) * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2) :=
        Finset.sum_le_sum hterm
    _ = ((⌊Real.logb 2 (Z ^ Scales.smallCutoffExponent)⌋₊ + 1 : ℕ) : ℝ)
          * ((A0 + Cε) * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) + 1) * Z ^ (ε / 2))
          * ((A0 + Cε) * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε / 2)) :=
        mul_le_mul_of_nonneg_right (count_bound ε hε Z hZ) hB0
    _ = ((A0 + Cε) * (Scales.smallCutoffExponent / (Real.log 2 * (ε / 2)) + 1))
          * Z ^ (Scales.mainExponent - 471999 / 10000000 + ε) := by
        have hsum : ε / 2 + (Scales.mainExponent - 471999 / 10000000 + ε / 2)
            = Scales.mainExponent - 471999 / 10000000 + ε := by ring
        rw [← hsum, Real.rpow_add hZ0 (ε / 2) (Scales.mainExponent - 471999 / 10000000 + ε / 2)]
        ring

end DedekindZetaZeroFree.Quantitative.RowsSmall
