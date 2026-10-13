module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowContourBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowsExceptional

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.DetectorDef
  DedekindZetaZeroFree.Quantitative.DetectorHeight

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def intermediateDyads (Z : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.logb 2 (Z ^ Scales.largeCutoffExponent)⌋₊ + 1)).filter
    (fun k => Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k)

def exceptionalDyadSum (ρ Z : ℝ) : ℂ :=
  ∑ k ∈ intermediateDyads Z, J D (exceptionalSet D ρ ((2 : ℝ) ^ k)) 4 4 2 Z

theorem exceptionalSet_sub (ρ U : ℝ) :
    exceptionalSet D ρ U ⊆ {u : D.Row | u.u ≠ 1} ∩ dyadRows D U := by
  intro u hu
  exact ⟨hu.1, hu.2.1, hu.2.2.1⟩

theorem exceptional_row_contour (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (U Z : ℝ) (hU : 2 ≤ U) (hZ : 2 ≤ Z) :
    (exceptionalSet D ρ U).Finite ∧
      J D (exceptionalSet D ρ U) 4 4 2 Z =
        RowLowContour.JCont D (exceptionalSet D ρ U) Scales.rightLine Scales.wLine Scales.zLine Z := by
  have hfin : (exceptionalSet D ρ U).Finite :=
    (ActualRowCount.dyadRows_finite D U).subset ((exceptionalSet_sub D ρ U).trans Set.inter_subset_right)
  exact ⟨hfin, RowLowContour.J_initial_eq D U Z hU hZ _ (exceptionalSet_sub D ρ U) hfin⟩

private lemma card_intermediateDyads_le (δ : ℝ) (hδ : 0 < δ) (Z : ℝ) (hZ : 2 ≤ Z) :
    ((intermediateDyads Z).card : ℝ) ≤ (1 / (δ * Real.log 2) + 1) * Z ^ δ := by
  have hZ0 : 0 < Z := by linarith
  have hκ : (0 : ℝ) ≤ Scales.largeCutoffExponent := by unfold Scales.largeCutoffExponent; norm_num
  have hκ1 : Scales.largeCutoffExponent ≤ 1 := by unfold Scales.largeCutoffExponent; norm_num
  have hZκ : (1 : ℝ) ≤ Z ^ Scales.largeCutoffExponent := Real.one_le_rpow (by linarith) hκ
  set L : ℝ := Real.logb 2 (Z ^ Scales.largeCutoffExponent) with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hZκ
  have hsub : intermediateDyads Z ⊆ Finset.range (⌊L⌋₊ + 1) := Finset.filter_subset _ _
  have hcard : ((intermediateDyads Z).card : ℝ) ≤ (⌊L⌋₊ + 1 : ℝ) := by
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hfl : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL0
  have hlogL : L ≤ Real.log Z / Real.log 2 := by
    rw [hL, Real.logb, Real.log_rpow hZ0]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    have : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
    nlinarith
  have hlogZ : Real.log Z ≤ Z ^ δ / δ := Real.log_le_rpow_div hZ0.le hδ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ Z ^ δ := Real.one_le_rpow (by linarith) hδ.le
  have hfinal : (⌊L⌋₊ + 1 : ℝ) ≤ (1 / (δ * Real.log 2) + 1) * Z ^ δ := by
    have e1 : Real.log Z / Real.log 2 ≤ Z ^ δ / (δ * Real.log 2) := by
      rw [div_le_div_iff₀ hl2 (by positivity)]
      have := hlogZ
      rw [le_div_iff₀ hδ] at this
      nlinarith
    have e2 : Z ^ δ / (δ * Real.log 2) = (1 / (δ * Real.log 2)) * Z ^ δ := by ring
    have hpos : 0 ≤ 1 / (δ * Real.log 2) := by positivity
    nlinarith
  linarith

theorem rows_exceptional (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ‖exceptionalDyadSum D ρ Z‖ ≤ C * Z ^ (Scales.mainExponent - 2617 / 80000 + ε) := by
  obtain ⟨Cc, hCc, U₀, hU₀, hcard⟩ := Detect.exceptionalSet_card D A_F ρ hA hconv hρ
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hJb := RowLowContour.JCont_bound D Cc (317 / 500) hCc (ε / 4) hε4
  obtain ⟨Cj, hCj, hJ⟩ := hJb
  have hδ : (0 : ℝ) < ε / 4 := by linarith
  have hE : Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine + Scales.largeCutoffExponent * (337 / 500) =
      Scales.mainExponent - 2617 / 80000 := by
    unfold Scales.kernelExponent Scales.rightLine Scales.contourOffset Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.mainExponent Scales.wLine
      Scales.zLine Scales.largeCutoffExponent
    norm_num
  set T : ℝ := Scales.mainExponent - 2617 / 80000 + ε / 4 with hT
  have hκs : Scales.smallCutoffExponent = 1 / 5 := by unfold Scales.smallCutoffExponent; norm_num
  have hκ1 : Scales.largeCutoffExponent ≤ 1 := by unfold Scales.largeCutoffExponent; norm_num
  have hκ0 : (0 : ℝ) ≤ Scales.largeCutoffExponent := by unfold Scales.largeCutoffExponent; norm_num
  refine ⟨(1 / (ε / 4 * Real.log 2) + 1) * Cj, by positivity, max 2 (U₀ ^ (5 : ℝ)),
    le_max_left _ _, ?_⟩
  intro Z hZ
  have hZ2 : 2 ≤ Z := le_trans (le_max_left _ _) hZ
  have hZpos : 0 < Z := by linarith
  have h5 : U₀ ^ (5 : ℝ) ≤ Z := le_trans (le_max_right _ _) hZ
  have hZκs : U₀ ≤ Z ^ Scales.smallCutoffExponent := by
    rw [hκs]
    calc U₀ = (U₀ ^ (5 : ℝ)) ^ (1 / 5 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ Z ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) h5 (by norm_num)
  have hterm : ∀ k ∈ intermediateDyads Z,
      ‖J D (exceptionalSet D ρ ((2 : ℝ) ^ k)) 4 4 2 Z‖ ≤ Cj * Z ^ T := by
    intro k hk
    unfold intermediateDyads at hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkL, hkZ⟩ := hk
    have hUU₀ : U₀ ≤ (2 : ℝ) ^ k := le_of_lt (lt_of_le_of_lt hZκs hkZ)
    have hU2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := le_trans hU₀ hUU₀
    have hUle : (2 : ℝ) ^ k ≤ Z ^ Scales.largeCutoffExponent := by
      have hk' : k ≤ ⌊Real.logb 2 (Z ^ Scales.largeCutoffExponent)⌋₊ := Nat.lt_succ_iff.mp hkL
      have hL0 : 0 ≤ Real.logb 2 (Z ^ Scales.largeCutoffExponent) :=
        Real.logb_nonneg (by norm_num) (Real.one_le_rpow (by linarith) hκ0)
      have hkR : (k : ℝ) ≤ Real.logb 2 (Z ^ Scales.largeCutoffExponent) :=
        le_trans (by exact_mod_cast hk') (Nat.floor_le hL0)
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hkR
      rw [Real.rpow_logb (by norm_num) (by norm_num) (Real.rpow_pos_of_pos hZpos _),
        Real.rpow_natCast] at this
      exact this
    obtain ⟨hfin, _⟩ := hcard _ hUU₀
    have hsub := exceptionalSet_sub D ρ ((2 : ℝ) ^ k)
    have hcardb : ((exceptionalSet D ρ ((2 : ℝ) ^ k)).ncard : ℝ) ≤ Cc * ((2 : ℝ) ^ k) ^ (317 / 500 : ℝ) :=
      (hcard _ hUU₀).2
    have hJc := hJ ((2 : ℝ) ^ k) Z hU2 hZ2 (exceptionalSet D ρ ((2 : ℝ) ^ k)) hsub hfin hcardb
    rw [(exceptional_row_contour D A_F ρ hA hconv hρ ((2 : ℝ) ^ k) Z hU2 hZ2).2]
    have hp : (0 : ℝ) ≤ 317 / 500 + 1 / 25 + ε / 4 := by linarith
    have hUp : ((2 : ℝ) ^ k) ^ (317 / 500 + 1 / 25 + ε / 4) ≤
        Z ^ (Scales.largeCutoffExponent * (317 / 500 + 1 / 25 + ε / 4)) := by
      calc ((2 : ℝ) ^ k) ^ (317 / 500 + 1 / 25 + ε / 4) ≤ (Z ^ Scales.largeCutoffExponent) ^ (317 / 500 + 1 / 25 + ε / 4) :=
            Real.rpow_le_rpow (by linarith) hUle hp
        _ = Z ^ (Scales.largeCutoffExponent * (317 / 500 + 1 / 25 + ε / 4)) := by
            rw [← Real.rpow_mul hZpos.le]
    have hexp : Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine + Scales.largeCutoffExponent * (317 / 500 + 1 / 25 + ε / 4)
        ≤ T := by
      have e : Scales.largeCutoffExponent * (317 / 500 + 1 / 25 + ε / 4) =
          Scales.largeCutoffExponent * (337 / 500) + Scales.largeCutoffExponent * (ε / 4) := by ring
      have h2 : Scales.largeCutoffExponent * (ε / 4) ≤ ε / 4 := mul_le_of_le_one_left (by linarith) hκ1
      rw [e, hT]
      linarith
    have hEpos : 0 ≤ Cj := hCj.le
    calc ‖RowLowContour.JCont D (exceptionalSet D ρ ((2 : ℝ) ^ k)) Scales.rightLine Scales.wLine Scales.zLine Z‖
        ≤ Cj * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * ((2 : ℝ) ^ k) ^ (317 / 500 + 1 / 25 + ε / 4) := hJc
      _ ≤ Cj * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
            Z ^ (Scales.largeCutoffExponent * (317 / 500 + 1 / 25 + ε / 4)) :=
          mul_le_mul_of_nonneg_left hUp (by positivity)
      _ = Cj * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine +
            Scales.largeCutoffExponent * (317 / 500 + 1 / 25 + ε / 4)) := by
          rw [Real.rpow_add hZpos]; ring
      _ ≤ Cj * Z ^ T := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hEpos
  have hsum_le : ‖exceptionalDyadSum D ρ Z‖ ≤
      ∑ k ∈ intermediateDyads Z, Cj * Z ^ T := by
    unfold exceptionalDyadSum
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum_le
  have hcnt := card_intermediateDyads_le (ε / 4) hδ Z hZ2
  have hTpos : 0 ≤ Cj * Z ^ T := by positivity
  have hfin2 : ((intermediateDyads Z).card : ℝ) * (Cj * Z ^ T) ≤
      ((1 / (ε / 4 * Real.log 2) + 1) * Z ^ (ε / 4)) * (Cj * Z ^ T) :=
    mul_le_mul_of_nonneg_right hcnt hTpos
  have hsum : Z ^ (ε / 4) * Z ^ T = Z ^ (Scales.mainExponent - 2617 / 80000 + ε / 2) := by
    rw [← Real.rpow_add hZpos, hT]; congr 1; ring
  have hfinal : Z ^ (Scales.mainExponent - 2617 / 80000 + ε / 2) ≤ Z ^ (Scales.mainExponent - 2617 / 80000 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc ‖exceptionalDyadSum D ρ Z‖ ≤ _ := hsum_le
    _ ≤ _ := hfin2
    _ = (1 / (ε / 4 * Real.log 2) + 1) * Cj * (Z ^ (ε / 4) * Z ^ T) := by ring
    _ = (1 / (ε / 4 * Real.log 2) + 1) * Cj * Z ^ (Scales.mainExponent - 2617 / 80000 + ε / 2) := by
        rw [hsum]
    _ ≤ (1 / (ε / 4 * Real.log 2) + 1) * Cj * Z ^ (Scales.mainExponent - 2617 / 80000 + ε) := by
        apply mul_le_mul_of_nonneg_left hfinal
        positivity

end

end DedekindZetaZeroFree.Quantitative.RowsExceptional
