module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.GoodRowDeformation
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.ExceptionalSum

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowsGoodCentral

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.DetectorDef
  DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.RowsExceptional

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def goodRows (ρ U : ℝ) : Set D.Row :=
  {u | u ∈ dyadRows D U ∧ u ∉ principalRows D ∧ u ∉ exceptionalSet D ρ U}

theorem entireNumerator_of_ne_one (u : D.Row) (hu : u.u ≠ 1) :
    RowKernelGrowth.EntireNumerator D u := by
  have hnp : ¬ (D.inducers u).plus.character.IsPrincipal :=
    (RowNonprincipal.inducers_nonprincipal D u hu).1
  obtain ⟨G, hG, hGL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A (D.inducers u).plus hnp
  have hm := RowHeckeBridge.mask_differentiable D.recipe.A (D.inducers u).plus hnp
    (RowHeckeBridge.deletionSet D u) (RowHeckeBridge.deletionSet_finite D u)
  refine ⟨fun s => Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
    (fun v => (D.inducers u).plus.character v.asIdeal) s * G s, hm.mul hG, fun s hs => ?_⟩
  beta_reduce
  rw [hGL s (by linarith)]
  exact (RowHeckeBridge.Lpsi_eq_mask_mul D u hnp s hs).symm

theorem rows_good_central_dyad (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ U : ℝ, U₀ ≤ U →
      Z ^ Scales.smallCutoffExponent < U → U ≤ Z ^ Scales.largeCutoffExponent →
        ‖Jcentral D (goodRows D ρ U) Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ ≤
          C * Z ^ Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine * U ^ (26 / 25 + ε) := by
  classical
  obtain ⟨C1, hC1, U1, hU1, h1⟩ :=
    RowKernelGrowth.wzIntegral_decay_rect D A_F ρ hA hconv hρ ε hε 2 (by norm_num)
  obtain ⟨C2, hC2, hcnt⟩ := ActualRowCount.dyadRows_count D
  have hint : MeasureTheory.Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by simp)
  set K : ℝ := ∫ t : ℝ, (1 + ‖t‖) ^ (-(2 : ℝ)) with hK
  have hK0 : 0 ≤ K := MeasureTheory.integral_nonneg (fun t => by positivity)
  refine ⟨(C2 * (C1 * (K + 1))) + 1, by positivity, U1, hU1, ?_⟩
  intro Z hZ U hU _ _
  have hU2 : 2 ≤ U := hU1.trans hU
  have hU0 : 0 < U := by linarith
  have hZ0 : 0 < Z := by linarith
  obtain ⟨hfinD, hcard⟩ := hcnt U (by linarith)
  have hfin : (goodRows D ρ U).Finite := hfinD.subset (fun u (hu : u ∈ goodRows D ρ U) => hu.1)
  have hcardG : ((goodRows D ρ U).ncard : ℝ) ≤ C2 * U := by
    refine le_trans ?_ hcard
    exact_mod_cast Set.ncard_le_ncard (fun u (hu : u ∈ goodRows D ρ U) => hu.1) hfinD
  set E0 := Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine with hE0
  set P := U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) with hP
  have hPnn : 0 ≤ P := by positivity
  have hZE : 0 ≤ Z ^ E0 := by positivity

  have hrow : ∀ u ∈ goodRows D ρ U,
      ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
        wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        (C1 * (K + 1)) * Z ^ E0 * P := by
    intro u hu
    obtain ⟨hud, hup, hue⟩ := hu
    have hu1 : u.u ≠ 1 := hup
    have hent := entireNumerator_of_ne_one D u hu1
    have hρU : 0 ≤ U ^ ρ := by positivity
    have hb : ∀ t ∈ Set.Icc (-(U ^ ρ)) (U ^ ρ),
        ‖wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
          (C1 * Z ^ E0 * P) * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
      intro t ht
      have htab : |t| ≤ U ^ ρ := abs_le.mpr ⟨ht.1, ht.2⟩
      have := h1 U hU u hu1 hent hud.1 hud.2 hue ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Z hZ0
        (by simp) (by
          have : Scales.goodLine ≤ Scales.rightLine := by
            unfold Scales.goodLine Scales.rightLine Scales.contourOffset; norm_num
          simpa using this) (by simpa using htab.trans (by linarith))
      simpa [hE0, Scales.kernelExponent, hP, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using this
    have hg : MeasureTheory.Integrable (fun t : ℝ => (C1 * Z ^ E0 * P) * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      hint.const_mul _
    have h2 : ‖∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
        wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        ∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ), (C1 * Z ^ E0 * P) * (1 + ‖t‖) ^ (-(2 : ℝ)) :=
      MeasureTheory.norm_integral_le_of_norm_le hg.integrableOn
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hb)
    have h3 : ∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ), (C1 * Z ^ E0 * P) * (1 + ‖t‖) ^ (-(2 : ℝ)) ≤
        ∫ t : ℝ, (C1 * Z ^ E0 * P) * (1 + ‖t‖) ^ (-(2 : ℝ)) :=
      MeasureTheory.setIntegral_le_integral hg
        (Filter.Eventually.of_forall (fun t => by positivity))
    have e3 : ∫ t : ℝ, (C1 * Z ^ E0 * P) * (1 + ‖t‖) ^ (-(2 : ℝ)) = (C1 * Z ^ E0 * P) * K :=
      MeasureTheory.integral_const_mul _ _
    have hpi : ‖(2 * (Real.pi : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_mul]
      simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have := Real.pi_gt_three
      rw [inv_le_one₀ (by positivity)]
      linarith
    rw [norm_mul]
    have hB : 0 ≤ C1 * Z ^ E0 * P := by positivity
    calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
          wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖
        ≤ 1 * ((C1 * Z ^ E0 * P) * K) :=
          mul_le_mul hpi (h2.trans (h3.trans e3.le)) (norm_nonneg _) zero_le_one
      _ ≤ (C1 * (K + 1)) * Z ^ E0 * P := by
          have : 0 ≤ C1 * Z ^ E0 * P := hB
          nlinarith [mul_nonneg this hK0]

  unfold Jcentral
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsum := norm_sum_le hfin.toFinset (fun u => (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
      wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z)
  refine hsum.trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ (fun u hu => hrow u ((Set.Finite.mem_toFinset hfin).mp hu))).trans ?_
  rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin]
  have hUp : U * P = U ^ (26 / 25 + ε) := by
    rw [hP, ← Real.rpow_one_add' hU0.le (by unfold Scales.zLine; linarith)]
    congr 1
    unfold Scales.zLine; ring
  have hB : 0 ≤ (C1 * (K + 1)) * Z ^ E0 * P := by positivity
  calc ((goodRows D ρ U).ncard : ℝ) * ((C1 * (K + 1)) * Z ^ E0 * P)
      ≤ (C2 * U) * ((C1 * (K + 1)) * Z ^ E0 * P) := mul_le_mul_of_nonneg_right hcardG hB
    _ = (C2 * (C1 * (K + 1))) * Z ^ E0 * (U * P) := by ring
    _ = (C2 * (C1 * (K + 1))) * Z ^ E0 * U ^ (26 / 25 + ε) := by rw [hUp]
    _ ≤ ((C2 * (C1 * (K + 1))) + 1) * Z ^ E0 * U ^ (26 / 25 + ε) := by
        have : 0 ≤ Z ^ E0 * U ^ (26 / 25 + ε) := by positivity
        nlinarith

theorem exponent_sum :
    Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine + Scales.largeCutoffExponent * (26 / 25) =
      Scales.mainExponent - 7949 / 250000 := by
  unfold Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.largeCutoffExponent Scales.mainExponent
  norm_num

theorem mem_intermediateDyads {Z : ℝ} (hZ : 1 ≤ Z) {k : ℕ} (hk : k ∈ intermediateDyads Z) :
    Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ Z ^ Scales.largeCutoffExponent := by
  unfold intermediateDyads at hk
  rw [Finset.mem_filter, Finset.mem_range] at hk
  refine ⟨hk.2, ?_⟩
  have hpos : (0 : ℝ) < Z ^ Scales.largeCutoffExponent := Real.rpow_pos_of_pos (by linarith) _
  have h1 : (1 : ℝ) ≤ Z ^ Scales.largeCutoffExponent :=
    Real.one_le_rpow hZ (by unfold Scales.largeCutoffExponent; norm_num)
  have hnn : 0 ≤ Real.logb 2 (Z ^ Scales.largeCutoffExponent) :=
    Real.logb_nonneg (by norm_num) h1
  have hk' : (k : ℝ) ≤ Real.logb 2 (Z ^ Scales.largeCutoffExponent) := by
    have := Nat.lt_succ_iff.mp hk.1
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hnn)
  have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).mp hk'
  simpa using this

theorem card_intermediateDyads_le {Z : ℝ} (hZ : 1 ≤ Z) :
    ((intermediateDyads Z).card : ℝ) ≤ Real.log Z / Real.log 2 + 1 := by
  unfold intermediateDyads
  have h1 : (1 : ℝ) ≤ Z ^ Scales.largeCutoffExponent :=
    Real.one_le_rpow hZ (by unfold Scales.largeCutoffExponent; norm_num)
  have hnn : 0 ≤ Real.logb 2 (Z ^ Scales.largeCutoffExponent) := Real.logb_nonneg (by norm_num) h1
  have hc : ((Finset.range (⌊Real.logb 2 (Z ^ Scales.largeCutoffExponent)⌋₊ + 1)).filter
      (fun k => Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k)).card ≤ ⌊Real.logb 2 (Z ^ Scales.largeCutoffExponent)⌋₊ + 1 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have hc' : (((Finset.range (⌊Real.logb 2 (Z ^ Scales.largeCutoffExponent)⌋₊ + 1)).filter
      (fun k => Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k)).card : ℝ) ≤
      Real.logb 2 (Z ^ Scales.largeCutoffExponent) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hc
    push_cast at this
    linarith [Nat.floor_le hnn]
  refine hc'.trans ?_
  have hlog : Real.logb 2 (Z ^ Scales.largeCutoffExponent) = Scales.largeCutoffExponent * (Real.log Z / Real.log 2) := by
    rw [Real.logb, Real.log_rpow (by linarith)]; ring
  rw [hlog]
  have hl : 0 ≤ Real.log Z / Real.log 2 :=
    div_nonneg (Real.log_nonneg hZ) (Real.log_nonneg (by norm_num))
  have : Scales.largeCutoffExponent ≤ 1 := by unfold Scales.largeCutoffExponent; norm_num
  nlinarith

theorem rows_good_central (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ‖∑ k ∈ intermediateDyads Z,
          Jcentral D (goodRows D ρ ((2 : ℝ) ^ k)) Scales.goodLine Scales.wLine Scales.zLine
            (((2 : ℝ) ^ k) ^ ρ) Z‖ ≤
        C * Z ^ (Scales.mainExponent - 7949 / 250000 + ε) := by
  obtain ⟨C, hC, U₀, hU₀, hdy⟩ :=
    rows_good_central_dyad D A_F ρ hA hconv hρ (ε / 2) (by positivity)
  have hκl : Scales.largeCutoffExponent ≤ 1 := by unfold Scales.largeCutoffExponent; norm_num
  have hκl0 : 0 < Scales.largeCutoffExponent := by unfold Scales.largeCutoffExponent; norm_num
  refine ⟨C * (2 / (ε * Real.log 2) + 1), by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity, max 2 (U₀ ^ 5), le_max_left _ _, fun Z hZ => ?_⟩
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZpos : 0 < Z := by linarith
  have hZU : U₀ ^ 5 ≤ Z := (le_max_right _ _).trans hZ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 ≠ 0 := hlog2.ne'
  have hU0nn : 0 ≤ U₀ := by linarith

  have hterm : ∀ k ∈ intermediateDyads Z,
      ‖Jcentral D (goodRows D ρ ((2 : ℝ) ^ k)) Scales.goodLine Scales.wLine Scales.zLine
            (((2 : ℝ) ^ k) ^ ρ) Z‖ ≤ C * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent) := by
    intro k hk
    obtain ⟨h1, h2⟩ := mem_intermediateDyads hZ1 hk
    have hU : U₀ ≤ (2 : ℝ) ^ k := by
      have : U₀ ≤ Z ^ Scales.smallCutoffExponent := by
        have h0 := hU0nn
        calc U₀ = (U₀ ^ 5) ^ Scales.smallCutoffExponent := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
              unfold Scales.smallCutoffExponent; norm_num
          _ ≤ Z ^ Scales.smallCutoffExponent :=
              Real.rpow_le_rpow (pow_nonneg hU0nn 5) hZU (by unfold Scales.smallCutoffExponent; norm_num)
      exact this.trans h1.le
    have := hdy Z hZ2 _ hU h1 h2
    refine this.trans ?_
    have hUpow : ((2 : ℝ) ^ k) ^ (26 / 25 + ε / 2) ≤ Z ^ (Scales.largeCutoffExponent * (26 / 25 + ε / 2)) := by
      rw [Real.rpow_mul hZpos.le]
      exact Real.rpow_le_rpow (by positivity) h2 (by positivity)
    have hexp : (Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent = Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine + Scales.largeCutoffExponent * (26 / 25 + ε / 2) := by
      rw [← exponent_sum]; ring
    rw [hexp, Real.rpow_add hZpos, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hUpow (by positivity)) hC.le
  calc ‖∑ k ∈ intermediateDyads Z,
          Jcentral D (goodRows D ρ ((2 : ℝ) ^ k)) Scales.goodLine Scales.wLine Scales.zLine
            (((2 : ℝ) ^ k) ^ ρ) Z‖
      ≤ ∑ k ∈ intermediateDyads Z, ‖Jcentral D (goodRows D ρ ((2 : ℝ) ^ k)) Scales.goodLine
          Scales.wLine Scales.zLine (((2 : ℝ) ^ k) ^ ρ) Z‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ intermediateDyads Z, C * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent) :=
        Finset.sum_le_sum hterm
    _ = ((intermediateDyads Z).card : ℝ) * (C * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.log Z / Real.log 2 + 1) * (C * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent)) :=
        mul_le_mul_of_nonneg_right (card_intermediateDyads_le hZ1) (by positivity)
    _ ≤ ((2 / (ε * Real.log 2) + 1) * Z ^ (ε / 2)) * (C * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hl : Real.log Z ≤ Z ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hZpos.le (by positivity)
        have h1 : 1 ≤ Z ^ (ε / 2) := Real.one_le_rpow hZ1 (by positivity)
        have : Real.log Z / Real.log 2 ≤ 2 / (ε * Real.log 2) * Z ^ (ε / 2) := by
          rw [div_le_iff₀ hlog2]
          calc Real.log Z ≤ Z ^ (ε / 2) / (ε / 2) := hl
            _ = 2 / (ε * Real.log 2) * Z ^ (ε / 2) * Real.log 2 := by
              have : ε ≠ 0 := hε.ne'
              field_simp
        nlinarith
    _ ≤ (C * (2 / (ε * Real.log 2) + 1)) * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε) := by
        have h3 : Z ^ (ε / 2) * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent) ≤ Z ^ ((Scales.mainExponent - 7949 / 250000) + ε) := by
          rw [← Real.rpow_add hZpos]
          exact Real.rpow_le_rpow_of_exponent_le hZ1 (by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hκl)])
        have hc : 0 ≤ C * (2 / (ε * Real.log 2) + 1) := by positivity
        calc ((2 / (ε * Real.log 2) + 1) * Z ^ (ε / 2)) * (C * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent))
            = (C * (2 / (ε * Real.log 2) + 1)) *
              (Z ^ (ε / 2) * Z ^ ((Scales.mainExponent - 7949 / 250000) + ε / 2 * Scales.largeCutoffExponent)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h3 hc

end

end DedekindZetaZeroFree.Quantitative.RowsGoodCentral
