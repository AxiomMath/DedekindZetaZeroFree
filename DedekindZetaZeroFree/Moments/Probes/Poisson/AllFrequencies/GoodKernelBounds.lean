module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.FrequencyRectangles
public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelRegularity
public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawGoodKernelBounds31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

private theorem L6_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = Scales.zLine → ‖D.recipe.L (6 * z)‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := RawRightHecke31.recipe_L_right D (2 / 5) (by norm_num)
  exact ⟨C, hC, fun z hz => (h z (by rw [hz]; norm_num [Scales.zLine])).2.1⟩

private theorem corr_box_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Frequency D.recipe, ∀ ξ w z : ℂ, Scales.goodLine ≤ ξ.re →
      Scales.wLine ≤ w.re → Scales.zLine ≤ z.re →
      ‖AllRowEuler.InitialSeparation.correctionProduct D.context (FixedData.rawFrequency D u)
          ξ w z‖ ≤ C * frequencyNorm D.recipe u ^ ε := by
  obtain ⟨C, hC, h⟩ := RawEulerProduct31.correctionProduct_subpower_boxes D ε hε
  refine ⟨C, hC, fun u ξ w z h1 h2 h3 => ?_⟩
  have hp : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.boxes := by
    refine Or.inl (Or.inl ?_)
    exact ⟨h1, h2, h3⟩
  have := (h (FixedData.rawFrequency D u) _ hp).2
  rw [FixedData.rawFrequency_norm D u] at this
  exact this

private theorem minus_inv_rect (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ ξ : ℂ, Scales.goodLine ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
        ‖((FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C * U ^ ε := by
  obtain ⟨C1, hC1, U1, hU1, h1⟩ :=
    RawReciprocalPrimitive31.raw_reciprocal_primitive D A ρ hA hconv hρ (ε / 2) (by positivity)
  obtain ⟨C2, hC2, h2⟩ := RawDeletionMask31.minus_mask_subpower D Scales.goodLine (ε / 2)
    (by norm_num [Scales.goodLine]) (by positivity)
  refine ⟨C1 * (C2 * 2 ^ (ε / 2)), by positivity, U1, hU1, ?_⟩
  intro U hU u hu hq1 hq2 hex ξ hξ him
  have hU0 : 0 < U := by linarith
  have hxg : (8801 / 10000 : ℝ) ≤ ξ.re := by simpa [Scales.goodLine] using hξ
  have hξ0 : 0 < ξ.re := by linarith
  have hnp := ((FixedData.pkg D).nonprincipal u hu).2
  obtain ⟨g, hg, hgeq⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A (FixedData.primMinus D u) hnp
  have hgL : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (FixedData.primMinus D u).character s :=
    fun s hs => (hgeq s (by linarith)).trans
      (RowHeckeBridge.hecke_eq_idealLSeries _ _ _ s hs)
  have hmin : (FixedData.pkg D).minus u ξ =
      g ξ * Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) ξ := by
    rw [RawHeckeIdentification31.minus_eq_hecke_mul_mask D u hu ξ hξ0, ← hgeq ξ hξ0]
  obtain ⟨-, hginv⟩ := h1 U hU u hu hq1 hq2 hex g hg hgL ξ hxg him
  obtain ⟨-, -, hmask⟩ := h2 u ξ hξ
  rw [hmin, mul_inv]
  have hq : frequencyNorm D.recipe u ^ (ε / 2) ≤ 2 ^ (ε / 2) * U ^ (ε / 2) := by
    rw [← Real.mul_rpow (by norm_num) hU0.le]
    exact Real.rpow_le_rpow (by linarith) hq2.le (by positivity)
  have hU3 : U ^ (ε / 2) * U ^ (ε / 2) = U ^ ε := by
    rw [← Real.rpow_add hU0]; congr 1; ring
  rw [norm_mul]
  calc ‖(g ξ)⁻¹‖ * ‖(Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) ξ)⁻¹‖
      ≤ (C1 * U ^ (ε / 2)) * (C2 * (2 ^ (ε / 2) * U ^ (ε / 2))) :=
        mul_le_mul hginv (hmask.trans (mul_le_mul_of_nonneg_left hq hC2.le))
          (norm_nonneg _) (by positivity)
    _ = C1 * (C2 * 2 ^ (ε / 2)) * (U ^ (ε / 2) * U ^ (ε / 2)) := by ring
    _ = _ := by rw [hU3]

private theorem rawKernel_norm_eq (u : Frequency D.recipe) (hq : 0 < frequencyNorm D.recipe u)
    (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ) (hZ : 0 < Z) :
    ‖FixedData.rawKernel D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
        ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.kernelExponent ξ.re y v) * frequencyNorm D.recipe u ^ (-v) *
        WeightConvolution.weightModulus D ξ v y p *
        ‖FixedData.rawFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
          ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ := by
  unfold FixedData.rawKernel
  have hZc : (0 : ℝ) < Z := hZ
  have hqc : (0 : ℝ) < frequencyNorm D.recipe u := hq
  have hre : ∀ A B C X E R : ℂ, A * B * C * X * E * R = A * E * (B * C * X) * R := by
    intro A B C X E R; ring
  have hkey : ∀ A E X R : ℂ, ‖A * E * X * R‖ = ‖A‖ * ‖E‖ * ‖X‖ * ‖R‖ := by
    intro A E X R; simp only [norm_mul]
  rw [hre, hkey]
  unfold WeightConvolution.weightModulus
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZc, Complex.norm_cpow_eq_rpow_re_of_pos hqc]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_natCast]
  simp only [zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_sub]
  unfold Scales.kernelExponent
  try ring_nf

private theorem rawFactor_combine (u : Frequency D.recipe) (U : ℝ) (hU : 0 < U)
    (hq : frequencyNorm D.recipe u < 2 * U) (hq0 : 0 < frequencyNorm D.recipe u) (ε : ℝ)
    (hε : 0 < ε) (ξ w z : ℂ) (C1 C2 C3 C4 P : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hP : 0 ≤ P)
    (hz : ‖D.recipe.L (6 * z)‖ ≤ C1)
    (hL : ‖(FixedData.pkg D).plus u w‖ ≤ C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P)
    (hcorr : ‖AllRowEuler.InitialSeparation.correctionProduct D.context
        (FixedData.rawFrequency D u) ξ w z‖ ≤ C3 * frequencyNorm D.recipe u ^ (ε / 3))
    (hinv : ‖((FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C4 * U ^ (ε / 3)) :
    ‖FixedData.rawFactor D u ξ w z‖ ≤
      (C1 * C2 * C3 * C4 * 2 ^ (ε / 3)) * U ^ ((11 / 25 : ℝ) + ε) * P := by
  have e : ‖FixedData.rawFactor D u ξ w z‖ =
      ‖D.recipe.L (6 * z)‖ * ‖(FixedData.pkg D).plus u w‖ *
        ‖AllRowEuler.InitialSeparation.correctionProduct D.context
          (FixedData.rawFrequency D u) ξ w z‖ * ‖((FixedData.pkg D).minus u ξ)⁻¹‖ := by
    unfold FixedData.rawFactor
    simp only [div_eq_mul_inv, norm_mul]
  have hq2 : frequencyNorm D.recipe u ^ (ε / 3) ≤ 2 ^ (ε / 3) * U ^ (ε / 3) := by
    rw [← Real.mul_rpow (by norm_num) hU.le]
    exact Real.rpow_le_rpow hq0.le hq.le (by positivity)
  have hU3 : U ^ ((11 / 25 : ℝ) + ε / 3) * U ^ (ε / 3) * U ^ (ε / 3) =
      U ^ ((11 / 25 : ℝ) + ε) := by
    rw [← Real.rpow_add hU, ← Real.rpow_add hU]
    congr 1
    ring
  have hcorr' : ‖AllRowEuler.InitialSeparation.correctionProduct D.context
        (FixedData.rawFrequency D u) ξ w z‖ ≤ C3 * (2 ^ (ε / 3) * U ^ (ε / 3)) :=
    hcorr.trans (mul_le_mul_of_nonneg_left hq2 hC3)
  have hA : 0 ≤ C1 * (C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P) := by positivity
  have hB : 0 ≤ C1 * (C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P) *
      (C3 * (2 ^ (ε / 3) * U ^ (ε / 3))) := by positivity
  calc ‖FixedData.rawFactor D u ξ w z‖
      = ‖D.recipe.L (6 * z)‖ * ‖(FixedData.pkg D).plus u w‖ *
        ‖AllRowEuler.InitialSeparation.correctionProduct D.context
          (FixedData.rawFrequency D u) ξ w z‖ * ‖((FixedData.pkg D).minus u ξ)⁻¹‖ := e
    _ ≤ C1 * (C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P) *
          (C3 * (2 ^ (ε / 3) * U ^ (ε / 3))) * (C4 * U ^ (ε / 3)) :=
        mul_le_mul (mul_le_mul (mul_le_mul hz hL (norm_nonneg _) hC1) hcorr' (norm_nonneg _) hA)
          hinv (norm_nonneg _) hB
    _ = (C1 * C2 * C3 * C4 * 2 ^ (ε / 3)) *
          (U ^ ((11 / 25 : ℝ) + ε / 3) * U ^ (ε / 3) * U ^ (ε / 3)) * P := by ring
    _ = (C1 * C2 * C3 * C4 * 2 ^ (ε / 3)) * U ^ ((11 / 25 : ℝ) + ε) * P := by rw [hU3]

private theorem rawKernel_majorant_aux (u : Frequency D.recipe) (U : ℝ) (hU0 : 0 < U)
    (hqU : U ≤ frequencyNorm D.recipe u) (ε A C : ℝ) (hC : 0 ≤ C) (ξ : ℂ) (Z : ℝ) (hZ : 0 < Z)
    (p : ℝ × ℝ)
    (hR : ‖FixedData.rawFactor D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
      C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |p.2|) ^ A) :
    ‖FixedData.rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      C * Z ^ (Scales.kernelExponent ξ.re Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
        (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A) := by
  have hq0 : 0 < frequencyNorm D.recipe u := lt_of_lt_of_le hU0 hqU
  rw [rawKernel_norm_eq D u hq0 ξ Scales.zLine Scales.wLine p Z hZ]
  unfold Scales.kernelExponent
  have hqz : frequencyNorm D.recipe u ^ (-Scales.zLine) ≤ U ^ (-Scales.zLine) :=
    Real.rpow_le_rpow_of_nonpos hU0 hqU (by unfold Scales.zLine; norm_num)
  have hsplit : U ^ ((1 / 25 : ℝ) + ε) = U ^ (-Scales.zLine) * U ^ ((11 / 25 : ℝ) + ε) := by
    rw [← Real.rpow_add hU0]
    congr 1
    unfold Scales.zLine
    ring
  rw [hsplit]
  have hW : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := by
    unfold WeightConvolution.weightModulus
    exact norm_nonneg _
  have hZp : 0 ≤ Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) := Real.rpow_nonneg hZ.le _
  have hUz : 0 ≤ U ^ (-Scales.zLine) := Real.rpow_nonneg hU0.le _
  have h1 : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        frequencyNorm D.recipe u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p ≤
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        U ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqz hZp) hW
  have h2 : 0 ≤ C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |p.2|) ^ A := by positivity
  calc _ ≤ Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        U ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        (C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |p.2|) ^ A) :=
        mul_le_mul h1 hR (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem rawKernel_majorant_rect (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ (ξ : ℂ) (Z : ℝ) (p : ℝ × ℝ), 0 < Z → Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine →
        |ξ.im| ≤ 2 * U ^ ρ →
        ‖FixedData.rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * Z ^ (Scales.kernelExponent ξ.re Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
            (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A) := by
  obtain ⟨C1, hC1, h1⟩ := L6_line_bound D
  obtain ⟨C2, hC2, h2⟩ := hconv.1 (ε / 3) (by positivity)
  obtain ⟨C3, hC3, h3⟩ := corr_box_bound D (ε / 3) (by positivity)
  obtain ⟨C4, hC4, U4, hU4, h4⟩ := minus_inv_rect D A ρ hA hconv hρ (ε / 3) (by positivity)
  refine ⟨C1 * C2 * C3 * C4 * 2 ^ (ε / 3), by positivity, U4, hU4, ?_⟩
  intro U hU u hu hqU hqU2 hex ξ Z p hZ hξ1 _ hξim
  have hU2 : 2 ≤ U := hU4.trans hU
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < frequencyNorm D.recipe u := by linarith
  have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
  have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
  have hinv := h4 U hU u hu hqU hqU2 hex ξ hξ1 hξim
  have hR := rawFactor_combine D u U hU0 hqU2 hq0 ε hε ξ
    (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)
    (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I) C1 C2 C3 C4 ((2 + |p.2|) ^ A)
    hC1.le hC2.le hC3.le hC4.le (by positivity) (h1 _ hz)
    (h2 u hu U hU2 hqU hqU2 p.2)
    (h3 u ξ _ _ hξ1 hw.ge hz.ge) hinv
  exact rawKernel_majorant_aux D u U hU0 hqU ε A _ (by positivity) ξ Z hZ p hR

theorem rawKernel_majorant_right (A : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U →
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
      ∀ (ξ : ℂ) (Z : ℝ) (p : ℝ × ℝ), 0 < Z → ξ.re = Scales.rightLine →
        ‖FixedData.rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
            (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A) := by
  obtain ⟨C1, hC1, h1⟩ := L6_line_bound D
  obtain ⟨C2, hC2, h2⟩ := hconv.1 (ε / 3) (by positivity)
  obtain ⟨C3, hC3, h3⟩ := corr_box_bound D (ε / 3) (by positivity)
  obtain ⟨C4, hC4, h4⟩ := RawReciprocal31.raw_reciprocal_right D
  refine ⟨C1 * C2 * C3 * C4 * 2 ^ (ε / 3), by positivity, ?_⟩
  intro U hU2 u hu hqU hqU2 ξ Z p hZ hξ
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < frequencyNorm D.recipe u := by linarith
  have hxg : Scales.goodLine ≤ ξ.re := by
    rw [hξ, Scales.rightLine_eq]
    unfold Scales.goodLine
    norm_num
  have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
  have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
  have hUe : 1 ≤ U ^ (ε / 3) := Real.one_le_rpow (by linarith) (by positivity)
  have hinv : ‖((FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C4 * U ^ (ε / 3) :=
    (h4 u hu ξ hξ.ge).2.trans (le_mul_of_one_le_right hC4.le hUe)
  have hR := rawFactor_combine D u U hU0 hqU2 hq0 ε hε ξ
    (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)
    (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I) C1 C2 C3 C4 ((2 + |p.2|) ^ A)
    hC1.le hC2.le hC3.le hC4.le (by positivity) (h1 _ hz)
    (h2 u hu U hU2 hqU hqU2 p.2)
    (h3 u ξ _ _ hxg hw.ge hz.ge) hinv
  have := rawKernel_majorant_aux D u U hU0 hqU ε A _ (by positivity) ξ Z hZ p hR
  rwa [hξ] at this

end

end DedekindZetaZeroFree.Quantitative.RawGoodKernelBounds31
