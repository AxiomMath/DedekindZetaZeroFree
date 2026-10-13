module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.Rectangles
public import DedekindZetaZeroFree.Analysis.ContourIntegration.KernelWeightIntegration
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelHolomorphy

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowKernelGrowth

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.EulerDomain
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def EntireNumerator (u : D.Row) : Prop :=
  ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s

theorem Hu_box_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, ∀ ξ w z : ℂ, Scales.goodLine ≤ ξ.re → Scales.wLine ≤ w.re →
      Scales.zLine ≤ z.re → ‖Hu D u ξ w z‖ ≤ C * D.q u ^ ε := by
  obtain ⟨C, hC, h⟩ := EulerSubpower.Hu_subpower_boxes D ε hε
  refine ⟨C, hC, fun u ξ w z h1 h2 h3 => ?_⟩
  have hp : ((ξ, w, z) : Coordinates) ∈ boxes := by
    refine Or.inl (Or.inl ?_)
    exact ⟨h1, h2, h3⟩
  exact (h u _ hp).2

theorem zetaSCont_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = Scales.zLine → ‖D.zetaSCont (6 * z)‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (12 / 5) (by norm_num)
  refine ⟨C, hC, fun z hz => h (6 * z) ?_⟩
  have h6 : (6 * z).re = 6 * z.re := by simp [Complex.mul_re]
  rw [h6, hz]
  norm_num [Scales.zLine]

theorem Lpsi_line_bound (A_F : ℝ) (hconv : ConvexityExponent D A_F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, u.toFrequency.u ≠ 1 → EntireNumerator D u → ∀ U : ℝ, 2 ≤ U →
      U ≤ D.q u → D.q u < 2 * U → ∀ w : ℂ, w.re = Scales.wLine →
        ‖D.Lpsi u w‖ ≤ C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |w.im|) ^ A_F := by
  obtain ⟨C, hC, h⟩ := hconv.1 ε hε
  refine ⟨C, hC, fun u hu1 hent U hU hq1 hq2 w hw => ?_⟩
  obtain ⟨g, hg, hgeq⟩ := hent
  have hy : Scales.wLine = 3 / 25 := by unfold Scales.wLine; norm_num
  have hw0 : 0 < w.re := by rw [hw, hy]; norm_num
  have e : D.Lpsi u w = g w :=
    (RowAnalyticContinuation.entire_eq_Lpsi D u hu1 hg hgeq w hw0).symm
  have hwe : w = ((Scales.wLine : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hw]
  have key := h u hu1 U hU hq1 hq2 g hg hgeq w.im
  calc ‖D.Lpsi u w‖ = ‖g (((Scales.wLine : ℝ) : ℂ) + (w.im : ℂ) * Complex.I)‖ := by
        rw [e, ← hwe]
    _ ≤ C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |w.im|) ^ A_F := by
        rw [hy]; exact key

theorem Llam_inv_right_line (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
      ∀ ξ : ℂ, ξ.re = Scales.rightLine → D.Llam u ξ ≠ 0 ∧ ‖(D.Llam u ξ)⁻¹‖ ≤ C * U ^ ε := by
  have hx1 : (1 : ℝ) < Scales.rightLine := by rw [Scales.rightLine_eq]; norm_num
  obtain ⟨C, hC, h⟩ := RightHeckeBounds.Llam_inv_norm_le_right D Scales.rightLine hx1
  refine ⟨C, hC, fun u _ U hU _ _ ξ hξ => ?_⟩
  have hUe : 1 ≤ U ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hne : D.Llam u ξ ≠ 0 :=
    RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ (by rw [hξ]; exact hx1)
  refine ⟨hne, ?_⟩
  calc ‖(D.Llam u ξ)⁻¹‖ ≤ C := h u ξ hξ.ge
    _ ≤ C * U ^ ε := le_mul_of_one_le_right hC.le hUe

private theorem recip_bound' (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ Uε : ℝ, 2 ≤ Uε ∧ ∀ U : ℝ, Uε ≤ U →
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
        ∀ s : ℂ, Scales.goodLine ≤ s.re → |s.im| ≤ 2 * U ^ ρ →
          D.Llam u s ≠ 0 ∧ ‖(D.Llam u s)⁻¹‖ ≤ C * U ^ ε :=
  Recip.recip_bound D A_F ρ hA hconv hρ ε hε

private theorem rowFactor_combine (u : D.Row) (U : ℝ) (hU : 0 < U) (hq : D.q u < 2 * U)
    (hq0 : 0 < D.q u) (ε : ℝ) (hε : 0 < ε) (ξ w z : ℂ) (C1 C2 C3 C4 P : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hP : 0 ≤ P)
    (hz : ‖D.zetaSCont (6 * z)‖ ≤ C1)
    (hL : ‖D.Lpsi u w‖ ≤ C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P)
    (hHu : ‖Hu D u ξ w z‖ ≤ C3 * D.q u ^ (ε / 3))
    (hinv : ‖(D.Llam u ξ)⁻¹‖ ≤ C4 * U ^ (ε / 3)) :
    ‖rowFactor D u ξ w z‖ ≤ (C1 * C2 * C3 * C4 * 2 ^ (ε / 3)) * U ^ ((11 / 25 : ℝ) + ε) * P := by
  have e : ‖rowFactor D u ξ w z‖ =
      ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖(D.Llam u ξ)⁻¹‖ * ‖Hu D u ξ w z‖ := by
    unfold rowFactor
    simp only [div_eq_mul_inv, norm_mul]
  have hq2 : D.q u ^ (ε / 3) ≤ 2 ^ (ε / 3) * U ^ (ε / 3) := by
    rw [← Real.mul_rpow (by norm_num) hU.le]
    exact Real.rpow_le_rpow hq0.le hq.le (by positivity)
  have hU3 : U ^ ((11 / 25 : ℝ) + ε / 3) * U ^ (ε / 3) * U ^ (ε / 3) =
      U ^ ((11 / 25 : ℝ) + ε) := by
    rw [← Real.rpow_add hU, ← Real.rpow_add hU]
    congr 1
    ring
  have hHu' : ‖Hu D u ξ w z‖ ≤ C3 * (2 ^ (ε / 3) * U ^ (ε / 3)) :=
    hHu.trans (mul_le_mul_of_nonneg_left hq2 hC3)
  have hA : 0 ≤ C1 * (C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P) := by positivity
  have hB : 0 ≤ C1 * (C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P) * (C4 * U ^ (ε / 3)) := by
    positivity
  calc ‖rowFactor D u ξ w z‖
      = ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖(D.Llam u ξ)⁻¹‖ * ‖Hu D u ξ w z‖ := e
    _ ≤ C1 * (C2 * U ^ ((11 / 25 : ℝ) + ε / 3) * P) * (C4 * U ^ (ε / 3)) *
          (C3 * (2 ^ (ε / 3) * U ^ (ε / 3))) :=
        mul_le_mul (mul_le_mul (mul_le_mul hz hL (norm_nonneg _) hC1) hinv (norm_nonneg _) hA)
          hHu' (norm_nonneg _) hB
    _ = (C1 * C2 * C3 * C4 * 2 ^ (ε / 3)) *
          (U ^ ((11 / 25 : ℝ) + ε / 3) * U ^ (ε / 3) * U ^ (ε / 3)) * P := by ring
    _ = (C1 * C2 * C3 * C4 * 2 ^ (ε / 3)) * U ^ ((11 / 25 : ℝ) + ε) * P := by rw [hU3]

theorem rowFactor_rect_bound (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
      ∀ ξ w z : ℂ, Scales.goodLine ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ → w.re = Scales.wLine →
        z.re = Scales.zLine →
          ‖rowFactor D u ξ w z‖ ≤ C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |w.im|) ^ A_F := by
  obtain ⟨C1, hC1, h1⟩ := zetaSCont_line_bound D
  obtain ⟨C2, hC2, h2⟩ := Lpsi_line_bound D A_F hconv (ε / 3) (by positivity)
  obtain ⟨C3, hC3, h3⟩ := Hu_box_bound D (ε / 3) (by positivity)
  obtain ⟨C4, hC4, U4, hU4, h4⟩ := recip_bound' D A_F ρ hA hconv hρ (ε / 3) (by positivity)
  refine ⟨C1 * C2 * C3 * C4 * 2 ^ (ε / 3), by positivity, U4, hU4, ?_⟩
  intro U hU u hu1 hent hqU hqU2 hex ξ w z hξ hξim hw hz
  have hU2 : 2 ≤ U := hU4.trans hU
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  obtain ⟨_, hinv⟩ := h4 U hU u hu1 hqU hqU2 hex ξ hξ hξim
  exact rowFactor_combine D u U hU0 hqU2 hq0 ε hε ξ w z C1 C2 C3 C4 _ hC1.le hC2.le hC3.le
    hC4.le (by positivity) (h1 z hz) (h2 u hu1 hent U hU2 hqU hqU2 w hw)
    (h3 u ξ w z hξ hw.ge hz.ge) hinv

theorem rowFactor_right_bound (A_F : ℝ) (hconv : ConvexityExponent D A_F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U →
      ∀ ξ w z : ℂ, ξ.re = Scales.rightLine → w.re = Scales.wLine → z.re = Scales.zLine →
        ‖rowFactor D u ξ w z‖ ≤ C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |w.im|) ^ A_F := by
  obtain ⟨C1, hC1, h1⟩ := zetaSCont_line_bound D
  obtain ⟨C2, hC2, h2⟩ := Lpsi_line_bound D A_F hconv (ε / 3) (by positivity)
  obtain ⟨C3, hC3, h3⟩ := Hu_box_bound D (ε / 3) (by positivity)
  obtain ⟨C4, hC4, h4⟩ := Llam_inv_right_line D (ε / 3) (by positivity)
  refine ⟨C1 * C2 * C3 * C4 * 2 ^ (ε / 3), by positivity, ?_⟩
  intro U hU2 u hu1 hent hqU hqU2 ξ w z hξ hw hz
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hxg : Scales.goodLine ≤ ξ.re := by
    rw [hξ, Scales.rightLine_eq]
    unfold Scales.goodLine
    norm_num
  obtain ⟨_, hinv⟩ := h4 u hu1 U hU2 hqU hqU2 ξ hξ
  exact rowFactor_combine D u U hU0 hqU2 hq0 ε hε ξ w z C1 C2 C3 C4 _ hC1.le hC2.le hC3.le
    hC4.le (by positivity) (h1 z hz) (h2 u hu1 hent U hU2 hqU hqU2 w hw)
    (h3 u ξ w z hxg hw.ge hz.ge) hinv

theorem K_norm_eq (u : D.Row) (hq : 0 < D.q u) (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ)
    (hZ : 0 < Z) :
    ‖K D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * v + Scales.yExponent * (y - 1)) * D.q u ^ (-v) *
        WeightConvolution.weightModulus D ξ v y p *
        ‖rowFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
          ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ := by
  unfold K kernelWith
  have hZc : (0 : ℝ) < Z := hZ
  have hqc : (0 : ℝ) < D.q u := hq
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
  try ring_nf

private theorem K_majorant_aux (u : D.Row) (U : ℝ) (hU0 : 0 < U) (hqU : U ≤ D.q u)
    (ε A_F C x : ℝ) (hC : 0 ≤ C) (ξ : ℂ) (hx : ξ.re = x) (Z : ℝ) (hZ : 0 < Z) (p : ℝ × ℝ)
    (hR : ‖rowFactor D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
      C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |p.2|) ^ A_F) :
    ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      C * Z ^ (Scales.xExponent / 2 + x - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
        (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A_F) := by
  have hq0 : 0 < D.q u := lt_of_lt_of_le hU0 hqU
  rw [K_norm_eq D u hq0 ξ Scales.zLine Scales.wLine p Z hZ, hx]
  have hqz : D.q u ^ (-Scales.zLine) ≤ U ^ (-Scales.zLine) :=
    Real.rpow_le_rpow_of_nonpos hU0 hqU (by unfold Scales.zLine; norm_num)
  have hsplit : U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) =
      U ^ (-Scales.zLine) * U ^ ((11 / 25 : ℝ) + ε) := by
    rw [← Real.rpow_add hU0]
    congr 1
    ring
  rw [hsplit]
  have hW : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := by
    unfold WeightConvolution.weightModulus
    exact norm_nonneg _
  have hZp : 0 ≤ Z ^ (Scales.xExponent / 2 + x - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) :=
    Real.rpow_nonneg hZ.le _
  have hUz : 0 ≤ U ^ (-Scales.zLine) := Real.rpow_nonneg hU0.le _
  have h1 : Z ^ (Scales.xExponent / 2 + x - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        D.q u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p ≤
      Z ^ (Scales.xExponent / 2 + x - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        U ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqz hZp) hW
  have h2 : 0 ≤ C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |p.2|) ^ A_F := by positivity
  calc _ ≤ Z ^ (Scales.xExponent / 2 + x - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
        U ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        (C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |p.2|) ^ A_F) :=
        mul_le_mul h1 hR (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem kernel_majorant_rect (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
      ∀ (ξ : ℂ) (Z : ℝ) (p : ℝ × ℝ), 0 < Z → Scales.goodLine ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
        ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
            U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
            (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
              (2 + |p.2|) ^ A_F) := by
  obtain ⟨C, hC, U₀, hU₀, h⟩ := rowFactor_rect_bound D A_F ρ hA hconv hρ ε hε
  refine ⟨C, hC, U₀, hU₀, ?_⟩
  intro U hU u hu1 hent hqU hqU2 hex ξ Z p hZ hξ hξim
  have hU0 : 0 < U := by linarith
  have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
  have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
  have him : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
  have hR := h U hU u hu1 hent hqU hqU2 hex ξ _ _ hξ hξim hw hz
  rw [him] at hR
  exact K_majorant_aux D u U hU0 hqU ε A_F C ξ.re hC.le ξ rfl Z hZ p hR

theorem kernel_majorant_right (A_F : ℝ) (hconv : ConvexityExponent D A_F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U →
      ∀ (ξ : ℂ) (Z : ℝ) (p : ℝ × ℝ), 0 < Z → ξ.re = Scales.rightLine →
        ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
              Scales.yExponent * (Scales.wLine - 1)) *
            U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
            (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
              (2 + |p.2|) ^ A_F) := by
  obtain ⟨C, hC, h⟩ := rowFactor_right_bound D A_F hconv ε hε
  refine ⟨C, hC, ?_⟩
  intro U hU2 u hu1 hent hqU hqU2 ξ Z p hZ hξ
  have hU0 : 0 < U := by linarith
  have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
  have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
  have him : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
  have hR := h U hU2 u hu1 hent hqU hqU2 ξ _ _ hξ hw hz
  rw [him] at hR
  exact K_majorant_aux D u U hU0 hqU ε A_F C Scales.rightLine hC.le ξ hξ Z hZ p hR

private theorem xg_pad_le_x1 : Scales.goodLine - EulerDomain.pad ≤ Scales.rightLine := by
  rw [Scales.rightLine_eq]
  unfold Scales.goodLine EulerDomain.pad
  norm_num

private theorem xg_pad_lt_x1 : Scales.goodLine - EulerDomain.pad < Scales.rightLine := by
  rw [Scales.rightLine_eq]
  unfold Scales.goodLine EulerDomain.pad
  norm_num

private theorem z₀_pos : 0 < Scales.zLine := by unfold Scales.zLine; norm_num

private theorem x_g_le_x₁ : Scales.goodLine ≤ Scales.rightLine := by
  rw [Scales.rightLine_eq]
  unfold Scales.goodLine
  norm_num

private theorem K_cont_swap (u : D.Row) (hu : u.toFrequency.u ≠ 1) (hq : 0 < D.q u) (Z : ℝ)
    (hZ : 0 < Z) (ξ : ℂ) (hx : Scales.goodLine - EulerDomain.pad ≤ ξ.re) (hξ : D.Llam u ξ ≠ 0) :
    Continuous (fun p : ℝ × ℝ => K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) :=
  by
  have h := RowAnalyticContinuation.K_continuous_heights D u hu hq Z hZ ξ hx hξ
  have h2 := h.comp (continuous_swap (X := ℝ) (Y := ℝ))
  exact h2

private theorem Llam_ne_rect (ρ U : ℝ) (hU : 0 ≤ U) (u : D.Row) (hu : u.toFrequency.u ≠ 1)
    (hU1 : U ≤ D.q u) (hU2 : D.q u < 2 * U) (hexc : u ∉ exceptionalSet D ρ U) (ξ : ℂ)
    (hx : Scales.goodLine ≤ ξ.re) (him : |ξ.im| ≤ 2 * U ^ ρ) : D.Llam u ξ ≠ 0 := by
  have hnn : 0 ≤ U ^ ρ := Real.rpow_nonneg hU ρ
  refine RowAnalyticContinuation.Llam_ne_zero_of_not_exceptional D ρ U u hu hU1 hU2 hexc ξ ?_
    (by linarith)
  unfold DedekindZetaZeroFree.Quantitative.DetectorDef.σ₀
  unfold Scales.goodLine at hx
  linarith

private theorem weight_dom (ξ : ℂ) (v y : ℝ) (Cc A A' : ℝ) (hCc : 0 ≤ Cc) (hA : A ≤ A')
    (hA' : 0 ≤ A') (p : ℝ × ℝ) (x : ℝ)
    (hx : x ≤ Cc * (WeightConvolution.weightModulus D ξ v y p * (2 + |p.2|) ^ A)) :
    x ≤ Cc * WeightConvolution.weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ A' := by
  have hW : 0 ≤ WeightConvolution.weightModulus D ξ v y p := by
    unfold WeightConvolution.weightModulus
    exact norm_nonneg _
  have h0 := abs_nonneg p.1
  have h0' := abs_nonneg p.2
  have h0'' := abs_nonneg ξ.im
  have h1 : (2 + |p.2|) ^ A ≤ (2 + |p.2|) ^ A' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  have h2 : (2 + |p.2|) ^ A' ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ A' :=
    Real.rpow_le_rpow (by linarith) (by linarith) hA'
  calc x ≤ Cc * (WeightConvolution.weightModulus D ξ v y p * (2 + |p.2|) ^ A) := hx
    _ ≤ Cc * (WeightConvolution.weightModulus D ξ v y p *
          (2 + |p.1| + |p.2| + |ξ.im|) ^ A') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2) hW) hCc
    _ = _ := by ring

theorem K_integrable_rect (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
      ∀ (ξ : ℂ) (Z : ℝ), 0 < Z → Scales.goodLine ≤ ξ.re → |ξ.im| ≤ 2 * U ^ ρ →
        Integrable (fun p : ℝ × ℝ => K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) := by
  obtain ⟨C, hC, U₀, hU₀, h⟩ := kernel_majorant_rect D A_F ρ hA hconv hρ 1 one_pos
  refine ⟨U₀, hU₀, ?_⟩
  intro U hU u hu1 hent hqU hqU2 hex ξ Z hZ hξ hξim
  have hU2 : 2 ≤ U := hU₀.trans hU
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hne := Llam_ne_rect D ρ U hU0.le u hu1 hqU hqU2 hex ξ hξ hξim
  have hpad : (0 : ℝ) ≤ EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  have hcont := K_cont_swap D u hu1 hq0 Z hZ ξ (by linarith) hne
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.joint_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine Scales.goodLine ξ.re z₀_pos le_rfl le_rfl hξ 1 A_F one_pos hA
  have hCc : 0 ≤ C * Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + 1 - Scales.zLine) := by positivity
  exact (hCw ξ hξ le_rfl Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl _ hCc _
    hcont.aestronglyMeasurable (fun p => weight_dom D ξ Scales.zLine Scales.wLine _ A_F A_F hCc le_rfl hA p _
      (by simpa only [mul_assoc] using h U hU u hu1 hent hqU hqU2 hex ξ Z p hZ hξ hξim))).1

theorem K_integrable_right (A_F : ℝ) (hconv : ConvexityExponent D A_F) :
    ∀ U : ℝ, 2 ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 → EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U →
      ∀ (ξ : ℂ) (Z : ℝ), 0 < Z → ξ.re = Scales.rightLine →
        Integrable (fun p : ℝ × ℝ => K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) := by
  obtain ⟨C, hC, h⟩ := kernel_majorant_right D A_F hconv 1 one_pos
  obtain ⟨C4, hC4, h4⟩ := Llam_inv_right_line D 1 one_pos
  intro U hU2 u hu1 hent hqU hqU2 ξ Z hZ hξ
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hne := (h4 u hu1 U hU2 hqU hqU2 ξ hξ).1
  have hcont := K_cont_swap D u hu1 hq0 Z hZ ξ (by rw [hξ]; exact xg_pad_le_x1) hne
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.joint_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine ξ.re ξ.re z₀_pos le_rfl le_rfl le_rfl 1 (max A_F 0) one_pos (le_max_right _ _)
  have hCc : 0 ≤ C * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + 1 - Scales.zLine) := by positivity
  exact (hCw ξ le_rfl le_rfl Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl _ hCc _
    hcont.aestronglyMeasurable (fun p => weight_dom D ξ Scales.zLine Scales.wLine _ A_F (max A_F 0) hCc
      (le_max_left _ _) (le_max_right _ _) p _
      (by simpa only [mul_assoc] using h U hU2 u hu1 hent hqU hqU2 ξ Z p hZ hξ))).1

theorem wzIntegral_decay_rect (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
      ∀ (ξ : ℂ) (Z : ℝ), 0 < Z → Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine → |ξ.im| ≤ 2 * U ^ ρ →
        ‖wzIntegral D u ξ Scales.wLine Scales.zLine Z‖ ≤
          C * Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
            U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) * (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨C, hC, U₀, hU₀, h⟩ := kernel_majorant_rect D A_F ρ hA hconv hρ ε hε
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.nested_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine Scales.goodLine Scales.rightLine z₀_pos le_rfl le_rfl x_g_le_x₁ B A_F hB hA
  have hc0 : 0 ≤ C * Cw * ((2 * Real.pi)⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg hC.le hCw0) (sq_nonneg _)
  refine ⟨C * Cw * ((2 * Real.pi)⁻¹) ^ 2 + 1, by linarith, U₀, hU₀, ?_⟩
  intro U hU u hu1 hent hqU hqU2 hex ξ Z hZ hξ hξ1 hξim
  have hU2 : 2 ≤ U := hU₀.trans hU
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hne := Llam_ne_rect D ρ U hU0.le u hu1 hqU hqU2 hex ξ hξ hξim
  have hpad : (0 : ℝ) ≤ EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  have hcont := K_cont_swap D u hu1 hq0 Z hZ ξ (by linarith) hne
  have hCc : 0 ≤ C * Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) := by positivity
  have hle := (hCw ξ hξ hξ1 Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl _ hCc
    (fun w z => K D u ξ w z Z) hcont.aestronglyMeasurable
    (fun p => weight_dom D ξ Scales.zLine Scales.wLine _ A_F A_F hCc le_rfl hA p _
      (by simpa only [mul_assoc] using h U hU u hu1 hent hqU hqU2 hex ξ Z p hZ hξ hξim))).2.2.2
  have hP : 0 ≤ Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
      (1 + |ξ.im|) ^ (-B) := by positivity
  calc ‖wzIntegral D u ξ Scales.wLine Scales.zLine Z‖
      ≤ ((2 * Real.pi)⁻¹) ^ 2 * ((C * Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine)) * Cw *
        (1 + |ξ.im|) ^ (-B)) := hle
    _ = (C * Cw * ((2 * Real.pi)⁻¹) ^ 2) * (Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
      (1 + |ξ.im|) ^ (-B)) := by ring
    _ ≤ (C * Cw * ((2 * Real.pi)⁻¹) ^ 2 + 1) * (Z ^ (Scales.xExponent / 2 + ξ.re - 1 +
      Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
      (1 + |ξ.im|) ^ (-B)) := mul_le_mul_of_nonneg_right (by linarith) hP
    _ = _ := by ring

theorem wzIntegral_decay_right (A_F : ℝ) (hconv : ConvexityExponent D A_F) (ε : ℝ) (hε : 0 < ε)
    (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U →
      ∀ (t : ℝ) (Z : ℝ), 0 < Z →
        ‖wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
          C * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
              Scales.yExponent * (Scales.wLine - 1)) *
            U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) * (1 + |t|) ^ (-B) := by
  obtain ⟨C, hC, h⟩ := kernel_majorant_right D A_F hconv ε hε
  obtain ⟨C4, hC4, h4⟩ := Llam_inv_right_line D 1 one_pos
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.nested_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine Scales.rightLine Scales.rightLine z₀_pos le_rfl le_rfl le_rfl B (max A_F 0) hB
    (le_max_right _ _)
  have hc0 : 0 ≤ C * Cw * ((2 * Real.pi)⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg hC.le hCw0) (sq_nonneg _)
  refine ⟨C * Cw * ((2 * Real.pi)⁻¹) ^ 2 + 1, by linarith, ?_⟩
  intro U hU2 u hu1 hent hqU hqU2 t Z hZ
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hre : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = Scales.rightLine := by simp
  have him : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hne := (h4 u hu1 U hU2 hqU hqU2 _ hre).1
  have hcont := K_cont_swap D u hu1 hq0 Z hZ _ (by rw [hre]; exact xg_pad_le_x1) hne
  have hCc : 0 ≤ C * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) := by positivity
  have hle := (hCw _ hre.ge hre.le Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl _ hCc
    (fun w z => K D u (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I) w z Z)
    hcont.aestronglyMeasurable
    (fun p => weight_dom D _ Scales.zLine Scales.wLine _ A_F (max A_F 0) hCc
      (le_max_left _ _) (le_max_right _ _) p _
      (by simpa only [mul_assoc] using h U hU2 u hu1 hent hqU hqU2 _ Z p hZ hre))).2.2.2
  rw [him] at hle
  have hP : 0 ≤ Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
      (1 + |t|) ^ (-B) := by positivity
  calc ‖wzIntegral D u (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖
      ≤ ((2 * Real.pi)⁻¹) ^ 2 * ((C * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine)) * Cw *
        (1 + |t|) ^ (-B)) := hle
    _ = (C * Cw * ((2 * Real.pi)⁻¹) ^ 2) * (Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 +
      Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
      (1 + |t|) ^ (-B)) := by ring
    _ ≤ (C * Cw * ((2 * Real.pi)⁻¹) ^ 2 + 1) * (Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 +
      Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) *
      (1 + |t|) ^ (-B)) := mul_le_mul_of_nonneg_right (by linarith) hP
    _ = _ := by ring

def nbhd (u : D.Row) : Set ℂ :=
  {ξ : ℂ | Scales.goodLine - pad < ξ.re ∧ D.Llam u ξ ≠ 0}

theorem wzIntegral_differentiableOn (A_F : ℝ) (hconv : ConvexityExponent D A_F) (u : D.Row)
    (hu1 : u.toFrequency.u ≠ 1) (hq2 : 2 ≤ D.q u)
    (hu : EntireNumerator D u) (Z : ℝ) (hZ : 0 < Z) :
    IsOpen (nbhd D u) ∧
      DifferentiableOn ℂ (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) (nbhd D u) := by
  have hq0 : 0 < D.q u := by linarith
  have hpad : (0 : ℝ) ≤ EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  have hopen : IsOpen (nbhd D u) := by
    have hc : ContinuousOn (D.Llam u) {s : ℂ | Scales.goodLine - pad < s.re} := by
      refine (RowAnalyticContinuation.Llam_analyticOnNhd D u hu1).continuousOn.mono ?_
      intro s hs
      have hs' : Scales.goodLine - pad < s.re := hs
      show 0 < s.re
      unfold Scales.goodLine EulerDomain.pad at hs'
      linarith
    have hs : IsOpen {s : ℂ | Scales.goodLine - pad < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have := hc.isOpen_inter_preimage hs (isOpen_compl_singleton (x := (0 : ℂ)))
    exact this
  refine ⟨hopen, ?_⟩
  have hdiff : ∀ ξ ∈ nbhd D u, ∀ s t : ℝ, DifferentiableAt ℂ
      (fun x : ℂ => K D u x ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I) Z) ξ := by
    intro ξ hξ s t
    have hw : ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I).re = Scales.wLine := by simp
    have hz : ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.zLine := by simp
    refine RowAnalyticContinuation.K_differentiableAt_xi D u hu1 hq0 Z hZ ξ _ _
      (RowAnalyticContinuation.mem_OmegaStar_of_re ξ _ _ hξ.1.le hw hz) ?_ hξ.2
    intro h
    have := congrArg Complex.re h
    have h6 : (6 * ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I)).re = 6 * Scales.zLine := by simp
    rw [h6] at this
    unfold Scales.zLine at this
    norm_num at this
  have hcont : ∀ ξ ∈ nbhd D u, Continuous (fun p : ℝ × ℝ => K D u ξ
      ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) :=
    fun ξ hξ => K_cont_swap D u hu1 hq0 Z hZ ξ hξ.1.le hξ.2
  have hmaj : ∀ ξ₀ ∈ nbhd D u, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ nbhd D u ∧ ∃ C k : ℝ,
      0 ≤ C ∧ 0 ≤ k ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
    intro ξ₀ hξ₀
    obtain ⟨r, hr, hball, C, k, hC, hk, hb⟩ :=
      RowKernelHolomorphy.K_local_majorant D A_F hconv u hu1 hq2 hu Z hZ ξ₀ hξ₀.1 hξ₀.2
    exact ⟨r, hr, fun ξ hξ => hball ξ hξ, C, k, hC, hk, hb⟩
  exact RowKernelHolomorphy.differentiableOn_nested_integral D (nbhd D u) hopen
    (fun ξ w z => K D u ξ w z Z) Scales.wLine Scales.zLine z₀_pos hdiff hcont hmaj

theorem wzIntegral_integrable_right (A_F : ℝ) (hconv : ConvexityExponent D A_F) :
    ∀ U : ℝ, 2 ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 → EntireNumerator D u → U ≤ D.q u → D.q u < 2 * U →
      ∀ Z : ℝ, 0 < Z → Integrable (fun t : ℝ =>
        wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) := by
  intro U hU u hu1 hent hqU hqU2 Z hZ
  obtain ⟨C, hC, h⟩ := wzIntegral_decay_right D A_F hconv 1 one_pos 2 two_pos
  obtain ⟨C4, hC4, h4⟩ := Llam_inv_right_line D 1 one_pos
  obtain ⟨-, hdiff⟩ := wzIntegral_differentiableOn D A_F hconv u hu1 (by linarith) hent Z hZ
  have hmem : ∀ t : ℝ, ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) ∈ nbhd D u := by
    intro t
    have hre : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = Scales.rightLine := by simp
    refine ⟨?_, (h4 u hu1 U hU hqU hqU2 _ hre).1⟩
    rw [hre]
    exact xg_pad_lt_x1
  have hcont : Continuous (fun t : ℝ =>
      wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) :=
    hdiff.continuousOn.comp_continuous
      (f := fun t : ℝ => (Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) (by fun_prop) hmem
  have hI : Integrable (fun t : ℝ => (C * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
      Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + 1 - Scales.zLine)) *
      (1 + |t|) ^ (-(2 : ℝ))) :=
    (KernelWeightIntegration.one_add_abs_rpow_integrable 2 (by norm_num)).const_mul _
  exact Integrable.mono' hI hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => h U hU u hu1 hent hqU hqU2 t Z hZ)

end

end DedekindZetaZeroFree.Quantitative.RowKernelGrowth
