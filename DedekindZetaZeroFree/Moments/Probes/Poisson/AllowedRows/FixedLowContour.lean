module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.GoodCentralSum

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.FixedLowRowContour

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def lowRowFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

def rowIntegral (Fu : D.Row → ℂ → ℂ → ℂ → ℂ) (u : D.Row) (x y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral x (fun ξ =>
    comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => kernelWith D Fu u ξ w z Z)))

theorem J_singleton (u : D.Row) (Z : ℝ) :
    J D {u} 4 4 2 Z = rowIntegral D (rowFactor D) u 4 4 2 Z := by
  classical
  simp [J, rowIntegral, wzIntegral, K]

theorem triple_eq_rowIntegral (u : D.Row) (x y v Z : ℝ) :
    LowRowKernelDefinitions.triple D u x y v Z = rowIntegral D (lowRowFactor D) u x y v Z := by
  unfold LowRowKernelDefinitions.triple LowRowKernelDefinitions.Iwz LowRowKernelDefinitions.Iz
    rowIntegral
  simp only [LowRowKernelDefinitions.K_eq_kernelWith]
  rfl

theorem fixedRow_initial_eq_all (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    J D {u} 4 4 2 Z =
      rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z := by
  rw [J_singleton]
  have h := LowRowContourShifts.triple_shift D u hu Z (by linarith)
  rw [triple_eq_rowIntegral, triple_eq_rowIntegral] at h
  have e : rowIntegral D (rowFactor D) u 4 4 2 Z =
      LowRowKernelDefinitions.triple D u 4 4 2 Z := rfl
  rw [e, triple_eq_rowIntegral]
  exact h

theorem fixedRow_initial_eq_small (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 2 ≤ Z)
    (hq : D.q u < 2) :
    J D {u} 4 4 2 Z =
      rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z :=
  fixedRow_initial_eq_all D u hu Z hZ

theorem Lpsi_line_fixed :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : D.Row, u.u ≠ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) →
        ∀ t : ℝ, ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (2 + |t|) ^ A := by
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  obtain ⟨A_F, hA0, hconv⟩ := convex_normalized F hF
  refine ⟨A_F, hA0, ?_⟩
  obtain ⟨C1, hC1, hnorm⟩ := hconv (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨Ce, hCe, heb⟩ :=
    EulerDeletion.euler_product_bound_with_S D (3 / 25) (by norm_num) 1 one_pos
  intro u hu
  obtain ⟨hnpP, -⟩ := RowNonprincipal.inducers_nonprincipal D u hu
  have hq1 : 1 ≤ D.q u := ActualRowCount.one_le_q D u
  have hq0 : 0 < D.q u := lt_of_lt_of_le one_pos hq1
  have hQpos : 0 < 1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ) := by positivity
  refine ⟨Ce * D.q u ^ (1 : ℝ) * C1 *
    (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ)) ^ ((1 + 1 / 10 - 3 / 25 : ℝ) / 2) + 1,
    by positivity, ?_⟩
  intro g hg hgs t
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := ⟨_, rfl⟩
  rw [← hs]
  have hsre : s.re = 3 / 25 := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hg_eq := ConvexBridge.entire_eq_mask_mul D u hnpP hg hgs s (by rw [hsre]; norm_num)
  have hN_eq := nonprincipalHeckeEntireContinuation_eq F hF (D.inducers u).plus.conductor
      (D.inducers u).plus.conductor_ne_zero (D.inducers u).plus.character
      (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) s (by rw [hsre]; norm_num)
  have hmask := (RowHeckeBridge.mask_norm_le D u (D.inducers u).plus (3 / 25) (by norm_num) s
      (by rw [hsre])).1
  have hprod := (heb u hq1).1
  have hNb := hnorm (D.inducers u).plus.conductor (D.inducers u).plus.conductor_ne_zero
      (D.inducers u).plus.character (D.inducers u).plus.primitive hnpP
      (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) s (by rw [hsre]; norm_num)
      (by rw [hsre]; norm_num)
  rw [hsre, hsim] at hNb
  have hnorm_eq : ‖g s‖ = ‖Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s‖ *
        ‖nonprincipalHeckeEntireContinuation F (D.inducers u).plus.conductor
          (D.inducers u).plus.character
          (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) s‖ := by
    exact (congrArg norm hg_eq).trans ((norm_mul _ _).trans
        (congrArg (fun x => _ * ‖x‖) hN_eq.symm))
  rw [hnorm_eq]
  have hY : (0 : ℝ) ≤ (2 + |t|) ^ A_F := by positivity
  have hm2 := hmask.trans hprod
  have hQ0 : 0 ≤ (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ)) ^
      ((1 + 1 / 10 - 3 / 25 : ℝ) / 2) := by positivity
  have hbig : 0 ≤ Ce * D.q u ^ (1 : ℝ) * C1 *
      (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ)) ^ ((1 + 1 / 10 - 3 / 25 : ℝ) / 2) *
        (2 + |t|) ^ A_F := by positivity
  calc _ ≤ (Ce * D.q u ^ (1 : ℝ)) * (C1 *
        (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ)) ^ ((1 + 1 / 10 - 3 / 25 : ℝ) / 2) *
          (2 + |t|) ^ A_F) :=
        mul_le_mul hm2 hNb (norm_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [hY, hbig]

theorem rowFactor_right_fixed :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : D.Row, u.u ≠ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ ξ w z : ℂ, ξ.re = Scales.rightLine → w.re = Scales.wLine → z.re = Scales.zLine →
        ‖rowFactor D u ξ w z‖ ≤ C * (2 + |w.im|) ^ A := by
  obtain ⟨A, hA, hL⟩ := Lpsi_line_fixed D
  obtain ⟨C1, hC1, h1⟩ := RowKernelGrowth.zetaSCont_line_bound D
  obtain ⟨C3, hC3, h3⟩ := RowKernelGrowth.Hu_box_bound D 1 one_pos
  have hx1 : (1 : ℝ) < Scales.rightLine := by rw [Scales.rightLine_eq]; norm_num
  obtain ⟨C4, hC4, h4⟩ := RightHeckeBounds.Llam_inv_norm_le_right D Scales.rightLine hx1
  refine ⟨A, hA, fun u hu => ?_⟩
  obtain ⟨C2, hC2, h2⟩ := hL u hu
  have hq0 : 0 < D.q u := lt_of_lt_of_le one_pos (ActualRowCount.one_le_q D u)
  obtain ⟨g, hg, hgeq⟩ := RowsGoodCentral.entireNumerator_of_ne_one D u hu
  refine ⟨C1 * C2 * C4 * (C3 * D.q u ^ (1 : ℝ)), by positivity, ?_⟩
  intro ξ w z hξ hw hz
  have hy : Scales.wLine = 3 / 25 := by unfold Scales.wLine; norm_num
  have hw0 : 0 < w.re := by rw [hw, hy]; norm_num
  have e : D.Lpsi u w = g w :=
    (RowAnalyticContinuation.entire_eq_Lpsi D u hu hg hgeq w hw0).symm
  have hwe : w = ((Scales.wLine : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hw]
  have key := h2 g hg hgeq w.im
  have hLb : ‖D.Lpsi u w‖ ≤ C2 * (2 + |w.im|) ^ A := by
    calc ‖D.Lpsi u w‖ = ‖g (((Scales.wLine : ℝ) : ℂ) + (w.im : ℂ) * Complex.I)‖ := by
          rw [e, ← hwe]
      _ ≤ C2 * (2 + |w.im|) ^ A := by rw [hy]; exact key
  have hz' : ‖D.zetaSCont (6 * z)‖ ≤ C1 := h1 z hz
  have hinv : ‖(D.Llam u ξ)⁻¹‖ ≤ C4 := h4 u ξ (by rw [hξ])
  have hHu : ‖EulerDomain.Hu D u ξ w z‖ ≤ C3 * D.q u ^ (1 : ℝ) := by
    refine h3 u ξ w z ?_ (by rw [hw]) (by rw [hz])
    rw [hξ, Scales.rightLine_eq]
    unfold Scales.goodLine
    norm_num
  have e2 : ‖rowFactor D u ξ w z‖ =
      ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖(D.Llam u ξ)⁻¹‖ * ‖EulerDomain.Hu D u ξ w z‖ := by
    unfold rowFactor
    simp only [div_eq_mul_inv, norm_mul]
  rw [e2]
  have hY : 0 ≤ (2 + |w.im|) ^ A := by positivity
  calc _ ≤ C1 * (C2 * (2 + |w.im|) ^ A) * C4 * (C3 * D.q u ^ (1 : ℝ)) := by gcongr
    _ = _ := by ring

private theorem weight_dom' (D : FixedData S η) (ξ : ℂ) (v y : ℝ) (Cc A : ℝ) (hCc : 0 ≤ Cc)
    (hA' : 0 ≤ A) (p : ℝ × ℝ) (x : ℝ)
    (hx : x ≤ Cc * (WeightConvolution.weightModulus D ξ v y p * (2 + |p.2|) ^ A)) :
    x ≤ Cc * WeightConvolution.weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ A := by
  have hW : 0 ≤ WeightConvolution.weightModulus D ξ v y p := by
    unfold WeightConvolution.weightModulus
    exact norm_nonneg _
  have h0 := abs_nonneg p.1
  have h0' := abs_nonneg p.2
  have h0'' := abs_nonneg ξ.im
  have h2 : (2 + |p.2|) ^ A ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ A :=
    Real.rpow_le_rpow (by linarith) (by linarith) hA'
  calc x ≤ Cc * (WeightConvolution.weightModulus D ξ v y p * (2 + |p.2|) ^ A) := hx
    _ ≤ Cc * (WeightConvolution.weightModulus D ξ v y p *
          (2 + |p.1| + |p.2| + |ξ.im|) ^ A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hW) hCc
    _ = _ := by ring

theorem K_maj_fixed (u : D.Row) (hq0 : 0 < D.q u) (A CR : ℝ)
    (hR' : ∀ ξ w z : ℂ, ξ.re = Scales.rightLine → w.re = Scales.wLine → z.re = Scales.zLine →
        ‖rowFactor D u ξ w z‖ ≤ CR * (2 + |w.im|) ^ A)
    (ξ : ℂ) (hre : ξ.re = Scales.rightLine) (Z : ℝ) (hZ : 0 < Z) (p : ℝ × ℝ) :
    ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      (CR * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * D.q u ^ (-Scales.zLine)) *
        (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A) := by
  have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
  have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
  have him2 : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
  have hRp := hR' ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
    ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) hre hw hz
  rw [him2] at hRp
  have hW : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := by
    unfold WeightConvolution.weightModulus
    exact norm_nonneg _
  have hZp : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := Real.rpow_nonneg hZ.le _
  have hqz : 0 ≤ D.q u ^ (-Scales.zLine) := (Real.rpow_pos_of_pos hq0 _).le
  have hn := RowKernelGrowth.K_norm_eq D u hq0 ξ Scales.zLine Scales.wLine p Z hZ
  rw [hre] at hn
  have hEq : Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1) =
      Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine := by unfold Scales.kernelExponent; ring
  rw [hEq] at hn
  rw [hn]
  calc _ ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * D.q u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (CR * (2 + |p.2|) ^ A) :=
        mul_le_mul_of_nonneg_left hRp (mul_nonneg (mul_nonneg hZp hqz) hW)
    _ = _ := by ring

set_option maxHeartbeats 1600000 in

theorem wz_decay_fixed (B : ℝ) (hB : 0 < B) (u : D.Row) (hu : u.u ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t Z : ℝ), 0 < Z →
      ‖wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * (1 + |t|) ^ (-B) := by
  obtain ⟨A, hA, hR⟩ := rowFactor_right_fixed D
  have hz0 : 0 < Scales.zLine := by unfold Scales.zLine; norm_num
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.nested_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine Scales.rightLine Scales.rightLine hz0 le_rfl le_rfl le_rfl B A hB hA
  obtain ⟨CR, hCR, hR'⟩ := hR u hu
  have hq0 : 0 < D.q u := lt_of_lt_of_le one_pos (ActualRowCount.one_le_q D u)
  have hqz : 0 < D.q u ^ (-Scales.zLine) := Real.rpow_pos_of_pos hq0 _
  have hx1 : (1 : ℝ) < Scales.rightLine := by rw [Scales.rightLine_eq]; norm_num
  refine ⟨CR * D.q u ^ (-Scales.zLine) * Cw * ((2 * Real.pi)⁻¹) ^ 2 + 1, by positivity, ?_⟩
  intro t Z hZ
  generalize hξ0 : (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I) = ξ0
  have hre : ξ0.re = Scales.rightLine := by rw [← hξ0]; simp
  have him : ξ0.im = t := by rw [← hξ0]; simp
  have hne : D.Llam u ξ0 ≠ 0 :=
    RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ0 (by rw [hre]; exact hx1)
  have hxg : Scales.goodLine - EulerDomain.pad ≤
      ξ0.re := by
    rw [hre, Scales.rightLine_eq]
    unfold Scales.goodLine EulerDomain.pad
    norm_num
  have hc0 := RowAnalyticContinuation.K_continuous_heights D u hu hq0 Z hZ ξ0 hxg hne
  have hc1 := hc0.comp (continuous_swap (X := ℝ) (Y := ℝ))
  have hcont : Continuous (fun p : ℝ × ℝ => K D u ξ0
      ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) := hc1
  have hZp : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := Real.rpow_nonneg hZ.le _
  have hCc : 0 ≤ CR * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * D.q u ^ (-Scales.zLine) := by
    positivity
  have hmaj : ∀ p : ℝ × ℝ, ‖K D u ξ0
      ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      (CR * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * D.q u ^ (-Scales.zLine)) *
        (WeightConvolution.weightModulus D ξ0
          Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A) :=
    fun p => K_maj_fixed D u hq0 A CR hR' ξ0 hre Z hZ p
  have hle := (hCw ξ0 hre.ge hre.le Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl _ hCc
    (fun w z => K D u ξ0 w z Z)
    hcont.aestronglyMeasurable
    (fun p => weight_dom' D ξ0 Scales.zLine Scales.wLine _ A hCc hA p _ (hmaj p))).2.2.2
  rw [him] at hle
  have hP : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * (1 + |t|) ^ (-B) := by positivity
  calc ‖wzIntegral D u ξ0 Scales.wLine Scales.zLine Z‖
      ≤ ((2 * Real.pi)⁻¹) ^ 2 * ((CR * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
          D.q u ^ (-Scales.zLine)) * Cw * (1 + |t|) ^ (-B)) := hle
    _ = (CR * D.q u ^ (-Scales.zLine) * Cw * ((2 * Real.pi)⁻¹) ^ 2) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * (1 + |t|) ^ (-B)) := by ring
    _ ≤ (CR * D.q u ^ (-Scales.zLine) * Cw * ((2 * Real.pi)⁻¹) ^ 2 + 1) *
          (Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * (1 + |t|) ^ (-B)) :=
        mul_le_mul_of_nonneg_right (by linarith) hP
    _ = _ := by ring

theorem vertical_norm_le' (G : ℂ → ℂ) (x A B : ℝ) (hB : 1 < B)
    (h : ∀ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-B)) :
    ‖comparisonVerticalIntegral x G‖ ≤
      (2 * Real.pi)⁻¹ * (A * ∫ t : ℝ, (1 + |t|) ^ (-B)) := by
  have hI : Integrable (fun t : ℝ => (1 + |t|) ^ (-B)) volume :=
    KernelWeightIntegration.one_add_abs_rpow_integrable B hB
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  unfold comparisonVerticalIntegral
  have h2 : ((2 * (Real.pi : ℂ))⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi]
  apply mul_le_mul_of_nonneg_left _ hpi
  calc ‖∫ t : ℝ, G ((x : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, A * (1 + |t|) ^ (-B) := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => norm_nonneg _) (hI.const_mul A)
          (Filter.Eventually.of_forall fun t => h t)
    _ = A * ∫ t : ℝ, (1 + |t|) ^ (-B) := integral_const_mul _ _

theorem fixedRow_low_bound_all (u : D.Row) (hu : u.u ≠ 1) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
        Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
  obtain ⟨C, hC, h⟩ := wz_decay_fixed D 2 (by norm_num) u hu
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) :=
    integral_nonneg (fun t => Real.rpow_nonneg (by positivity) _)
  refine ⟨(2 * Real.pi)⁻¹ * (C * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))) + 1, by positivity, ?_⟩
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZp : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := Real.rpow_nonneg hZ0.le _
  have e : rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z =
      comparisonVerticalIntegral Scales.rightLine (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) :=
    (triple_eq_rowIntegral D u _ _ _ Z).symm.trans
      (LowRowKernelDefinitions.triple_eq_J D u _ _ _ Z)
  rw [e]
  have hv := vertical_norm_le' (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) Scales.rightLine
    (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine)) 2 (by norm_num)
    (fun t => h t Z hZ0)
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have hnn : 0 ≤ (2 * Real.pi)⁻¹ * (C * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))) := by positivity
  calc _ ≤ (2 * Real.pi)⁻¹ * (C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
        ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))) := hv
    _ = ((2 * Real.pi)⁻¹ * (C * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)))) *
        Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by ring
    _ ≤ _ := by nlinarith [hZp, hnn]

theorem fixedRow_low_bound_small (u : D.Row) (hu : u.u ≠ 1) (hq : D.q u < 2) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
        Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) :=
  fixedRow_low_bound_all D u hu

theorem fixedRow_initial_eq (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    J D {u} 4 4 2 Z =
      rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z :=
  fixedRow_initial_eq_all D u hu Z hZ

theorem fixedRow_low_bound (u : D.Row) (hu : u.u ≠ 1) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖rowIntegral D (lowRowFactor D) u Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
        Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) :=
  fixedRow_low_bound_all D u hu

theorem fixedRow_initial_bound (u : D.Row) (hu : u.u ≠ 1) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖J D {u} 4 4 2 Z‖ ≤ Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
  obtain ⟨Cu, hC, h⟩ := fixedRow_low_bound D u hu
  exact ⟨Cu, hC, fun Z hZ => by rw [fixedRow_initial_eq D u hu Z hZ]; exact h Z hZ⟩

end

end DedekindZetaZeroFree.Quantitative.FixedLowRowContour
