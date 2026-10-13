module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.FrequencyRectangles
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LargeZControls
public import DedekindZetaZeroFree.Analysis.FrequencyPowerTails

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLargeRowShift31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem rawKernel_analytic_z (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) :
    AnalyticOnNhd ℂ (fun z : ℂ => rawKernel D u ξ w z Z) {z : ℂ | 1 / 6 < z.re} :=
  DedekindZetaZeroFree.Quantitative.RawLargeZControls31.rawKernel_analytic_z D u hu Z hZ ξ w hξ hw

theorem rawKernel_majorant_right (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z → ∀ σ ∈ Icc (2 : ℝ) Scales.tailShift, ∀ t : ℝ × ℝ × ℝ,
        ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
            ((σ : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
          Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε) * g t := by
  obtain ⟨C, hC, H⟩ := DedekindZetaZeroFree.Quantitative.RawLargeZControls31.rawKernel_product_majorant D ε hε
  have h1 : Integrable (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) := by
    have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := 2) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have hG : Integrable (fun p : ℝ × ℝ × ℝ =>
      ((1 + |p.1|) ^ 2)⁻¹ * (((1 + |p.2.1|) ^ 2)⁻¹ * ((1 + |p.2.2|) ^ 2)⁻¹)) := by
    have h2 : Integrable (fun q : ℝ × ℝ => ((1 + |q.1|) ^ 2)⁻¹ * ((1 + |q.2|) ^ 2)⁻¹)
        (volume.prod volume) := Integrable.mul_prod h1 h1
    exact Integrable.mul_prod h1 h2
  refine ⟨fun p => C * (((1 + |p.1|) ^ 2)⁻¹ * (((1 + |p.2.1|) ^ 2)⁻¹ * ((1 + |p.2.2|) ^ 2)⁻¹)),
    hG.const_mul C, fun p => mul_nonneg hC.le (by positivity), fun u hu Z hZ σ hσ t => ?_⟩
  have e1 : ((4 : ℂ) + (t.1 : ℂ) * I).im = t.1 := by simp
  have e2 : ((4 : ℂ) + (t.2.1 : ℂ) * I).im = t.2.1 := by simp
  have e3 : ((σ : ℂ) + (t.2.2 : ℂ) * I).im = t.2.2 := by simp
  have key := H u hu Z hZ σ hσ ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
    ((σ : ℂ) + (t.2.2 : ℂ) * I) (by simp) (by simp) (by simp)
  rw [e1, e2, e3] at key
  dsimp only
  refine key.trans (le_of_eq ?_)
  ring

theorem rawKernel_integrable_line (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) (σ : ℝ)
    (hσ : σ ∈ Icc (2 : ℝ) Scales.tailShift) :
    Integrable (fun t : ℝ => rawKernel D u ξ w ((σ : ℂ) + (t : ℂ) * I) Z) :=
  DedekindZetaZeroFree.Quantitative.RawLargeZControls31.rawKernel_integrable_line D u hu Z hZ ξ w hξ hw σ hσ

theorem rawKernel_horizontal_tendsto_zero (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : w.re = 4) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (2 : ℝ)..Scales.tailShift,
        rawKernel D u ξ w ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I) Z) atTop (𝓝 0) :=
  DedekindZetaZeroFree.Quantitative.RawLargeZControls31.rawKernel_horizontal_tendsto_zero D u hu Z hZ ξ w hξ hw ε hε

theorem raw_z_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) :
    Iz D u ξ w 2 Z = Iz D u ξ w Scales.tailShift Z :=
  DedekindZetaZeroFree.Quantitative.RawLargeZControls31.Iz_shift_two_R D u hu Z hZ ξ w hξ hw

private lemma cvi_congr {σ : ℝ} {f g : ℂ → ℂ}
    (h : ∀ t : ℝ, f ((σ : ℂ) + (t : ℂ) * Complex.I) = g ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    comparisonVerticalIntegral σ f = comparisonVerticalIntegral σ g := by
  unfold comparisonVerticalIntegral
  simp only [h]

theorem raw_Iwz_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 2 Z = Iwz D u ξ 4 Scales.tailShift Z := by
  unfold Iwz
  refine cvi_congr (fun t => ?_)
  exact raw_z_shift D u hu Z hZ ξ _ hξ (by simp)

theorem raw_initialRowIntegral_shift (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 2 ≤ Z) :
    initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z := by
  unfold initialRowIntegral triple
  refine cvi_congr (fun t => ?_)
  exact raw_Iwz_shift D u hu Z hZ _ (by simp)

theorem raw_large_triple_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z →
      Integrable (fun t : ℝ × ℝ × ℝ =>
        rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) ∧
      ∫ t : ℝ × ℝ × ℝ, ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
        C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
  obtain ⟨C, hC, H⟩ := DedekindZetaZeroFree.Quantitative.RawLargeZControls31.triple_norm_le D ε hε
  refine ⟨C, hC, fun u hu Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := H u hu Z hZ
  refine ⟨h1, h2.trans ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hE : Z ^ (Scales.kernelExponent 4 4 Scales.tailShift) ≤ Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold Scales.kernelExponent Scales.xExponent Scales.yExponent Scales.smoothingExponent
    linarith
  have hq : 0 ≤ frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) :=
    Real.rpow_nonneg (by linarith [RawFrequencyCount.one_le_frequencyNorm D.recipe u]) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hC.le) hq

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

theorem raw_large_row_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z →
        initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z ∧
        ‖initialRowIntegral D u Z‖ ≤
          C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
  obtain ⟨C0, hC0, H⟩ := raw_large_triple_bound D ε hε
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ‖(2 * (Real.pi : ℂ))⁻¹‖ *
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖(2 * (Real.pi : ℂ))⁻¹‖) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨(A + 1) * C0, by positivity, fun u hu Z hZ => ⟨raw_initialRowIntegral_shift D u hu Z hZ, ?_⟩⟩
  obtain ⟨hint, hb⟩ := H u hu Z hZ
  rw [raw_initialRowIntegral_shift D u hu Z hZ]
  have h := iter_triple (fun a b c => rawKernel D u ((4 : ℂ) + (a : ℂ) * Complex.I)
    ((4 : ℂ) + (b : ℂ) * Complex.I) (((Scales.tailShift : ℝ) : ℂ) + (c : ℂ) * Complex.I) Z) hint
  have hval : triple D u 4 4 Scales.tailShift Z =
      (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ × ℝ × ℝ,
          rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z)) := by
    rw [← h]
    simp only [triple, Iwz, Iz, comparisonVerticalIntegral, MeasureTheory.integral_const_mul,
      Complex.ofReal_ofNat]
  rw [hval]
  simp only [norm_mul]
  have h1 := (MeasureTheory.norm_integral_le_integral_norm _).trans hb
  have hn : 0 ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
  have hB : 0 ≤ C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
      frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
    have := hb
    exact le_trans (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)) this
  calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ‖∫ t : ℝ × ℝ × ℝ, rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖))
      = A * ‖∫ t : ℝ × ℝ × ℝ, rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ := by rw [hA]; ring
    _ ≤ A * (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          frequencyNorm D.recipe u ^ (-Scales.tailShift + ε)) := mul_le_mul_of_nonneg_left h1 hA0
    _ ≤ (A + 1) * (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          frequencyNorm D.recipe u ^ (-Scales.tailShift + ε)) :=
        mul_le_mul_of_nonneg_right (by linarith) hB
    _ = _ := by ring

theorem raw_rows_large (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Summable (fun u : {u : Frequency D.recipe //
          u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < frequencyNorm D.recipe u} =>
        ‖initialRowIntegral D u.1 Z‖) ∧
      ‖∑' u : {u : Frequency D.recipe //
          u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < frequencyNorm D.recipe u},
        initialRowIntegral D u.1 Z‖ ≤ C * Z ^ (Scales.mainExponent - 1481 / 2500 + ε) := by
  set ε₀ : ℝ := min ε 1 with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hRv : Scales.tailShift = 50000 := by norm_num [Scales.tailShift]
  obtain ⟨Cr, hCr, Hr⟩ := raw_large_row_bound D ε₀ hε₀
  obtain ⟨K, hK, hcount⟩ := DedekindZetaZeroFree.Quantitative.RawFrequencyCount.fixedData_frequency_count_lt D
  have hfin : ∀ Y : ℝ, {u : Frequency D.recipe | frequencyNorm D.recipe u ≤ Y}.Finite :=
    fun Y => (hcount (max Y 1 + 1) (by linarith [le_max_right Y 1])).1.subset
      (fun u hu => lt_of_le_of_lt (le_trans (show frequencyNorm D.recipe u ≤ Y from hu)
        (le_max_left Y 1)) (lt_add_one _))
  have hK' : ∀ Y : ℝ, 1 ≤ Y → (({u : Frequency D.recipe | frequencyNorm D.recipe u ≤ Y} :
      Set (Frequency D.recipe)).ncard : ℝ) ≤ (2 * K) * Y := by
    intro Y hY
    have hsub : {u : Frequency D.recipe | frequencyNorm D.recipe u ≤ Y} ⊆
        {u : Frequency D.recipe | frequencyNorm D.recipe u < Y + 1} :=
      fun u hu => lt_of_le_of_lt (show frequencyNorm D.recipe u ≤ Y from hu) (lt_add_one _)
    have h1 := (hcount (Y + 1) (by linarith)).2
    have h2 : ({u : Frequency D.recipe | frequencyNorm D.recipe u ≤ Y} :
        Set (Frequency D.recipe)).ncard ≤
        ({u : Frequency D.recipe | frequencyNorm D.recipe u < Y + 1} :
          Set (Frequency D.recipe)).ncard :=
      Set.ncard_le_ncard hsub (hcount (Y + 1) (by linarith)).1
    have h3 : ((({u : Frequency D.recipe | frequencyNorm D.recipe u ≤ Y} :
        Set (Frequency D.recipe)).ncard : ℕ) : ℝ) ≤
        ((({u : Frequency D.recipe | frequencyNorm D.recipe u < Y + 1} :
          Set (Frequency D.recipe)).ncard : ℕ) : ℝ) := by exact_mod_cast h2
    nlinarith [mul_nonneg hK.le (sub_nonneg.2 hY)]
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hp : (1 : ℝ) < Scales.tailShift - ε₀ := by rw [hRv]; linarith
  obtain ⟨Ct, hCt, Ht⟩ := FrequencyPowerTails.tail_dominated (frequencyNorm D.recipe)
    (Scales.tailShift - ε₀) (2 * K) hp hfin hK'
  refine ⟨Cr * Ct, mul_pos hCr hCt, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hX : 1 ≤ Z ^ Scales.largeCutoffExponent := Real.one_le_rpow hZ1 (by norm_num [Scales.largeCutoffExponent])
  have hB : 0 ≤ Cr * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) :=
    (mul_pos hCr (Real.rpow_pos_of_pos hZ0 _)).le
  have hsum := Ht (Z ^ Scales.largeCutoffExponent) hX _ hB
    {u : Frequency D.recipe | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < frequencyNorm D.recipe u}
    (fun u => ‖initialRowIntegral D u Z‖)
    (fun u hu => hu.2)
    (fun u hu => by
      refine ⟨norm_nonneg _, ?_⟩
      have hr := Hr u hu.1 Z hZ
      have hneg : -Scales.tailShift + ε₀ = -(Scales.tailShift - ε₀) := by ring
      rw [hneg] at hr
      calc ‖initialRowIntegral D u Z‖ ≤ Cr * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            frequencyNorm D.recipe u ^ (-(Scales.tailShift - ε₀)) := hr.2
        _ = _ := by ring)
  refine ⟨hsum.1, ?_⟩
  have hpow : Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
      (Z ^ Scales.largeCutoffExponent) ^ (1 - (Scales.tailShift - ε₀)) ≤ Z ^ (Scales.mainExponent - 1481 / 2500 + ε) := by
    rw [← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    unfold Scales.largeCutoffExponent Scales.mainExponent
    rw [hRv]
    linarith
  refine (norm_tsum_le_tsum_norm (f := fun u : ↥{u : Frequency D.recipe | u ≠
      principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < frequencyNorm D.recipe u} =>
      initialRowIntegral D u.1 Z) hsum.1).trans (hsum.2.trans ?_)
  calc _ = (Cr * Ct) * (Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
      (Z ^ Scales.largeCutoffExponent) ^ (1 - (Scales.tailShift - ε₀))) := by ring
    _ ≤ (Cr * Ct) * Z ^ (Scales.mainExponent - 1481 / 2500 + ε) :=
        mul_le_mul_of_nonneg_left hpow (mul_pos hCr hCt).le

theorem raw_rows_large_contribution :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖∑' u : {u : Frequency D.recipe //
          u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < frequencyNorm D.recipe u},
        initialRowIntegral D u.1 Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) := by
  obtain ⟨C, hC, h⟩ := raw_rows_large D (1 / 100) (by norm_num)
  refine ⟨C, hC, fun Z hZ => ?_⟩
  refine (h Z hZ).2.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  norm_num [Scales.mainExponent]

end

end DedekindZetaZeroFree.Quantitative.RawLargeRowShift31
