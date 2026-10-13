module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.GoodSideBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.RectangleDeformation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawGoodRowRectangle31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

def rawCentral (u : Frequency D.recipe) (ρ U Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
      Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z

def rawUpper (u : Frequency D.recipe) (ρ U Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ σ in Scales.goodLine..Scales.rightLine,
      Iwz D u ((σ : ℂ) + ((1 * U ^ ρ : ℝ) : ℂ) * Complex.I) Scales.wLine Scales.zLine Z

def rawLower (u : Frequency D.recipe) (ρ U Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ σ in Scales.rightLine..Scales.goodLine,
      Iwz D u ((σ : ℂ) + (((-1) * U ^ ρ : ℝ) : ℂ) * Complex.I) Scales.wLine Scales.zLine Z

def rawRightTail (u : Frequency D.recipe) (ρ U Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in {t : ℝ | U ^ ρ < |t|},
      Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z

theorem rawGood_rectangle_decomp (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ Z : ℝ, 0 < Z →
        triple D u Scales.rightLine Scales.wLine Scales.zLine Z =
          rawCentral D u ρ U Z + rawUpper D u ρ U Z + rawLower D u ρ U Z +
            rawRightTail D u ρ U Z := by
  refine ⟨2, le_rfl, fun U hU u hu hU1 hU2 hexc Z hZ => ?_⟩
  have hT : (0 : ℝ) ≤ U ^ ρ := Real.rpow_nonneg (by linarith) _
  have hab : Scales.goodLine ≤ Scales.rightLine := by
    norm_num [Scales.goodLine, Scales.rightLine, Scales.contourOffset]
  have hσ : DetectorDef.σ₀ ≤ Scales.goodLine - EulerDomain.pad / 2 := by
    norm_num [DetectorDef.σ₀, Scales.goodLine, EulerDomain.pad]
  have hpad : (0 : ℝ) < EulerDomain.pad := by norm_num [EulerDomain.pad]
  have hxg : (0 : ℝ) < Scales.goodLine := by norm_num [Scales.goodLine]
  have hf : DifferentiableOn ℂ (fun ξ : ℂ => Iwz D u ξ Scales.wLine Scales.zLine Z)
      (Set.uIcc Scales.goodLine Scales.rightLine ×ℂ Set.uIcc (-(U ^ ρ)) (U ^ ρ)) := by
    refine (RawGoodNestedControls31.Iwz_differentiableOn_goodNbhd D A hA hconv u hu Z hZ).mono ?_
    intro ξ hξ
    obtain ⟨hre, him⟩ := hξ
    rw [Set.uIcc_of_le hab] at hre
    rw [Set.uIcc_of_le (by linarith)] at him
    obtain ⟨h1, h2⟩ := hre
    obtain ⟨h3, h4⟩ := him
    have him' : |ξ.im| ≤ 4 * U ^ ρ := by
      rw [abs_le]; constructor <;> linarith
    refine ⟨by linarith, by linarith, ?_⟩
    exact (RawKernelRegularity31.minus_ne_zero_of_not_exceptional D ρ U u hu hU1 hU2 hexc ξ
      (by linarith) (by linarith) him').2
  have hint := RawGoodNestedControls31.Iwz_integrable_right D A hA hconv U hU u hu hU1 hU2 Z hZ
  have key := RowRectangleDeformation.rect_decomp
    (fun ξ : ℂ => Iwz D u ξ Scales.wLine Scales.zLine Z) Scales.goodLine Scales.rightLine (U ^ ρ) hab hT hf hint
  unfold triple rawCentral rawUpper rawLower rawRightTail
  simpa [comparisonVerticalIntegral] using key

private abbrev KK : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))

private theorem KK_int : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  simp only [Real.norm_eq_abs] at h
  exact h

private theorem KK_nonneg : 0 ≤ KK :=
  integral_nonneg fun t => by positivity

private theorem rpow_neg_le' {T s B : ℝ} (hT : 0 < T) (hs : T ≤ s) (hB : 0 ≤ B) :
    s ^ (-B) ≤ T ^ (-B) := by
  rw [Real.rpow_neg (hT.le.trans hs), Real.rpow_neg hT.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hT _) (Real.rpow_le_rpow hT.le hs hB)

private theorem pw_bound {U ρ B : ℝ} (hU : 1 ≤ U) (hρ : 0 < ρ) :
    U ^ ((1 / 25 : ℝ) + 1) * (U ^ ρ) ^ (-((B + 2) / ρ)) ≤ U ^ (-B) := by
  have hU0 : 0 ≤ U := by linarith
  rw [← Real.rpow_mul hU0, ← Real.rpow_add (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have : ρ * (-((B + 2) / ρ)) = -(B + 2) := by field_simp
  rw [this]
  linarith

private theorem final_mul {c C P V R W K : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hVR : V * R ≤ W) :
    c * (C * P * V * R * K) ≤ (C * (K + 1) * c) * P * W := by
  have h1 : 0 ≤ c * C * P * K := by positivity
  have h2 : (c * C * P * K) * (V * R) ≤ (c * C * P * K) * W :=
    mul_le_mul_of_nonneg_left hVR h1
  have h3 : 0 ≤ c * C * P * W := by positivity
  nlinarith [h2, h3]

private theorem tail_int (f : ℝ → ℂ) {T M B2 : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hB2 : 0 ≤ B2)
    (hf : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ M * (1 + |t|) ^ (-(2 + B2))) :
    ‖∫ t in {t : ℝ | T < |t|}, f t‖ ≤ M * T ^ (-B2) * KK := by
  have hs : MeasurableSet {t : ℝ | T < |t|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hint : Integrable (fun t : ℝ => M * T ^ (-B2) * (1 + |t|) ^ (-(2 : ℝ))) :=
    KK_int.const_mul _
  have hpt : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ M * T ^ (-B2) * (1 + |t|) ^ (-(2 : ℝ)) := by
    intro t ht
    have h1 := hf t ht
    have hpos : 0 < 1 + |t| := by positivity
    have h2 : (1 + |t|) ^ (-(2 + B2)) = (1 + |t|) ^ (-(2 : ℝ)) * (1 + |t|) ^ (-B2) := by
      rw [neg_add, Real.rpow_add hpos]
    have h3 : (1 + |t|) ^ (-B2) ≤ T ^ (-B2) := rpow_neg_le' hT (by linarith) hB2
    calc ‖f t‖ ≤ M * (1 + |t|) ^ (-(2 + B2)) := h1
      _ = M * ((1 + |t|) ^ (-(2 : ℝ)) * (1 + |t|) ^ (-B2)) := by rw [h2]
      _ ≤ M * ((1 + |t|) ^ (-(2 : ℝ)) * T ^ (-B2)) := by gcongr
      _ = M * T ^ (-B2) * (1 + |t|) ^ (-(2 : ℝ)) := by ring
  calc ‖∫ t in {t : ℝ | T < |t|}, f t‖
      ≤ ∫ t in {t : ℝ | T < |t|}, M * T ^ (-B2) * (1 + |t|) ^ (-(2 : ℝ)) :=
        norm_integral_le_of_norm_le hint.restrict
          (ae_restrict_of_forall_mem hs fun t ht => hpt t ht)
    _ ≤ ∫ t : ℝ, M * T ^ (-B2) * (1 + |t|) ^ (-(2 : ℝ)) :=
        setIntegral_le_integral hint
          (ae_of_all _ fun t => by show (0 : ℝ) ≤ _; positivity)
    _ = M * T ^ (-B2) * KK := integral_const_mul _ _

private theorem norm_inv_two_pi : ‖((2 : ℂ) * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, norm_mul]
  simp [abs_of_pos Real.pi_pos]

private theorem norm_inv_two_pi_I :
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul]
  simp [abs_of_pos Real.pi_pos]

theorem rawGood_central_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ Z : ℝ, 0 < Z →
        ‖rawCentral D u ρ U Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) := by
  obtain ⟨C, hC, U₀, hU₀, h⟩ :=
    RawGoodNestedControls31.Iwz_decay_rect D A ρ hA hconv hρ ε hε 2 (by norm_num)
  have hab : Scales.goodLine ≤ Scales.rightLine := by
    norm_num [Scales.goodLine, Scales.rightLine, Scales.contourOffset]
  refine ⟨C * (KK + 1) * (2 * Real.pi)⁻¹, by have := KK_nonneg; positivity, U₀, hU₀, ?_⟩
  intro U hU u hu hU1 hU2 hexc Z hZ
  have hUpos : 0 < U := by linarith
  have hT : (0 : ℝ) ≤ U ^ ρ := Real.rpow_nonneg hUpos.le _
  have hf : ∀ t ∈ Set.Icc (-(U ^ ρ)) (U ^ ρ),
      ‖Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
          (1 + |t|) ^ (-(2 : ℝ)) := by
    intro t ht
    have hre : ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.goodLine := by simp
    have him : ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have := h U hU u hu hU1 hU2 hexc ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Z hZ
      hre.symm.le (hre.le.trans hab)
      (by rw [him, abs_le]; constructor <;> linarith [ht.1, ht.2])
    rw [hre, him] at this
    exact this
  have hint : Integrable (fun t : ℝ =>
      C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
          (1 + |t|) ^ (-(2 : ℝ))) := KK_int.const_mul _
  have hbound : ‖∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
      Iwz D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
      C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) * KK := by
    calc _ ≤ ∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
          C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
            (1 + |t|) ^ (-(2 : ℝ)) :=
          norm_integral_le_of_norm_le hint.restrict
            (ae_restrict_of_forall_mem measurableSet_Icc hf)
      _ ≤ ∫ t : ℝ, C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) *
            (1 + |t|) ^ (-(2 : ℝ)) :=
          setIntegral_le_integral hint
            (ae_of_all _ fun t => by show (0 : ℝ) ≤ _; positivity)
      _ = _ := integral_const_mul _ _
  have hK := KK_nonneg
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hP : 0 ≤ C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + ε) := by
    positivity
  unfold rawCentral
  rw [norm_mul, norm_inv_two_pi]
  have h1 := mul_le_mul_of_nonneg_left hbound hpi.le
  have h2 : 0 ≤ (2 * Real.pi)⁻¹ * (C * Z ^ (Scales.kernelExponent Scales.goodLine Scales.wLine Scales.zLine) *
      U ^ ((1 / 25 : ℝ) + ε)) := by positivity
  nlinarith [h1, h2]

theorem rawGood_horiz_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U → u ∉ FixedData.rawExceptionalSet D ρ U →
      ∀ Z : ℝ, 1 ≤ Z →
        ‖rawUpper D u ρ U Z‖ ≤ C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) ∧
        ‖rawLower D u ρ U Z‖ ≤ C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) := by
  have hρ0 : 0 < ρ := hρ.1
  obtain ⟨C, hC, U₀, hU₀, h⟩ :=
    RawGoodNestedControls31.Iwz_decay_rect D A ρ hA hconv hρ 1 one_pos ((B + 2) / ρ)
      (by positivity)
  have hab : Scales.goodLine ≤ Scales.rightLine := by
    norm_num [Scales.goodLine, Scales.rightLine, Scales.contourOffset]
  refine ⟨C * (|Scales.rightLine - Scales.goodLine| + 1) * (2 * Real.pi)⁻¹,
    by positivity, U₀, hU₀, ?_⟩
  intro U hU u hu hU1 hU2 hexc Z hZ
  have hUpos : 0 < U := by linarith
  have hT0 : 0 < U ^ ρ := Real.rpow_pos_of_pos hUpos _
  have hZpos : 0 < Z := by linarith
  have hpt : ∀ s : ℝ, |s| = 1 → ∀ σ : ℝ, Scales.goodLine < σ → σ ≤ Scales.rightLine →
      ‖Iwz D u ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1) *
          (U ^ ρ) ^ (-((B + 2) / ρ)) := by
    intro s hs σ h1 h2
    have hre : ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I).im = s * U ^ ρ := by simp
    have habs : |s * U ^ ρ| = U ^ ρ := by
      rw [abs_mul, hs, one_mul, abs_of_pos hT0]
    have := h U hU u hu hU1 hU2 hexc ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I) Z hZpos
      (h1.le.trans hre.symm.le) (hre.le.trans h2)
      (by rw [him, habs]; linarith)
    rw [hre, him, habs] at this
    have hE : Scales.kernelExponent σ Scales.wLine Scales.zLine ≤ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine := by
      simp only [Scales.kernelExponent]; linarith
    have hZE : Z ^ (Scales.kernelExponent σ Scales.wLine Scales.zLine) ≤
        Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) :=
      Real.rpow_le_rpow_of_exponent_le hZ hE
    have hdec : (1 + U ^ ρ) ^ (-((B + 2) / ρ)) ≤ (U ^ ρ) ^ (-((B + 2) / ρ)) :=
      rpow_neg_le' hT0 (by linarith) (by positivity)
    refine this.trans ?_
    have hCU : 0 ≤ C * U ^ ((1 / 25 : ℝ) + 1) := by positivity
    have hpos : 0 ≤ (1 + U ^ ρ) ^ (-((B + 2) / ρ)) := by positivity
    calc C * Z ^ (Scales.kernelExponent σ Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1) *
          (1 + U ^ ρ) ^ (-((B + 2) / ρ))
        = (C * U ^ ((1 / 25 : ℝ) + 1)) * Z ^ (Scales.kernelExponent σ Scales.wLine Scales.zLine) *
          (1 + U ^ ρ) ^ (-((B + 2) / ρ)) := by ring
      _ ≤ (C * U ^ ((1 / 25 : ℝ) + 1)) * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) *
          (U ^ ρ) ^ (-((B + 2) / ρ)) := by
        gcongr
      _ = _ := by ring
  have hside : ∀ s : ℝ, |s| = 1 → ∀ a b : ℝ, (∀ σ ∈ Set.uIoc a b,
        Scales.goodLine < σ ∧ σ ≤ Scales.rightLine) →
      ‖∫ σ in a..b, Iwz D u ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I)
          Scales.wLine Scales.zLine Z‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1) *
          (U ^ ρ) ^ (-((B + 2) / ρ)) * |b - a| := by
    intro s hs a b hab'
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun σ hσ => hpt s hs σ (hab' σ hσ).1 (hab' σ hσ).2)
  have hpw := pw_bound (B := B) (U := U) (ρ := ρ) (by linarith) hρ0
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  have key : ∀ s : ℝ, |s| = 1 → ∀ a b : ℝ, (∀ σ ∈ Set.uIoc a b,
        Scales.goodLine < σ ∧ σ ≤ Scales.rightLine) → |b - a| = |Scales.rightLine - Scales.goodLine| →
      ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ σ in a..b, Iwz D u ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I)
          Scales.wLine Scales.zLine Z‖ ≤
        (C * (|Scales.rightLine - Scales.goodLine| + 1) * (2 * Real.pi)⁻¹) *
          Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) := by
    intro s hs a b hab' hba
    rw [norm_mul, norm_inv_two_pi_I]
    have h1 := hside s hs a b hab'
    rw [hba] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hpi.le
    refine h2.trans ?_
    exact final_mul hpi hC.le (by positivity) (abs_nonneg _) (by positivity) hpw
  constructor
  · unfold rawUpper
    refine key 1 (by simp) _ _ ?_ rfl
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    exact hσ
  · unfold rawLower
    refine key (-1) (by simp) _ _ ?_ (abs_sub_comm _ _)
    intro σ hσ
    rw [Set.uIoc_of_ge hab] at hσ
    exact hσ

theorem rawGood_tail_bound (A ρ : ℝ) (hA : 0 ≤ A) (hconv : RawConvexityExponent D A)
    (hρ : HeightSpec D A ρ) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : Frequency D.recipe,
      u ≠ principalFrequency D.recipe → U ≤ frequencyNorm D.recipe u →
      frequencyNorm D.recipe u < 2 * U →
      ∀ Z : ℝ, 0 < Z →
        ‖rawRightTail D u ρ U Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ (-B) := by
  have hρ0 : 0 < ρ := hρ.1
  obtain ⟨C, hC, h⟩ :=
    RawGoodNestedControls31.Iwz_decay_right D A hA hconv 1 one_pos (2 + (B + 2) / ρ)
      (by positivity)
  refine ⟨C * (KK + 1) * (2 * Real.pi)⁻¹, by have := KK_nonneg; positivity, 2, le_rfl, ?_⟩
  intro U hU u hu hU1 hU2 Z hZ
  have hUpos : 0 < U := by linarith
  have hT0 : 0 < U ^ ρ := Real.rpow_pos_of_pos hUpos _
  have hK := KK_nonneg
  have hint := tail_int (fun t : ℝ =>
      Iwz D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z)
    (T := U ^ ρ)
    (M := C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 / 25 : ℝ) + 1))
    (B2 := (B + 2) / ρ) hT0 (by positivity) (by positivity) (by
      intro t _
      have hre : ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.rightLine := by simp
      have him : ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      have := h U hU u hu hU1 hU2 ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Z hZ hre
      rw [him] at this
      exact this)
  have hpw := pw_bound (B := B) (U := U) (ρ := ρ) (by linarith) hρ0
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  unfold rawRightTail
  rw [norm_mul, norm_inv_two_pi]
  refine (mul_le_mul_of_nonneg_left hint hpi.le).trans ?_
  exact final_mul hpi hC.le (by positivity) hK (by positivity) hpw

end

end DedekindZetaZeroFree.Quantitative.RawGoodRowRectangle31
