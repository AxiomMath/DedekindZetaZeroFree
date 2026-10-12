module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalSchwartzIntegral
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactSubgroupCharacterIntegral
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalMellin.BallShellPole
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.NonarchimedeanWhittakerBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical WithZero NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TateFiniteShell

variable (F : Type) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

abbrev q (v : HeightOneSpectrum (𝓞 F)) : ℕ := Ideal.absNorm v.asIdeal

def unitShell (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F) :=
  (finiteCompletionBall F v 0 : Set _) \ (finiteCompletionBall F v 1 : Set _)

def annularTest (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F → ℂ :=
  (unitShell F v).indicator (fun _ => 1)

def ballTest (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) : v.adicCompletion F → ℂ :=
  (finiteCompletionBall F v n : Set _).indicator (fun _ => 1)

def HasConductor (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (m : ℤ) : Prop :=
  ∀ y, (∀ x ∈ finiteCompletionBall F v 0, ψ (x * y) = 1) ↔
    y ∈ finiteCompletionBall F v m

def fourier (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (y : v.adicCompletion F) : ℂ :=
  ∫ x, f x * (ψ (-x * y) : ℂ) ∂μ

def multiplicativeHaar (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) : Measure (v.adicCompletion F) :=
  (μ.restrict {0}ᶜ).withDensity
    (fun x => ENNReal.ofReal (((1 - (q F v : ℝ)⁻¹) * ‖x‖)⁻¹))

def mellin (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (s : ℝ) : ℂ :=
  ∫ x, f x * (↑(‖x‖ ^ s) : ℂ) ∂multiplicativeHaar F v μ

def tateRatio (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  (1 - (q F v : ℝ) ^ (s - 1)) / (1 - (q F v : ℝ) ^ (-s))

def conductorHaar (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) (m : ℤ) : Measure (v.adicCompletion F) :=
  ENNReal.ofReal ((q F v : ℝ) ^ ((m : ℝ) / 2)) • μ

def rescaledCharacter (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (a : v.adicCompletion F) :
    AddChar (v.adicCompletion F) Circle :=
  ψ.mulShift a

theorem tateRatio_pos (v : HeightOneSpectrum (𝓞 F)) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) : 0 < tateRatio F v s := by
  have hq : 1 < (q F v : ℝ) := by
    exact_mod_cast finiteCompletion_residueCard_gt_one F v
  have hn : (q F v : ℝ) ^ (s - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hd : (q F v : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  exact div_pos (sub_pos.mpr hn) (sub_pos.mpr hd)

theorem mem_unitShell_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    x ∈ unitShell F v ↔ Valued.v x = 1 := by
  change (Valued.v x ≤ WithZero.exp (-(0 : ℤ)) ∧
    ¬ Valued.v x ≤ WithZero.exp (-(1 : ℤ))) ↔ _
  generalize Valued.v x = g
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp i =>
    simp only [neg_zero, WithZero.exp_zero, ← WithZero.exp_zero,
      WithZero.exp_le_exp, WithZero.exp_inj]
    omega

theorem annularTest_mem_localSchwartz (v : HeightOneSpectrum (𝓞 F)) :
    annularTest F v ∈ localSchwartz F v := by
  have hU : IsClopen (unitShell F v) :=
    (show IsClopen (finiteCompletionBall F v 0 : Set _) from
      ⟨(isCompact_finiteCompletionBall F v 0).isClosed,
        isOpen_finiteCompletionBall F v 0⟩).diff
    ⟨(isCompact_finiteCompletionBall F v 1).isClosed,
      isOpen_finiteCompletionBall F v 1⟩
  constructor
  · exact (LocallyConstant.charFn ℂ hU).isLocallyConstant
  · apply HasCompactSupport.intro (isCompact_finiteCompletionBall F v 0)
    intro x hx
    exact Set.indicator_of_notMem (fun h => hx h.1) _

theorem rescaledCharacter_continuous (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : Continuous ψ)
    (a : v.adicCompletion F) : Continuous (rescaledCharacter F v ψ a) := by
  exact hψ.comp (continuous_const.mul continuous_id)

theorem rescaledCharacter_conductorZero (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (m : ℤ)
    (hc : HasConductor F v ψ m) (a : v.adicCompletion F)
    (ha : Valued.v a = WithZero.exp (-m)) :
    HasConductor F v (rescaledCharacter F v ψ a) 0 := by
  intro y
  change (∀ x ∈ finiteCompletionBall F v 0, ψ (a * (x * y)) = 1) ↔ _
  simp_rw [show ∀ x, a * (x * y) = x * (a * y) from fun x => by ring]
  rw [hc]
  simp only [mem_finiteCompletionBall, map_mul, ha, neg_zero, WithZero.exp_zero]
  simpa only [mul_one] using
    (mul_le_mul_iff_right₀ (WithZero.exp_pos (a := -m)) :
      WithZero.exp (-m) * Valued.v y ≤ WithZero.exp (-m) * 1 ↔ Valued.v y ≤ 1)

theorem fourier_rescaledCharacter (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (a : v.adicCompletion F) (ha : a ≠ 0) (y : v.adicCompletion F) :
    fourier F v (rescaledCharacter F v ψ a) μ f (y / a) = fourier F v ψ μ f y := by
  unfold fourier rescaledCharacter
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  simp only [AddChar.mulShift_apply]
  congr 1
  field_simp

theorem fourier_conductorHaar (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (m : ℤ) (y : v.adicCompletion F) :
    fourier F v ψ (conductorHaar F v μ m) f y =
      (↑((q F v : ℝ) ^ ((m : ℝ) / 2)) : ℂ) * fourier F v ψ μ f y := by
  have hq : 0 < (q F v : ℝ) := by
    exact_mod_cast Nat.zero_lt_one.trans (finiteCompletion_residueCard_gt_one F v)
  simp only [fourier, conductorHaar, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hq _).le, Complex.real_smul]

theorem finiteCompletionBall_mass (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) (n : ℤ) :
    μ.real (finiteCompletionBall F v n : Set _) = (q F v : ℝ) ^ (-n) := by
  have hq : (v.asIdeal.absNorm : ℝ≥0) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
  have hpn : ‖finiteCompletionUniformizer F v ^ n‖ = (q F v : ℝ) ^ (-n) := by
    rw [norm_zpow, FinitePlace.norm_def, finiteCompletionUniformizer_valuation,
      WithZeroMulInt.toNNReal_neg_apply hq WithZero.exp_ne_zero, WithZero.log_exp,
      NNReal.coe_zpow, ← zpow_mul]
    simp
  have heq : (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
      {x | ‖x‖ ≤ (q F v : ℝ) ^ (-n)} := by
    ext x
    change Valued.v x ≤ WithZero.exp (-n) ↔ ‖x‖ ≤ (q F v : ℝ) ^ (-n)
    rw [← hpn, Valued.toNormedField.norm_le_iff]
    simp [map_zpow₀, finiteCompletionUniformizer_valuation, ← WithZero.exp_zsmul]
  rw [heq, CompletionHaarModule.closedBall_measure]
  have hO : {x : v.adicCompletion F | ‖x‖ ≤ 1} = (v.adicCompletionIntegers F : Set _) := by
    ext x
    exact Valued.toNormedField.norm_le_one_iff
  rw [hO]
  simp only [Measure.real, hμ, ENNReal.toReal_one, mul_one]

theorem fourier_ballTest (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : Continuous ψ)
    (hc : HasConductor F v ψ 0)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (n : ℤ) (y : v.adicCompletion F) :
    fourier F v ψ μ (ballTest F v n) y =
      (↑((q F v : ℝ) ^ (-n)) : ℂ) * ballTest F v (-n) y := by
  let χ : AddChar (v.adicCompletion F) Circle := ψ.mulShift (-y)
  have hχ : Continuous χ := hψ.comp (continuous_const.mul continuous_id)
  have ho := compactSubgroup_character_integral μ (finiteCompletionBall F v n)
    (isCompact_finiteCompletionBall F v n) χ hχ
  have ht : (∀ x ∈ finiteCompletionBall F v n, χ x = 1) ↔
      y ∈ finiteCompletionBall F v (-n) := by
    have hs : (∀ x ∈ finiteCompletionBall F v n, χ x = 1) ↔
        ∀ x ∈ finiteCompletionBall F v 0,
          ψ (x * (finiteCompletionUniformizer F v ^ n * (-y))) = 1 := by
      constructor
      · intro h x hx
        have hxO : x ∈ v.adicCompletionIntegers F := by
          rw [finiteCompletionBall_zero] at hx
          exact hx
        have hmem := finiteCompletionUniformizer_mul_mem_ball F v n ⟨x, hxO⟩
        simpa [χ, AddChar.mulShift_apply, mul_assoc, mul_comm, mul_left_comm] using h _ hmem
      · intro h u hu
        obtain ⟨x, hx, rfl⟩ := (Set.ext_iff.mp
          (finiteCompletionBall_eq_uniformizer_image F v _
            (finiteCompletionUniformizer_valuation F v) n) u).mp hu
        have hxB : x ∈ finiteCompletionBall F v 0 := by
          rw [finiteCompletionBall_zero]
          exact hx
        simpa [χ, AddChar.mulShift_apply, mul_assoc, mul_comm, mul_left_comm] using h x hxB
    rw [hs, hc]
    change Valued.v (finiteCompletionUniformizer F v ^ n * (-y)) ≤ WithZero.exp (-0) ↔ _
    rw [map_mul, map_zpow₀, finiteCompletionUniformizer_valuation,
      ← WithZero.exp_zsmul, Valuation.map_neg]
    simp only [zsmul_eq_mul, mul_neg, mul_one, neg_zero, WithZero.exp_zero]
    rw [← le_inv_mul_iff₀ WithZero.exp_pos, ← WithZero.exp_neg]
    simp [mem_finiteCompletionBall]
  have hint : fourier F v ψ μ (ballTest F v n) y =
      ∫ x in (finiteCompletionBall F v n : Set _), (χ x : ℂ) ∂μ := by
    unfold fourier ballTest
    rw [← integral_indicator (isCompact_finiteCompletionBall F v n).measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ finiteCompletionBall F v n
    · simp [Set.indicator_of_mem hx, χ, mul_comm, neg_mul, mul_neg]
    · simp [Set.indicator_of_notMem hx]
  rw [hint, ho.2, ← Measure.real, finiteCompletionBall_mass F v μ hμ n]
  by_cases hy : y ∈ finiteCompletionBall F v (-n)
  · rw [if_pos (ht.mpr hy)]
    simp only [ballTest, Set.indicator_of_mem hy, mul_one]
  · rw [if_neg (mt ht.mp hy)]
    simp only [ballTest, Set.indicator_of_notMem hy, mul_zero]

theorem fourier_ballTestIntegrand_integrable (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : Continuous ψ)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (n : ℤ) (y : v.adicCompletion F) :
    Integrable (fun x => ballTest F v n x * (ψ (-x * y) : ℂ)) μ := by
  have hcl : IsClopen (finiteCompletionBall F v n : Set (v.adicCompletion F)) :=
    ⟨(isCompact_finiteCompletionBall F v n).isClosed, isOpen_finiteCompletionBall F v n⟩
  have hcont : Continuous (ballTest F v n) := (LocallyConstant.charFn ℂ hcl).isLocallyConstant.continuous
  have hsupp : HasCompactSupport (ballTest F v n) := by
    apply HasCompactSupport.intro (isCompact_finiteCompletionBall F v n)
    intro x hx
    exact Set.indicator_of_notMem hx _
  have hphase : Continuous (fun x : v.adicCompletion F => (ψ (-x * y) : ℂ)) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.neg.mul continuous_const))
  exact (hcont.mul hphase).integrable_of_hasCompactSupport hsupp.mul_right

theorem annularTest_eq_sub (v : HeightOneSpectrum (𝓞 F)) :
    annularTest F v = ballTest F v 0 - ballTest F v 1 := by
  funext x
  have hsub := (finiteCompletionBall_le_iff F v 0 1).mpr (by omega)
  by_cases h1 : x ∈ finiteCompletionBall F v 1
  · have h0 := hsub h1
    simp [annularTest, unitShell, ballTest, Set.indicator, h0, h1]
  · by_cases h0 : x ∈ finiteCompletionBall F v 0
    · simp [annularTest, unitShell, ballTest, Set.indicator, h0, h1]
    · simp [annularTest, unitShell, ballTest, Set.indicator, h0, h1]

theorem fourier_annularTest (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : Continuous ψ)
    (hc : HasConductor F v ψ 0)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (y : v.adicCompletion F) :
    fourier F v ψ μ (annularTest F v) y =
      ballTest F v 0 y - (↑((q F v : ℝ)⁻¹) : ℂ) * ballTest F v (-1) y := by
  rw [annularTest_eq_sub]
  have heq : fourier F v ψ μ (ballTest F v 0 - ballTest F v 1) y =
      fourier F v ψ μ (ballTest F v 0) y - fourier F v ψ μ (ballTest F v 1) y := by
    unfold fourier
    simp only [Pi.sub_apply, sub_mul]
    exact integral_sub (fourier_ballTestIntegrand_integrable F v ψ hψ μ 0 y)
      (fourier_ballTestIntegrand_integrable F v ψ hψ μ 1 y)
  rw [heq, fourier_ballTest F v ψ hψ hc μ hμ, fourier_ballTest F v ψ hψ hc μ hμ]
  simp

theorem unitShell_mass (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) :
    μ (unitShell F v) = ENNReal.ofReal (1 - (q F v : ℝ)⁻¹) := by
  have hs : μ (unitShell F v) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_finiteCompletionBall F v 0).measure_lt_top.ne
      (measure_mono Set.diff_subset)
  apply ENNReal.toReal_eq_toReal_iff' hs ENNReal.ofReal_ne_top |>.mp
  have hq : 1 < (q F v : ℝ) := by exact_mod_cast finiteCompletion_residueCard_gt_one F v
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le))]
  change μ.real ((finiteCompletionBall F v 0 : Set _) \ (finiteCompletionBall F v 1 : Set _)) = _
  rw [measureReal_sdiff ((finiteCompletionBall_le_iff F v 0 1).mpr (by omega))
    (isCompact_finiteCompletionBall F v 1).measurableSet
    (isCompact_finiteCompletionBall F v 0).measure_lt_top.ne,
    finiteCompletionBall_mass F v μ hμ, finiteCompletionBall_mass F v μ hμ]
  simp

theorem multiplicativeHaar_unitShell (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) :
    multiplicativeHaar F v μ (unitShell F v) = 1 := by
  have hS : MeasurableSet (unitShell F v) :=
    (isCompact_finiteCompletionBall F v 0).measurableSet.diff
      (isCompact_finiteCompletionBall F v 1).measurableSet
  have hzero : unitShell F v ⊆ ({0}ᶜ : Set (v.adicCompletion F)) := by
    intro x hx
    have hv := (mem_unitShell_iff F v x).mp hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx0
    simpa [hx0] using hv
  unfold multiplicativeHaar
  rw [withDensity_apply _ hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hzero]
  calc
    (∫⁻ x in unitShell F v, ENNReal.ofReal (((1 - (q F v : ℝ)⁻¹) * ‖x‖)⁻¹) ∂μ) =
        ∫⁻ _ in unitShell F v, ENNReal.ofReal ((1 - (q F v : ℝ)⁻¹)⁻¹) ∂μ := by
      apply setLIntegral_congr_fun hS
      intro x hx
      dsimp only
      rw [Valued.toNormedField.norm_eq_one_iff.mpr ((mem_unitShell_iff F v x).mp hx), mul_one]
    _ = 1 := by
      have hq : 1 < (q F v : ℝ) := by exact_mod_cast finiteCompletion_residueCard_gt_one F v
      have hh : 0 < 1 - (q F v : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)
      rw [lintegral_const, Measure.restrict_apply_univ, unitShell_mass F v μ hμ,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
      rw [inv_mul_cancel₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)).ne']
      simp

theorem mellin_annularTest (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) (s : ℝ) :
    Integrable (fun x => annularTest F v x * (↑(‖x‖ ^ s) : ℂ))
      (multiplicativeHaar F v μ) ∧ mellin F v μ (annularTest F v) s = 1 := by
  have hS : MeasurableSet (unitShell F v) :=
    (isCompact_finiteCompletionBall F v 0).measurableSet.diff
      (isCompact_finiteCompletionBall F v 1).measurableSet
  have heq : (fun x => annularTest F v x * (↑(‖x‖ ^ s) : ℂ)) =
      (unitShell F v).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ unitShell F v
    · have hn := Valued.toNormedField.norm_eq_one_iff.mpr ((mem_unitShell_iff F v x).mp hx)
      simp only [annularTest, Set.indicator_of_mem hx, hn, Real.one_rpow, Complex.ofReal_one, mul_one]
    · simp only [annularTest, Set.indicator_of_notMem hx, zero_mul]
  have hfinite : IsFiniteMeasure ((multiplicativeHaar F v μ).restrict (unitShell F v)) := by
    constructor
    simp only [Measure.restrict_apply_univ, multiplicativeHaar_unitShell F v μ hμ]
    exact ENNReal.one_lt_top
  haveI := hfinite
  constructor
  · rw [heq]
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (C := (1 : ℂ))
      (by rw [multiplicativeHaar_unitShell F v μ hμ]; exact ENNReal.one_ne_top)
  · unfold mellin
    rw [heq, integral_indicator hS, setIntegral_const]
    simp only [Measure.real, multiplicativeHaar_unitShell F v μ hμ, ENNReal.toReal_one, Complex.real_smul,
      Complex.ofReal_one, mul_one]

theorem multiplicativeHaar_map_mul (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (a : v.adicCompletion F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) (multiplicativeHaar F v μ) = multiplicativeHaar F v μ := by
  let D := fun x : v.adicCompletion F =>
    ({0}ᶜ : Set (v.adicCompletion F)).indicator
      (fun x => ENNReal.ofReal (((1 - (q F v : ℝ)⁻¹) * ‖x‖)⁻¹)) x
  have hD : Measurable D := by
    apply Measurable.indicator _ (MeasurableSet.singleton 0).compl
    exact ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_norm).inv)
  have hν : multiplicativeHaar F v μ = μ.withDensity D := by
    exact (withDensity_indicator (MeasurableSet.singleton 0).compl _).symm
  have hq : 1 < (q F v : ℝ) := by exact_mod_cast finiteCompletion_residueCard_gt_one F v
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hh : 0 < 1 - (q F v : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)
  have hmul (x : v.adicCompletion F) : D (a * x) = (ENNReal.ofReal ‖a‖)⁻¹ * D x := by
    by_cases hx : x = 0
    · simp [D, hx]
    · have hax : a * x ≠ 0 := mul_ne_zero ha hx
      simp only [D, Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set _) by simpa),
        Set.indicator_of_mem (show a * x ∈ ({0}ᶜ : Set _) by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hax)]
      rw [norm_mul]
      have he : ((1 - (q F v : ℝ)⁻¹) * (‖a‖ * ‖x‖))⁻¹ =
          ‖a‖⁻¹ * (((1 - (q F v : ℝ)⁻¹) * ‖x‖)⁻¹) := by
        rw [show (1 - (q F v : ℝ)⁻¹) * (‖a‖ * ‖x‖) =
          ‖a‖ * ((1 - (q F v : ℝ)⁻¹) * ‖x‖) by ring, mul_inv]
      rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hp.le), ENNReal.ofReal_inv_of_pos hp]
  rw [hν]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, withDensity_apply _ (hs.preimage (by fun_prop)),
    withDensity_apply _ hs]
  have hm := setLIntegral_map (μ := μ) (g := fun x => a * x) (s := s) hs hD (by fun_prop)
  have hscale : Measure.map (fun x => a * x) μ = (ENNReal.ofReal ‖a‖)⁻¹ • μ := by
    simpa only [Units.val_mk0] using CompletionHaarModule.map_mul F v μ (Units.mk0 a ha)
  rw [hscale, Measure.restrict_smul, lintegral_smul_measure] at hm
  simp only [ENNReal.smul_def, smul_eq_mul, Units.val_mk0] at hm
  simp_rw [hmul] at hm
  rw [lintegral_const_mul _ hD] at hm
  exact (ENNReal.mul_right_inj (by simp [ha]) (by simp [ha])).mp hm.symm

theorem multiplicativeHaar_eq_smul (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (v.adicCompletion F)) :
    multiplicativeHaar F v μ = ENNReal.ofReal ((1 - (q F v : ℝ)⁻¹)⁻¹) •
      KPRankOneMellin.multiplicativeMeasure F v μ := by
  unfold multiplicativeHaar KPRankOneMellin.multiplicativeMeasure
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  dsimp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_inv, ENNReal.ofReal_mul]
  have hq : 1 < (q F v : ℝ) := by exact_mod_cast finiteCompletion_residueCard_gt_one F v
  exact inv_nonneg.mpr (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le))

theorem finiteCompletionBall_eq_closedBall (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    (finiteCompletionBall F v n : Set _) = Metric.closedBall (0 : v.adicCompletion F) ((q F v : ℝ) ^ (-n)) := by
  have hq : (v.asIdeal.absNorm : ℝ≥0) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
  have hpn : ‖finiteCompletionUniformizer F v ^ n‖ = (q F v : ℝ) ^ (-n) := by
    rw [norm_zpow, FinitePlace.norm_def, finiteCompletionUniformizer_valuation,
      WithZeroMulInt.toNNReal_neg_apply hq WithZero.exp_ne_zero, WithZero.log_exp,
      NNReal.coe_zpow, ← zpow_mul]
    simp
  ext x
  change Valued.v x ≤ WithZero.exp (-n) ↔ dist x 0 ≤ _
  rw [dist_zero_right, ← hpn, Valued.toNormedField.norm_le_iff]
  simp [map_zpow₀, finiteCompletionUniformizer_valuation, ← WithZero.exp_zsmul]

theorem realMellinIntegrand_eq_complex (v : HeightOneSpectrum (𝓞 F)) (f : v.adicCompletion F → ℂ) (s : ℝ) :
    (fun x => f x * (↑(‖x‖ ^ s) : ℂ)) = (fun x => f x * (‖x‖ : ℂ) ^ (s : ℂ)) := by
  funext x
  congr 1
  exact Complex.ofReal_cpow (norm_nonneg x) s

theorem mellin_ballTest (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (n : ℤ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x => ballTest F v n x * (↑(‖x‖ ^ s) : ℂ)) (multiplicativeHaar F v μ) ∧
      mellin F v μ (ballTest F v n) s =
        (↑((q F v : ℝ) ^ (-s)) : ℂ) ^ n / (1 - (↑((q F v : ℝ) ^ (-s)) : ℂ)) := by
  have hq : 1 < (q F v : ℝ) := by exact_mod_cast finiteCompletion_residueCard_gt_one F v
  have ha := KPRankOneMellin.FiniteShellExpansion.q_ball_mellin_integrable F v μ n (s : ℂ) (by simpa)
  have he := KPRankOneMellin.FiniteShellExpansion.q_ball_mellin_eq_shell_series F v μ n (s : ℂ) (by simpa)
  have hg := KPRankOneMellin.FiniteShellExpansion.mellin_shell_series_eq_geometric_tail
    (q F v : ℝ) 1 hq n (s : ℂ) (by simpa)
  have hmass : (μ (v.adicCompletionIntegers F : Set _)).toReal = 1 := by rw [hμ]; simp
  have ha' : Integrable (fun x => ballTest F v n x * (‖x‖ : ℂ) ^ ((s : ℂ) - 1)) μ := by
    simpa only [ballTest, finiteCompletionBall_eq_closedBall] using ha
  letI : NullSingletonClass μ := KPRankOneMellin.completion_addHaar_nullSingletonClass F v μ
  have hi := (KPRankOneMellin.mellin_integrable_iff_additive F v μ (ballTest F v n) (s : ℂ)).mpr ha'
  constructor
  · rw [realMellinIntegrand_eq_complex, multiplicativeHaar_eq_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  · unfold mellin
    rw [realMellinIntegrand_eq_complex, multiplicativeHaar_eq_smul, integral_smul_measure]
    change ((ENNReal.ofReal ((1 - (q F v : ℝ)⁻¹)⁻¹)).toReal) •
      KPRankOneMellin.mellin F v μ (ballTest F v n) (s : ℂ) = _
    rw [KPRankOneMellin.mellin_eq_additive_integral]
    have he' : (∫ x, ballTest F v n x * (‖x‖ : ℂ) ^ ((s : ℂ) - 1) ∂μ) =
        (↑(1 - (q F v : ℝ)⁻¹) : ℂ) *
          Complex.exp (-(s : ℂ) * (Real.log (q F v : ℝ) : ℂ)) ^ n /
            (1 - Complex.exp (-(s : ℂ) * (Real.log (q F v : ℝ) : ℂ))) := by
      simpa only [ballTest, finiteCompletionBall_eq_closedBall, hmass, one_mul] using he.trans (by simpa only [hmass, one_mul] using hg)
    rw [he']
    have hQ : Complex.exp (-(s : ℂ) * (Real.log (q F v : ℝ) : ℂ)) =
        (↑((q F v : ℝ) ^ (-s)) : ℂ) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
      congr 1
      ring
    rw [hQ, ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le))),
      Complex.real_smul]
    have hh : (1 - (q F v : ℝ)⁻¹) ≠ 0 := (sub_pos.mpr (inv_lt_one_of_one_lt₀ hq)).ne'
    have hhC : (1 - (q F v : ℂ)⁻¹) ≠ 0 := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
        Complex.ofReal_natCast, ne_eq, Complex.ofReal_eq_zero] using
          (show (↑(1 - (q F v : ℝ)⁻¹) : ℂ) ≠ 0 by exact_mod_cast hh)
    push_cast
    field_simp [hhC]

theorem mellin_fourier_annularTest (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : Continuous ψ)
    (hc : HasConductor F v ψ 0)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    Integrable (fun x => fourier F v ψ μ (annularTest F v) x * (↑(‖x‖ ^ s) : ℂ))
      (multiplicativeHaar F v μ) ∧
    mellin F v μ (fourier F v ψ μ (annularTest F v)) s =
      (↑(tateRatio F v s) : ℂ) * mellin F v μ (annularTest F v) (1 - s) ∧
    0 < tateRatio F v s ∧
    mellin F v μ (fourier F v ψ μ (annularTest F v)) s ≠ 0 := by
  have h0 := mellin_ballTest F v μ hμ 0 s hs
  have h1 := mellin_ballTest F v μ hμ (-1) s hs
  have heq : (fun x => fourier F v ψ μ (annularTest F v) x * (↑(‖x‖ ^ s) : ℂ)) =
      (fun x => ballTest F v 0 x * (↑(‖x‖ ^ s) : ℂ)) -
        (fun x => (↑((q F v : ℝ)⁻¹) : ℂ) * (ballTest F v (-1) x * (↑(‖x‖ ^ s) : ℂ))) := by
    funext x
    rw [fourier_annularTest F v ψ hψ hc μ hμ]
    simp only [Pi.sub_apply]
    ring
  have hi : Integrable (fun x => fourier F v ψ μ (annularTest F v) x * (↑(‖x‖ ^ s) : ℂ))
      (multiplicativeHaar F v μ) := by
    rw [heq]
    exact h0.1.sub (h1.1.const_mul _)
  have hm : mellin F v μ (fourier F v ψ μ (annularTest F v)) s = (↑(tateRatio F v s) : ℂ) := by
    unfold mellin
    rw [heq]
    change (∫ x, ballTest F v 0 x * (↑(‖x‖ ^ s) : ℂ) -
      (↑((q F v : ℝ)⁻¹) : ℂ) * (ballTest F v (-1) x * (↑(‖x‖ ^ s) : ℂ)) ∂multiplicativeHaar F v μ) = _
    rw [integral_sub h0.1 (h1.1.const_mul _), integral_const_mul]
    change mellin F v μ (ballTest F v 0) s -
      (↑((q F v : ℝ)⁻¹) : ℂ) * mellin F v μ (ballTest F v (-1)) s = _
    rw [h0.2, h1.2]
    simp only [zpow_zero, zpow_neg_one]
    have hq : 0 < (q F v : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans (finiteCompletion_residueCard_gt_one F v)
    have hpow : (q F v : ℝ)⁻¹ * ((q F v : ℝ) ^ (-s))⁻¹ = (q F v : ℝ) ^ (s - 1) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_neg hq.le, neg_neg, ← Real.rpow_add hq]
      congr 1
      ring
    have hQ : ((q F v : ℝ) ^ (-s)) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
    unfold tateRatio
    push_cast
    rw [← hpow]
    push_cast
    ring
  refine ⟨hi, ?_, tateRatio_pos F v s hs hs1, ?_⟩
  · rw [hm, (mellin_annularTest F v μ hμ (1 - s)).2, mul_one]
  · rw [hm]
    exact_mod_cast (tateRatio_pos F v s hs hs1).ne'

theorem exists_conductorZero_rescaling (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) Circle) (hψ : Continuous ψ)
    (hn : ∃ x, ψ x ≠ 1) :
    ∃ a : v.adicCompletion F, a ≠ 0 ∧ HasConductor F v (rescaledCharacter F v ψ a) 0 := by
  obtain ⟨r, hr, htr⟩ := KPFiniteLocal.character_trivial_near_zero ψ hψ
  obtain ⟨x, hx⟩ := hn
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  let π := finiteCompletionUniformizer F v
  have hπ0 : π ≠ 0 := finiteCompletionUniformizer_ne_zero F v
  have hπn : ‖π‖ = (q F v : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, finiteCompletionUniformizer_valuation,
      WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) WithZero.exp_ne_zero,
      WithZero.log_exp, NNReal.coe_zpow]
    simp [q]
  have hq : 1 < (q F v : ℝ) := by exact_mod_cast finiteCompletion_residueCard_gt_one F v
  let P : ℕ → Prop := fun n => ∀ u ∈ finiteCompletionBall F v 0, ψ (x * π ^ n * u) = 1
  have hP : ∃ n, P n := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr (norm_pos_iff.mpr hx0))
      (inv_lt_one_of_one_lt₀ hq)
    refine ⟨n, fun u hu => htr _ ?_⟩
    have hu' : ‖u‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hu
    rw [norm_mul, norm_mul, norm_pow, hπn]
    have hnn : ‖x‖ * ((q F v : ℝ)⁻¹ ^ n) < r := by simpa [mul_comm] using (lt_div_iff₀ (norm_pos_iff.mpr hx0)).mp hn
    exact (mul_le_of_le_one_right (by positivity) hu').trans_lt hnn
  let n := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  have hn0 : n ≠ 0 := by
    intro he
    have ht := hnP 1 (by simp [mem_finiteCompletionBall])
    simp [he] at ht
    exact hx ht
  have hprev : ¬ P (n - 1) := Nat.find_min hP (by omega)
  obtain ⟨u, hu⟩ := not_forall.mp hprev
  obtain ⟨huO, hu⟩ := not_imp.mp hu
  let a := x * π ^ n
  have ha : a ≠ 0 := mul_ne_zero hx0 (pow_ne_zero _ hπ0)
  have hnt : ψ (a * (u / π)) ≠ 1 := by
    have he : a * (u / π) = x * π ^ (n - 1) * u := by
      dsimp [a]
      rw [show n = n - 1 + 1 by omega, pow_succ]
      field_simp
      simp [mul_comm]
    rwa [he]
  refine ⟨a, ha, ?_⟩
  intro y
  constructor
  · intro hy
    by_contra hyO
    have hy0 : y ≠ 0 := by intro he; simp [he, mem_finiteCompletionBall] at hyO
    have hval : 1 ≤ Valued.v (π * y) := by
      rw [map_mul, finiteCompletionUniformizer_valuation]
      change 1 ≤ WithZero.exp (-1) * Valued.v y
      have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr hy0
      rw [← WithZero.exp_log hv0]
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      have : ¬ Valued.v y ≤ WithZero.exp (-(0 : ℤ)) := hyO
      rw [← WithZero.exp_log hv0, WithZero.exp_le_exp] at this
      omega
    have hmem : u / (π * y) ∈ finiteCompletionBall F v 0 := by
      change Valued.v (u / (π * y)) ≤ 1
      rw [map_div₀]
      exact div_le_one₀ (lt_of_lt_of_le (by simp) hval) |>.mpr
        (le_trans huO hval)
    have ht := hy (u / (π * y)) hmem
    apply hnt
    simpa only [rescaledCharacter, AddChar.mulShift_apply,
      show a * (u / (π * y) * y) = a * (u / π) by field_simp] using ht
  · intro hy u hu
    have hm : u * y ∈ finiteCompletionBall F v 0 := by
      change Valued.v (u * y) ≤ 1
      rw [map_mul]
      exact mul_le_one₀ hu (by simp) hy
    simpa [rescaledCharacter, AddChar.mulShift_apply, a, mul_assoc] using hnP (u * y) hm

theorem mellin_dilate_test (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (f : v.adicCompletion F → ℂ) (a : v.adicCompletion F) (ha : a ≠ 0) (s : ℝ) :
    mellin F v μ (fun x => f (x / a)) s =
      (↑(‖a‖ ^ s) : ℂ) * mellin F v μ f s := by
  let e : v.adicCompletion F ≃ᵐ v.adicCompletion F := MeasurableEquiv.smul₀ a ha
  have he : (e : v.adicCompletion F → v.adicCompletion F) = fun x => a * x := rfl
  have hm : Measure.map e (multiplicativeHaar F v μ) = multiplicativeHaar F v μ :=
    multiplicativeHaar_map_mul F v μ a ha
  have hi := integral_map_equiv (μ := multiplicativeHaar F v μ) e
    (fun x => f (x / a) * (↑(‖x‖ ^ s) : ℂ))
  rw [hm] at hi
  unfold mellin
  rw [hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [he, norm_mul, Real.mul_rpow (norm_nonneg a) (norm_nonneg x), Complex.ofReal_mul]
  rw [mul_div_cancel_left₀ _ ha]
  ring

theorem canonicalTrace_adapter (v : HeightOneSpectrum (𝓞 F)) :
    HasConductor F v (localFiniteCharacter F v) (-(localDifferentExponent F v : ℤ)) ∧
    conductorHaar F v
      (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v))
      (-(localDifferentExponent F v : ℤ)) = localNormalizedHaar F v ∧
    (∀ (f : v.adicCompletion F → ℂ) (y : v.adicCompletion F),
      fourier F v (localFiniteCharacter F v) (localNormalizedHaar F v) f y =
        localFourierIntegral F v f y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have h := localFiniteAnnihilator_finiteCompletionBall F v 0
    have hy := SetLike.ext_iff.mp h y
    simpa only [mem_localFiniteAnnihilator, neg_zero, zero_sub] using hy
  · unfold conductorHaar localNormalizedHaar localHalfDifferentFactor q
    simp only [Int.cast_neg, Int.cast_natCast]
  · intro f y
    exact (localFourierIntegral_apply F v f y).symm

end DedekindZetaZeroFree.TateFiniteShell

end
