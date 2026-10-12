module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalMellin.TestFunctionPole
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicBetaAndMellinEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open scoped NumberField
set_option autoImplicit false
open scoped Classical
open scoped Topology
set_option linter.style.haveILetI false
namespace TwistedMellinProof
section Generic
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
local instance : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [@BorelSpace.measurable_eq K _ _ _,
    Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
private lemma exponent_nonneg_iff (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (y : Kˣ) :
    0 ≤ KPCubicExpansion.valuationExponent K y ↔ (y : K) ∈ (valuation K).integer := by
  let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hne : iso (valuation K (y : K)) ≠ 0 := by
    exact (map_ne_zero_iff iso iso.injective).mpr ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  rw [Valuation.mem_integer_iff]
  rw [← map_le_map_iff iso, map_one]
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp only [KPCubicExpansion.valuationExponent]
  dsimp [iso] at *
  omega

private lemma shell_measure (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx ((valuation K).integer : Set K) = ENNReal.ofReal m) (j : ℤ) :
    MeasurableSet {y : Kˣ | KPCubicExpansion.valuationExponent K y = j} ∧
    KPCubicHaar.multiplicativeHaar K dx {y : Kˣ |
      KPCubicExpansion.valuationExponent K y = j} =
      ENNReal.ofReal (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)) := by
  obtain ⟨p, hp⟩ := (valuation_surjective (uniformizer K))
  have hpne : p ≠ 0 := by
    intro h
    simp [h] at hp
    exact uniformizer_ne_zero hp.symm
  let π : Kˣ := Units.mk0 p hpne
  have hπ : valuation K (π : K) = uniformizer K := hp
  let ν := KPCubicHaar.multiplicativeHaar K dx
  have hhaar := kp_rankone_cubic_haar_power_measure K dx m hm hvol
  letI : ν.IsHaarMeasure := hhaar.1
  let U : Set Kˣ := {y | (y : K) ∈ (valuation K).integer ∧ ((y⁻¹ : Kˣ) : K) ∈ (valuation K).integer}
  have hU : MeasurableSet U := by
    exact ((valuation K).isOpen_integer.preimage Units.continuous_val).measurableSet.inter
      ((valuation K).isOpen_integer.preimage (Units.continuous_val.comp continuous_inv)).measurableSet
  have hUeq (y : Kˣ) : y ∈ U ↔ KPCubicExpansion.valuationExponent K y = 0 := by
    change ((y : K) ∈ (valuation K).integer ∧ ((y⁻¹ : Kˣ) : K) ∈ (valuation K).integer) ↔ _
    have hinv : KPCubicExpansion.valuationExponent K y⁻¹ =
        -KPCubicExpansion.valuationExponent K y := by
      have h := KPCubicExpansion.valuationExponent_mul y y⁻¹
      simpa [KPCubicExpansion.valuationExponent] using h
    rw [← exponent_nonneg_iff K y, ← exponent_nonneg_iff K y⁻¹, hinv]
    omega
  have hexp (y : Kˣ) : KPCubicExpansion.valuationExponent K (π^(-j) * y) =
      -j + KPCubicExpansion.valuationExponent K y := by
    rw [KPCubicExpansion.valuationExponent_mul, KPCubicExpansion.valuationExponent_zpow,
      KPCubicExpansion.valuationExponent_uniformizer π hπ, mul_one]
  have hset : {y | KPCubicExpansion.valuationExponent K y = j} =
      (fun y => π^(-j) * y) ⁻¹' U := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hUeq, hexp]
    omega
  constructor
  · rw [hset]
    exact hU.preimage (continuous_const.mul continuous_id).measurable
  · change ν _ = _
    rw [hset, measure_preimage_mul]
    exact hhaar.2

private lemma cubic_norm (χ : Kˣ →ₜ* ℂˣ) (hχ : ∀ x, χ x ^ 3 = 1) (x : Kˣ) :
    ‖(χ x : ℂ)‖ = 1 := by
  have hp : ‖(χ x : ℂ)‖ ^ (3 : ℕ) = 1 := by
    rw [← norm_pow]
    have he := congrArg (fun z : ℂˣ => (z : ℂ)) (hχ x)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at he
    rw [he, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp hp

private lemma shell_character_integral
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx ((valuation K).integer : Set K) = ENNReal.ofReal m)
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (χ : Kˣ →ₜ* ℂˣ) (j : ℤ) :
    (∫ y : Kˣ in {y | KPCubicExpansion.valuationExponent K y = j}, (χ y : ℂ)
      ∂KPCubicHaar.multiplicativeHaar K dx) =
      if ∀ u : ((valuation K).integer)ˣ,
          χ (KPRankOneCubicProjection.unitInclusion K u) = 1 then
        ((m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹) : ℝ) : ℂ) * (χ π : ℂ)^j
      else 0 := by
  let μ := KPCubicHaar.multiplicativeHaar K dx
  let S : Set Kˣ := {y | KPCubicExpansion.valuationExponent K y = j}
  have hS := (shell_measure K dx m hm hvol j).1
  letI : μ.IsHaarMeasure := (kp_rankone_cubic_haar_power_measure K dx m hm hvol).1
  by_cases hu : ∀ u : ((valuation K).integer)ˣ,
      χ (KPRankOneCubicProjection.unitInclusion K u) = 1
  · rw [if_pos hu]
    have he : Set.EqOn (fun y : Kˣ => (χ y : ℂ)) (fun _ => (χ π : ℂ)^j) S := by
      intro y hy
      change KPCubicExpansion.valuationExponent K y = j at hy
      change (χ y : ℂ) = (χ π : ℂ)^j
      obtain ⟨k, u, hyu⟩ := RegulatedResidue.uniformizer_unit_decomposition K π hπ y
      have hj : k = j := by
        rw [hyu, KPCubicExpansion.valuationExponent_mul,
          KPCubicExpansion.valuationExponent_zpow,
          KPCubicExpansion.valuationExponent_uniformizer π hπ,
          KPCubicExpansion.valuationExponent_unit, mul_one, add_zero] at hy
        exact hy
      rw [hyu, map_mul, map_zpow]
      change (↑((χ π)^k * χ (KPRankOneCubicProjection.unitInclusion K u)) : ℂ) = _
      rw [hu u, mul_one, hj, Units.val_zpow_eq_zpow_val]
    rw [setIntegral_congr_fun hS he, integral_const]
    change (μ.restrict S).real Set.univ • (χ π : ℂ)^j = _
    rw [Measure.real_def, Measure.restrict_apply_univ, (shell_measure K dx m hm hvol j).2,
      ENNReal.toReal_ofReal]
    · simp [Complex.real_smul]
    · have hq : (1 : ℝ) ≤ KPCubicUnitIndices.residueCard K := by
        exact_mod_cast le_trans (by decide : 1 ≤ 2) (KPCubicUnitIndices.two_le_residueCard K)
      exact mul_nonneg hm.le (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq))
  · rw [if_neg hu]
    push_neg at hu
    obtain ⟨u, hu⟩ := hu
    let z := KPRankOneCubicProjection.unitInclusion K u
    have hz : KPCubicExpansion.valuationExponent K z = 0 :=
      KPCubicExpansion.valuationExponent_unit u
    let f : Kˣ → ℂ := S.indicator (fun y => (χ y : ℂ))
    have hmem (y : Kˣ) : z*y ∈ S ↔ y ∈ S := by
      simp only [S, Set.mem_ofPred_eq, KPCubicExpansion.valuationExponent_mul, hz, zero_add]
    have he (y : Kˣ) : f (z*y) = (χ z : ℂ) * f y := by
      by_cases hy : y ∈ S
      · simp [f, hy, (hmem y).mpr hy, map_mul]
      · simp [f, hy, (hmem y).not.mpr hy]
    have hi := integral_mul_left_eq_self f z (μ := μ)
    simp_rw [he] at hi
    rw [integral_const_mul] at hi
    have hn : (χ z : ℂ) ≠ 1 := fun h => hu (Units.ext h)
    have hf : ∫ y, f y ∂μ = 0 := by
      apply (mul_eq_zero.mp (show ((χ z : ℂ)-1) * (∫ y, f y ∂μ) = 0 by
        rw [sub_mul, hi, one_mul, sub_self])).resolve_left (sub_ne_zero.mpr hn)
    rw [integral_indicator hS] at hf
    exact hf

private lemma twisted_shell_bounds
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx ((valuation K).integer : Set K) = ENNReal.ofReal m)
    (φ : K → ℂ) (hφlc : IsLocallyConstant φ) (hφcs : HasCompactSupport φ)
    (χ : Kˣ →ₜ* ℂˣ) (hχ : ∀ x, χ x ^ 3 = 1)
    (r : ℂ) (hrne : r ≠ 0) (hrnorm : ‖r‖ < 1) (nmin : ℤ) :
    let f := fun y : Kˣ => φ (y : K) * (χ y : ℂ) * r ^ KPCubicExpansion.valuationExponent K y
    let ν := KPCubicHaar.multiplicativeHaar K dx
    (∀ k : ℕ, MeasurableSet {y : Kˣ | KPCubicExpansion.valuationExponent K y = nmin + (k : ℤ)}) ∧
    (∀ k : ℕ, IntegrableOn f {y : Kˣ | KPCubicExpansion.valuationExponent K y = nmin + (k : ℤ)} ν) ∧
    Summable (fun k : ℕ => ∫ y : Kˣ in {y | KPCubicExpansion.valuationExponent K y = nmin + (k : ℤ)}, ‖f y‖ ∂ν) := by
  classical
  let ν := KPCubicHaar.multiplicativeHaar K dx
  let f := fun y : Kˣ => φ (y : K) * (χ y : ℂ) * r ^ KPCubicExpansion.valuationExponent K y
  let S := fun j : ℤ => {y : Kˣ | KPCubicExpansion.valuationExponent K y = j}
  have hS (j : ℤ) : MeasurableSet (S j) := (shell_measure K dx m hm hvol j).1
  have hmass (j : ℤ) : ν (S j) =
      ENNReal.ofReal (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)) :=
    (shell_measure K dx m hm hvol j).2
  have hfinite (j : ℤ) : ν (S j) ≠ ⊤ := by rw [hmass]; exact ENNReal.ofReal_ne_top
  have hcont : Continuous (fun y : Kˣ => φ (y : K) * (χ y : ℂ)) :=
    (hφlc.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp χ.continuous)
  obtain ⟨C, hC⟩ := hφcs.exists_bound_of_continuous hφlc.continuous
  have hbound (j : ℤ) : ∀ y ∈ S j, ‖f y‖ ≤ C * ‖r ^ j‖ := by
    intro y hy
    change KPCubicExpansion.valuationExponent K y = j at hy
    dsimp only [f]
    rw [hy, norm_mul, norm_mul, cubic_norm K χ hχ, mul_one]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  have hint (j : ℤ) : IntegrableOn f (S j) ν := by
    have hg : IntegrableOn (fun y : Kˣ => φ (y : K) * (χ y : ℂ) * r ^ j) (S j) ν := by
      apply Measure.integrableOn_of_bounded (M := C * ‖r ^ j‖)
        (hfinite j) (hcont.mul continuous_const).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun y => by
        change ‖φ (y : K) * (χ y : ℂ) * r ^ j‖ ≤ C * ‖r ^ j‖
        rw [norm_mul, norm_mul, cubic_norm K χ hχ, mul_one]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
    apply hg.congr_fun _ (hS j)
    intro y hy
    change KPCubicExpansion.valuationExponent K y = j at hy
    simp only [f, hy]
  have hreal (j : ℤ) : (ν.restrict (S j)).real Set.univ =
      (ENNReal.ofReal (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹))).toReal := by
    rw [Measure.real_def, Measure.restrict_apply_univ, hmass]
  let M := (ENNReal.ofReal (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹))).toReal
  have hibound (j : ℤ) : (∫ y in S j, ‖f y‖ ∂ν) ≤ C * ‖r ^ j‖ * M := by
    letI : IsFiniteMeasure (ν.restrict (S j)) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (hfinite j).lt_top⟩
    have hb : ∀ᵐ y ∂ν.restrict (S j), ‖‖f y‖‖ ≤ C * ‖r ^ j‖ := by
      filter_upwards [ae_restrict_mem (hS j)] with y hy
      simpa only [norm_norm] using hbound j y hy
    have hh := norm_integral_le_of_norm_le_const hb
    rw [hreal] at hh
    exact (le_abs_self _).trans hh
  refine ⟨fun k => hS _, fun k => hint _, ?_⟩
  have hs : Summable (fun k : ℕ => C * ‖r ^ (nmin + (k : ℤ))‖ * M) := by
    have hh := ((summable_geometric_of_lt_one (norm_nonneg r) hrnorm).mul_left
      (C * ‖r ^ nmin‖)).mul_right M
    simpa only [zpow_add₀ hrne, norm_mul, zpow_natCast, norm_pow, mul_assoc] using hh
  apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun y => norm_nonneg _))
    (fun k => hibound _) hs

private lemma twisted_series
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx ((valuation K).integer : Set K) = ENNReal.ofReal m)
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (φ : K → ℂ) (hφlc : IsLocallyConstant φ) (hφcs : HasCompactSupport φ)
    (χ : Kˣ →ₜ* ℂˣ) (hχ : ∀ x, χ x ^ 3 = 1)
    (nmin n₀ : ℤ) (hle : nmin ≤ n₀)
    (hlower : KPRankOneTestFunctionMellinPole.IsSupportCutoff K φ nmin)
    (htail : KPRankOneTestFunctionMellinPole.IsTailCutoff K φ n₀)
    (r : ℂ) (hr : r ≠ 0) (hrnorm : ‖r‖ < 1) :
    let c := fun j : ℤ => ∫ y : Kˣ in {y | KPCubicExpansion.valuationExponent K y = j},
      φ (y : K) * (χ y : ℂ) ∂KPCubicHaar.multiplicativeHaar K dx
    let D := ((m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹) : ℝ) : ℂ) * φ 0
    let unram := ∀ u : ((valuation K).integer)ˣ, χ (KPRankOneCubicProjection.unitInclusion K u) = 1
    Integrable (fun y : Kˣ => φ (y : K) * (χ y : ℂ) * r ^ KPCubicExpansion.valuationExponent K y)
      (KPCubicHaar.multiplicativeHaar K dx) ∧
    (∫ y : Kˣ, φ (y : K) * (χ y : ℂ) * r ^ KPCubicExpansion.valuationExponent K y
      ∂KPCubicHaar.multiplicativeHaar K dx) =
      (∑ j ∈ Finset.Ico nmin n₀, c j * r^j) +
      if unram then D * ((χ π : ℂ)*r)^n₀ / (1-(χ π : ℂ)*r) else 0 := by
  dsimp only
  let μ := KPCubicHaar.multiplicativeHaar K dx
  let c := fun j : ℤ => ∫ y : Kˣ in {y | KPCubicExpansion.valuationExponent K y = j},
    φ (y : K) * (χ y : ℂ) ∂μ
  let D := ((m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹) : ℝ) : ℂ) * φ 0
  let unram := ∀ u : ((valuation K).integer)ˣ, χ (KPRankOneCubicProjection.unitInclusion K u) = 1
  let b : ℂ := χ π
  have hb : b ≠ 0 := (χ π).ne_zero
  obtain ⟨hS, hint, hsum⟩ := twisted_shell_bounds K dx m hm hvol φ hφlc hφcs χ hχ r hr hrnorm nmin
  have hre := KPRankOneMellinShellReassembly.shell_reassembly μ
    (KPCubicExpansion.valuationExponent K) (fun y => φ (y : K)*(χ y : ℂ)) r nmin
    (fun y hy => by rw [hlower y hy, zero_mul]) hS hint hsum
  refine ⟨hre.1, ?_⟩
  have htailc (j : ℤ) (hj : n₀ ≤ j) : c j = (if unram then D else 0) * b^j := by
    have he : Set.EqOn (fun y : Kˣ => φ (y : K) * (χ y : ℂ))
        (fun y => φ 0 * (χ y : ℂ)) {y | KPCubicExpansion.valuationExponent K y = j} := by
      intro y hy
      change φ (y : K) * (χ y : ℂ) = φ 0 * (χ y : ℂ)
      rw [htail y (by change KPCubicExpansion.valuationExponent K y = j at hy; omega)]
    dsimp only [c]
    rw [setIntegral_congr_fun (shell_measure K dx m hm hvol j).1 he, integral_const_mul,
      shell_character_integral K dx m hm hvol π hπ χ j]
    change φ 0 * (if unram then _ else 0) = (if unram then D else 0) * b^j
    by_cases hu : unram
    · simp [hu, D, b]; ring
    · simp [hu]
  have hbr : b*r ≠ 0 := mul_ne_zero hb hr
  have hbrnorm : ‖b*r‖ < 1 := by rw [norm_mul, cubic_norm K χ hχ π, one_mul]; exact hrnorm
  have hgeom := KPRankOneMellinShellReassembly.finite_geometric_tail
    (fun j => c j * b^(-j)) (if unram then D else 0) (b*r) hbr hbrnorm nmin n₀ hle
    (fun j hj => by rw [htailc j hj, mul_assoc, ← zpow_add₀ hb]; simp)
  have hterm (j : ℤ) : c j * b^(-j) * (b*r)^j = c j * r^j := by
    rw [mul_zpow, ← mul_assoc, mul_assoc (c j), ← zpow_add₀ hb]
    simp
  simp_rw [hterm] at hgeom
  have heq := hre.2.unique hgeom
  change _ = (∑ j ∈ Finset.Ico nmin n₀, c j*r^j) +
    if unram then D*(b*r)^n₀/(1-b*r) else 0
  by_cases hu : unram
  · simpa [hu] using heq
  · simpa [hu] using heq

 def Regular {F : Type*} [Field F] (u : F) (r : RatFunc F) : Prop :=
  r.denom.eval u ≠ 0

private lemma regular_C {F : Type*} [Field F] (u c : F) : Regular u (RatFunc.C c) := by
  simp [Regular]
private lemma regular_X {F : Type*} [Field F] (u : F) : Regular u (RatFunc.X : RatFunc F) := by
  simp [Regular]
private lemma regular_add {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : Regular u r) (hs : Regular u s) : Regular u (r+s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd r s) h)
private lemma regular_mul {F : Type*} [Field F] {u : F} {r s : RatFunc F}
    (hr : Regular u r) (hs : Regular u s) : Regular u (r*s) := by
  exact fun h => (mul_ne_zero hr hs) (by
    simpa using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd r s) h)
private lemma regular_inv {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (hr : Regular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) : Regular u r⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  intro h
  have hn := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_inv_dvd hr0) h
  apply hv
  simp [RatFunc.eval, Polynomial.eval₂_at_apply, hn]
private lemma eval_inv {F : Type*} [Field F] {u : F} {r : RatFunc F}
    (hr : Regular u r) (hv : RatFunc.eval (RingHom.id F) u r ≠ 0) :
    RatFunc.eval (RingHom.id F) u r⁻¹ = (RatFunc.eval (RingHom.id F) u r)⁻¹ := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hv
  have hm := RatFunc.eval_mul (f := RingHom.id F) (a := u) hr (regular_inv hr hv)
  rw [mul_inv_cancel₀ hr0, RatFunc.eval_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

 def Evaluates {F : Type*} [Field F] (u : F) (r : RatFunc F) (v : F) : Prop :=
  Regular u r ∧ RatFunc.eval (RingHom.id F) u r = v
private lemma Evaluates.const {F : Type*} [Field F] (u v : F) : Evaluates u (RatFunc.C v) v :=
  ⟨regular_C u v, by simp⟩
private lemma Evaluates.var {F : Type*} [Field F] (u : F) : Evaluates u RatFunc.X u :=
  ⟨regular_X u, by simp⟩
private lemma Evaluates.add {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r+s) (a+b) := by
  refine ⟨regular_add hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_add (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma Evaluates.mul {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r*s) (a*b) := by
  refine ⟨regular_mul hr.1 hs.1, ?_⟩
  rw [RatFunc.eval_mul (RingHom.id F) u hr.1 hs.1, hr.2, hs.2]
private lemma Evaluates.neg {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) : Evaluates u (-r) (-a) := by
  simpa only [map_neg, map_one, neg_one_mul] using (Evaluates.const u (-1)).mul hr
private lemma Evaluates.sub {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r-s) (a-b) := by
  simpa only [sub_eq_add_neg] using hr.add hs.neg
private lemma Evaluates.inv {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (ha : a ≠ 0) : Evaluates u r⁻¹ a⁻¹ := by
  have hv : RatFunc.eval (RingHom.id F) u r ≠ 0 := hr.2 ▸ ha
  exact ⟨regular_inv hr.1 hv, by rw [eval_inv hr.1 hv, hr.2]⟩
private lemma Evaluates.div {F : Type*} [Field F] {u a b : F} {r s : RatFunc F}
    (hr : Evaluates u r a) (hs : Evaluates u s b) (hb : b ≠ 0) : Evaluates u (r/s) (a/b) := by
  simpa only [div_eq_mul_inv] using hr.mul (hs.inv hb)
private lemma Evaluates.pow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (n : ℕ) : Evaluates u (r^n) (a^n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using Evaluates.const u 1
  | succ n ih => simpa only [pow_succ] using ih.mul hr
private lemma Evaluates.zpow {F : Type*} [Field F] {u a : F} {r : RatFunc F}
    (hr : Evaluates u r a) (ha : a ≠ 0) (n : ℤ) : Evaluates u (r^n) (a^n) := by
  cases n with
  | ofNat n => simpa using hr.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hr.pow (n+1)).inv (pow_ne_zero _ ha)
private lemma Evaluates.sum {F I : Type*} [Field F] {u : F} (s : Finset I)
    {r : I → RatFunc F} {a : I → F} (h : ∀ i ∈ s, Evaluates u (r i) (a i)) :
    Evaluates u (∑ i ∈ s, r i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using Evaluates.const u 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma exp_weight (ρ : ℂ) (y : Kˣ) :
    Complex.exp (ρ * (Real.log (KPCubicHaar.abs K (y : K)) : ℂ)) =
      Complex.exp (-ρ * (Real.log (KPCubicUnitIndices.residueCard K : ℝ) : ℂ)) ^
        KPCubicExpansion.valuationExponent K y := by
  rw [KPRankOneUnramifiedBetaShells.abs_eq_q_neg_valuation K y, Real.log_zpow,
    Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_neg, ← Complex.exp_int_mul]
  congr 1
  ring

private lemma exp_ratio_norm (ρ : ℂ) (hρ : 0 < ρ.re) :
    ‖Complex.exp (-ρ * (Real.log (KPCubicUnitIndices.residueCard K : ℝ) : ℂ))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have hq : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K))
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hρ) (Real.log_pos hq)

private lemma character_eq_one (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (χ : Kˣ →ₜ* ℂˣ)
    (hu : ∀ u : ((valuation K).integer)ˣ, χ (KPRankOneCubicProjection.unitInclusion K u) = 1)
    (hb : (χ π : ℂ) = 1) : χ = 1 := by
  have hb' : χ π = 1 := Units.ext hb
  ext y
  obtain ⟨j,u,hy⟩ := RegulatedResidue.uniformizer_unit_decomposition K π hπ y
  rw [hy, map_mul, map_zpow]
  change (↑(χ π ^ j * χ (KPRankOneCubicProjection.unitInclusion K u)) : ℂ) = _
  simp [hb', hu u]

private lemma laurent_eval (a : ℤ →₀ ℂ) (Q : ℂ) (hQ : Q ≠ 0) :
    Evaluates Q (∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n)
      (∑ n ∈ a.support, a n * Q^n) :=
  Evaluates.sum a.support (fun n _ => (Evaluates.const Q (a n)).mul ((Evaluates.var Q).zpow hQ n))

private lemma rational_eval (a : ℤ →₀ ℂ) (D b Q : ℂ) (n₀ : ℤ) (unram : Prop)
    (hb : b ≠ 0) (hQ : Q ≠ 0) (hden : 1-b*Q ≠ 0) :
    Evaluates Q ((∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n) +
      if unram then RatFunc.C D * (RatFunc.C b*RatFunc.X)^n₀ / (1-RatFunc.C b*RatFunc.X) else 0)
      ((∑ n ∈ a.support, a n*Q^n) + if unram then D*(b*Q)^n₀/(1-b*Q) else 0) := by
  have hL := laurent_eval a Q hQ
  by_cases hu : unram
  · simp only [hu, ite_eq_left]
    simpa only [map_one] using hL.add (((Evaluates.const Q D).mul
      (((Evaluates.const Q b).mul (Evaluates.var Q)).zpow (mul_ne_zero hb hQ) n₀)).div
      ((Evaluates.const Q 1).sub ((Evaluates.const Q b).mul (Evaluates.var Q))) hden)
  · simpa [hu] using hL

private lemma rational_residue_trivial (a : ℤ →₀ ℂ) (D : ℂ) (n₀ : ℤ) :
    Evaluates 1 ((1-RatFunc.X)*((∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n) +
      RatFunc.C D * RatFunc.X^n₀/(1-RatFunc.X))) D := by
  have hn : (1-RatFunc.X : RatFunc ℂ) ≠ 0 := by
    intro h
    have he := congrArg (RatFunc.eval (RingHom.id ℂ) 0) h
    have hv : RatFunc.eval (RingHom.id ℂ) 0 (1-RatFunc.X) = 1-0 := by
      simpa only [map_one] using ((Evaluates.const (0:ℂ) 1).sub (Evaluates.var 0)).2
    rw [hv] at he
    simp at he
  have he : (1-RatFunc.X)*((∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n) +
      RatFunc.C D * RatFunc.X^n₀/(1-RatFunc.X)) =
      (1-RatFunc.X)*(∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n) +
      RatFunc.C D * RatFunc.X^n₀ := by field_simp
  rw [he]
  have h := (((Evaluates.const (1:ℂ) 1).sub (Evaluates.var 1)).mul
    (laurent_eval a 1 one_ne_zero)).add
    ((Evaluates.const 1 D).mul ((Evaluates.var 1).zpow one_ne_zero n₀))
  simpa using h

end Generic
end TwistedMellinProof
variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
local instance twistedMellinValuativeRel : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance twistedMellinLocalField : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
local instance twistedMellinMeasurableSpace : MeasurableSpace (q.adicCompletion F) := borel (q.adicCompletion F)
local instance twistedMellinBorelSpace : BorelSpace (q.adicCompletion F) := ⟨rfl⟩

theorem actual_twisted_profile_geometric_tail
    (dx : Measure (q.adicCompletion F)) [dx.IsAddHaarMeasure]
    (π : (q.adicCompletion F)ˣ)
    (hπ : valuation (q.adicCompletion F) (π : q.adicCompletion F) = uniformizer (q.adicCompletion F))
    (χ : (q.adicCompletion F)ˣ →ₜ* ℂˣ) (hχ : ∀ x, χ x ^ 3 = 1)
    (φ : q.adicCompletion F → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    let K := q.adicCompletion F
    let A : ℂ := (CubicUnitCharacters.residueCard K : ℂ)⁻¹
    let m : ℂ := (KPRankOneRamifiedBeta.m K dx : ℂ)
    let unram : Prop := ∀ u : (𝒪[K])ˣ, χ (KPRankOneCubicProjection.unitInclusion K u) = 1
    ∃ (n₀ : ℤ) (a : ℤ →₀ ℂ),
      let M : RatFunc ℂ := (∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n) +
        if unram then RatFunc.C (m*(1-A)*φ 0) * (RatFunc.C (χ π : ℂ)*RatFunc.X)^n₀ /
          (1-RatFunc.C (χ π : ℂ)*RatFunc.X) else 0
      (∀ (ρ : ℂ), 0 < ρ.re →
        let Q := Complex.exp (-ρ * (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
        Integrable (fun x : Kˣ => φ (x : K) * (χ x : ℂ) *
          Complex.exp (ρ * (Real.log (KPCubicHaar.abs K (x : K)) : ℂ)))
          (KPCubicHaar.multiplicativeHaar K dx) ∧
        (∫ x : Kˣ, φ (x : K) * (χ x : ℂ) *
          Complex.exp (ρ * (Real.log (KPCubicHaar.abs K (x : K)) : ℂ))
          ∂KPCubicHaar.multiplicativeHaar K dx) =
          (∑ n ∈ a.support, a n * Q^n) +
            if unram then m*(1-A)*φ 0 * ((χ π : ℂ)*Q)^n₀ / (1-(χ π : ℂ)*Q) else 0) ∧
      (∀ (ρ : ℂ), 0 < ρ.re →
        let Q := Complex.exp (-ρ * (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
        M.denom.eval Q ≠ 0 ∧
        (∫ x : Kˣ, φ (x : K) * (χ x : ℂ) *
          Complex.exp (ρ * (Real.log (KPCubicHaar.abs K (x : K)) : ℂ))
          ∂KPCubicHaar.multiplicativeHaar K dx) = RatFunc.eval (RingHom.id ℂ) Q M) ∧
      (((1-RatFunc.X)*M).denom.eval (1 : ℂ) ≠ 0) ∧
      (RatFunc.eval (RingHom.id ℂ) 1 ((1-RatFunc.X)*M) =
        if χ = 1 then m*(1-A)*φ 0 else 0) ∧
      (χ ≠ 1 → M.denom.eval (1 : ℂ) ≠ 0) := by
  let K := q.adicCompletion F
  let μ := KPCubicHaar.multiplicativeHaar K dx
  let mR := KPRankOneRamifiedBeta.m K dx
  have hcpt : IsCompact ((valuation K).integer : Set K) :=
    IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have hop : IsOpen ((valuation K).integer : Set K) := (valuation K).isOpen_integer
  have hpos : 0 < dx ((valuation K).integer : Set K) := hop.measure_pos (μ := dx) ⟨0, by simp⟩
  have hm : 0 < mR := ENNReal.toReal_pos hpos.ne' hcpt.measure_lt_top.ne
  have hvol : dx ((valuation K).integer : Set K) = ENNReal.ofReal mR :=
    (ENNReal.ofReal_toReal hcpt.measure_lt_top.ne).symm
  let A : ℂ := (CubicUnitCharacters.residueCard K : ℂ)⁻¹
  let D : ℂ := (mR : ℂ)*(1-A)*φ 0
  let b : ℂ := χ π
  let unram := ∀ u : ((valuation K).integer)ˣ, χ (KPRankOneCubicProjection.unitInclusion K u) = 1
  have hb : b ≠ 0 := (χ π).ne_zero
  have hD : ((mR*(1-(KPCubicUnitIndices.residueCard K : ℝ)⁻¹) : ℝ) : ℂ)*φ 0 = D := by
    change ((mR*(1-(CubicUnitCharacters.residueCard K : ℝ)⁻¹) : ℝ) : ℂ)*φ 0 = D
    simp [D, A, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]
  obtain ⟨nmin,n₀,hle,hlower,htail,_⟩ :=
    KPRankOneTestFunctionMellinPole.exists_cutoffs K φ hφ hcφ π hπ
  let c := fun j : ℤ => ∫ y : Kˣ in {y | KPCubicExpansion.valuationExponent K y = j},
    φ (y : K)*(χ y : ℂ) ∂μ
  let I := Finset.Ico nmin n₀
  let a : ℤ →₀ ℂ := Finsupp.onFinset I (fun j => if j ∈ I then c j else 0)
    (fun j hj => by by_contra h; simp [h] at hj)
  have ha (j : ℤ) (hj : j ∈ I) : a j = c j := by simp [a, hj]
  have hasum (Q : ℂ) : (∑ n ∈ a.support, a n * Q^n) = ∑ n ∈ I, c n*Q^n := by
    change a.sum (fun n v => v*Q^n) = _
    rw [Finsupp.sum_onFinset]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [hn]
    · intro n hn; simp
  refine ⟨n₀,a,?_⟩
  let L : RatFunc ℂ := ∑ n ∈ a.support, RatFunc.C (a n) * (RatFunc.X : RatFunc ℂ)^n
  let M : RatFunc ℂ := L + if unram then
    RatFunc.C D * (RatFunc.C b*RatFunc.X)^n₀/(1-RatFunc.C b*RatFunc.X) else 0
  change (∀ ρ : ℂ, 0 < ρ.re → _) ∧ (∀ ρ : ℂ, 0 < ρ.re → _) ∧
    ((1-RatFunc.X)*M).denom.eval 1 ≠ 0 ∧
    RatFunc.eval (RingHom.id ℂ) 1 ((1-RatFunc.X)*M) = (if χ=1 then D else 0) ∧
    (χ≠1 → M.denom.eval 1 ≠ 0)
  have initial (ρ : ℂ) (hρ : 0 < ρ.re) :
      let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
      Integrable (fun x : Kˣ => φ (x : K)*(χ x : ℂ)*
        Complex.exp (ρ*(Real.log (KPCubicHaar.abs K (x : K)) : ℂ))) μ ∧
      (∫ x : Kˣ, φ (x : K)*(χ x : ℂ)*
        Complex.exp (ρ*(Real.log (KPCubicHaar.abs K (x : K)) : ℂ)) ∂μ) =
      (∑ n ∈ a.support, a n*Q^n) + if unram then D*(b*Q)^n₀/(1-b*Q) else 0 := by
    dsimp only
    let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
    have hi := TwistedMellinProof.twisted_series K dx mR hm hvol π hπ φ hφ hcφ χ hχ
      nmin n₀ hle hlower htail Q (Complex.exp_ne_zero _) (TwistedMellinProof.exp_ratio_norm K ρ hρ)
    simp only [hD] at hi
    simp_rw [TwistedMellinProof.exp_weight K]
    rw [hasum Q]
    exact hi
  have eval_initial (ρ : ℂ) (hρ : 0 < ρ.re) :
      let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
      M.denom.eval Q ≠ 0 ∧
      (∫ x : Kˣ, φ (x : K)*(χ x : ℂ)*
        Complex.exp (ρ*(Real.log (KPCubicHaar.abs K (x : K)) : ℂ)) ∂μ) =
        RatFunc.eval (RingHom.id ℂ) Q M := by
    dsimp only
    let Q := Complex.exp (-ρ*(Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))
    have hn : ‖b*Q‖ < 1 := by
      rw [norm_mul, TwistedMellinProof.cubic_norm K χ hχ π, one_mul]
      exact TwistedMellinProof.exp_ratio_norm K ρ hρ
    have hd : 1-b*Q ≠ 0 := sub_ne_zero.mpr (fun he => by rw [← he, norm_one] at hn; exact lt_irrefl _ hn)
    have he := TwistedMellinProof.rational_eval a D b Q n₀ unram hb (Complex.exp_ne_zero _) hd
    exact ⟨he.1,(initial ρ hρ).2.trans he.2.symm⟩
  refine ⟨initial,eval_initial,?_⟩
  by_cases hχ1 : χ = 1
  · have hu : unram := by intro u; simp [hχ1]
    have hb1 : b = 1 := by simp [b,hχ1]
    have hM : M = L + RatFunc.C D * RatFunc.X^n₀/(1-RatFunc.X) := by
      simp [M,hu,hb1]
    have he := TwistedMellinProof.rational_residue_trivial a D n₀
    rw [hM]
    exact ⟨he.1,by simpa [hχ1] using he.2,fun hn => (hn hχ1).elim⟩
  · have he : TwistedMellinProof.Evaluates 1 M
        ((∑ n ∈ a.support, a n*(1:ℂ)^n) + if unram then D*b^n₀/(1-b) else 0) := by
      by_cases hu : unram
      · have hb1 : b ≠ 1 := fun h => hχ1 (TwistedMellinProof.character_eq_one K π hπ χ hu h)
        simpa only [mul_one] using TwistedMellinProof.rational_eval a D b 1 n₀ unram hb one_ne_zero
          (by simpa only [mul_one] using sub_ne_zero.mpr (Ne.symm hb1))
      · simpa [M,hu] using TwistedMellinProof.laurent_eval a 1 one_ne_zero
    have hp := ((TwistedMellinProof.Evaluates.const (1:ℂ) 1).sub
      (TwistedMellinProof.Evaluates.var 1)).mul he
    exact ⟨by simpa only [map_one, TwistedMellinProof.Regular] using hp.1,
      by simpa [map_one,hχ1] using hp.2,fun _ => he.1⟩

end DedekindZetaZeroFree

end
