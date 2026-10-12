module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CubicBeta.UnramifiedLargeNormShells
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.UnramifiedBetaResidueRegion

@[expose] public section

section
namespace DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition

open MeasureTheory ValuativeRel Filter
open scoped Topology
noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

local instance smallRegionBorelSpaceUnits : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K),
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]⟩

private lemma q_gt_one : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K))

private lemma abs_formula (y : Kˣ) : KPCubicHaar.abs K (y : K) =
    (KPCubicUnitIndices.residueCard K : ℝ) ^ (-KPCubicExpansion.valuationExponent K y) := by
  simp [KPCubicHaar.abs, y.ne_zero, KPCubicExpansion.valuationExponent]

private lemma small_iff (y : Kˣ) : y ∈ small K ↔ 0 < KPCubicExpansion.valuationExponent K y := by
  change KPCubicHaar.abs K (y : K) < 1 ↔ _
  rw [abs_formula, zpow_lt_one_iff_right₀ (q_gt_one K)]
  omega

private lemma exponent_locally_constant (y : Kˣ) :
    ∀ᶠ x : Kˣ in nhds y, KPCubicExpansion.valuationExponent K x =
      KPCubicExpansion.valuationExponent K y := by
  letI : TopologicalSpace (ValueGroupWithZero K) := WithZeroTopology.topologicalSpace
  have hv := (IsValuativeTopology.continuous_valuation (R := K)).comp
    (Units.continuous_val (M := K))
  have hn : valuation K (y : K) ≠ 0 := by simp
  have h := (hv.continuousAt (x := y)).tendsto
  change Tendsto (fun x : Kˣ => valuation K (x : K)) (nhds y) (nhds (valuation K (y : K))) at h
  rw [WithZeroTopology.nhds_of_ne_zero hn] at h
  filter_upwards [Filter.tendsto_pure.mp h] with x hx
  simp [KPCubicExpansion.valuationExponent, hx]

private lemma shell_measurable (n : ℤ) :
    MeasurableSet {y : Kˣ | KPCubicExpansion.valuationExponent K y = n} := by
  apply IsOpen.measurableSet
  rw [isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [exponent_locally_constant K y] with x hx
  exact hx.trans hy

private lemma zero_shell : {y : Kˣ | KPCubicExpansion.valuationExponent K y = 0} =
    {y : Kˣ | (y : K) ∈ 𝒪[K] ∧ ((y⁻¹ : Kˣ) : K) ∈ 𝒪[K]} := by
  ext y
  have hne : (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (valuation K (y : K)) ≠ 0 := by simp
  have he : KPCubicExpansion.valuationExponent K y = 0 ↔ valuation K (y : K) = 1 := by
    constructor
    · intro h
      have hl : WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (valuation K (y : K))) = 0 := by
        simpa [KPCubicExpansion.valuationExponent] using h
      have hh := WithZero.exp_log hne
      rw [hl, WithZero.exp_zero] at hh
      exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective (by simpa using hh.symm)
    · intro h
      simp [KPCubicExpansion.valuationExponent, h]
  simp only [Set.mem_setOf_eq, he, Valuation.mem_integer_iff, Units.val_inv_eq_inv_val,
    map_inv₀]
  constructor
  · intro h; simp [h]
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ ((Valuation.ne_zero_iff (valuation K)).mpr y.ne_zero).bot_lt).mp h2)

private lemma rawIntegrand_eq_b_zpow_on_small_region (b u : ℂˣ) (y : Kˣ) (hy : y ∈ small K) :
    rawIntegrand K b u y = (b ^ KPCubicExpansion.valuationExponent K y : ℂˣ) := by
  have hv : valuation K (y : K) < 1 := by
    simpa using (KPCubicHaar.abs_lt_iff K (one_ne_zero : (1 : K) ≠ 0)).mp (by simpa [small] using hy)
  have hs : valuation K (1 - (y : K)) = 1 := by
    simpa only [map_one] using (valuation K).map_sub_eq_of_lt_left
      (x := (1 : K)) (y := (y : K)) (by simpa only [map_one] using hv)
  have hne : 1 - (y : K) ≠ 0 := by
    intro h
    simp [h] at hs
  have he : KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) hne) = 0 := by
    simp [KPCubicExpansion.valuationExponent, hs]
  have ha : KPCubicHaar.abs K (1 - (y : K)) = 1 := by
    simp [KPCubicHaar.abs, hne, hs]
  simp [rawIntegrand, hne, he, ha, KPRankOneCubicProjection.eta]

theorem small_region (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m)
    (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m)
    (b u : ℂˣ) (hb : ‖(b : ℂ)‖ < 1) :
    IntegrableOn (rawIntegrand K b u) (small K)
        (KPCubicHaar.multiplicativeHaar K dx) ∧
      (∫ y in small K, rawIntegrand K b u y
        ∂KPCubicHaar.multiplicativeHaar K dx) =
        (m : ℂ) * (1 - rawA K) * ((b : ℂ) / (1 - (b : ℂ))) := by
  classical
  let ν := KPCubicHaar.multiplicativeHaar K dx
  let shell : ℕ → Set Kˣ := fun j => {y | KPCubicExpansion.valuationExponent K y = (j + 1 : ℕ)}
  have hmeas (j : ℕ) : MeasurableSet (shell j) := shell_measurable K _
  have hdisj : Pairwise (Function.onFun Disjoint shell) := by
    intro i j hij
    change Disjoint (shell i) (shell j)
    rw [Set.disjoint_left]
    intro y hi hj
    change KPCubicExpansion.valuationExponent K y = (i + 1 : ℕ) at hi
    change KPCubicExpansion.valuationExponent K y = (j + 1 : ℕ) at hj
    exact hij (by omega)
  have hcover : (⋃ j, shell j) = small K := by
    ext y
    simp only [Set.mem_iUnion, small_iff]
    constructor
    · rintro ⟨j, hj⟩
      change KPCubicExpansion.valuationExponent K y = (j + 1 : ℕ) at hj
      omega
    · intro h
      refine ⟨(KPCubicExpansion.valuationExponent K y - 1).toNat, ?_⟩
      change KPCubicExpansion.valuationExponent K y = _
      omega
  have hval (j : ℕ) (y : Kˣ) (hy : y ∈ shell j) : rawIntegrand K b u y = (b : ℂ) ^ (j + 1) := by
    have hys : y ∈ small K := by rw [← hcover]; exact Set.mem_iUnion.mpr ⟨j, hy⟩
    rw [rawIntegrand_eq_b_zpow_on_small_region K b u y hys, hy]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  haveI : ν.IsHaarMeasure := (kp_rankone_cubic_haar_power_measure K dx m hm hvol).1
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective (K := K) (uniformizer K)
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
    exact (uniformizer_pos (R := K)).ne' hp.symm
  let π : Kˣ := Units.mk0 p hp0
  have hπ : KPCubicExpansion.valuationExponent K π = 1 :=
    KPCubicExpansion.valuationExponent_uniformizer π hp
  let M : ℝ := m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)
  have hM : 0 ≤ M := le_of_lt (mul_pos hm (sub_pos.mpr (inv_lt_one_of_one_lt₀ (q_gt_one K))))
  have hmass (j : ℕ) : ν (shell j) = ENNReal.ofReal M := by
    have heq : shell j = (fun y : Kˣ => π ^ (-((j + 1 : ℕ) : ℤ)) * y) ⁻¹'
        {y : Kˣ | KPCubicExpansion.valuationExponent K y = 0} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, KPCubicExpansion.valuationExponent_mul,
        KPCubicExpansion.valuationExponent_zpow, hπ, mul_one]
      change _ ↔ _
      dsimp [shell]
      omega
    rw [heq, measure_preimage_mul, zero_shell]
    exact KPRankOneCubicProjection.unit_mass K dx m hm hvol
  have hfinite (j : ℕ) : ν (shell j) ≠ ⊤ := by rw [hmass]; exact ENNReal.ofReal_ne_top
  have hreal (j : ℕ) : ν.real (shell j) = M := by simp [Measure.real, hmass, ENNReal.toReal_ofReal hM]
  have hi (j : ℕ) : IntegrableOn (rawIntegrand K b u) (shell j) ν :=
    (integrableOn_const (hfinite j) (C := (b : ℂ) ^ (j + 1))).congr_fun
      (fun y hy => (hval j y hy).symm) (hmeas j)
  have hin (j : ℕ) : (∫ y in shell j, ‖rawIntegrand K b u y‖ ∂ν) = M * ‖(b : ℂ)‖ ^ (j + 1) := by
    rw [setIntegral_congr_fun (hmeas j) (fun y hy => congrArg norm (hval j y hy)),
      setIntegral_const, hreal, smul_eq_mul, norm_pow]
  have hs : Summable (fun j : ℕ => ‖(b : ℂ)‖ ^ (j + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg (b : ℂ)) hb).mul_right ‖(b : ℂ)‖
  have hu : IntegrableOn (rawIntegrand K b u) (⋃ j, shell j) ν :=
    integrableOn_iUnion_of_summable_integral_norm hi (by simpa only [hin] using hs.mul_left M)
  rw [← hcover]
  refine ⟨hu, ?_⟩
  rw [integral_iUnion hmeas hdisj hu]
  simp_rw [setIntegral_congr_fun (hmeas _) (hval _), setIntegral_const, hreal, Complex.real_smul]
  rw [tsum_mul_left]
  have hg : HasSum (fun j : ℕ => (b : ℂ) ^ (j + 1)) ((b : ℂ) / (1 - (b : ℂ))) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_norm_lt_one hb).mul_right (b : ℂ)
  rw [hg.tsum_eq]
  simp [M, rawA, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]

end
end DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition

end

section
namespace DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition
open MeasureTheory ValuativeRel
noncomputable section
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [mK : MeasurableSpace K] [BorelSpace K]
 instance instMeasurableMulUnramifiedBetaUnits : MeasurableMul Kˣ where
  measurable_const_mul a := by
    apply measurable_comap_iff.mpr
    exact (measurable_const_mul (a : K)).comp MeasurableSpace.le_map_comap
  measurable_mul_const a := by
    apply measurable_comap_iff.mpr
    exact (measurable_mul_const (a : K)).comp MeasurableSpace.le_map_comap
private lemma abs_v (y : Kˣ) :
    KPCubicHaar.abs K (y : K) = (KPCubicUnitIndices.residueCard K : ℝ) ^ (-KPCubicExpansion.valuationExponent K y) := by
  simp [KPCubicHaar.abs, y.ne_zero, KPCubicExpansion.valuationExponent]
private lemma abs_le (y : Kˣ) :
    KPCubicHaar.abs K (y : K) ≤ 1 ↔ valuation K (y : K) ≤ 1 := by
  simpa using not_congr (KPCubicHaar.abs_lt_iff K (x := (1 : K)) y.ne_zero)
private lemma unitSet :
    {y : Kˣ | KPCubicHaar.abs K (y : K) = 1} =
    {y : Kˣ | (y : K) ∈ 𝒪[K] ∧ ((y⁻¹ : Kˣ) : K) ∈ 𝒪[K]} := by
  ext y
  change _ ↔ _ ∧ _
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← abs_le K y, ← abs_le K y⁻¹]
  simp only [Units.val_inv_eq_inv_val, KPCubicHaar.abs_inv]
  constructor
  · intro h; change KPCubicHaar.abs K (y : K) = 1 at h; simp [h]
  · rintro ⟨h, hi⟩
    have hp := KPCubicHaar.abs_pos K y.ne_zero
    have h' : 1 ≤ KPCubicHaar.abs K (y : K) := (inv_le_one₀ hp).mp hi
    exact le_antisymm h h'
private lemma shell_mass (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m)
    (j : ℕ) :
    (KPCubicHaar.multiplicativeHaar K dx)
      {y : Kˣ | KPCubicHaar.abs K (y : K) = (KPCubicUnitIndices.residueCard K : ℝ) ^ (j + 1)} =
      ENNReal.ofReal (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)) := by
  have hH := kp_rankone_cubic_haar_power_measure K dx m hm hvol
  letI := hH.1
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer K)
  have hp0 : p ≠ 0 := by
    intro h
    subst p
    simpa using hp.symm.trans (by simp : valuation K (0 : K) = 0)
  let π := Units.mk0 p hp0
  have hπ : valuation K (π : K) = ValuativeRel.uniformizer K := hp
  have ha : KPCubicHaar.abs K (π : K) = (KPCubicUnitIndices.residueCard K : ℝ)⁻¹ :=
    KPCubicHaar.abs_uniformizer K π hπ
  have hq : (0 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (by have := KPCubicUnitIndices.two_le_residueCard K; omega : 0 < KPCubicUnitIndices.residueCard K)
  have hs : (fun y : Kˣ => π ^ (j + 1) * y) ⁻¹' {y : Kˣ | KPCubicHaar.abs K (y : K) = 1} =
      {y : Kˣ | KPCubicHaar.abs K (y : K) = (KPCubicUnitIndices.residueCard K : ℝ) ^ (j + 1)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Units.val_mul, Units.val_pow_eq_pow_val,
      KPCubicHaar.abs_mul, KPCubicHaar.abs_pow, ha, inv_pow]
    exact (inv_mul_eq_one₀ (pow_ne_zero _ hq.ne')).trans eq_comm
  rw [← hs, measure_preimage_mul, unitSet K]
  exact hH.2
private lemma large_value (b u : ℂˣ) (y : Kˣ)
    (hy : 1 < KPCubicHaar.abs K (y : K)) :
    rawIntegrand K b u y = ((b * u) ^ KPCubicExpansion.valuationExponent K y : ℂˣ) /
      (KPCubicHaar.abs K (y : K) : ℂ) := by
  have hv : 1 < valuation K (y : K) := by
    simpa only [map_one] using (KPCubicHaar.abs_lt_iff K (x := (1 : K)) y.ne_zero).mp (by simpa using hy)
  have hs : valuation K (1 - (y : K)) = valuation K (y : K) := by
    exact (valuation K).map_sub_eq_of_lt_right (by simpa using hv)
  have hne : 1 - (y : K) ≠ 0 := by
    intro h
    have hv0 := (Valuation.ne_zero_iff (valuation K)).mpr y.ne_zero
    exact hv0 (by simpa [h] using hs.symm)
  have he : KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) hne) =
      KPCubicExpansion.valuationExponent K y := by
    simp [KPCubicExpansion.valuationExponent, hs]
  have ha : KPCubicHaar.abs K (1 - (y : K)) = KPCubicHaar.abs K (y : K) := by
    simp [KPCubicHaar.abs, hne, y.ne_zero, hs]
  simp [rawIntegrand, hne, he, ha, KPRankOneCubicProjection.eta, mul_zpow, Units.val_mul]
private lemma shell_value (b u : ℂˣ) (y : Kˣ) (j : ℕ)
    (hy : KPCubicHaar.abs K (y : K) = (KPCubicUnitIndices.residueCard K : ℝ) ^ (j + 1)) :
    rawIntegrand K b u y = (rawA K / ((b : ℂ) * (u : ℂ))) ^ (j + 1) := by
  have hq : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K))
  have hv : KPCubicExpansion.valuationExponent K y = -((j + 1 : ℕ) : ℤ) := by
    have h := hy
    rw [abs_v K] at h
    have hi := (zpow_right_inj₀ (lt_trans zero_lt_one hq) hq.ne').mp
      (h.trans (zpow_natCast _ _).symm)
    omega
  rw [large_value K b u y (by rw [hy]; exact one_lt_pow₀ hq (by omega)), hv, hy]
  simp only [zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_mul, Complex.ofReal_pow, Complex.ofReal_natCast, div_pow, rawA, inv_pow]
  ring
private lemma large_cover : large K = ⋃ j : ℕ,
    {y : Kˣ | KPCubicHaar.abs K (y : K) = (KPCubicUnitIndices.residueCard K : ℝ) ^ (j + 1)} := by
  have hq : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K))
  ext y
  simp only [large, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    rw [abs_v K] at h
    have hi : 0 < -KPCubicExpansion.valuationExponent K y := by
      have h' := (zpow_lt_zpow_iff_right₀ hq).mp
        (show (KPCubicUnitIndices.residueCard K : ℝ) ^ (0 : ℤ) < (KPCubicUnitIndices.residueCard K : ℝ) ^ (-KPCubicExpansion.valuationExponent K y) by simpa only [zpow_zero] using h)
      exact h'
    refine ⟨(-KPCubicExpansion.valuationExponent K y).toNat - 1, ?_⟩
    rw [abs_v K, ← zpow_natCast]
    congr 1
    omega
  · rintro ⟨j, hj⟩
    rw [hj]
    exact one_lt_pow₀ hq (by omega)
 instance instBorelSpaceUnramifiedBetaLargeRegionUnits : BorelSpace Kˣ := by
  constructor
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [show mK = borel K from BorelSpace.measurable_eq, Units.isEmbedding_val₀.eq_induced, borel_comap]

theorem large_region (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m)
    (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m)
    (b u : ℂˣ) (hbu : (KPCubicUnitIndices.residueCard K : ℝ)⁻¹ <
      ‖(b : ℂ)‖ * ‖(u : ℂ)‖) :
    IntegrableOn (rawIntegrand K b u) (large K)
        (KPCubicHaar.multiplicativeHaar K dx) ∧
      (∫ y in large K, rawIntegrand K b u y
        ∂KPCubicHaar.multiplicativeHaar K dx) =
        (m : ℂ) * (1 - rawA K) * (rawA K / ((b : ℂ) * (u : ℂ) - rawA K)) := by
  classical
  let shell := fun j : ℕ => {y : Kˣ | KPCubicHaar.abs K (y : K) =
    (KPCubicUnitIndices.residueCard K : ℝ) ^ (j + 1)}
  let ν := KPCubicHaar.multiplicativeHaar K dx
  let r := rawA K / ((b : ℂ) * (u : ℂ))
  have hq : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K))
  have hqp : (0 : ℝ) < KPCubicUnitIndices.residueCard K := lt_trans zero_lt_one hq
  have ha : ‖rawA K‖ = (KPCubicUnitIndices.residueCard K : ℝ)⁻¹ := by
    simp only [rawA, norm_inv, Complex.norm_natCast]
  have hr : ‖r‖ < 1 := by
    dsimp only [r]
    rw [norm_div, norm_mul, ha]
    exact (div_lt_one (mul_pos (norm_pos_iff.mpr b.ne_zero) (norm_pos_iff.mpr u.ne_zero))).mpr hbu
  have hmeas (j : ℕ) : MeasurableSet (shell j) :=
    (isClosed_eq (KPCubicHaar.abs_units_locallyConstant K).continuous continuous_const).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint shell) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hi hj
    have he := (pow_right_inj₀ hqp hq.ne').mp (hi.symm.trans hj)
    exact hij (by omega)
  have hmsh (j : ℕ) : ν (shell j) = ENNReal.ofReal
      (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)) :=
    shell_mass K dx m hm hvol j
  have hfinite (j : ℕ) : ν (shell j) ≠ ⊤ := by rw [hmsh]; exact ENNReal.ofReal_ne_top
  have hmpos : 0 ≤ m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹) := by
    exact mul_nonneg hm.le (sub_nonneg.mpr ((inv_le_one₀ hqp).mpr hq.le))
  have hmass (j : ℕ) : ν.real (shell j) = m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹) := by
    rw [Measure.real, hmsh, ENNReal.toReal_ofReal hmpos]
  have hsum := KPRankOneBetaUnramified.ShellIntegrals.geometric_shell_integral ν shell hmeas hdisj
    (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)) hfinite hmass
    (rawIntegrand K b u) r hr (fun j y hy => shell_value K b u y j hy)
  change IntegrableOn _ (⋃ j, shell j) ν ∧ _ at hsum
  have hcover : (⋃ j, shell j) = large K := (large_cover K).symm
  rw [hcover] at hsum
  refine ⟨hsum.1, ?_⟩
  rw [hsum.2]
  have hg : HasSum (fun j : ℕ => r ^ (j + 1)) (r / (1 - r)) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_norm_lt_one hr).mul_right r
  rw [hg.tsum_eq]
  have hratio : r / (1 - r) = rawA K / ((b : ℂ) * (u : ℂ) - rawA K) := by
    dsimp only [r]
    field_simp
  rw [hratio]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_inv, Complex.ofReal_natCast, rawA]

end
end DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition

end

section
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition
noncomputable section
open scoped Classical
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
 instance instBorelSpaceUnramifiedBetaCoordinatesUnits : BorelSpace Kˣ := ⟨by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K), ← borel_comap]
  rw [← Units.isEmbedding_val₀.isInducing.eq_induced]⟩
private theorem emb : MeasurableEmbedding (fun y : Kˣ => (y : K)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  exact (IsOpen.isOpenEmbedding_subtypeVal (isClosed_singleton (x := (0 : K))).isOpen_compl).measurableEmbedding.comp
    (unitsHomeomorphNeZero (G₀ := K)).measurableEmbedding
private theorem coords (dx : Measure K) (g : K → ℂ) (hg : g 0 = 0) :
    (Integrable (fun y : Kˣ => g y) (KPCubicHaar.multiplicativeHaar K dx) ↔
      Integrable (fun x => (KPCubicHaar.abs K x)⁻¹ • g x) dx) ∧
    (∫ y : Kˣ, g y ∂KPCubicHaar.multiplicativeHaar K dx) =
      ∫ x, (KPCubicHaar.abs K x)⁻¹ • g x ∂dx := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  let ν := dx.withDensity (fun x => ENNReal.ofReal ((KPCubicHaar.abs K x)⁻¹))
  have he := emb K
  have hrange : Set.range (fun y : Kˣ => (y : K)) = ({0} : Set K)ᶜ := by
    ext x
    exact Units.exists_iff_ne_zero (p := (· = x)) |>.trans (by simp)
  have hi : (Set.range (fun y : Kˣ => (y : K))).indicator g = g := by
    funext x; rw [hrange]; by_cases h : x = 0 <;> simp [h, hg]
  have hmeas : Measurable (fun x => ENNReal.ofReal ((KPCubicHaar.abs K x)⁻¹)) :=
    (KPRamifiedBetaConductorSeries.normalizedAbs_measurable K).inv.ennreal_ofReal
  have hsmul : (fun x => (ENNReal.ofReal ((KPCubicHaar.abs K x)⁻¹)).toReal • g x) =
      (fun x => (KPCubicHaar.abs K x)⁻¹ • g x) := by
    funext x
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (by
      by_cases h : x = 0
      · simp [h]
      · exact (KPCubicHaar.abs_pos K h).le))]
  constructor
  · change Integrable (g ∘ fun y : Kˣ => (y : K)) (Measure.comap _ ν) ↔ _
    rw [← he.integrable_map_iff, he.map_comap]
    change IntegrableOn g (Set.range (fun y : Kˣ => (y : K))) ν ↔ _
    rw [← integrable_indicator_iff he.measurableSet_range, hi]
    unfold ν
    rw [integrable_withDensity_iff_integrable_smul₀' hmeas.aemeasurable (by simp), hsmul]
  · change (∫ y : Kˣ, g y ∂Measure.comap (fun y : Kˣ => (y : K)) ν) = _
    rw [← he.integral_map g, he.map_comap, ← integral_indicator he.measurableSet_range, hi]
    unfold ν
    rw [integral_withDensity_eq_integral_toReal_smul hmeas (by simp), hsmul]
 def weight (u : ℂˣ) (x : K) : ℂ :=
  if hx : x = 0 then 0 else (u ^ KPCubicExpansion.valuationExponent K (Units.mk0 x hx) : ℂ)
private theorem rawIntegrand_eq_valuationWeight_of_abs_lt_one (b u : ℂˣ) (y : Kˣ)
    (hy : KPCubicHaar.abs K (y : K) < 1) : rawIntegrand K b u y = weight K b y := by
  have hv : valuation K (y : K) < 1 := by
    simpa using (KPCubicHaar.abs_lt_iff K (one_ne_zero : (1 : K) ≠ 0)).mp (by simpa using hy)
  have hs : valuation K (1 - (y : K)) = 1 := by
    simpa only [map_one] using (valuation K).map_sub_eq_of_lt_left
      (x := (1 : K)) (y := (y : K)) (by simpa only [map_one] using hv)
  have hne : 1 - (y : K) ≠ 0 := by intro h; simp [h] at hs
  have he : KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) hne) = 0 := by
    simp [KPCubicExpansion.valuationExponent, hs]
  have ha : KPCubicHaar.abs K (1 - (y : K)) = 1 := by simp [KPCubicHaar.abs, hne, hs]
  have hmk : Units.mk0 (y : K) y.ne_zero = y := by ext; rfl
  simp [rawIntegrand, hne, he, ha, KPRankOneCubicProjection.eta, weight, y.ne_zero, hmk]
private theorem near_abs (x : K) (hx : KPCubicHaar.abs K (1 - x) < 1) :
    KPCubicHaar.abs K x = 1 := by
  have hv : valuation K (1 - x) < 1 := by
    simpa using (KPCubicHaar.abs_lt_iff K (one_ne_zero : (1 : K) ≠ 0)).mp (by simpa using hx)
  have hs : valuation K x = 1 := by
    simpa only [sub_sub_cancel, map_one] using (valuation K).map_sub_eq_of_lt_left
      (x := (1 : K)) (y := 1 - x) (by simpa only [map_one] using hv)
  have hn : x ≠ 0 := by intro h; simp [h] at hs
  simp [KPCubicHaar.abs, hn, hs]
private theorem near_value (b u : ℂˣ) (y : Kˣ)
    (hy : KPCubicHaar.abs K (1 - (y : K)) < 1) :
    rawIntegrand K b u y = weight K u (1 - (y : K)) / (KPCubicHaar.abs K (1 - (y : K)) : ℂ) := by
  have ha := near_abs K (y : K) hy
  have hs : valuation K (y : K) = 1 := by
    have hv : valuation K (1 - (y : K)) < 1 := by
      simpa using (KPCubicHaar.abs_lt_iff K (one_ne_zero : (1 : K) ≠ 0)).mp (by simpa using hy)
    simpa only [sub_sub_cancel, map_one] using (valuation K).map_sub_eq_of_lt_left
      (x := (1 : K)) (y := 1 - (y : K)) (by simpa only [map_one] using hv)
  have he : KPCubicExpansion.valuationExponent K y = 0 := by simp [KPCubicExpansion.valuationExponent, hs]
  by_cases hn : 1 - (y : K) = 0
  · simp [rawIntegrand, weight, hn]
  · simp [rawIntegrand, weight, hn, he, KPRankOneCubicProjection.eta]

theorem near_one_region (dx : Measure K) [dx.IsAddHaarMeasure] (m : ℝ) (hm : 0 < m)
    (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m) (b u : ℂˣ) (hu : ‖(u : ℂ)‖ < 1) :
    IntegrableOn (rawIntegrand K b u) (nearOne K) (KPCubicHaar.multiplicativeHaar K dx) ∧
      (∫ y in nearOne K, rawIntegrand K b u y ∂KPCubicHaar.multiplicativeHaar K dx) =
        (m : ℂ) * (1 - rawA K) * ((u : ℂ) / (1 - (u : ℂ))) := by
  classical
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  have habs : Measurable (KPCubicHaar.abs K) := KPRamifiedBetaConductorSeries.normalizedAbs_measurable K
  have hsmall : MeasurableSet (small K) := measurableSet_lt (habs.comp (emb K).measurable) measurable_const
  have hnear : MeasurableSet (nearOne K) := measurableSet_lt (habs.comp ((continuous_const.sub Units.continuous_val).measurable)) measurable_const
  let g : K → ℂ := fun x => if KPCubicHaar.abs K x < 1 then weight K u x else 0
  let h : K → ℂ := fun x => if KPCubicHaar.abs K (1-x) < 1 then
    weight K u (1-x) / (KPCubicHaar.abs K (1-x) : ℂ) else 0
  have hg : g 0 = 0 := by simp [g, weight]
  have hh : h 0 = 0 := by simp [h]
  have hgs : (fun y : Kˣ => g y) = (small K).indicator (rawIntegrand K u b) := by
    funext y
    by_cases hy : KPCubicHaar.abs K (y : K) < 1
    · simp [g, small, hy, rawIntegrand_eq_valuationWeight_of_abs_lt_one K u b y hy]
    · simp [g, small, hy]
  have hhn : (fun y : Kˣ => h y) = (nearOne K).indicator (rawIntegrand K b u) := by
    funext y
    by_cases hy : KPCubicHaar.abs K (1 - (y : K)) < 1
    · simp [h, nearOne, hy, near_value K b u y hy]
    · simp [h, nearOne, hy]
  have hw : (fun x => (KPCubicHaar.abs K x)⁻¹ • h x) = h := by
    funext x
    by_cases hx : KPCubicHaar.abs K (1-x) < 1
    · rw [near_abs K x hx]; simp
    · simp [h, hx]
  have ht : (fun x => h (1-x)) = (fun x => (KPCubicHaar.abs K x)⁻¹ • g x) := by
    funext x
    by_cases hx : KPCubicHaar.abs K x < 1
    · simp only [h, sub_sub_cancel, if_pos hx, g]
      simp [hx, Complex.real_smul, div_eq_mul_inv, mul_comm]
    · simp [h, g, hx]
  have hs := small_region K dx m hm hvol u b hu
  have hc := coords K dx g hg
  rw [hgs, integrable_indicator_iff hsmall, integral_indicator hsmall] at hc
  have hi := hc.1.mp hs.1
  have hv := hc.2.symm.trans hs.2
  have he := (Homeomorph.subLeft (1 : K)).measurableEmbedding
  have hp : MeasurePreserving (fun x : K => 1-x) dx dx := by
    have hneg : KPCubicHaar.abs K (-1 : K) = 1 := by
      simp [KPCubicHaar.abs]
    haveI : dx.IsNegInvariant := ⟨by
      change Measure.map (fun x : K => -x) dx = dx
      simpa only [neg_one_mul, hneg, ENNReal.ofReal_one, inv_one, one_smul] using
        NonarchimedeanHaarScaling.map_mul K dx (-1) (by simp)⟩
    exact Measure.measurePreserving_sub_left dx 1
  have hn := coords K dx h hh
  rw [hhn, integrable_indicator_iff hnear, integral_indicator hnear, hw] at hn
  have hi' : Integrable h dx := by
    apply (hp.integrable_comp_emb he).mp
    simpa only [Function.comp_def, ht] using hi
  refine ⟨hn.1.mpr hi', hn.2.trans ?_⟩
  rw [← hp.integral_comp he h, ht]
  exact hv
end
end DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition

end

section

namespace DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells

open MeasureTheory ValuativeRel Filter
open scoped Topology

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def aReal : ℝ := (KPCubicUnitIndices.residueCard K : ℝ)⁻¹

def a : ℂ := (KPCubicUnitIndices.residueCard K : ℂ)⁻¹

def integrand (b u : ℂˣ) (y : Kˣ) : ℂ := by
  classical
  exact if h : 1 - (y : K) = 0 then 0 else
    (KPRankOneCubicProjection.eta K b y : ℂ) *
      (u ^ KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) h) : ℂ) /
      (KPCubicHaar.abs K (1 - (y : K)) : ℂ)

variable [MeasurableSpace K] [BorelSpace K]

def betaIntegral (dx : Measure K) (b u : ℂˣ) : ℂ :=
  ∫ y : Kˣ, integrand K b u y ∂KPCubicHaar.multiplicativeHaar K dx

def formula (m : ℝ) (b u : ℂ) : ℂ :=
  (m : ℂ) * ((1 - a K) *
    (b / (1 - b) + u / (1 - u) + a K / (b * u - a K)) + 1 - 2 * a K)

def ConvergenceRegion (b u : ℂ) : Prop :=
  aReal K < ‖b‖ ∧ ‖b‖ < 1 ∧ aReal K / ‖b‖ < ‖u‖ ∧ ‖u‖ < 1

private lemma aReal_bounds : 0 < aReal K ∧ aReal K < 1 := by
  have hq : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (KPCubicUnitIndices.two_le_residueCard K))
  constructor
  · exact inv_pos.mpr (by linarith)
  · exact inv_lt_one_of_one_lt₀ hq

lemma abs_eq_q_neg_valuation (y : Kˣ) :
    KPCubicHaar.abs K (y : K) =
      (KPCubicUnitIndices.residueCard K : ℝ) ^ (-KPCubicExpansion.valuationExponent K y) := by
  simp [KPCubicHaar.abs, y.ne_zero, KPCubicExpansion.valuationExponent]

theorem integral_three_region (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m)
    (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m)
    (b u : ℂˣ) (hbu : ConvergenceRegion K b u) :
    Integrable (integrand K b u) (KPCubicHaar.multiplicativeHaar K dx) ∧
      betaIntegral K dx b u = formula K m b u := by
  have hprod : (KPCubicUnitIndices.residueCard K : ℝ)⁻¹ <
      ‖(b : ℂ)‖ * ‖(u : ℂ)‖ := by
    have hbpos : 0 < ‖(b : ℂ)‖ := lt_trans (aReal_bounds K).1 hbu.1
    simpa only [aReal, mul_comm] using (div_lt_iff₀ hbpos).mp hbu.2.2.1
  obtain ⟨hs, hsi⟩ := RegionDecomposition.small_region K dx m hm hvol b u hbu.2.1
  obtain ⟨hn, hni⟩ := RegionDecomposition.near_one_region K dx m hm hvol b u hbu.2.2.2
  obtain ⟨hl, hli⟩ := RegionDecomposition.large_region K dx m hm hvol b u hprod
  obtain ⟨hr, hri⟩ := RegionDecomposition.residue_region K dx m hm hvol b u
  have hparts := RegionDecomposition.four_regions K (KPCubicHaar.multiplicativeHaar K dx)
    (RegionDecomposition.rawIntegrand K b u) hs hn hl hr
  refine ⟨hparts.1, ?_⟩
  change (∫ y : Kˣ, RegionDecomposition.rawIntegrand K b u y
    ∂KPCubicHaar.multiplicativeHaar K dx) = formula K m b u
  rw [hparts.2, hsi, hni, hli, hri]
  change (m : ℂ) * (1 - a K) * ((b : ℂ) / (1 - (b : ℂ))) +
    (m : ℂ) * (1 - a K) * ((u : ℂ) / (1 - (u : ℂ))) +
    (m : ℂ) * (1 - a K) * (a K / ((b : ℂ) * (u : ℂ) - a K)) +
    (m : ℂ) * (1 - 2 * a K) = formula K m b u
  unfold formula
  ring

end
end DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells

end
