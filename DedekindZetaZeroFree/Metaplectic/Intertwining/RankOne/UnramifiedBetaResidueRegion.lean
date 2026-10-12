module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.UnramifiedBetaIntegralRegions

@[expose] public section

open MeasureTheory ValuativeRel
open scoped ENNReal
namespace DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition
noncomputable section
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
 [TopologicalSpace K] [IsNonarchimedeanLocalField K]
 [MeasurableSpace K] [BorelSpace K]
private lemma eq_one (x : K) : KPCubicHaar.abs K x = 1 ↔ valuation K x = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have hq : (1 : ℝ) < KPCubicUnitIndices.residueCard K := by
    exact_mod_cast (show 1 < KPCubicUnitIndices.residueCard K from lt_of_lt_of_le (by decide) (KPCubicUnitIndices.two_le_residueCard K))
  simp only [KPCubicHaar.abs, if_neg hx]
  rw [zpow_eq_one_iff_right₀ (le_trans zero_le_one hq.le) (ne_of_gt hq)]
  constructor
  · intro h
    have hn : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) ≠ 0 := by simpa using hx
    have he := WithZero.exp_log hn
    rw [h, WithZero.exp_zero] at he
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective (he.symm.trans (map_one _).symm)
  · intro h; simp [h]
local instance : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
local instance : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
private lemma measurable_ball : MeasurableSet {x : K | valuation K x < 1} := by
  have h := (valuation K).isOpen_ball 1
  convert h.measurableSet using 1
  ext x
  exact (valuation K).restrict_lt_one_iff.symm
private lemma ball_ideal : {x : K | valuation K x < 1} =
    (𝒪[K]).subtype '' (IsLocalRing.maximalIdeal (𝒪[K]) : Set (𝒪[K])) := by
  ext x
  constructor
  · intro hx
    have hx' : valuation K x < 1 := hx
    let y : 𝒪[K] := ⟨x, hx'.le⟩
    refine ⟨y, ?_, rfl⟩
    change ¬ IsUnit y
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mpr hx
  · rintro ⟨y, hy, rfl⟩
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp hy
local instance : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    calc
      MeasurableSpace.comap Units.val ‹MeasurableSpace K› =
          MeasurableSpace.comap Units.val (borel K) :=
        congrArg (MeasurableSpace.comap Units.val)
          (BorelSpace.measurable_eq (α := K))
      _ = borel Kˣ := by
        rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]⟩
private lemma embedding : MeasurableEmbedding (Units.val : Kˣ → K) := by
  apply (Units.isEmbedding_val₀ (G₀ := K)).measurableEmbedding
  have he : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [he]
  exact (MeasurableSet.singleton 0).compl
private lemma integrand_one (b u : ℂˣ) (y : Kˣ) (hy : y ∈ residue K) :
    rawIntegrand K b u y = 1 := by
  have hv : valuation K (y : K) = 1 := (eq_one K _).mp hy.1
  have hw : valuation K (1 - (y : K)) = 1 := (eq_one K _).mp hy.2
  have hn : 1 - (y : K) ≠ 0 := by intro h; simp [h] at hw
  have he : KPCubicExpansion.valuationExponent K y = 0 := by
    simp [KPCubicExpansion.valuationExponent, hv]
  have hf : KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) hn) = 0 := by
    simp [KPCubicExpansion.valuationExponent, hw]
  simp [rawIntegrand, hn, KPRankOneCubicProjection.eta, he, hf, hy.2]
 def R : Set K := {x | valuation K x = 1 ∧ valuation K (1-x) = 1}
private lemma R_diff : R K = (𝒪[K] : Set K) \
    ({x : K | valuation K x < 1} ∪ {x : K | valuation K (1-x) < 1}) := by
  ext x
  change (valuation K x = 1 ∧ valuation K (1-x) = 1) ↔
    (valuation K x ≤ 1 ∧ ¬ (valuation K x < 1 ∨ valuation K (1-x) < 1))
  have hv : valuation K (1-x) ≤ max 1 (valuation K x) := by simpa using (valuation K).map_sub 1 x
  constructor
  · rintro ⟨h1,h2⟩; simp [h1,h2]
  · rintro ⟨h1,h2⟩
    have hn := not_or.mp h2
    have h3 : valuation K (1-x) ≤ 1 := by simpa [max_eq_left h1] using hv
    exact ⟨le_antisymm h1 (not_lt.mp hn.1), le_antisymm h3 (not_lt.mp hn.2)⟩
private lemma R_measurable : MeasurableSet (R K) := by
  rw [R_diff]
  exact (Valued.isClosed_integer K).measurableSet.diff
    ((measurable_ball K).union ((measurable_ball K).preimage (by fun_prop)))
private lemma residue_measurable : MeasurableSet (residue K) := by
  have he : residue K = (Units.val : Kˣ → K) ⁻¹' R K := by
    ext y; exact and_congr (eq_one K _) (eq_one K _)
  rw [he]
  exact (R_measurable K).preimage (embedding K).measurable
private lemma residue_image : (Units.val : Kˣ → K) '' residue K = R K := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact ⟨(eq_one K _).mp hy.1, (eq_one K _).mp hy.2⟩
  · intro hx
    have hn : x ≠ 0 := by intro h; have := hx.1; simp [h] at this
    exact ⟨Units.mk0 x hn, ⟨(eq_one K _).mpr hx.1,(eq_one K _).mpr hx.2⟩,rfl⟩
private lemma residue_mass (dx : Measure K) :
    KPCubicHaar.multiplicativeHaar K dx (residue K) = dx (R K) := by
  rw [KPCubicHaar.multiplicativeHaar, (embedding K).comap_apply, residue_image,
    withDensity_apply _ (R_measurable K)]
  calc
    _ = ∫⁻ x in R K, (1 : ℝ≥0∞) ∂dx := setLIntegral_congr_fun (R_measurable K) (by
      intro x hx; simp [(eq_one K x).mpr hx.1])
    _ = _ := by simp
private lemma R_volume (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m) :
    dx.real (R K) = m * (1 - 2 * (KPCubicUnitIndices.residueCard K : ℝ)⁻¹) := by
  let B : Set K := {x | valuation K x < 1}
  let C : Set K := {x | valuation K (1-x) < 1}
  have hB : MeasurableSet B := measurable_ball K
  have hC : MeasurableSet C := hB.preimage (by fun_prop)
  have hBs : B ⊆ (𝒪[K] : Set K) := fun x hx => (show valuation K x < 1 from hx).le
  have hCs : C ⊆ (𝒪[K] : Set K) := by
    intro x hx
    have h := (valuation K).map_sub 1 (1-x)
    have hx' : valuation K (1-x) < 1 := hx
    change valuation K x ≤ 1
    simpa [max_eq_left hx'.le] using h
  have hd : Disjoint B C := by
    rw [Set.disjoint_left]
    intro x hx hy
    have h := (valuation K).map_add x (1-x)
    have hx' : valuation K x < 1 := hx
    have hy' : valuation K (1-x) < 1 := hy
    have : 1 ≤ max (valuation K x) (valuation K (1-x)) := by simpa using h
    exact (not_le_of_gt (max_lt hx' hy')) this
  have hfinite : dx (𝒪[K] : Set K) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hBfinite : dx B ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono hBs)
  have hCfinite : dx C ≠ ⊤ := ne_top_of_le_ne_top hfinite (measure_mono hCs)
  have hBmass : dx.real B = m / (KPCubicUnitIndices.residueCard K : ℝ) := by
    have h := NonarchimedeanHaarScaling.residue_index_measure K dx
    rw [← ball_ideal K] at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hvol, ENNReal.toReal_ofReal hm.le] at h'
    change (KPCubicUnitIndices.residueCard K : ℝ) * dx.real B = m at h'
    have hq : (KPCubicUnitIndices.residueCard K : ℝ) ≠ 0 := by
      exact_mod_cast (show KPCubicUnitIndices.residueCard K ≠ 0 from by
        have := KPCubicUnitIndices.two_le_residueCard K; omega)
    apply (eq_div_iff hq).mpr
    simpa [mul_comm] using h'
  have hCmass : dx.real C = dx.real B := by
    have he : C = (fun x : K => -1 + x) ⁻¹' B := by
      ext x
      change valuation K (1-x) < 1 ↔ valuation K (-1+x) < 1
      have he : -1+x = -(1-x) := by ring
      rw [he, Valuation.map_neg]
    rw [measureReal_def, he, measure_preimage_add, ← measureReal_def]
  have hU : dx.real (B ∪ C) = dx.real B + dx.real C := by
    rw [measureReal_def, measure_union hd hC, ENNReal.toReal_add hBfinite hCfinite]
    rfl
  rw [R_diff]
  change dx.real ((𝒪[K] : Set K) \ (B ∪ C)) = _
  rw [measureReal_diff (Set.union_subset hBs hCs) (hB.union hC) hfinite,
    hU, hCmass, hBmass, measureReal_def, hvol, ENNReal.toReal_ofReal hm.le]
  ring

theorem residue_region (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m)
    (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m)
    (b u : ℂˣ) :
    IntegrableOn (rawIntegrand K b u) (residue K)
        (KPCubicHaar.multiplicativeHaar K dx) ∧
      (∫ y in residue K, rawIntegrand K b u y
        ∂KPCubicHaar.multiplicativeHaar K dx) =
        (m : ℂ) * (1 - 2 * rawA K) := by
  have hfinite : KPCubicHaar.multiplicativeHaar K dx (residue K) ≠ ⊤ := by
    rw [residue_mass]
    have hR : R K ⊆ (𝒪[K] : Set K) := fun x hx => hx.1.le
    exact ne_top_of_le_ne_top (by rw [hvol]; exact ENNReal.ofReal_ne_top) (measure_mono hR)
  have he : Set.EqOn (rawIntegrand K b u) (fun _ => (1 : ℂ)) (residue K) :=
    fun y hy => integrand_one K b u y hy
  refine ⟨(integrableOn_const hfinite (C := (1 : ℂ))).congr_fun he.symm (residue_measurable K), ?_⟩
  rw [setIntegral_congr_fun (residue_measurable K) he, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, residue_mass,
    R_volume K dx m hm hvol, Complex.real_smul, mul_one]
  change (dx.real (R K) : ℂ) = _
  rw [R_volume K dx m hm hvol]
  simp [rawA]
end
end DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition
