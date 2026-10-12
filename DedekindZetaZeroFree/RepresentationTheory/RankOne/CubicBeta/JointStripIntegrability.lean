module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.NonarchimedeanScaling
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicUnitCharacterConductors

@[expose] public section

namespace DedekindZetaZeroFree.KPRamifiedBetaConductorSeries

open scoped Classical

open scoped ValuativeRel Topology
open MeasureTheory ValuativeRel

theorem character_norm_on_units
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (u : (𝒪[K])ˣ) :
    ‖(χ (Units.map (𝒪[K]).subtype.toMonoidHom u) : ℂ)‖ = 1 := by
  rw [hχ]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (ξ u).property

theorem character_norm_uniformizer_unit
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (π : Kˣ) (b : ℂˣ) (hb : χ π = b) (j : ℤ) (u : (𝒪[K])ˣ) :
    ‖(χ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) : ℂ)‖ =
      ‖(b : ℂ)‖ ^ j := by
  rw [map_mul, map_zpow, hb, Units.val_mul, Units.val_zpow_eq_zpow_val,
    norm_mul, character_norm_on_units K ξ χ hχ u, mul_one, norm_zpow]

open scoped WithZeroTopology in

theorem normalizedAbs_continuousAt_ne_zero
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) (hx : x ≠ 0) :
    ContinuousAt (fun y : K => if y = 0 then (0 : ℝ) else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K y))) x := by
  have hv : ValuativeRel.valuation K x ≠ 0 :=
    (Valuation.ne_zero_iff (ValuativeRel.valuation K)).mpr hx
  have he : ∀ᶠ y in 𝓝 x, ValuativeRel.valuation K y = ValuativeRel.valuation K x :=
    (WithZeroTopology.tendsto_of_ne_zero hv).mp
      (IsValuativeTopology.continuous_valuation.continuousAt :
        ContinuousAt (ValuativeRel.valuation K) x)
  apply (continuousAt_const (y := (CubicUnitCharacters.residueCard K : ℝ) ^
    WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (ValuativeRel.valuation K x)))).congr
  filter_upwards [he] with y hy
  have hy0 : y ≠ 0 := by
    intro hy0
    have := hy
    simp [hy0] at this
    exact hv this.symm
  simp only [if_neg hx, if_neg hy0, hy]

theorem normalizedAbs_measurable
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] :
    Measurable (fun y : K => if y = 0 then (0 : ℝ) else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K y))) := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  apply ContinuousOn.measurable_of_countable_compl (s := ({0} : Set K)ᶜ)
  · intro x hx
    exact (normalizedAbs_continuousAt_ne_zero K x (by simpa using hx)).continuousWithinAt
  · simp

theorem multiplicative_density_measurable
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] :
    Measurable (fun y : K => ENNReal.ofReal ((if y = 0 then (0 : ℝ) else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K y)))⁻¹)) := by
  exact (normalizedAbs_measurable K).inv.ennreal_ofReal

theorem character_norm_on_valuation_shell
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (π : Kˣ) (b : ℂˣ) (hb : χ π = b) (j : ℤ) (x : Kˣ)
    (hx : valuation K (x : K) = valuation K ((π ^ j : Kˣ) : K)) :
    ‖(χ x : ℂ)‖ = ‖(b : ℂ)‖ ^ j := by
  let y : Kˣ := x / π ^ j
  have hy : valuation K (y : K) = 1 := by
    dsimp [y]
    rw [Units.val_div_eq_div_val, map_div₀, hx]
    exact div_self ((Valuation.ne_zero_iff (valuation K)).mpr (Units.ne_zero _))
  let z : 𝒪[K] := ⟨(y : K), by simpa [Valuation.mem_integer_iff, hy]⟩
  have hz : IsUnit z := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mpr
    exact hy
  obtain ⟨u, hu⟩ := hz
  have heu : Units.map (𝒪[K]).subtype.toMonoidHom u = y := by
    apply Units.ext
    exact congrArg (fun a : 𝒪[K] => (a : K)) hu
  have he : x = π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u := by
    rw [heu]
    dsimp [y]
    rw [mul_comm, div_mul_cancel]
  rw [he]
  exact character_norm_uniformizer_unit K ξ χ hχ π b hb j u

theorem integrand_continuousOn
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (χ : Kˣ →ₜ* ℂˣ) (s : ℂ) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K x))
    ContinuousOn (fun x : K ↦ if hx : x = 0 then (0 : ℂ) else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s))
      ({0, 1} : Set K)ᶜ := by
  dsimp only
  let A : K → ℝ := fun x ↦ if x = 0 then 0 else
    (CubicUnitCharacters.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x))
  intro x hx
  have ⟨hx0, hx1⟩ : x ≠ 0 ∧ x ≠ 1 := by
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] using hx
  have hχc : ContinuousOn (fun x : K ↦ if hx : x = 0 then (0 : ℂ) else
      (χ (Units.mk0 x hx) : ℂ)) ({0} : Set K)ᶜ := by
    have he : ({0} : Set K)ᶜ = {x : K | x ≠ 0} := by ext; simp
    rw [he, continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun x : {x : K // x ≠ 0} ↦
        (χ ((unitsHomeomorphNeZero (G₀ := K)).symm x) : ℂ)) :=
      Units.continuous_val.comp (χ.continuous.comp (unitsHomeomorphNeZero (G₀ := K)).symm.continuous)
    apply hc.congr
    intro a
    have ha : (a : K) ≠ 0 := a.property
    change (χ ((unitsHomeomorphNeZero (G₀ := K)).symm a) : ℂ) =
      if h : (a : K) = 0 then 0 else (χ (Units.mk0 (a : K) h) : ℂ)
    rw [dif_neg ha]
    apply congrArg (fun t : Kˣ => ((χ t : ℂˣ) : ℂ))
    apply Units.ext
    exact congrArg Subtype.val ((unitsHomeomorphNeZero (G₀ := K)).apply_symm_apply a)
  have hAc : ContinuousAt A (1 - x) :=
    normalizedAbs_continuousAt_ne_zero K (1 - x) (sub_ne_zero.mpr hx1.symm)
  have hApos : 0 < A (1 - x) := by
    dsimp [A]
    rw [if_neg (sub_ne_zero.mpr hx1.symm)]
    apply zpow_pos
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K])).trans_le' (by decide)
  have hc : ContinuousWithinAt (fun y : K => (A (1-y) : ℂ) ^ (-s)) ({0, 1} : Set K)ᶜ x := by
    apply ((Complex.continuous_ofReal.continuousAt.comp
      (hAc.comp (continuousAt_const.sub continuousAt_id))).cpow continuousAt_const ?_).continuousWithinAt
    exact Complex.ofReal_mem_slitPlane.mpr hApos
  have hh := (hχc x (by simpa using hx0)).mono (show ({0, 1} : Set K)ᶜ ⊆ {0}ᶜ by
    simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]; tauto) |>.mul hc
  have heq : (fun y : K => (if hy : y = 0 then (0 : ℂ) else
      (χ (Units.mk0 y hy) : ℂ)) * (A (1-y) : ℂ)^(-s)) =
      (fun y : K => if hy : y = 0 then (0 : ℂ) else
        (χ (Units.mk0 y hy) : ℂ) * (A (1-y) : ℂ)^(-s)) := by
    funext y
    by_cases hy : y = 0 <;> simp [hy]
  change ContinuousWithinAt (fun y : K => if hy : y = 0 then (0 : ℂ) else
        (χ (Units.mk0 y hy) : ℂ) * (A (1-y) : ℂ)^(-s)) ({0, 1} : Set K)ᶜ x
  rw [← heq]
  exact hh

theorem normalizedAbs_pos
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) (hx : x ≠ 0) :
    0 < (if x = 0 then (0 : ℝ) else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))) := by
  rw [if_neg hx]
  apply zpow_pos
  exact_mod_cast (Finite.one_lt_card (α := 𝓀[K])).trans_le' (by decide)

theorem integrand_measurable
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (χ : Kˣ →ₜ* ℂˣ) (s : ℂ) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K x))
    Measurable (fun x : K ↦ if hx : x = 0 then (0 : ℂ) else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)) := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  apply ContinuousOn.measurable_of_countable_compl (s := ({0, 1} : Set K)ᶜ)
  · exact integrand_continuousOn K χ s
  · simp

theorem integrableOn_shell_union_of_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (hf : AEStronglyMeasurable f μ)
    (shell : ℕ → Set X) (hm : ∀ j, MeasurableSet (shell j))
    (hfinite : ∀ j, μ (shell j) ≠ ⊤)
    (bound : ℕ → ℝ) (hbound : ∀ j, 0 ≤ bound j)
    (hdom : ∀ j, ∀ x ∈ shell j, ‖f x‖ ≤ bound j)
    (hsum : Summable (fun j => μ.real (shell j) * bound j)) :
    IntegrableOn f (⋃ j, shell j) μ := by
  have hi : ∀ j, IntegrableOn f (shell j) μ := by
    intro j
    apply (integrableOn_const (hfinite j) (C := bound j)).mono'
      (hf.restrict)
    exact (ae_restrict_mem (hm j)).mono (fun x hx => hdom j x hx)
  apply integrableOn_iUnion_of_summable_integral_norm hi
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun x => norm_nonneg _))
    (fun j => ?_) hsum
  calc
    (∫ x in shell j, ‖f x‖ ∂μ) ≤ ∫ _ in shell j, bound j ∂μ :=
      integral_mono_ae (hi j).norm (integrableOn_const (hfinite j))
        ((ae_restrict_mem (hm j)).mono (fun x hx => hdom j x hx))
    _ = μ.real (shell j) * bound j := by simp

theorem uniformizer_value_exponent
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (uniformizer K) =
      WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (uniformizer K) = _
  apply le_antisymm
  · have hlt : e (uniformizer K) < 1 := by
      simpa using e.strictMono (uniformizer_lt_one (R := K))
    have hlog : WithZero.log (e (uniformizer K)) < (0 : ℤ) :=
      (WithZero.log_lt_iff_lt_exp (by simp [e, uniformizer_ne_zero])).mpr
        (by simpa using hlt)
    apply WithZero.le_exp_of_log_le
    omega
  · have hsmall : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hlt : e.symm (WithZero.exp (-1 : ℤ)) < 1 := by
      simpa using e.symm.strictMono hsmall
    have hle := le_uniformizer_iff.mpr hlt
    simpa using e.strictMono.monotone hle

theorem character_norm_on_log_shell
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (b : ℂˣ) (hb : χ π = b) (x : Kˣ) (k : ℤ)
    (hx : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (x : K))) = k) :
    ‖(χ x : ℂ)‖ = ‖(b : ℂ)‖ ^ (-k) := by
  apply character_norm_on_valuation_shell K ξ χ hχ π b hb (-k) x
  apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, hπ]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)) =
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (uniformizer K)) ^ (-k)
  rw [uniformizer_value_exponent]
  rw [← WithZero.exp_log (show IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (valuation K (x : K)) ≠ 0 by simp), hx,
    ← WithZero.exp_log (show WithZero.exp (-1 : ℤ) ^ (-k) ≠ 0 by simp),
    WithZero.log_zpow, WithZero.log_exp]
  simp

theorem character_norm_on_abs_shell
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (b : ℂˣ) (hb : χ π = b) (x : K) (hx0 : x ≠ 0) (k : ℤ)
    (hx : (if x = 0 then (0 : ℝ) else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K x))) = (CubicUnitCharacters.residueCard K : ℝ) ^ k) :
    ‖(χ (Units.mk0 x hx0) : ℂ)‖ = ‖(b : ℂ)‖ ^ (-k) := by
  apply character_norm_on_log_shell K ξ χ hχ π hπ b hb (Units.mk0 x hx0) k
  rw [if_neg hx0] at hx
  exact (zpow_right_strictMono₀ (show (1 : ℝ) < CubicUnitCharacters.residueCard K by
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K])))).injective hx

theorem normalized_shell_mass_bound
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (k : ℤ) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K x))
    μ {x | A x = (CubicUnitCharacters.residueCard K : ℝ) ^ k} ≠ ⊤ ∧
      μ.real {x | A x = (CubicUnitCharacters.residueCard K : ℝ) ^ k} ≤
        (CubicUnitCharacters.residueCard K : ℝ) ^ k * μ.real (𝒪[K] : Set K) := by
  dsimp only
  let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K x))
  let q : ℝ := CubicUnitCharacters.residueCard K
  have hmass : μ {x | A x ≤ q ^ k} = ENNReal.ofReal (q ^ k) * μ (𝒪[K] : Set K) :=
    NonarchimedeanHaarScaling.closedBall_measure K μ k
  have hO : μ (𝒪[K] : Set K) ≠ ⊤ := by
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
  have hfinite : μ {x | A x ≤ q ^ k} ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO
  have hsub : {x | A x = q ^ k} ⊆ {x | A x ≤ q ^ k} :=
    fun x hx => le_of_eq hx
  refine ⟨ne_top_of_le_ne_top hfinite (measure_mono hsub), ?_⟩
  calc
    μ.real {x | A x = q ^ k} ≤ μ.real {x | A x ≤ q ^ k} := measureReal_mono hsub hfinite
    _ = q ^ k * μ.real (𝒪[K] : Set K) := by
      rw [Measure.real, hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
      · rfl
      · have hq : 1 < q := by
          dsimp [q, CubicUnitCharacters.residueCard]
          exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
        exact (zpow_pos (lt_trans zero_lt_one hq) k).le

theorem weighted_integrand_norm
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (χ : Kˣ →ₜ* ℂˣ)
    (s : ℂ) (hs : 0 < s.re) (x : K) (hx : x ≠ 0) :
    let A : K → ℝ := fun y ↦ if y = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K y))
    let I : K → ℂ := fun y ↦ if hy : y = 0 then 0 else
      (χ (Units.mk0 y hy) : ℂ) * (A (1-y) : ℂ) ^ (-s)
    ‖(A x)⁻¹ • I x‖ =
      (A x)⁻¹ * ‖(χ (Units.mk0 x hx) : ℂ)‖ * (A (1-x)).rpow (-s.re) := by
  dsimp only
  let A : K → ℝ := fun y ↦ if y = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (valuation K y))
  have hA : ∀ y, 0 ≤ A y := by
    intro y
    dsimp [A]
    split_ifs
    · exact le_rfl
    · exact (zpow_pos (show (0 : ℝ) < CubicUnitCharacters.residueCard K by
        exact_mod_cast (Finite.one_lt_card (α := 𝓀[K])).trans_le' (by decide)) _).le
  change ‖(A x)⁻¹ • (if hy : x = 0 then 0 else
    (χ (Units.mk0 x hy) : ℂ) * (A (1-x) : ℂ)^(-s))‖ = _
  rw [dif_neg hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hA x)),
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (hA (1-x))
      (show (-s).re ≠ 0 by simp; linarith)]
  simp only [Complex.neg_re]
  exact (mul_assoc _ _ _).symm

theorem multiplicative_shell_mass_le
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (k : ℤ) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
    ν {x | A x = (CubicUnitCharacters.residueCard K : ℝ) ^ k} ≤
      μ ((ValuativeRel.valuation K).integer : Set K) := by
  dsimp only
  let A : K → ℝ := fun x ↦ if x = 0 then 0 else
    (CubicUnitCharacters.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K x))
  let r : ℝ := (CubicUnitCharacters.residueCard K : ℝ) ^ k
  have hr : 0 < r := by
    apply zpow_pos
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K])).trans_le' (by decide)
  have hA : Measurable A := normalizedAbs_measurable K
  have hs : MeasurableSet {x | A x = r} := hA (measurableSet_singleton r)
  change (μ.withDensity (fun x => ENNReal.ofReal ((A x)⁻¹))) {x | A x = r} ≤ _
  rw [withDensity_apply _ hs]
  have heq : (∫⁻ x in {x | A x = r}, ENNReal.ofReal ((A x)⁻¹) ∂μ) =
      ENNReal.ofReal r⁻¹ * μ {x | A x = r} := by
    calc
      _ = ∫⁻ x in {x | A x = r}, ENNReal.ofReal r⁻¹ ∂μ := by
        apply setLIntegral_congr_fun hs
        intro x hx
        dsimp only
        rw [show A x = r from hx]
      _ = _ := by simp
  rw [heq]
  have hm : μ {x | A x = r} ≤ ENNReal.ofReal r * μ ((ValuativeRel.valuation K).integer : Set K) := by
    calc
      _ ≤ μ {x | A x ≤ r} := measure_mono (by intro x hx; exact hx.le)
      _ = _ := NonarchimedeanHaarScaling.closedBall_measure K μ k
  calc
    _ ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal r * μ ((ValuativeRel.valuation K).integer : Set K)) := by gcongr
    _ = _ := by
      rw [← mul_assoc, ENNReal.ofReal_inv_of_pos hr,
        ENNReal.inv_mul_cancel (by exact (ENNReal.ofReal_pos.mpr hr).ne') ENNReal.ofReal_ne_top, one_mul]

private theorem abs_lt_valuation
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x y : K} (hy : y ≠ 0) :
    KPCubicHaar.abs K x < KPCubicHaar.abs K y ↔ valuation K x < valuation K y := by
  have hq : (1 : ℝ) < CubicUnitCharacters.residueCard K := by
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  by_cases hx : x = 0
  · subst x
    apply iff_of_true
    · change (if (0 : K) = 0 then (0 : ℝ) else _) <
        (if y = 0 then (0 : ℝ) else (CubicUnitCharacters.residueCard K : ℝ) ^ _)
      rw [if_pos rfl]
      exact normalizedAbs_pos K y hy
    · exact ((Valuation.ne_zero_iff _).mpr hy).bot_lt
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hex : e (valuation K x) ≠ 0 := by simp [e, hx]
  have hey : e (valuation K y) ≠ 0 := by simp [e, hy]
  change (if x = 0 then (0 : ℝ) else _ ^ WithZero.log (e (valuation K x))) <
    (if y = 0 then (0 : ℝ) else _ ^ WithZero.log (e (valuation K y))) ↔ _
  rw [if_neg hx, if_neg hy]
  change (CubicUnitCharacters.residueCard K : ℝ) ^ _ <
    (CubicUnitCharacters.residueCard K : ℝ) ^ _ ↔ _
  rw [zpow_lt_zpow_iff_right₀ hq]
  rw [← e.toOrderIso.lt_iff_lt]
  change WithZero.log (e (valuation K x)) < WithZero.log (e (valuation K y)) ↔
    e (valuation K x) < e (valuation K y)
  conv_rhs => rw [← WithZero.exp_log hex, ← WithZero.exp_log hey]
  exact WithZero.exp_lt_exp.symm

private theorem abs_eq_of_val_eq
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x y : K}
    (h : valuation K x = valuation K y) : KPCubicHaar.abs K x = KPCubicHaar.abs K y := by
  have he : x = 0 ↔ y = 0 := by
    rw [← (Valuation.zero_iff (valuation K)), ← (Valuation.zero_iff (valuation K)), h]
  simp only [KPCubicHaar.abs, he, h]

private theorem shell_geometric_integrable
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (hf : AEStronglyMeasurable f μ)
    (S : ℕ → Set X) (hm : ∀ j, MeasurableSet (S j))
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (M t : ℝ) (hM : 0 ≤ M)
    (ht : 0 ≤ t) (ht1 : t < 1)
    (hmass : ∀ j, μ (S j) ≠ ⊤ ∧ μ.real (S j) ≤ r j * M)
    (hbound : ∀ j, ∀ x ∈ S j, ‖f x‖ ≤ t ^ j / r j) :
    IntegrableOn f (⋃ j, S j) μ := by
  apply integrableOn_shell_union_of_bounds μ f hf S hm (fun j => (hmass j).1)
    (fun j => t ^ j / r j) (fun j => div_nonneg (pow_nonneg ht _) (hr j).le) hbound
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (measureReal_nonneg)
      (div_nonneg (pow_nonneg ht _) (hr j).le))
    (fun j => ?_) ((summable_geometric_of_lt_one ht ht1).mul_left M)
  calc
    μ.real (S j) * (t ^ j / r j) ≤ (r j * M) * (t ^ j / r j) := by
      exact mul_le_mul_of_nonneg_right (hmass j).2
        (div_nonneg (pow_nonneg ht _) (hr j).le)
    _ = M * t ^ j := by field_simp [(hr j).ne']

theorem integrable_in_joint_strip
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (π : Kˣ) (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K)
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (b : ℂˣ) (hb : χ π = b)
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hbs : (CubicUnitCharacters.residueCard K : ℝ).rpow (-s.re) < ‖(b : ℂ)‖)
    (hb1 : ‖(b : ℂ)‖ < 1) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))
    let I : K → ℂ := fun x ↦ if hx : x = 0 then 0 else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
    Integrable I ν := by
  dsimp only
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let A : K → ℝ := KPCubicHaar.abs K
  let I : K → ℂ := fun x => if hx : x = 0 then 0 else
    (χ (Units.mk0 x hx) : ℂ) * (A (1-x) : ℂ) ^ (-s)
  let W : K → ℂ := fun x => (A x)⁻¹ • I x
  let q : ℝ := CubicUnitCharacters.residueCard K
  let B : ℝ := ‖(b : ℂ)‖
  let M : ℝ := μ.real (𝒪[K] : Set K)
  have hq : 1 < q := by
    dsimp [q, CubicUnitCharacters.residueCard]
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hB : 0 < B := norm_pos_iff.mpr (Units.ne_zero b)
  have hA : Measurable A := normalizedAbs_measurable K
  have hA0 : A 0 = 0 := by simp [A, KPCubicHaar.abs]
  have hA1 : A 1 = 1 := by simp [A, KPCubicHaar.abs]
  have hAp : ∀ x, 0 ≤ A x := by
    intro x
    by_cases hx : x = 0
    · simp [hx, hA0]
    · exact (normalizedAbs_pos K x hx).le
  have hW : AEStronglyMeasurable W μ :=
    (hA.inv.smul (integrand_measurable K χ s)).aestronglyMeasurable
  have hnorm (x : K) (hx : x ≠ 0) :
      ‖W x‖ = (A x)⁻¹ * ‖(χ (Units.mk0 x hx) : ℂ)‖ * (A (1-x)).rpow (-s.re) :=
    weighted_integrand_norm K χ s hs0 x hx
  have hchar (x : K) (hx : x ≠ 0) (k : ℤ) (hk : A x = q ^ k) :
      ‖(χ (Units.mk0 x hx) : ℂ)‖ = B ^ (-k) :=
    character_norm_on_abs_shell K ξ χ hχ π hπ b hb x hx k hk
  let S₀ : ℕ → Set K := fun n => {x | A x = q ^ (-(n : ℤ)) ∧ A (1-x) = 1}
  let Sinf : ℕ → Set K := fun n => {x | A x = q ^ (n : ℤ) ∧ A (1-x) = A x}
  let S₁ : ℕ → Set K := fun n => {x | A (1-x) = q ^ (-(n : ℤ)) ∧ A x = 1}
  have hm₀ (n) : MeasurableSet (S₀ n) :=
    (hA (measurableSet_singleton _)).inter
      ((hA.comp ((continuous_const.sub continuous_id).measurable)) (measurableSet_singleton _))
  have hmInf (n) : MeasurableSet (Sinf n) :=
    (hA (measurableSet_singleton _)).inter
      (measurableSet_eq_fun (hA.comp ((continuous_const.sub continuous_id).measurable)) hA)
  have hm₁ (n) : MeasurableSet (S₁ n) :=
    ((hA.comp ((continuous_const.sub continuous_id).measurable)) (measurableSet_singleton _)).inter
      (hA (measurableSet_singleton _))
  have mass (k : ℤ) (S : Set K) (hS : S ⊆ {x | A x = q ^ k}) :
      μ S ≠ ⊤ ∧ μ.real S ≤ q ^ k * M := by
    obtain ⟨hf, hb⟩ := normalized_shell_mass_bound K μ k
    exact ⟨ne_top_of_le_ne_top hf (measure_mono hS),
      (measureReal_mono hS hf).trans hb⟩
  have mass₁ (n : ℕ) : μ (S₁ n) ≠ ⊤ ∧ μ.real (S₁ n) ≤ q ^ (-(n : ℤ)) * M := by
    let T : Set K := {x | A x = q ^ (-(n : ℤ))}
    have hT : MeasurableSet T := hA (measurableSet_singleton _)
    have he : μ ((fun x : K => x-1) ⁻¹' T) = μ T :=
      by simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right μ (-1)).measure_preimage hT.nullMeasurableSet
    have hsub : S₁ n ⊆ (fun x : K => x-1) ⁻¹' T := by
      intro x hx
      change A (x-1) = _
      rw [show A (x-1) = A (1-x) from abs_eq_of_val_eq K ((valuation K).map_sub_swap x 1)]
      exact hx.1
    obtain ⟨hf, hb⟩ := normalized_shell_mass_bound K μ (-(n : ℤ))
    have hfinite : μ ((fun x : K => x-1) ⁻¹' T) ≠ ⊤ := by rw [he]; exact hf
    refine ⟨ne_top_of_le_ne_top hfinite (measure_mono hsub), ?_⟩
    apply (measureReal_mono hsub hfinite).trans
    change (μ ((fun x : K => x-1) ⁻¹' T)).toReal ≤ _
    rw [he]
    exact hb
  have hi₀ : IntegrableOn W (⋃ n, S₀ n) μ := by
    apply shell_geometric_integrable μ W hW S₀ hm₀
      (fun n => q ^ (-(n : ℤ))) (fun n => zpow_pos hq0 _) M B
      measureReal_nonneg hB.le hb1
      (fun n => mass _ _ (fun x hx => hx.1))
    intro n x hx
    have hx0 : x ≠ 0 := by intro he; have hz := hx.1; rw [he, hA0] at hz; exact (zpow_ne_zero _ hq0.ne') hz.symm
    rw [hnorm x hx0, hchar x hx0 _ hx.1, hx.1, hx.2]
    simp only [neg_neg, zpow_natCast, Real.one_rpow, mul_one]
    exact le_of_eq (by simp [div_eq_mul_inv, mul_comm])
  have hiInf : IntegrableOn W (⋃ n, Sinf n) μ := by
    apply shell_geometric_integrable μ W hW Sinf hmInf
      (fun n => q ^ (n : ℤ)) (fun n => zpow_pos hq0 _) M (q.rpow (-s.re) / B)
      measureReal_nonneg (div_nonneg (Real.rpow_nonneg hq0.le _) hB.le)
      ((div_lt_one hB).mpr hbs)
      (fun n => mass _ _ (fun x hx => hx.1))
    intro n x hx
    have hx0 : x ≠ 0 := by intro he; have hz := hx.1; rw [he, hA0] at hz; exact (zpow_ne_zero _ hq0.ne') hz.symm
    rw [hnorm x hx0, hchar x hx0 _ hx.1, hx.2, hx.1]
    have hr : (q ^ (n : ℤ)).rpow (-s.re) = (q.rpow (-s.re)) ^ (n : ℤ) :=
      (Real.rpow_zpow_comm hq0.le (-s.re) (n : ℤ)).symm
    rw [hr, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, div_pow]
    exact le_of_eq (by simp only [div_eq_mul_inv]; ring)
  have hi₁ : IntegrableOn W (⋃ n, S₁ n) μ := by
    apply shell_geometric_integrable μ W hW S₁ hm₁
      (fun n => q ^ (-(n : ℤ))) (fun n => zpow_pos hq0 _) M (q.rpow (s.re-1))
      measureReal_nonneg (Real.rpow_nonneg hq0.le _)
      (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)) mass₁
    intro n x hx
    have hx0 : x ≠ 0 := by intro he; simpa [he, hA0] using hx.2
    have hc : ‖(χ (Units.mk0 x hx0) : ℂ)‖ = 1 := by
      simpa using hchar x hx0 0 (by simpa using hx.2)
    rw [hnorm x hx0, hc, hx.2, hx.1]
    simp only [inv_one, one_mul]
    have hr : (q ^ (-(n : ℤ))).rpow (-s.re) = (q.rpow (-s.re)) ^ (-(n : ℤ)) :=
      (Real.rpow_zpow_comm hq0.le (-s.re) (-(n : ℤ))).symm
    rw [hr, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    have he : q.rpow (s.re - 1) / q⁻¹ = (q.rpow (-s.re))⁻¹ := by
      have hn : q.rpow (-s.re) = (q.rpow s.re)⁻¹ := Real.rpow_neg hq0.le s.re
      have hs : q.rpow (s.re-1) = q.rpow s.re / q := Real.rpow_sub_one hq0.ne' s.re
      rw [hn, hs, inv_inv]
      field_simp
    rw [← inv_pow q, ← div_pow, he, inv_pow]
  have hi : IntegrableOn W ((⋃ n, S₀ n) ∪ (⋃ n, Sinf n) ∪ (⋃ n, S₁ n)) μ :=
    (integrableOn_union.mpr ⟨integrableOn_union.mpr ⟨hi₀, hiInf⟩, hi₁⟩)
  have hcover : ∀ x, x ≠ 0 → x ≠ 1 →
      x ∈ ((⋃ n, S₀ n) ∪ (⋃ n, Sinf n) ∪ (⋃ n, S₁ n)) := by
    intro x hx0 hx1
    have hex (y : K) (hy : y ≠ 0) : ∃ k : ℤ, A y = q ^ k := by
      exact ⟨WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (valuation K y)), by change (if y = 0 then (0 : ℝ) else _) = _; rw [if_neg hy]; rfl⟩
    have low (y : K) (hy : y ≠ 0) (hyl : A y ≤ 1) :
        ∃ n : ℕ, A y = q ^ (-(n : ℤ)) := by
      obtain ⟨k, hk⟩ := hex y hy
      have hk0 : k ≤ 0 := by
        apply (zpow_right_strictMono₀ hq).le_iff_le.mp
        simpa only [zpow_zero] using hk.symm ▸ hyl
      refine ⟨(-k).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
      exact hk
    rcases lt_trichotomy (A x) 1 with hlt | heq | hgt
    · have hv : valuation K x < valuation K 1 :=
        (abs_lt_valuation K one_ne_zero).mp (by change A x < A 1; rw [hA1]; exact hlt)
      have hother : A (1-x) = 1 := by
        rw [show A (1-x) = A 1 from
          abs_eq_of_val_eq K ((valuation K).map_sub_eq_of_lt_left hv), hA1]
      obtain ⟨n, hn⟩ := low x hx0 hlt.le
      exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨n, ⟨hn, hother⟩⟩))
    · have hother : A (1-x) ≤ 1 := by
        by_contra hn
        have hv : valuation K 1 < valuation K (1-x) :=
          (abs_lt_valuation K (sub_ne_zero.mpr hx1.symm)).mp
            (by change A 1 < A (1-x); rw [hA1]; exact lt_of_not_ge hn)
        have he : A (1-(1-x)) = A (1-x) :=
          abs_eq_of_val_eq K ((valuation K).map_sub_eq_of_lt_right hv)
        have he' : A (1-x) = 1 := by simpa only [sub_sub_cancel, heq] using he.symm
        exact hn he'.le
      obtain ⟨n, hn⟩ := low (1-x) (sub_ne_zero.mpr hx1.symm) hother
      exact Or.inr (Set.mem_iUnion.mpr ⟨n, ⟨hn, heq⟩⟩)
    · have hv : valuation K 1 < valuation K x :=
        (abs_lt_valuation K hx0).mp (by change A 1 < A x; rw [hA1]; exact hgt)
      have hother : A (1-x) = A x :=
        abs_eq_of_val_eq K ((valuation K).map_sub_eq_of_lt_right hv)
      obtain ⟨k, hk⟩ := hex x hx0
      have hk0 : 0 ≤ k := by
        apply (zpow_right_strictMono₀ hq).le_iff_le.mp
        simpa only [zpow_zero] using hk ▸ hgt.le
      refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k.toNat, ?_⟩))
      exact ⟨by rw [Int.toNat_of_nonneg hk0]; exact hk, hother⟩
  have hWI : Integrable W μ := hi.integrable_of_forall_notMem_eq_zero (by
    intro x hx
    by_cases hx0 : x = 0
    · simp [W, I, hx0]
    by_cases hx1 : x = 1
    · subst x
      have hsne : s ≠ 0 := by intro he; simp [he] at hs0
      simp [W, I, A, KPCubicHaar.abs, Complex.zero_cpow (neg_ne_zero.mpr hsne), hsne]
    · exact False.elim (hx (hcover x hx0 hx1)))
  apply (integrable_withDensity_iff_integrable_smul' (multiplicative_density_measurable K)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).mpr
  convert hWI using 1
  funext x
  change (ENNReal.ofReal ((A x)⁻¹)).toReal • I x = (A x)⁻¹ • I x
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (hAp x))]

end DedekindZetaZeroFree.KPRamifiedBetaConductorSeries
