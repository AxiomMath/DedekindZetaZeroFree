module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicUnitCharacterExtension
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CubicBeta.JointStripIntegrability

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCubicFamilyResolution

open scoped ValuativeRel
open ValuativeRel

 noncomputable def exponent (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (-WithZero.log
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x)))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (by simp) (by simp)]
    simp [add_comm]

private lemma exponent_eq_one_iff (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Kˣ) :
    exponent K x = 1 ↔ valuation K (x : K) = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change Multiplicative.ofAdd (-WithZero.log (e (valuation K (x : K)))) = 1 ↔ _
  constructor
  · intro h
    have hlog : WithZero.log (e (valuation K (x : K))) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    have he : e (valuation K (x : K)) = 1 := by
      rw [← WithZero.exp_log (show e (valuation K (x : K)) ≠ 0 by simp [e]), hlog]
      exact WithZero.exp_zero
    exact e.injective (by simpa using he)
  · intro h
    simp [h]

private lemma exponent_uniformizer (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (π : Kˣ)
    (hπ : valuation K (π : K) = uniformizer K) :
    exponent K π = Multiplicative.ofAdd 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have he : e (uniformizer K) = WithZero.exp (-1) := by
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
  change Multiplicative.ofAdd (-WithZero.log (e (valuation K (π : K)))) = _
  rw [hπ, he, WithZero.log_exp]
  rfl

 noncomputable def coordinateMap (K : Type*) [Field K] [ValuativeRel K]
    (π : Kˣ) : Multiplicative ℤ × (𝒪[K])ˣ →* Kˣ where
  toFun p := π ^ p.1.toAdd * Units.map (𝒪[K]).subtype.toMonoidHom p.2
  map_one' := by simp
  map_mul' p q := by
    dsimp
    rw [zpow_add, map_mul]
    ac_rfl

private lemma coordinateMap_bijective (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (π : Kˣ)
    (hπ : valuation K (π : K) = uniformizer K) :
    Function.Bijective (coordinateMap K π) := by
  let m := Units.map (𝒪[K]).subtype.toMonoidHom
  have hm (u : (𝒪[K])ˣ) : exponent K (m u) = 1 := by
    apply (exponent_eq_one_iff K _).mpr
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
  have hν (p : Multiplicative ℤ × (𝒪[K])ˣ) :
      exponent K (coordinateMap K π p) = p.1 := by
    change exponent K (π ^ p.1.toAdd * m p.2) = _
    rw [map_mul, map_zpow, exponent_uniformizer K π hπ, hm, mul_one]
    apply Multiplicative.toAdd.injective
    change p.1.toAdd * 1 = p.1.toAdd
    simp
  constructor
  · intro p q hpq
    have h1 : p.1 = q.1 := by simpa only [hν] using congrArg (exponent K) hpq
    apply Prod.ext h1
    have hu : m p.2 = m q.2 := by
      apply mul_left_cancel (a := π ^ p.1.toAdd)
      simpa only [coordinateMap, MonoidHom.coe_mk, OneHom.coe_mk, h1] using hpq
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hu
  · intro x
    let n := exponent K x
    let y := π ^ (-n.toAdd) * x
    have hy : exponent K y = 1 := by
      dsimp [y]
      rw [map_mul, map_zpow, exponent_uniformizer K π hπ]
      change Multiplicative.ofAdd (-n.toAdd * 1 + n.toAdd) = 1
      simp
    have hv := (exponent_eq_one_iff K y).mp hy
    let a : 𝒪[K] := ⟨(y : K), hv.le⟩
    have ha : IsUnit a := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mpr hv
    obtain ⟨u, hu⟩ := ha
    have hum : m u = y := by
      apply Units.ext
      exact congrArg Subtype.val hu
    refine ⟨(n, u), ?_⟩
    change π ^ n.toAdd * m u = x
    rw [hum]
    dsimp [y]
    rw [← mul_assoc, ← zpow_add]
    simp

private lemma cube_coordinate_iff (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (π : Kˣ)
    (hπ : valuation K (π : K) = uniformizer K) (j : ℤ) (u : (𝒪[K])ˣ) :
    π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u ∈
      (powMonoidHom (α := Kˣ) 3).range ↔
      (3 : ℤ) ∣ j ∧ u ∈ KPCubicUnitIndices.cubeUnits K := by
  let f := coordinateMap K π
  have hf := coordinateMap_bijective K π hπ
  change f (Multiplicative.ofAdd j, u) ∈ (powMonoidHom (α := Kˣ) 3).range ↔ _
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hf.2 y
    have hp : p ^ 3 = (Multiplicative.ofAdd j, u) :=
      hf.1 ((map_pow f p 3).trans hy)
    have hj := congrArg (fun q : Multiplicative ℤ × (𝒪[K])ˣ => q.1.toAdd) hp
    have hu := congrArg Prod.snd hp
    refine ⟨?_, p.2, hu⟩
    change (3 : ℤ) ∣ j
    change 3 * p.1.toAdd = j at hj
    rw [← hj]
    exact dvd_mul_right _ _
  · rintro ⟨⟨n, hn⟩, w, hw⟩
    refine ⟨f (Multiplicative.ofAdd n, w), ?_⟩
    change f (Multiplicative.ofAdd n, w) ^ 3 = _
    rw [← map_pow]
    apply congrArg f
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      exact hn.symm
    · exact hw

open scoped Classical in

theorem cubic_family_resolution
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (t z : ℂˣ) (hz : z ^ 3 = t) (Ω : Kˣ → ℂ)
    (hΩ : ∀ (j : ℤ) (u : (𝒪[K])ˣ),
      Ω (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) = ((t ^ j : ℂˣ) : ℂ))
    (χ : CubicUnitCharacters.Character K → CubicCharacters.Mu3 → (Kˣ →ₜ* ℂˣ))
    (hχ : ∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3)
      (j : ℤ) (u : (𝒪[K])ˣ),
      χ ξ ζ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) =
        ((ζ : ℂˣ) * z) ^ j * (ξ u : ℂˣ))
    (hsum : ∀ (j : ℤ) (u : (𝒪[K])ˣ),
      (1 / 3 : ℂ) * (∑ᶠ ξ : CubicUnitCharacters.Character K,
        ∑ᶠ ζ : CubicCharacters.Mu3,
          (χ ξ ζ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) : ℂ)) =
        if (3 : ℤ) ∣ j ∧ u ∈ KPCubicUnitIndices.cubeUnits K then
          (((powMonoidHom (α := Kˣ) 3).range.index : ℂ) / 3) * ((z ^ j : ℂˣ) : ℂ)
        else 0) :
    (∀ y : Kˣ, Ω y = (χ 1 1 (y ^ 3) : ℂ)) ∧
    (∀ v : Kˣ,
      (1 / 3 : ℂ) * (∑ᶠ ξ : CubicUnitCharacters.Character K,
        ∑ᶠ ζ : CubicCharacters.Mu3, (χ ξ ζ v : ℂ)) =
      (((powMonoidHom (α := Kˣ) 3).range.index : ℂ) / 3) *
        Set.indicator ((powMonoidHom (α := Kˣ) 3).range : Set Kˣ)
          (fun v : Kˣ => (χ 1 1 v : ℂ)) v) := by
  classical
  have hf := coordinateMap_bijective K π hπ
  have hone (j : ℤ) (u : (𝒪[K])ˣ) :
      χ 1 1 (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) = z ^ j := by
    simpa using hχ 1 1 j u
  constructor
  · intro y
    obtain ⟨⟨n, u⟩, rfl⟩ := hf.2 y
    change Ω (π ^ n.toAdd * Units.map (𝒪[K]).subtype.toMonoidHom u) = _
    rw [hΩ]
    have hc : (coordinateMap K π (n, u)) ^ 3 =
        π ^ (n.toAdd * 3) * Units.map (𝒪[K]).subtype.toMonoidHom (u ^ 3) := by
      simp only [coordinateMap, MonoidHom.coe_mk, OneHom.coe_mk, mul_pow, map_pow]
      rw [← zpow_natCast, ← zpow_mul]
      rfl
    rw [hc, hone]
    congr 1
    rw [← hz, ← zpow_natCast, ← zpow_mul]
    congr 1
    omega
  · intro v
    obtain ⟨⟨n, u⟩, rfl⟩ := hf.2 v
    change (1 / 3 : ℂ) * (∑ᶠ ξ : CubicUnitCharacters.Character K,
      ∑ᶠ ζ : CubicCharacters.Mu3,
        (χ ξ ζ (π ^ n.toAdd * Units.map (𝒪[K]).subtype.toMonoidHom u) : ℂ)) = _
    dsimp only [coordinateMap, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hsum]
    by_cases h : (3 : ℤ) ∣ n.toAdd ∧ u ∈ KPCubicUnitIndices.cubeUnits K
    · have hv := (cube_coordinate_iff K π hπ n.toAdd u).mpr h
      rw [if_pos h, Set.indicator_of_mem hv]
      rw [hone]
    · have hv := mt (cube_coordinate_iff K π hπ n.toAdd u).mp h
      rw [if_neg h, Set.indicator_of_notMem hv, mul_zero]

end DedekindZetaZeroFree.KPCubicFamilyResolution

end

section

namespace DedekindZetaZeroFree.KPCubicFamilyResolution

open scoped ValuativeRel
open MeasureTheory ValuativeRel

theorem integrate_cube_resolution
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (κ : 𝒪[K]) (hκ : IsPrimitiveRoot κ 3)
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (I J : Type*) [Finite I] [Finite J]
    (χ : I → J → (Kˣ →ₜ* ℂˣ)) (ψ : Kˣ →ₜ* ℂˣ)
    (Ω : Kˣ → ℂ) (hΩ : ∀ y : Kˣ, Ω y = (ψ (y ^ 3) : ℂ))
    (a : ℂ)
    (hresolution : ∀ v : Kˣ,
      a * (∑ᶠ i : I, ∑ᶠ j : J, (χ i j v : ℂ)) =
        (((powMonoidHom (α := Kˣ) 3).range.index : ℂ) / 3) *
          Set.indicator ((powMonoidHom (α := Kˣ) 3).range : Set Kˣ)
            (fun v : Kˣ => (ψ v : ℂ)) v)
    (F : Kˣ → ℂ)
    (hF : Integrable (fun y : Kˣ => Ω y * F (y ^ 3))
      (KPCubicHaar.multiplicativeHaar K dx))
    (hχF : ∀ (i : I) (j : J),
      Integrable (fun v : Kˣ => (χ i j v : ℂ) * F v)
        (KPCubicHaar.multiplicativeHaar K dx)) :
    (∫ y : Kˣ, Ω y * F (y ^ 3) ∂KPCubicHaar.multiplicativeHaar K dx) =
      a * ∑ᶠ i : I, ∑ᶠ j : J,
        ∫ v : Kˣ, (χ i j v : ℂ) * F v ∂KPCubicHaar.multiplicativeHaar K dx := by
  classical
  letI := Fintype.ofFinite I
  letI := Fintype.ofFinite J
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [@BorelSpace.measurable_eq K _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  let μ := KPCubicHaar.multiplicativeHaar K dx
  let H := (powMonoidHom (α := Kˣ) 3).range
  let c : ℂ := (H.index : ℂ) / 3
  haveI : H.FiniteIndex := KPCubicHaar.fieldCubes_finiteIndex K
  have hc : c ≠ 0 := div_ne_zero (by
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := H))) (by norm_num)
  simp only [finsum_eq_sum_of_fintype] at hresolution ⊢
  have hcont : Continuous (fun v : Kˣ => a * ∑ i : I, ∑ j : J, (χ i j v : ℂ)) := by
    exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => Units.continuous_val.comp (χ i j).continuous)
  have hH : MeasurableSet (H : Set Kˣ) := by
    have he : (H : Set Kˣ) = {v : Kˣ | a * ∑ i : I, ∑ j : J, (χ i j v : ℂ) ≠ 0} := by
      ext v
      change v ∈ H ↔ a * ∑ i : I, ∑ j : J, (χ i j v : ℂ) ≠ 0
      rw [hresolution v]
      change v ∈ H ↔ c * Set.indicator (H : Set Kˣ) (fun v => (ψ v : ℂ)) v ≠ 0
      by_cases hv : v ∈ H
      · simp [Set.indicator_of_mem hv, hv, hc, Units.ne_zero]
      · simp [Set.indicator_of_notMem hv, hv]
    rw [he]
    exact (isClosed_singleton.preimage hcont).measurableSet.compl
  let G : Kˣ → ℂ := fun v => a * ∑ i : I, ∑ j : J, (χ i j v : ℂ) * F v
  have hG : Integrable G μ := by
    exact (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hχF i j).const_mul a
  have hGeq : ∀ v, G v = c * Set.indicator (H : Set Kˣ)
      (fun v => (ψ v : ℂ) * F v) v := by
    intro v
    have hh := congrArg (fun z : ℂ => z * F v) (hresolution v)
    simpa [G, c, H, Finset.sum_mul, mul_assoc, Set.indicator_mul_left] using hh
  have hmap : Measure.map (fun y : Kˣ => y ^ 3) μ =
      ENNReal.ofReal ((H.index : ℝ) / 3) • μ.restrict (H : Set Kˣ) :=
    KPCubicHaarTransport.cube_pushforward K κ hκ dx
  have hsub : (∫ y : Kˣ, G (y ^ 3) ∂μ) = c * ∫ v : Kˣ in (H : Set Kˣ), G v ∂μ := by
    have hmeas : AEStronglyMeasurable G (Measure.map (fun y : Kˣ => y ^ 3) μ) := by
      rw [hmap]
      exact hG.aestronglyMeasurable.restrict.smul_measure _
    rw [← integral_map (continuous_pow 3).measurable.aemeasurable hmeas,
      hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_ofNat, c]
  have hcomp : ∀ y : Kˣ, G (y ^ 3) = c * (Ω y * F (y ^ 3)) := by
    intro y
    rw [hGeq, Set.indicator_of_mem, hΩ y]
    exact ⟨y, rfl⟩
  have hrestrict : (∫ v : Kˣ in (H : Set Kˣ), G v ∂μ) = ∫ v : Kˣ, G v ∂μ := by
    rw [← integral_indicator hH]
    apply integral_congr_ae
    filter_upwards [] with v
    by_cases hv : v ∈ H
    · simp [hv]
    · simp [hv, hGeq v, Set.indicator_of_notMem hv]
  simp_rw [hcomp] at hsub
  rw [integral_const_mul, hrestrict] at hsub
  have hh := (mul_left_cancel₀ hc hsub)
  rw [hh, integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hχF i j))]
  congr 1
  funext i
  exact integral_finsetSum _ (fun j _ => hχF i j)

end DedekindZetaZeroFree.KPCubicFamilyResolution

end

section

namespace DedekindZetaZeroFree.KPCubicFamilyResolution

open MeasureTheory

noncomputable section

open scoped ValuativeRel
open ValuativeRel

private lemma units_borel (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] :
    BorelSpace Kˣ := by
  constructor
  unfold Units.instMeasurableSpace
  rw [‹BorelSpace K›.measurable_eq, ← borel_comap]
  rw [← (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced]

private theorem cube_proper (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    IsProperMap (fun x : Kˣ => x ^ 3) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have hp : IsProperMap (fun x : K => x ^ 3) := by
    convert (Polynomial.X ^ 3 : Polynomial K).isProperMap_eval (by simp) using 1
    funext x
    simp
  have hprod : IsProperMap (fun p : K × Kᵐᵒᵖ => (p.1 ^ 3, p.2 ^ 3)) := hp.prodMap (by
    simpa only [MulOpposite.op_pow] using
      (MulOpposite.opHomeomorph.isProperMap.comp hp).comp
        MulOpposite.opHomeomorph.symm.isProperMap)
  have hcomm : (fun p : K × Kᵐᵒᵖ => (p.1 ^ 3, p.2 ^ 3)) ∘ Units.embedProduct K =
      Units.embedProduct K ∘ (fun x : Kˣ => x ^ 3) := by
    funext x; ext <;> simp [Units.embedProduct]
  apply isProperMap_of_comp_of_inj (by fun_prop) Units.continuous_embedProduct
    (by rw [← hcomm]; exact hprod.comp Units.isClosedEmbedding_embedProduct.isProperMap)
  exact Units.embedProduct_injective K

theorem compact_test_integrability
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (ψ : Kˣ →ₜ* ℂˣ) (Ω : Kˣ → ℂ)
    (hΩ : ∀ y : Kˣ, Ω y = (ψ (y ^ 3) : ℂ))
    (F : Kˣ → ℂ) (hF : IsLocallyConstant F) (hFc : HasCompactSupport F) :
    Integrable (fun y : Kˣ => Ω y * F (y ^ 3))
      (KPCubicHaar.multiplicativeHaar K dx) ∧
    (∀ χ : Kˣ →ₜ* ℂˣ, Integrable (fun v : Kˣ => (χ v : ℂ) * F v)
      (KPCubicHaar.multiplicativeHaar K dx)) := by
  classical
  letI : BorelSpace Kˣ := units_borel K
  let m := dx.real (KPCubicUnitIndices.Integers K : Set K)
  have hfinite : dx (KPCubicUnitIndices.Integers K : Set K) ≠ ⊤ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
  have hm : 0 < m :=
    ENNReal.toReal_pos
      ((ValuativeRel.valuation K).isOpen_integer.measure_ne_zero dx ⟨0, by simp⟩) hfinite
  have hvol : dx (KPCubicUnitIndices.Integers K : Set K) = ENNReal.ofReal m :=
    (ENNReal.ofReal_toReal hfinite).symm
  haveI : IsFiniteMeasureOnCompacts (KPCubicHaar.multiplicativeHaar K dx) :=
    (KPCubicHaarTransport.haar_structure_and_unit_mass K dx m hm hvol).1.toIsFiniteMeasureOnCompacts
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun v : Kˣ => (ψ v : ℂ) * F v) :=
      (Units.continuous_val.comp ψ.continuous).mul hF.continuous
    have hcs : HasCompactSupport (fun v : Kˣ => (ψ v : ℂ) * F v) := hFc.mul_left
    have hcs2 : HasCompactSupport
        ((fun v : Kˣ => (ψ v : ℂ) * F v) ∘ fun y : Kˣ => y ^ 3) := by
      rw [hasCompactSupport_def]
      refine IsCompact.of_isClosed_subset ((cube_proper K).isCompact_preimage hcs.isCompact)
        (isClosed_tsupport _) ?_
      exact tsupport_comp_subset_preimage _ (continuous_id.pow 3)
    have hint : Integrable (fun y : Kˣ => (ψ (y ^ 3) : ℂ) * F (y ^ 3))
        (KPCubicHaar.multiplicativeHaar K dx) :=
      (hcont.comp (continuous_id.pow 3)).integrable_of_hasCompactSupport hcs2
    refine hint.congr ?_
    filter_upwards with y
    simp only [Function.comp_apply, hΩ y]
  · intro χ
    exact ((Units.continuous_val.comp χ.continuous).mul hF.continuous).integrable_of_hasCompactSupport
      hFc.mul_left

end

end DedekindZetaZeroFree.KPCubicFamilyResolution

end

section

namespace DedekindZetaZeroFree.KPCubicFamilyResolution

open scoped ValuativeRel
open MeasureTheory ValuativeRel

theorem integrable_cube_pullback
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (κ : 𝒪[K]) (hκ : IsPrimitiveRoot κ 3)
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (G : Kˣ → ℂ) (hG : Integrable G (KPCubicHaar.multiplicativeHaar K dx)) :
    Integrable (fun y : Kˣ => G (y ^ 3))
      (KPCubicHaar.multiplicativeHaar K dx) := by
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [@BorelSpace.measurable_eq K _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  have hμ : KPCubicHaarTransport.haar K dx = KPCubicHaar.multiplicativeHaar K dx := rfl
  have hmap := KPCubicHaarTransport.cube_pushforward K κ hκ dx
  rw [hμ] at hmap
  have hfin : ENNReal.ofReal
      (((powMonoidHom (α := Kˣ) 3).range.index : ℝ) / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : Integrable G (ENNReal.ofReal
        (((powMonoidHom (α := Kˣ) 3).range.index : ℝ) / 3) •
      (KPCubicHaar.multiplicativeHaar K dx).restrict
        ((powMonoidHom (α := Kˣ) 3).range : Set Kˣ)) :=
    (hG.mono_measure (Measure.restrict_le_self)).smul_measure hfin
  rw [← hmap] at h1
  exact h1.comp_measurable (continuous_id.pow 3).measurable

end DedekindZetaZeroFree.KPCubicFamilyResolution

end

section

namespace DedekindZetaZeroFree
namespace KPCubicExpansion

open ValuativeRel

noncomputable def valuationExponent (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (y : Kˣ) : ℤ :=
  -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (valuation K (y : K)))

noncomputable def omega (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (t : ℂˣ) (y : Kˣ) : ℂ :=
  ((t ^ valuationExponent K y : ℂˣ) : ℂ)

noncomputable def betaFunction (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (s : ℂ) (v : Kˣ) : ℂ := by
  classical
  exact if v = 1 then 0 else (KPCubicHaar.abs K (1 - (v : K)) : ℂ) ^ (-s)

open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

lemma valuationExponent_mul (y z : Kˣ) :
    valuationExponent K (y * z) = valuationExponent K y + valuationExponent K z := by
  have hy : ValuativeRel.valuation K ((y : K)) ≠ 0 :=
    (Valuation.ne_zero_iff (ValuativeRel.valuation K)).mpr (Units.ne_zero y)
  have hz : ValuativeRel.valuation K ((z : K)) ≠ 0 :=
    (Valuation.ne_zero_iff (ValuativeRel.valuation K)).mpr (Units.ne_zero z)
  have hiy : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (ValuativeRel.valuation K (y : K)) ≠ 0 := fun h =>
    hy ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
      (h.trans (map_zero (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm))
  have hiz : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (ValuativeRel.valuation K (z : K)) ≠ 0 := fun h =>
    hz ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
      (h.trans (map_zero (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm))
  simp only [valuationExponent, Units.val_mul, map_mul,
    map_mul (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)]
  rw [WithZero.log_mul hiy hiz]
  ring

lemma valueGroupWithZeroIsoInt_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.uniformizer K) =
      WithZero.exp (-1 : ℤ) := by
  set iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K with hiso
  have hu : ValuativeRel.uniformizer K ≠ 0 := ValuativeRel.uniformizer_ne_zero
  have hne : iso (ValuativeRel.uniformizer K) ≠ 0 := fun h =>
    hu (iso.injective (h.trans (map_zero iso).symm))
  have hlt : iso (ValuativeRel.uniformizer K) < 1 := by
    rw [← map_one iso]
    exact (map_lt_map_iff iso).mpr ValuativeRel.uniformizer_lt_one
  have hexp1 : WithZero.exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have h1 : WithZero.exp (-1 : ℤ) ≤ iso (ValuativeRel.uniformizer K) := by
    have hsym : iso.symm (WithZero.exp (-1 : ℤ)) < (1 : ValuativeRel.ValueGroupWithZero K) := by
      have h := (map_lt_map_iff iso.symm).mpr hexp1
      rwa [map_one iso.symm] at h
    have hthis : iso.symm (WithZero.exp (-1 : ℤ)) ≤ ValuativeRel.uniformizer K :=
      ValuativeRel.le_uniformizer_iff.mpr hsym
    have h := (map_le_map_iff iso).mpr hthis
    rwa [OrderMonoidIso.apply_symm_apply] at h
  have h2 : iso (ValuativeRel.uniformizer K) ≤ WithZero.exp (-1 : ℤ) := by
    have hk : (iso (ValuativeRel.uniformizer K)).log < 0 := by
      refine (WithZero.exp_lt_exp (a := (iso (ValuativeRel.uniformizer K)).log)
        (b := 0)).mp ?_
      rw [WithZero.exp_log hne, WithZero.exp_zero]
      exact hlt
    rw [← WithZero.exp_log hne]
    exact WithZero.exp_le_exp.mpr (by omega)
  exact le_antisymm h2 h1

lemma valuationExponent_uniformizer (π : Kˣ)
    (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K) :
    valuationExponent K π = 1 := by
  simp only [valuationExponent, hπ, valueGroupWithZeroIsoInt_uniformizer, WithZero.log_exp]
  norm_num

lemma valuationExponent_unit (u : (𝒪[K])ˣ) :
    valuationExponent K (Units.map (𝒪[K]).subtype.toMonoidHom u) = 0 := by
  have hcoe : ((Units.map (𝒪[K]).subtype.toMonoidHom u : Kˣ) : K) = ((u : 𝒪[K]) : K) := rfl
  have hv : ValuativeRel.valuation K ((u : 𝒪[K]) : K) = 1 :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (ValuativeRel.valuation K))).mp u.isUnit
  rw [valuationExponent, hcoe, hv, map_one, WithZero.log_one, neg_zero]

lemma sum_mu3_zpow (j : ℤ) :
    (∑ᶠ ζ : CubicCharacters.Mu3, ((ζ : ℂˣ) ^ j : ℂ)) =
      if (3 : ℤ) ∣ j then 3 else 0 := by
  classical
  haveI : Fintype CubicCharacters.Mu3 := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  by_cases h : (3 : ℤ) ∣ j
  · rw [if_pos h]
    have h1 : ∀ ζ : CubicCharacters.Mu3, ((ζ : ℂˣ) ^ j : ℂ) = 1 := by
      intro ζ
      have h3 : (((ζ : ℂˣ) : ℂ)) ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
          ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.2, Units.val_one]
      obtain ⟨k, hk⟩ := h
      rw [hk, zpow_mul]
      simp only [h3, one_zpow]
    rw [Finset.sum_congr rfl fun ζ _ => h1 ζ, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity 3]
    norm_num
  · rw [if_neg h]
    have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
      Complex.isPrimitiveRoot_exp 3 (by norm_num)
    let ζ₀ : CubicCharacters.Mu3 := hprim.toRootsOfUnity
    have hωj : (ζ₀ : ℂˣ) ^ j ≠ 1 := by
      intro hc
      refine h ((hprim.zpow_eq_one_iff_dvd j).mp ?_)
      have hval : (((ζ₀ : ℂˣ)) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / 3) := by
        simp [ζ₀, IsPrimitiveRoot.toRootsOfUnity, rootsOfUnity.mkOfPowEq, Units.val_mk0]
      rw [← hval, ← Units.val_zpow_eq_zpow_val, hc, Units.val_one]
    set S : ℂ := ∑ ζ : CubicCharacters.Mu3, ((ζ : ℂˣ) ^ j : ℂ) with hS
    have hre : (∑ ζ : CubicCharacters.Mu3, (((ζ₀ * ζ : CubicCharacters.Mu3) : ℂˣ) ^ j : ℂ)) = S :=
      Fintype.sum_equiv (Equiv.mulLeft ζ₀)
        (fun ζ : CubicCharacters.Mu3 => (((ζ₀ * ζ : CubicCharacters.Mu3) : ℂˣ) ^ j : ℂ))
        (fun ζ : CubicCharacters.Mu3 => ((ζ : ℂˣ) ^ j : ℂ)) (fun ζ => rfl)
    have hre' : (∑ ζ : CubicCharacters.Mu3, (((ζ₀ : ℂˣ) ^ j : ℂ) * ((ζ : ℂˣ) ^ j : ℂ))) = S := by
      rw [← hre]
      exact Finset.sum_congr rfl fun ζ _ => by
        simp only [Subgroup.coe_mul, mul_zpow, Units.val_mul]
    rw [← Finset.mul_sum] at hre'
    have hzero : ((((ζ₀ : ℂˣ) ^ j : ℂ) - 1) * S = 0) := by
      rw [sub_mul, one_mul, hre']; ring
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact absurd (sub_eq_zero.mp hc)
        fun hh => hωj (Units.ext (by rw [Units.val_zpow_eq_zpow_val]; exact hh))
    · exact hc

section ValuationAndCharacterSum

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

lemma valuationExponent_zpow (x : Kˣ) (j : ℤ) : valuationExponent K (x^j) = j * valuationExponent K x := by
  simp [valuationExponent, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, mul_neg]

lemma omega_cube (t z : ℂˣ) (hz : z^3 = t) (y : Kˣ) :
    omega K t y = omega K z (y^3) := by
  unfold omega
  rw [← zpow_natCast y 3, valuationExponent_zpow, ← hz, ← zpow_natCast z 3, ← zpow_mul]

lemma omega_uniformizer_unit (t : ℂˣ) (π : Kˣ)
    (hπ : valuation K (π : K) = uniformizer K) (j : ℤ) (u : (𝒪[K])ˣ) :
    omega K t (π^j * Units.map (𝒪[K]).subtype.toMonoidHom u) = ((t^j : ℂˣ) : ℂ) := by
  rw [omega, valuationExponent_mul, valuationExponent_zpow, valuationExponent_uniformizer π hπ, valuationExponent_unit]
  simp

lemma omega_mul (t : ℂˣ) (x y : Kˣ) : omega K t (x*y) = omega K t x * omega K t y := by
  simp [omega, valuationExponent_mul, zpow_add]

lemma sum_cubic_character_values_uniformizer_unit [Finite (CubicUnitCharacters.Character K)] (z : ℂˣ) (j : ℤ) (u : (𝒪[K])ˣ) :
    (∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ζ : CubicCharacters.Mu3,
      ((((ζ : ℂˣ) * z)^j * (ξ u : ℂˣ) : ℂˣ) : ℂ)) =
      if (3 : ℤ) ∣ j then
        3 * ((z^j : ℂˣ) : ℂ) * ∑ᶠ ξ : CubicUnitCharacters.Character K, ((ξ u : ℂˣ) : ℂ)
      else 0 := by
  classical
  letI : Fintype (CubicUnitCharacters.Character K) := Fintype.ofFinite _
  letI : Fintype CubicCharacters.Mu3 := Fintype.ofFinite _
  have hξ (ξ : CubicUnitCharacters.Character K) :
      (∑ ζ : CubicCharacters.Mu3, ((((ζ : ℂˣ) * z)^j * (ξ u : ℂˣ) : ℂˣ) : ℂ)) =
      (if (3 : ℤ) ∣ j then 3 else 0) * ((z^j : ℂˣ) : ℂ) * ((ξ u : ℂˣ) : ℂ) := by
    simp only [mul_zpow, Units.val_mul]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    simp only [Units.val_zpow_eq_zpow_val]
    rw [← finsum_eq_sum_of_fintype, sum_mu3_zpow]
  simp only [finsum_eq_sum_of_fintype]
  simp_rw [hξ]
  rw [← Finset.mul_sum]
  split_ifs <;> simp

theorem exists_cubic_character_family
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K) (z : ℂˣ) :
    ∃ χ : CubicUnitCharacters.Character K → CubicCharacters.Mu3 → (Kˣ →ₜ* ℂˣ),
      ∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3)
          (j : ℤ) (u : (𝒪[K])ˣ),
        χ ξ ζ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) =
          ((ζ : ℂˣ) * z) ^ j * (ξ u : ℂˣ) := by
  classical
  have he (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3) :=
    KPRamifiedBetaConductorSeries.exists_character_extension K π hπ ξ ((ζ : ℂˣ) * z)
  choose χ hu hp using he
  refine ⟨χ, ?_⟩
  intro ξ ζ j u
  rw [map_mul, map_zpow, hp, hu]

theorem isOpen_unit_cubes [CharZero K] : IsOpen (KPCubicUnitIndices.cubeUnits K : Set (𝒪[K])ˣ) := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  haveI : T2Space K := inferInstance
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  apply Subgroup.isOpen_of_isClosed_of_finiteIndex
  have he : (KPCubicUnitIndices.cubeUnits K : Set (𝒪[K])ˣ) =
      (fun u : (𝒪[K])ˣ => u ^ 3) '' Set.univ := by
    ext u
    simp [KPCubicUnitIndices.cubeUnits, MonoidHom.mem_range]
  rw [he]
  exact (isCompact_univ.image (continuous_id.pow 3)).isClosed

section UnitDual
variable [CharZero K]

noncomputable def unitCubicDualEquiv : CubicUnitCharacters.Character K ≃
    (((𝒪[K])ˣ ⧸ KPCubicUnitIndices.cubeUnits K) →* ℂˣ) := by
  let H := KPCubicUnitIndices.cubeUnits K
  letI : DiscreteTopology ((𝒪[K])ˣ ⧸ H) := QuotientGroup.discreteTopology (isOpen_unit_cubes K)
  refine {
    toFun := fun χ => QuotientGroup.lift H
      ((rootsOfUnity 3 ℂ).subtype.comp χ.toMonoidHom) ?_
    invFun := fun f => ⟨(f.comp (QuotientGroup.mk' H)).codRestrict
      (rootsOfUnity 3 ℂ) ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro x ⟨y, rfl⟩
    change (χ (y^3) : ℂˣ) = 1
    rw [map_pow, Subgroup.coe_pow]
    exact (mem_rootsOfUnity 3 _).mp (χ y).property
  · intro x
    rw [mem_rootsOfUnity, ← map_pow]
    change f ((QuotientGroup.mk' H) (x^3)) = 1
    have hp : (QuotientGroup.mk' H) (x^3) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    rw [hp, map_one]
  · apply Continuous.subtype_mk
    exact (continuous_of_discreteTopology (f := f)).comp QuotientGroup.continuous_mk
  · intro χ
    ext x
    rfl
  · intro f
    apply MonoidHom.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    rfl

theorem card_unit_cubic_characters :
    Nat.card (CubicUnitCharacters.Character K) = (KPCubicUnitIndices.cubeUnits K).index := by
  let H := KPCubicUnitIndices.cubeUnits K
  haveI : H.FiniteIndex := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent ((𝒪[K])ˣ ⧸ H)) :=
    HasEnoughRootsOfUnity.of_dvd ℂ (show Monoid.exponent ((𝒪[K])ˣ ⧸ H) ∣ 3 from
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩))
  have hc := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((𝒪[K])ˣ ⧸ H) ℂ
  exact (Nat.card_congr (unitCubicDualEquiv K)).trans hc
open scoped Classical in

theorem sum_unit_cubic_characters (u : (𝒪[K])ˣ) :
    (∑ᶠ ξ : CubicUnitCharacters.Character K, ((ξ u : ℂˣ) : ℂ)) =
      if u ∈ KPCubicUnitIndices.cubeUnits K then
        ((KPCubicUnitIndices.cubeUnits K).index : ℂ) else 0 := by
  classical
  let H := KPCubicUnitIndices.cubeUnits K
  haveI : H.FiniteIndex := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  let Q := (𝒪[K])ˣ ⧸ H
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    HasEnoughRootsOfUnity.of_dvd ℂ (show Monoid.exponent Q ∣ 3 from
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩))
  haveI : Finite (Q →* ℂˣ) := inferInstance
  haveI : Finite (CubicUnitCharacters.Character K) :=
    Finite.of_equiv (Q →* ℂˣ) (unitCubicDualEquiv K).symm
  letI : Fintype (CubicUnitCharacters.Character K) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  by_cases hu : u ∈ H
  · rw [if_pos hu]
    have h1 (ξ : CubicUnitCharacters.Character K) : ((ξ u : ℂˣ) : ℂ) = 1 := by
      obtain ⟨y, rfl⟩ := hu
      change ((ξ (y^3) : ℂˣ) : ℂ) = 1
      rw [map_pow, Subgroup.coe_pow, (mem_rootsOfUnity 3 _).mp (ξ y).property]
      rfl
    simp_rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card, card_unit_cubic_characters]
  · rw [if_neg hu]
    have hq : (QuotientGroup.mk' H) u ≠ 1 := by
      intro h
      exact hu ((QuotientGroup.eq_one_iff u).mp h)
    obtain ⟨f, hf⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q ℂ hq
    let ξ₀ := (unitCubicDualEquiv K).symm f
    have hξ : ((ξ₀ u : ℂˣ) : ℂ) ≠ 1 := by
      intro hh
      apply hf
      apply Units.ext
      exact hh
    set S : ℂ := ∑ ξ : CubicUnitCharacters.Character K, ((ξ u : ℂˣ) : ℂ) with hS
    have he : (∑ ξ : CubicUnitCharacters.Character K, (((ξ₀ * ξ) u : ℂˣ) : ℂ)) = S :=
      Fintype.sum_equiv (Equiv.mulLeft ξ₀) _ _ (fun ξ => rfl)
    have he' : ((ξ₀ u : ℂˣ) : ℂ) * S = S := by
      conv_lhs => rw [hS, Finset.mul_sum]
      rw [← he]
      apply Finset.sum_congr rfl
      intro ξ _
      rfl
    have hz : (((ξ₀ u : ℂˣ) : ℂ) - 1) * S = 0 := by
      rw [sub_mul, he', one_mul, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hξ)

open scoped Classical in

theorem sum_cubic_character_values_exact
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (z : ℂˣ) (j : ℤ) (u : (𝒪[K])ˣ) :
    (1 / 3 : ℂ) * (∑ᶠ ξ : CubicUnitCharacters.Character K, ∑ᶠ ζ : CubicCharacters.Mu3,
      ((((ζ : ℂˣ) * z)^j * (ξ u : ℂˣ) : ℂˣ) : ℂ)) =
      if (3 : ℤ) ∣ j ∧ u ∈ KPCubicUnitIndices.cubeUnits K then
        (((powMonoidHom (α := Kˣ) 3).range.index : ℂ) / 3) * ((z^j : ℂˣ) : ℂ)
      else 0 := by
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  haveI : Finite (CubicUnitCharacters.Character K) := Nat.finite_of_card_ne_zero (by
    rw [card_unit_cubic_characters]
    exact Subgroup.index_ne_zero_of_finite)
  rw [sum_cubic_character_values_uniformizer_unit, sum_unit_cubic_characters]
  have hi := KPCubicHaarTransport.field_cube_index K
  have hi' : ((powMonoidHom (α := Kˣ) 3).range.index : ℂ) =
      3 * ((KPCubicUnitIndices.cubeUnits K).index : ℂ) := by exact_mod_cast hi
  rw [hi']
  split_ifs <;> simp_all <;> ring

end UnitDual

end ValuationAndCharacterSum

section BetaIntegrability

open MeasureTheory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

local instance : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [@BorelSpace.measurable_eq K _ _ _,
    Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩

theorem integrable_character_beta
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (π : Kˣ) (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K)
    (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (b : ℂˣ) (hb : χ π = b)
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hbs : (CubicUnitCharacters.residueCard K : ℝ).rpow (-s.re) < ‖(b : ℂ)‖)
    (hb1 : ‖(b : ℂ)‖ < 1) :
    Integrable (fun v : Kˣ => (χ v : ℂ) * betaFunction K s v)
      (KPCubicHaar.multiplicativeHaar K dx) := by
  classical
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  let A := KPCubicHaar.abs K
  let I : K → ℂ := fun x => if hx : x = 0 then 0 else
    (χ (Units.mk0 x hx) : ℂ) * (A (1-x) : ℂ) ^ (-s)
  have hi : Integrable I (dx.withDensity (fun x => ENNReal.ofReal ((A x)⁻¹))) :=
    KPRamifiedBetaConductorSeries.integrable_in_joint_strip K dx π hπ ξ χ hχ b hb s hs0 hs1 hbs hb1
  have he : MeasurableEmbedding (fun v : Kˣ => (v : K)) :=
    Units.isEmbedding_val₀.measurableEmbedding (by
      have hr : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
        ext x
        simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
      rw [hr]
      exact isOpen_compl_singleton.measurableSet)
  have hc := he.integrableOn_range_iff_comap.mp hi.integrableOn
  have heq : (fun v : Kˣ => (χ v : ℂ) * betaFunction K s v) =
      I ∘ (fun v : Kˣ => (v : K)) := by
    ext v
    have hs : -s ≠ 0 := neg_ne_zero.mpr (fun h => by simp [h] at hs0)
    simp only [Function.comp_apply, I, Units.ne_zero, dite_false]
    have hv : Units.mk0 (v : K) (Units.ne_zero v) = v := Units.ext rfl
    rw [hv]
    by_cases hv1 : v = 1
    · subst v
      simp [betaFunction, A, KPCubicHaar.abs, Complex.zero_cpow hs]
    · simp [betaFunction, hv1, A]
  rw [heq]
  exact hc

theorem family_beta_integrable
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (π : Kˣ) (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K)
    (z : ℂˣ)
    (χ : CubicUnitCharacters.Character K → CubicCharacters.Mu3 → (Kˣ →ₜ* ℂˣ))
    (hχ : ∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3)
      (j : ℤ) (u : (𝒪[K])ˣ),
      χ ξ ζ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) =
        ((ζ : ℂˣ) * z) ^ j * (ξ u : ℂˣ))
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hbs : (CubicUnitCharacters.residueCard K : ℝ).rpow (-s.re) < ‖(z : ℂ)‖)
    (hb1 : ‖(z : ℂ)‖ < 1) :
    ∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3),
      Integrable (fun v : Kˣ => (χ ξ ζ v : ℂ) * betaFunction K s v)
        (KPCubicHaar.multiplicativeHaar K dx) := by
  intro ξ ζ
  have hn : ‖(((ζ : ℂˣ) * z : ℂˣ) : ℂ)‖ = ‖(z : ℂ)‖ := by
    rw [Units.val_mul, norm_mul]
    have hpow : (((ζ : ℂˣ) : ℂ)) ^ 3 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val ((mem_rootsOfUnity 3 _).mp ζ.property)
    have hnorm : ‖((ζ : ℂˣ) : ℂ)‖ = 1 := by
      exact Complex.norm_eq_one_of_pow_eq_one hpow (by norm_num)
    rw [hnorm, one_mul]
  apply integrable_character_beta K dx π hπ ξ (χ ξ ζ)
    (fun u => by simpa using hχ ξ ζ 0 u) ((ζ : ℂˣ) * z)
    (by simpa using hχ ξ ζ 1 1) s hs0 hs1
  · rwa [hn]
  · rwa [hn]

end BetaIntegrability

end KPCubicExpansion

open scoped ValuativeRel
open MeasureTheory ValuativeRel KPCubicExpansion

theorem kp_rankone_cubic_character_expansion
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (κ : 𝒪[K]) (hκ : IsPrimitiveRoot κ 3)
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (π : Kˣ) (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K)
    (t z : ℂˣ) (hz : z ^ 3 = t) :
    Finite (CubicUnitCharacters.Character K) ∧
    ∃ χ : CubicUnitCharacters.Character K → CubicCharacters.Mu3 → (Kˣ →ₜ* ℂˣ),
      (∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3)
          (j : ℤ) (u : (𝒪[K])ˣ),
        χ ξ ζ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) =
          ((ζ : ℂˣ) * z) ^ j * (ξ u : ℂˣ)) ∧
      (∀ (F : Kˣ → ℂ), IsLocallyConstant F → HasCompactSupport F →
        (∫ y : Kˣ, omega K t y * F (y ^ 3) ∂KPCubicHaar.multiplicativeHaar K dx) =
          (1 / 3 : ℂ) * ∑ᶠ ξ : CubicUnitCharacters.Character K,
            ∑ᶠ ζ : CubicCharacters.Mu3,
              ∫ v : Kˣ, (χ ξ ζ v : ℂ) * F v ∂KPCubicHaar.multiplicativeHaar K dx) ∧
      (∀ (F : Kˣ → ℂ),
        Integrable (fun y : Kˣ => omega K t y * F (y ^ 3))
          (KPCubicHaar.multiplicativeHaar K dx) →
        (∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3),
          Integrable (fun v : Kˣ => (χ ξ ζ v : ℂ) * F v)
            (KPCubicHaar.multiplicativeHaar K dx)) →
        (∫ y : Kˣ, omega K t y * F (y ^ 3) ∂KPCubicHaar.multiplicativeHaar K dx) =
          (1 / 3 : ℂ) * ∑ᶠ ξ : CubicUnitCharacters.Character K,
            ∑ᶠ ζ : CubicCharacters.Mu3,
              ∫ v : Kˣ, (χ ξ ζ v : ℂ) * F v ∂KPCubicHaar.multiplicativeHaar K dx) ∧
      (∀ (s : ℂ), 0 < s.re → s.re < 1 →
        (CubicUnitCharacters.residueCard K : ℝ).rpow (-s.re) < ‖(z : ℂ)‖ →
        ‖(z : ℂ)‖ < 1 →
        Integrable (fun y : Kˣ => omega K t y * betaFunction K s (y ^ 3))
          (KPCubicHaar.multiplicativeHaar K dx) ∧
        (∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3),
          Integrable (fun v : Kˣ => (χ ξ ζ v : ℂ) * betaFunction K s v)
            (KPCubicHaar.multiplicativeHaar K dx)) ∧
        (∫ y : Kˣ, omega K t y * betaFunction K s (y ^ 3)
            ∂KPCubicHaar.multiplicativeHaar K dx) =
          (1 / 3 : ℂ) * ∑ᶠ ξ : CubicUnitCharacters.Character K,
            ∑ᶠ ζ : CubicCharacters.Mu3,
              ∫ v : Kˣ, (χ ξ ζ v : ℂ) * betaFunction K s v
                ∂KPCubicHaar.multiplicativeHaar K dx) := by
  classical
  haveI := KPCubicHaar.cubeUnits_finiteIndex (K := K)
  haveI : Finite (CubicUnitCharacters.Character K) := Nat.finite_of_card_ne_zero (by
    rw [card_unit_cubic_characters]
    exact Subgroup.index_ne_zero_of_finite)
  obtain ⟨χ, hχ⟩ := exists_cubic_character_family K π hπ z
  have hsum (j : ℤ) (u : (𝒪[K])ˣ) :=
    sum_cubic_character_values_exact K z j u
  have hsumχ (j : ℤ) (u : (𝒪[K])ˣ) :
      (1 / 3 : ℂ) * (∑ᶠ ξ : CubicUnitCharacters.Character K,
        ∑ᶠ ζ : CubicCharacters.Mu3,
          (χ ξ ζ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) : ℂ)) =
        if (3 : ℤ) ∣ j ∧ u ∈ KPCubicUnitIndices.cubeUnits K then
          (((powMonoidHom (α := Kˣ) 3).range.index : ℂ) / 3) * ((z ^ j : ℂˣ) : ℂ)
        else 0 := by
    simpa only [hχ] using hsum j u
  obtain ⟨hdesc, hresolution⟩ := KPCubicFamilyResolution.cubic_family_resolution
    K π hπ t z hz (omega K t) (omega_uniformizer_unit K t π hπ) χ hχ hsumχ
  have habs (F : Kˣ → ℂ)
      (hF : Integrable (fun y : Kˣ => omega K t y * F (y ^ 3))
        (KPCubicHaar.multiplicativeHaar K dx))
      (hχF : ∀ (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3),
        Integrable (fun v : Kˣ => (χ ξ ζ v : ℂ) * F v)
          (KPCubicHaar.multiplicativeHaar K dx)) :=
    KPCubicFamilyResolution.integrate_cube_resolution K κ hκ dx
      (CubicUnitCharacters.Character K) CubicCharacters.Mu3 χ (χ 1 1)
      (omega K t) hdesc (1 / 3 : ℂ) hresolution F hF hχF
  refine ⟨inferInstance, χ, hχ, ?_, habs, ?_⟩
  · intro F hF hFc
    obtain ⟨hpull, htwists⟩ := KPCubicFamilyResolution.compact_test_integrability
      K dx (χ 1 1) (omega K t) hdesc F hF hFc
    exact habs F hpull (fun ξ ζ => htwists (χ ξ ζ))
  · intro s hs0 hs1 hz0 hz1
    have htwists := family_beta_integrable K dx π hπ z χ hχ s hs0 hs1 hz0 hz1
    have hpull : Integrable
        (fun y : Kˣ => omega K t y * betaFunction K s (y ^ 3))
        (KPCubicHaar.multiplicativeHaar K dx) := by
      simpa only [hdesc] using KPCubicFamilyResolution.integrable_cube_pullback
        K κ hκ dx (fun v : Kˣ => (χ 1 1 v : ℂ) * betaFunction K s v) (htwists 1 1)
    exact ⟨hpull, htwists, habs (betaFunction K s) hpull htwists⟩

end DedekindZetaZeroFree

end
