module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicUnitCharacterConductors

@[expose] public section

namespace DedekindZetaZeroFree.KPRamifiedBetaConductorSeries

open scoped Classical ValuativeRel Topology
open ValuativeRel WithZero

noncomputable def valuationExponent (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd
    (-log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x)))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (show (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (valuation K (x : K)) ≠ 0 by simp) (show (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (valuation K (y : K)) ≠ 0 by simp)]
    simp [add_comm]

private lemma valuationExponent_units (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (u : (𝒪[K])ˣ) :
    valuationExponent K (Units.map (𝒪[K]).subtype.toMonoidHom u) = 1 := by
  have hv : valuation K (u : K) = 1 :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
  simp [valuationExponent, hv]

private lemma valuationExponent_uniformizer (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (π : Kˣ)
    (hπ : valuation K (π : K) = uniformizer K) :
    valuationExponent K π = Multiplicative.ofAdd 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have he : e (uniformizer K) = exp (-1) := by
    apply le_antisymm
    · have hlt : e (uniformizer K) < 1 := by
        simpa using e.strictMono (uniformizer_lt_one (R := K))
      have hlog : log (e (uniformizer K)) < (0 : ℤ) :=
        (WithZero.log_lt_iff_lt_exp (by simp [e, uniformizer_ne_zero])).mpr (by simpa using hlt)
      apply WithZero.le_exp_of_log_le
      omega
    · have hsmall : exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      have hlt : e.symm (exp (-1 : ℤ)) < 1 := by
        simpa using e.symm.strictMono hsmall
      have hle := le_uniformizer_iff.mpr hlt
      simpa using e.strictMono.monotone hle
  change Multiplicative.ofAdd (-log (e (valuation K (π : K)))) = _
  rw [hπ, he, log_exp]
  rfl

theorem exists_character_extension
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (π : Kˣ) (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K)
    (ξ : CubicUnitCharacters.Character K) (b : ℂˣ) :
    ∃ χ : Kˣ →ₜ* ℂˣ,
      (∀ u : (𝒪[K])ˣ, χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ)) ∧
      χ π = b := by
  classical
  let i : (𝒪[K])ˣ →* Kˣ := Units.map (𝒪[K]).subtype.toMonoidHom
  have hiind : Topology.IsInducing i :=
    (Topology.IsEmbedding.subtypeVal.units_map).isInducing
  have hi : Function.Injective i :=
    (Topology.IsEmbedding.subtypeVal.units_map).injective
  have hirange : Set.range i = ((𝒪[K]).toSubsemiring.toSubmonoid.units : Set Kˣ) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val.2, u.inv.2⟩
    · rintro ⟨h, h'⟩
      refine ⟨⟨⟨x.val, h⟩, ⟨x.inv, h'⟩, ?_, ?_⟩, ?_⟩
      · apply Subtype.ext; exact x.val_inv
      · apply Subtype.ext; exact x.inv_val
      · apply Units.ext; rfl
  have hmem : Set.range i ∈ nhds (i 1) := by
    rw [hirange]
    apply IsOpen.mem_nhds
    · apply Submonoid.isOpen_units
      exact Valuation.isOpen_integer (v := ValuativeRel.valuation K)
    · exact ⟨(𝒪[K]).one_mem, (𝒪[K]).one_mem⟩
  letI : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ (by
    intro n hn a
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.pos_of_ne_zero hn).ne'] at hz
      exact a.toMul.ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    change Additive.ofMul ((Units.mk0 z hz0) ^ n) = a
    apply congrArg Additive.ofMul
    apply Units.ext
    exact hz)
  letI : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  let ω : (𝒪[K])ˣ →* ℂˣ := (rootsOfUnity 3 ℂ).subtype.comp ξ.toMonoidHom
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    i.toAdditive hi ω.toAdditive
  let fM : Kˣ →* ℂˣ :=
    { toFun := fun a => (f (Additive.ofMul a)).toMul
      map_one' := f.map_zero
      map_mul' := f.map_add }
  have hext : ∀ u, fM (i u) = (ξ u : ℂˣ) := by
    intro u
    exact congrArg Additive.toMul (DFunLike.congr_fun hf (Additive.ofMul u))
  let a : ℂˣ := b / fM π
  let h : Kˣ →* ℂˣ :=
    { toFun := fun x => a ^ (valuationExponent K x).toAdd
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [map_mul]
        exact zpow_add a _ _ }
  have hu : ∀ u, h (i u) = 1 := by
    intro u
    change a ^ (valuationExponent K (Units.map (𝒪[K]).subtype.toMonoidHom u)).toAdd = 1
    rw [valuationExponent_units]
    exact zpow_zero a
  let g : Kˣ →* ℂˣ := fM * h
  have hgext : ∀ u, g (i u) = (ξ u : ℂˣ) := by
    intro u
    simp [g, hext, hu]
  have hc : Continuous (g ∘ i) := by
    have heq : g ∘ i = fun u => (ξ u : ℂˣ) := funext hgext
    rw [heq]
    exact continuous_subtype_val.comp ξ.continuous
  have hgcont : Continuous g := by
    apply continuous_of_continuousAt_one g
    have hcat := (hiind.continuousAt_iff' hmem).mp (hc.continuousAt (x := 1))
    simpa only [map_one] using hcat
  refine ⟨⟨g, hgcont⟩, hgext, ?_⟩
  change g π = b
  change fM π * a ^ (valuationExponent K π).toAdd = b
  rw [valuationExponent_uniformizer K π hπ]
  change fM π * a ^ (1 : ℤ) = b
  rw [zpow_one]
  simp [a]

end DedekindZetaZeroFree.KPRamifiedBetaConductorSeries
