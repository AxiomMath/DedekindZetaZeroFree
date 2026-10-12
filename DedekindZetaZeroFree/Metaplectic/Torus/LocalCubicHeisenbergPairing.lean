module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.FilteredCubicCharacterCounts
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnitCubeIndex
public import DedekindZetaZeroFree.Arithmetic.LocalFields.MultiplicativeCubeIndex

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalTorus

open scoped Valued
open ValuativeRel

abbrev CubeClasses (K : Type*) [CommGroup K] := K ⧸ CubicCharacters.cubes K

noncomputable def inverseThreeModule (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ℕ :=
  (Nat.card 𝓀[K]) ^ (IsDiscreteValuationRing.addVal 𝒪[K] (3 : 𝒪[K])).toNat

theorem finite_cubeClasses (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : Finite (CubeClasses Kˣ) := by
  exact ClassFieldTheory.powerClassGroup_finite K 3 (by norm_num)

private theorem integral_root (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ z : 𝒪[K], IsPrimitiveRoot z 3 := by
  have hv : valuation K ζ = 1 := by
    have hp : (valuation K ζ) ^ 3 = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
  let z : 𝒪[K] := ⟨ζ, hv.le⟩
  exact ⟨z, hζ.of_map_of_injective (f := (valuation K).integer.subtype)
    Subtype.val_injective⟩

open KPCubicUnitIndices

private theorem log_integer (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (a : Integers K) (ha : a ≠ 0) :
    WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (a : K))) = -((IsDiscreteValuationRing.addVal (Integers K) a).toNat : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨p, hp⟩ := valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hep : e (valuation K p) = WithZero.exp (-1 : ℤ) := by rw [hp, e.apply_symm_apply]
  have hpint : valuation K p ≤ 1 := by
    apply (map_le_map_iff e).mp
    rw [map_one, hep]
    change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
    exact WithZero.exp_le_exp.mpr (by omega)
  let π : Integers K := ⟨p, hpint⟩
  have hm : IsLocalRing.maximalIdeal (Integers K) = Ideal.span {π} := by
    ext b
    change b ∈ IsLocalRing.maximalIdeal (valuation K).integer ↔ b ∈ Ideal.span {π}
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation K)).dvd_iff_le]
    change valuation K (b : K) ≠ 1 ↔ valuation K p ≥ valuation K (b : K)
    rw [ne_iff_lt_iff_le.mpr (show valuation K (b : K) ≤ 1 from b.property)]
    rw [← (map_lt_map_iff e (a := valuation K (b : K)) (b := 1))]
    change _ ↔ valuation K (b : K) ≤ valuation K p
    rw [← (map_le_map_iff e (a := valuation K (b : K)) (b := valuation K p)), map_one, hep]
    generalize e (valuation K (b : K)) = z
    cases z using WithZero.recZeroCoe with
    | zero => simp
    | coe z =>
      change (z : WithZero (Multiplicative ℤ)) < ↑(1 : Multiplicative ℤ) ↔
        (z : WithZero (Multiplicative ℤ)) ≤ ↑(Multiplicative.ofAdd (-1 : ℤ))
      rw [WithZero.coe_lt_coe, WithZero.coe_le_coe]
      change z.toAdd < 0 ↔ z.toAdd ≤ -1
      omega
  have hi : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hm
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hi
  rw [hu, IsDiscreteValuationRing.addVal_def' u hi]
  simp only [ENat.toNat_coe]
  have hvu : valuation K ((u : Integers K) : K) = 1 :=
    (Valuation.integer.integers (valuation K)).one_of_isUnit u.isUnit
  change WithZero.log (e (valuation K
    (((u : Integers K) : K) * p^n))) = -(n : ℤ)
  rw [map_mul, map_pow, hvu, map_mul, map_pow, map_one, one_mul, hep]
  rw [← WithZero.exp_nsmul, WithZero.log_exp]
  simp [nsmul_eq_mul]

theorem card_cubeClasses (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (CubeClasses Kˣ) = 9 * inverseThreeModule K := by
  obtain ⟨z, hz⟩ := integral_root K ζ hζ
  have hlog := log_integer K (3 : 𝒪[K]) (by norm_num)
  have hmodule : KPCubicHaarTransport.abs K (3 : K) =
      ((inverseThreeModule K : ℕ) : ℝ)⁻¹ := by
    simp only [KPCubicHaarTransport.abs, if_neg (show (3 : K) ≠ 0 by norm_num)]
    rw [show (3 : K) = ((3 : 𝒪[K]) : K) from rfl, hlog]
    simp [inverseThreeModule, residueCard, zpow_neg, zpow_natCast]
  have hc := KPCubicHaarTransport.unit_cube_index K z hz
  rw [hmodule, div_inv_eq_mul] at hc
  have hnat : (cubeUnits K).index = 3 * inverseThreeModule K := by
    exact_mod_cast hc
  change (CubicCharacters.cubes Kˣ).index = _
  rw [CubicCharacters.cubes, KPCubicHaarTransport.field_cube_index K, hnat]
  omega

theorem inverseThreeModule_eq_one_of_tame (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (htame : (3 : 𝒪[K]) ∉ 𝓂[K]) : inverseThreeModule K = 1 := by
  have hunit : IsUnit (3 : 𝒪[K]) := by
    by_contra h
    exact htame ((IsLocalRing.mem_maximalIdeal (3 : 𝒪[K])).mpr (mem_nonunits_iff.mpr h))
  have hval : IsDiscreteValuationRing.addVal 𝒪[K] (3 : 𝒪[K]) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hunit
  simp [inverseThreeModule, hval]

theorem card_cubeClasses_tame (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (htame : (3 : 𝒪[K]) ∉ 𝓂[K]) :
    Nat.card (CubeClasses Kˣ) = 9 := by
  rw [card_cubeClasses K ζ hζ, inverseThreeModule_eq_one_of_tame K htame, mul_one]

end DedekindZetaZeroFree.KPLocalTorus
