module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TruncatedCubicUnitIndices

@[expose] public section

namespace DedekindZetaZeroFree.KPCubicHaarTransport
open KPCubicUnitIndices ValuativeRel
open scoped ValuativeRel
noncomputable section
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
def exponent : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (WithZero.log
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x)))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [Units.val_mul, map_mul]
    exact WithZero.log_mul (by simp) (by simp)

private lemma exponent_eq_one_iff (x : Kˣ) :
    exponent K x = 1 ↔ valuation K (x : K) = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change Multiplicative.ofAdd (WithZero.log (e (valuation K (x : K)))) = 1 ↔ _
  constructor
  · intro h
    have hlog : WithZero.log (e (valuation K (x : K))) = 0 :=
      congrArg Multiplicative.toAdd h
    have he : e (valuation K (x : K)) = 1 := by
      rw [← WithZero.exp_log (show e (valuation K (x : K)) ≠ 0 by simp [e]), hlog]
      exact WithZero.exp_zero
    exact e.injective (by simpa using he)
  · intro h
    simp [h]

private lemma exists_exponent_one : ∃ π : Kˣ, exponent K π = Multiplicative.ofAdd 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (1 : ℤ)))
  have hx0 : x ≠ 0 := by
    intro h
    have := congrArg e hx
    simp [h, e] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  change Multiplicative.ofAdd (WithZero.log (e (valuation K x))) = _
  rw [hx, e.apply_symm_apply, WithZero.log_exp]

def unitMap : (Integers K)ˣ →* Kˣ :=
  Units.map (valuation K).integer.subtype.toMonoidHom

private lemma exponent_unitMap (u : (Integers K)ˣ) :
    exponent K (unitMap K u) = 1 := by
  apply (exponent_eq_one_iff K _).mpr
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation K))).mp u.isUnit

private lemma unitMap_injective : Function.Injective (unitMap K) := by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val h

private lemma exists_unitMap (x : Kˣ) (hx : exponent K x = 1) :
    ∃ u : (Integers K)ˣ, unitMap K u = x := by
  have hv := (exponent_eq_one_iff K x).mp hx
  let y : Integers K := ⟨(x : K), hv.le⟩
  have hy : IsUnit y :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mpr hv
  obtain ⟨u, hu⟩ := hy
  refine ⟨u, ?_⟩
  apply Units.ext
  exact congrArg Subtype.val hu

def splitMap (π : Kˣ) : Multiplicative ℤ × (Integers K)ˣ →* Kˣ where
  toFun p := π ^ p.1.toAdd * unitMap K p.2
  map_one' := by simp
  map_mul' p q := by
    dsimp
    rw [zpow_add, map_mul]
    ac_rfl

private lemma splitMap_bijective (π : Kˣ) (hπ : exponent K π = Multiplicative.ofAdd 1) :
    Function.Bijective (splitMap K π) := by
  have hν (p : Multiplicative ℤ × (Integers K)ˣ) :
      exponent K (splitMap K π p) = p.1 := by
    change exponent K (π ^ p.1.toAdd * unitMap K p.2) = _
    rw [map_mul, map_zpow, hπ, exponent_unitMap, mul_one]
    apply Multiplicative.toAdd.injective
    change p.1.toAdd * 1 = p.1.toAdd
    simp
  constructor
  · intro p q hpq
    have h1 : p.1 = q.1 := by simpa only [hν] using congrArg (exponent K) hpq
    apply Prod.ext h1
    apply unitMap_injective K
    apply mul_left_cancel (a := π ^ p.1.toAdd)
    simpa only [splitMap, MonoidHom.coe_mk, OneHom.coe_mk, h1] using hpq
  · intro x
    let n := exponent K x
    have hx : exponent K (π ^ (-n.toAdd) * x) = 1 := by
      rw [map_mul, map_zpow, hπ]
      change (Multiplicative.ofAdd 1) ^ (-n.toAdd) * n = 1
      change Multiplicative.ofAdd (-n.toAdd * 1 + n.toAdd) = 1
      simp
    obtain ⟨u, hu⟩ := exists_unitMap K _ hx
    refine ⟨(n, u), ?_⟩
    change π ^ n.toAdd * unitMap K u = x
    rw [hu, ← mul_assoc, ← zpow_add]
    simp
private lemma exponent_cube_index :
    (powMonoidHom (α := Multiplicative ℤ) 3).range.index = 3 := by
  have hr : (powMonoidHom (α := Multiplicative ℤ) 3).range =
      (AddSubgroup.zmultiples (3 : ℤ)).toSubgroup := by
    ext x
    change (∃ y : Multiplicative ℤ, y ^ 3 = x) ↔
      x.toAdd ∈ AddSubgroup.zmultiples (3 : ℤ)
    rw [Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      change (3 : ℤ) ∣ 3 * y.toAdd
      exact dvd_mul_right _ _
    · rintro ⟨n, hn⟩
      refine ⟨Multiplicative.ofAdd n, ?_⟩
      apply Multiplicative.toAdd.injective
      exact hn.symm
  rw [hr, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  rfl

theorem field_cube_index
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    (powMonoidHom (α := Kˣ) 3).range.index = 3 * (cubeUnits K).index := by
  obtain ⟨π, hπ⟩ := exists_exponent_one K
  let f := splitMap K π
  have hf : Function.Bijective f := splitMap_bijective K π hπ
  have hr : (powMonoidHom (α := Kˣ) 3).range =
      ((powMonoidHom (α := Multiplicative ℤ × (Integers K)ˣ) 3).range).map f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨p, rfl⟩ := hf.2 y
      exact ⟨p ^ 3, ⟨p, rfl⟩, map_pow f p 3⟩
    · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
      exact ⟨f p, (map_pow f p 3).symm⟩
  have hp : powMonoidHom (α := Multiplicative ℤ × (Integers K)ˣ) 3 =
      (powMonoidHom (α := Multiplicative ℤ) 3).prodMap
        (powMonoidHom (α := (Integers K)ˣ) 3) := by
    ext p <;> rfl
  rw [hr, Subgroup.index_map_of_bijective hf, hp, MonoidHom.range_prodMap,
    Subgroup.index_prod, exponent_cube_index]
  rfl
end
end DedekindZetaZeroFree.KPCubicHaarTransport
