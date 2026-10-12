module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBeta.RamifiedConductorFormula

@[expose] public section

namespace DedekindZetaZeroFree.KPTameValuationCoordinates

open ValuativeRel

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

def unitCubeClasses : Subgroup (KPLocalTorus.CubeClasses Kˣ) :=
  ((KPRamifiedBeta.unitsInclusion K).range ⊔ CubicCharacters.cubes Kˣ).map
    (QuotientGroup.mk' (CubicCharacters.cubes Kˣ))

def uniformizerClass (π : Kˣ) (j : ℤ) : KPLocalTorus.CubeClasses Kˣ :=
  QuotientGroup.mk' (CubicCharacters.cubes Kˣ) (π ^ j)

 def modVal : Kˣ →* Multiplicative (ZMod 3) where
  toFun y := Multiplicative.ofAdd (KPCubicExpansion.valuationExponent K y : ZMod 3)
  map_one' := by simp [KPCubicExpansion.valuationExponent]
  map_mul' y z := by
    change (KPCubicExpansion.valuationExponent K (y*z) : ZMod 3) =
      (KPCubicExpansion.valuationExponent K y : ZMod 3) +
      (KPCubicExpansion.valuationExponent K z : ZMod 3)
    rw [KPCubicExpansion.valuationExponent_mul, Int.cast_add]

lemma unit_of_exponent_zero (y : Kˣ)
    (h : KPCubicExpansion.valuationExponent K y = 0) :
    y ∈ (KPRamifiedBeta.unitsInclusion K).range := by
  have hn : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (y : K)) ≠ 0 := by
    simpa using (Units.ne_zero y)
  have hv : valuation K (y : K) = 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (y : K)) =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K 1
    rw [map_one, ← WithZero.exp_log hn]
    have hlog : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (valuation K (y : K))) = 0 := neg_eq_zero.mp h
    rw [hlog, WithZero.exp_zero]
  let a : 𝒪[K] := ⟨(y : K), hv.le⟩
  have ha : IsUnit a := (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation K))).mpr hv
  obtain ⟨u, hu⟩ := ha
  refine ⟨u, ?_⟩
  apply Units.ext
  exact congrArg (fun x : 𝒪[K] => (x : K)) hu

private lemma cubes_le_modVal_ker : CubicCharacters.cubes Kˣ ≤ (modVal K).ker := by
  intro y hy
  change ∃ x : Kˣ, x ^ 3 = y at hy
  obtain ⟨x, rfl⟩ := hy
  change (KPCubicExpansion.valuationExponent K (x^3) : ZMod 3) = 0
  rw [← zpow_natCast x 3, KPCubicExpansion.valuationExponent_zpow, Int.cast_mul]
  change (3 : ZMod 3) * (KPCubicExpansion.valuationExponent K x : ZMod 3) = 0
  rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]

private lemma modVal_ker (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ)) :
    (modVal K).ker = (KPRamifiedBeta.unitsInclusion K).range ⊔ CubicCharacters.cubes Kˣ := by
  have hp : KPCubicExpansion.valuationExponent K π = 1 := by
    simp only [KPCubicExpansion.valuationExponent, hπ, WithZero.log_exp]
    norm_num
  apply le_antisymm
  · intro y hy
    change (KPCubicExpansion.valuationExponent K y : ZMod 3) = 0 at hy
    obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hy
    let u := y * π ^ (-KPCubicExpansion.valuationExponent K y)
    have hu : KPCubicExpansion.valuationExponent K u = 0 := by
      dsimp [u]
      rw [KPCubicExpansion.valuationExponent_mul, KPCubicExpansion.valuationExponent_zpow, hp]
      ring
    have hum := unit_of_exponent_zero K u hu
    have hcm : π ^ KPCubicExpansion.valuationExponent K y ∈ CubicCharacters.cubes Kˣ := by
      change ∃ x : Kˣ, x ^ 3 = π ^ KPCubicExpansion.valuationExponent K y
      refine ⟨π ^ j, ?_⟩
      rw [← zpow_natCast (π^j) 3, ← zpow_mul, hj]
      congr 1
      ring
    have heq : y = u * π ^ KPCubicExpansion.valuationExponent K y := by
      dsimp [u]
      rw [mul_assoc, ← zpow_add]
      simp
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hum) (Subgroup.mem_sup_right hcm)
  · refine sup_le ?_ (cubes_le_modVal_ker K)
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    change (KPCubicExpansion.valuationExponent K ((KPRamifiedBeta.unitsInclusion K) u) : ZMod 3) = 0
    change (KPCubicExpansion.valuationExponent K (Units.map (𝒪[K]).subtype.toMonoidHom u) : ZMod 3) = 0
    rw [KPCubicExpansion.valuationExponent_unit]
    rfl

theorem valuation_quotient_coordinates [CharZero K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 12) (htame : (3 : 𝒪[K]) ∉ 𝓂[K])
    (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ)) :
    ∃ e : (KPLocalTorus.CubeClasses Kˣ ⧸ unitCubeClasses K) ≃*
        Multiplicative (ZMod 3),
      (∀ y : Kˣ,
        e (QuotientGroup.mk' (unitCubeClasses K)
          (QuotientGroup.mk' (CubicCharacters.cubes Kˣ) y)) =
            Multiplicative.ofAdd (KPCubicExpansion.valuationExponent K y : ZMod 3)) ∧
      (∀ j : Fin 3,
        e (QuotientGroup.mk' (unitCubeClasses K)
          (uniformizerClass K π (j.val : ℤ))) =
            Multiplicative.ofAdd (j.val : ZMod 3)) := by
  let φ : KPLocalTorus.CubeClasses Kˣ →* Multiplicative (ZMod 3) :=
    QuotientGroup.lift (CubicCharacters.cubes Kˣ) (modVal K) (cubes_le_modVal_ker K)
  have hker : unitCubeClasses K = φ.ker := by
    rw [QuotientGroup.ker_lift, modVal_ker K π hπ]
    rfl
  have hp : KPCubicExpansion.valuationExponent K π = 1 := by
    simp only [KPCubicExpansion.valuationExponent, hπ, WithZero.log_exp]
    norm_num
  have hsurj : Function.Surjective φ := by
    intro j
    refine ⟨uniformizerClass K π (j.toAdd.val : ℤ), ?_⟩
    change Multiplicative.ofAdd (KPCubicExpansion.valuationExponent K
      (π ^ (j.toAdd.val : ℤ)) : ZMod 3) = j
    rw [KPCubicExpansion.valuationExponent_zpow, hp, mul_one]
    change (((j.toAdd.val : ℤ) : ZMod 3)) = j.toAdd
    simp
  refine ⟨QuotientGroup.liftEquiv (unitCubeClasses K) hsurj hker, ?_, ?_⟩
  · intro y
    rfl
  · intro j
    change Multiplicative.ofAdd (KPCubicExpansion.valuationExponent K
      (π ^ (j.val : ℤ)) : ZMod 3) = Multiplicative.ofAdd (j.val : ZMod 3)
    rw [KPCubicExpansion.valuationExponent_zpow, hp, mul_one]
    rfl

abbrev DiagonalValuations := ℤ × ℤ

def transportExponent (j : Fin 3) : ℤ := if j = 2 then 2 else 1

end

end DedekindZetaZeroFree.KPTameValuationCoordinates
