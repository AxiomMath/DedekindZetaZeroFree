module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFieldMultiplicativeMeasure
public import ClassFieldTheory.All

@[expose] public section

namespace DedekindZetaZeroFree.KPCubicHaarTransport
noncomputable section
open KPCubicUnitIndices ValuativeRel

open Polynomial in
private theorem cube_near_one (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (c : Integers K) (hc : c ∈ IsLocalRing.maximalIdeal (Integers K)) :
    ∃ t : (Integers K)ˣ, (t : Integers K)^3 = 1 + 9*c := by
  let O := Integers K
  let p := IsLocalRing.maximalIdeal O
  letI : HenselianRing O p := (LocalFieldTheory.localCompleteDVF K).henselianRing
  let P : O[X] := Polynomial.X^3 - Polynomial.X^2 - Polynomial.C (3*c)*Polynomial.X - Polynomial.C (3*c^2)
  have hm : P.Monic := by
    have hP : P = Polynomial.X^3 - (Polynomial.X^2 + Polynomial.C (3*c)*Polynomial.X + Polynomial.C (3*c^2)) := by dsimp [P]; ring
    rw [hP]
    apply Polynomial.monic_X_pow_sub
    compute_degree
    norm_num
  have he : P.eval 1 ∈ p := by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul, one_pow, mul_one, sub_self]
    exact p.sub_mem (p.sub_mem (Ideal.zero_mem _) (p.mul_mem_left 3 hc))
      (p.mul_mem_left 3 (by simpa [pow_two] using p.mul_mem_left c hc))
  have hd : IsUnit ((Ideal.Quotient.mk p) (P.derivative.eval 1)) := by
    have h : (Ideal.Quotient.mk p) (P.derivative.eval 1) = 1 := by
      simp [P, Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_mul, show (Ideal.Quotient.mk p) c = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hc]
      norm_num [map_ofNat]
    rw [h]
    exact isUnit_one
  obtain ⟨w, hw, hwp⟩ := HenselianRing.is_henselian P hm 1 he hd
  have hwunit : IsUnit w := by
    have hnone : ¬w ∈ p := by
      intro h
      have hone := p.sub_mem h hwp
      simp only [sub_sub_cancel] at hone
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    simpa [p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnone
  have hwf : w^3-w^2-3*c*w-3*c^2 = 0 := by
    simpa [Polynomial.IsRoot, P] using hw
  let t : O := 1 + 3*c*↑(hwunit.unit⁻¹)
  have ht : t^3 = 1+9*c := by
    apply Subtype.val_injective
    have hwn : (w : K) ≠ 0 := by
      have hh := (Valuation.integer.integers (valuation K)).one_of_isUnit hwunit
      change valuation K (w : K) = 1 at hh
      intro hz
      simp [hz] at hh
    have hwi : ((↑(hwunit.unit⁻¹) : O) : K) = (w : K)⁻¹ := by
      have hmul : (w : K) * ((↑(hwunit.unit⁻¹) : O) : K) = 1 := by
        have hO : (hwunit.unit : O) * (↑(hwunit.unit⁻¹) : O) = 1 := by simp
        simpa only [Subring.coe_mul, Subring.coe_one, hwunit.unit_spec] using
          congrArg (fun x : O => (x : K)) hO
      have := congrArg (fun x : K => (w : K)⁻¹*x) hmul
      simpa [hwn, ← mul_assoc] using this
    have hwfK := congrArg (fun x : O => (x : K)) hwf
    change (1 + 3*(c : K)*((↑(hwunit.unit⁻¹) : O) : K))^3 = 1+9*(c : K)
    rw [hwi]
    field_simp [hwn]
    change (O.subtype (w ^ 3 - w ^ 2 - 3*c*w - 3*c^2)) = O.subtype 0 at hwfK
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at hwfK
    change (w : K)^3 - (w : K)^2 - 3*(c : K)*(w : K) - 3*(c : K)^2 = 0 at hwfK
    linear_combination -9*(c : K)*hwfK
  have htu : IsUnit t := by
    have hnone : ¬t ∈ p := by
      intro htm
      have hdiff : t - 1 ∈ p := by
        dsimp [t]; simpa using p.mul_mem_right ↑(hwunit.unit⁻¹) (p.mul_mem_left 3 hc)
      have hone := p.sub_mem htm hdiff
      simp only [sub_sub_cancel] at hone
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    simpa [p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnone
  exact ⟨htu.unit, by rwa [htu.unit_spec]⟩

private theorem deep_units_cubes (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ∃ m : ℕ, principalUnits K m ≤ cubeUnits K := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  have h9 : Ideal.span ({(9 : Integers K)} : Set (Integers K)) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact by norm_num
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h9 hπ
  have hp : IsLocalRing.maximalIdeal (Integers K) ^ n = Ideal.span {(9 : Integers K)} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]
  refine ⟨n+1, ?_⟩
  intro u hu
  rw [mem_principalUnits] at hu
  rw [pow_succ, hp] at hu
  obtain ⟨c, hc, hcx⟩ := Ideal.mem_span_singleton_mul.mp hu
  obtain ⟨t, ht⟩ := cube_near_one K c hc
  change ∃ t : (Integers K)ˣ, t^3 = u
  refine ⟨t, ?_⟩
  apply Units.ext
  change (t : Integers K)^3 = (u : Integers K)
  rw [ht, hcx]
  ring

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

private theorem depth_three (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : Integers K) (hζ : IsPrimitiveRoot ζ 3) :
    (IsDiscreteValuationRing.addVal (Integers K) (3 : Integers K)).toNat = 2 * rootDepth K ζ := by
  let v := IsDiscreteValuationRing.addVal (Integers K)
  have hvz : v ζ = 0 := by
    obtain ⟨u, hu⟩ := hζ.isUnit (by decide)
    rw [← hu]
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit u
  have hpoly : ζ^2 + ζ + 1 = 0 := by
    have h : (ζ-1)*(ζ^2+ζ+1) = 0 := by
      calc
        _ = ζ^3 - 1 := by ring
        _ = 0 := by rw [hζ.pow_eq_one]; ring
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hζ.ne_one (by decide)))
  have hsecond : v (1-ζ^2) = v (1-ζ) := by
    have h : 1-ζ^2 = -ζ^2*(1-ζ) := by
      calc
        _ = -ζ^2*(1-ζ)+(1-ζ^3) := by ring
        _ = _ := by rw [hζ.pow_eq_one]; ring
    rw [h, v.map_mul, v.map_neg, v.map_pow, hvz, nsmul_zero, zero_add]
  have hprod : (1-ζ)*(1-ζ^2) = 3 := by
    calc
      _ = (ζ^3-1)-(ζ^2+ζ+1)+3 := by ring
      _ = _ := by rw [hζ.pow_eq_one, hpoly]; ring
  change (v 3).toNat = _
  have hfinite : v (1-ζ) ≠ ⊤ := by
    exact fun h => hζ.ne_one (by decide)
      (sub_eq_zero.mp (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)).symm
  rw [← hprod, v.map_mul, hsecond, ENat.toNat_add hfinite hfinite]
  change _ = 2 * (v (1-ζ)).toNat
  omega

theorem unit_cube_index
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : Integers K) (hζ : IsPrimitiveRoot ζ 3) :
    ((cubeUnits K).index : ℝ) = 3 / abs K (3 : K) := by
  obtain ⟨m, hm⟩ := deep_units_cubes K
  let j := max m (3 * rootDepth K ζ + 1)
  have hj : principalUnits K j ≤ cubeUnits K :=
    (principalUnits_antitone K m j (le_max_left _ _)).trans hm
  have hind : (cubeUnits K).index = 3 * residueCard K ^ (2 * rootDepth K ζ) := by
    have h := (kp_cubic_unit_truncated_indices K ζ hζ).2.2.2 j
      (by dsimp [j]; omega)
    simpa only [truncatedIndex, sup_eq_left.mpr hj] using h
  have h3 : abs K (3 : K) = (residueCard K : ℝ) ^ (-((2 * rootDepth K ζ : ℕ) : ℤ)) := by
    have hne : (3 : K) ≠ 0 := by norm_num
    have hO : (3 : Integers K) ≠ 0 := by norm_num
    simp only [abs, if_neg hne]
    rw [show (3 : K) = ((3 : Integers K) : K) from rfl,
      log_integer K (3 : Integers K) hO, depth_three K ζ hζ]
  rw [hind, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, h3, zpow_neg, zpow_natCast,
    div_inv_eq_mul]

end
end DedekindZetaZeroFree.KPCubicHaarTransport
