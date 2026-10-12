module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.CubicCharacterExpansion

@[expose] public section

namespace DedekindZetaZeroFree.KPRankoneCubicScalarSum

open scoped BigOperators

open Classical

noncomputable def unramifiedFactor {F : Type*} [Field F] (a b : F) : F :=
  (1 - a * b) * (1 - a * b⁻¹) / ((1 - b) * (1 - b⁻¹))

noncomputable def betaFactor
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {F : Type*} [Field F]
    (ξ : CubicUnitCharacters.Character K) (b : F) : F :=
  if ξ = 1 then unramifiedFactor (CubicUnitCharacters.residueCard K : F)⁻¹ b
  else (CubicUnitCharacters.residueCard K : F)⁻¹ ^ CubicUnitCharacters.conductor K ξ

noncomputable local instance : Fintype CubicCharacters.Mu3 := Fintype.ofFinite _

private lemma moments {F : Type*} [Field F] (c : ℂ →+* F) (n : ℕ) :
    (∑ ζ : CubicCharacters.Mu3, c (((ζ : ℂˣ) : ℂ)) ^ n) =
      if 3 ∣ n then (3 : F) else 0 := by
  have h := KPCubicExpansion.sum_mu3_zpow (n : ℤ)
  rw [finsum_eq_sum_of_fintype] at h
  have hn : (3 : ℤ) ∣ (n : ℤ) ↔ 3 ∣ n := by exact_mod_cast Iff.rfl
  simp only [zpow_natCast, hn] at h
  simpa only [Units.val_pow_eq_pow_val, map_sum, map_pow, map_ofNat, map_zero, apply_ite] using congrArg c h

private lemma root_sum {F : Type*} [Field F] (c : ℂ →+* F) (u : F)
    (hu : 1-u^3 ≠ 0) :
    (∑ ζ : CubicCharacters.Mu3, c (((ζ : ℂˣ) : ℂ)) * u / (1-c (((ζ : ℂˣ) : ℂ))*u)^2) =
      9*u^3/(1-u^3)^2 := by
  have h3 (ζ : CubicCharacters.Mu3) : (c (((ζ : ℂˣ) : ℂ))*u)^3 = u^3 := by
    have hz : (((ζ : ℂˣ) : ℂ))^3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.2, Units.val_one]
    rw [mul_pow, ← map_pow, hz, map_one, one_mul]
  have he (ζ : CubicCharacters.Mu3) :
      c (((ζ : ℂˣ) : ℂ))*u / (1-c (((ζ : ℂˣ) : ℂ))*u)^2 =
      ((c (((ζ : ℂˣ) : ℂ))*u) + 2*(c (((ζ : ℂˣ) : ℂ))*u)^2 +
       3*(c (((ζ : ℂˣ) : ℂ))*u)^3 + 2*(c (((ζ : ℂˣ) : ℂ))*u)^4 +
       (c (((ζ : ℂˣ) : ℂ))*u)^5)/(1-u^3)^2 := by
    set v := c (((ζ : ℂˣ) : ℂ))*u
    have hf : 1-u^3 = (1-v)*(1+v+v^2) := by rw [← h3 ζ]; dsimp [v]; ring
    have hv : 1-v ≠ 0 := by intro hz; rw [hf, hz, zero_mul] at hu; exact hu rfl
    apply (div_eq_div_iff (pow_ne_zero 2 hv) (pow_ne_zero 2 hu)).mpr
    rw [hf]; ring
  simp_rw [he]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  have hm1 := moments c 1
  simp only [pow_one] at hm1
  rw [hm1, moments c 2, moments c 3, moments c 4, moments c 5]
  norm_num
  ring

private lemma unr {F : Type*} [Field F] (a b : F) (hb : b ≠ 0) (hb1 : 1-b ≠ 0) :
    unramifiedFactor a b = a - (1-a)^2*b/(1-b)^2 := by
  have hi : 1-b⁻¹ ≠ 0 := by
    intro h
    have : b⁻¹ = 1 := by linear_combination -h
    have : b = 1 := inv_eq_one.mp this
    exact hb1 (by rw [this]; ring)
  unfold unramifiedFactor
  have hm : b - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hb1 (by rw [h]; ring))
  field_simp [hb, hb1, hi, hm]
  <;> ring

private lemma char_sum (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ω : K) (hω : IsPrimitiveRoot ω 3)
    {F : Type*} [Field F] [CharZero F] (c : ℂ →+* F) (u : F)
    (hu : u ≠ 0) (hu3 : 1-u^3 ≠ 0) :
    (1/9 : F) * (∑ᶠ ξ : CubicUnitCharacters.Character K,
      ∑ᶠ ζ : CubicCharacters.Mu3, betaFactor K ξ (c (((ζ : ℂˣ) : ℂ))*u)) =
      unramifiedFactor (CubicUnitCharacters.residueCard K : F)⁻¹ (u^3) := by
  obtain ⟨hf, _, _, hc, hs⟩ := kp_local_unramified_character_count K ω hω
  letI := hf
  letI : Fintype (CubicUnitCharacters.Character K) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at hs
  have hsum : (∑ ξ : CubicUnitCharacters.Character K,
      (CubicUnitCharacters.residueCard K : F)⁻¹ ^ CubicUnitCharacters.conductor K ξ) =
      1 + 2*(CubicUnitCharacters.residueCard K : F)⁻¹ := by
    have hh := congrArg (c.comp Complex.ofRealHom) hs
    simpa only [map_sum, map_pow, map_inv₀, map_natCast, map_add, map_mul,
      map_one, map_ofNat] using hh
  have hcond : CubicUnitCharacters.conductor K 1 = 0 := (hc 1).mpr rfl
  have hz0 (ζ : CubicCharacters.Mu3) : c (((ζ : ℂˣ) : ℂ)) ≠ 0 := by
    simpa only [map_zero] using c.injective.ne (Units.ne_zero (ζ : ℂˣ))
  have hz1 (ζ : CubicCharacters.Mu3) : 1-c (((ζ : ℂˣ) : ℂ))*u ≠ 0 := by
    intro he
    have he1 : c (((ζ : ℂˣ) : ℂ))*u = 1 := by linear_combination -he
    have hh : (c (((ζ : ℂˣ) : ℂ))*u)^3 = u^3 := by
      have hz : (((ζ : ℂˣ) : ℂ))^3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.2, Units.val_one]
      rw [mul_pow, ← map_pow, hz, map_one, one_mul]
    rw [he1, one_pow] at hh
    exact hu3 (by rw [← hh]; ring)
  have hb (ξ : CubicUnitCharacters.Character K) (ζ : CubicCharacters.Mu3) :
      betaFactor K ξ (c (((ζ : ℂˣ) : ℂ))*u) =
        (CubicUnitCharacters.residueCard K : F)⁻¹ ^ CubicUnitCharacters.conductor K ξ -
          if ξ = 1 then (1-(CubicUnitCharacters.residueCard K : F)⁻¹) +
            (1-(CubicUnitCharacters.residueCard K : F)⁻¹)^2 *
            (c (((ζ : ℂˣ) : ℂ))*u / (1-c (((ζ : ℂˣ) : ℂ))*u)^2) else 0 := by
    by_cases he : ξ = 1
    · subst ξ
      simp only [betaFactor, if_pos rfl, hcond, pow_zero, ↓reduceIte]
      rw [unr _ _ (mul_ne_zero (hz0 ζ) hu) (hz1 ζ)]
      ring
    · simp [betaFactor, he]
  simp_rw [finsum_eq_sum_of_fintype, hb, Finset.sum_sub_distrib]
  have hcard : Fintype.card CubicCharacters.Mu3 = 3 := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← Finset.mul_sum, hsum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum, root_sum c u hu3,
    unr _ _ (pow_ne_zero 3 hu) hu3]
  ring

theorem cubic_character_sum
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ω : K) (hω : IsPrimitiveRoot ω 3)
    (z t : ℂ) (hz : z ≠ 0) (hzt : z ^ 3 = t) (ht : t ≠ 1) :
    (1 / 9 : ℂ) *
      (∑ᶠ ξ : CubicUnitCharacters.Character K,
        ∑ᶠ ζ : CubicCharacters.Mu3, betaFactor K ξ (((ζ : ℂˣ) : ℂ) * z)) =
      unramifiedFactor (CubicUnitCharacters.residueCard K : ℂ)⁻¹ t := by
  have hu3 : 1-z^3 ≠ 0 := sub_ne_zero.mpr (fun h => ht (hzt.symm.trans h.symm))
  simpa only [hzt, RingHom.id_apply] using
    char_sum K ω hω (RingHom.id ℂ) z hz hu3

noncomputable def finiteScalar
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m j : ℝ) (z : ℂ) : ℂ :=
  ((m ^ 2 * j : ℝ) : ℂ) / 9 *
    (∑ᶠ ξ : CubicUnitCharacters.Character K,
      ∑ᶠ ζ : CubicCharacters.Mu3, betaFactor K ξ (((ζ : ℂˣ) : ℂ) * z))

theorem finiteScalar_eq
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ω : K) (hω : IsPrimitiveRoot ω 3)
    (m j : ℝ) (z t : ℂ) (hz : z ≠ 0) (hzt : z ^ 3 = t) (ht : t ≠ 1) :
    finiteScalar K m j z = ((m ^ 2 * j : ℝ) : ℂ) *
      ((1 - (CubicUnitCharacters.residueCard K : ℂ)⁻¹ * t) *
        (1 - (CubicUnitCharacters.residueCard K : ℂ)⁻¹ * t⁻¹) /
          ((1 - t) * (1 - t⁻¹))) := by
  have h := cubic_character_sum K ω hω z t hz hzt ht
  unfold finiteScalar
  rw [show ((m^2*j : ℝ) : ℂ)/9 = ((m^2*j : ℝ) : ℂ)*(1/9) by ring, mul_assoc, h]
  rfl

theorem finiteScalar_cube_root_independent
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ω : K) (hω : IsPrimitiveRoot ω 3)
    (m j : ℝ) (z z' t : ℂ) (hz : z ≠ 0) (hz' : z' ≠ 0)
    (hzt : z ^ 3 = t) (hz't : z' ^ 3 = t) (ht : t ≠ 1) :
    finiteScalar K m j z = finiteScalar K m j z' := by
  rw [finiteScalar_eq K ω hω m j z t hz hzt ht,
    finiteScalar_eq K ω hω m j z' t hz' hz't ht]

end DedekindZetaZeroFree.KPRankoneCubicScalarSum
