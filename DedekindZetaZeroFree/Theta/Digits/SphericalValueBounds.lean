module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalBruhatNorms

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField IsDedekindDomain ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma completion_integer_of_valuation_le_one (p : KPFinitePlace F) (a : F)
    (ha : p.valuation F a ≤ 1) :
    algebraMap F (p.adicCompletion F) a ∈ KPTameCompact.O F p := by
  letI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  apply (ValuativeRel.isEquiv (ValuativeRel.valuation (p.adicCompletion F))
    (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one.mpr
  change Valued.v (a : p.adicCompletion F) ≤ 1
  rwa [HeightOneSpectrum.adicCompletion.valued_coe]

abbrev RowPrime (m : ThetaReflectionData.Row R.A) :=
  ThetaDigitAverage.rowPrimes R.A m.val m.property

def rowExterior (m : ThetaReflectionData.Row R.A) (p : RowPrime R m) :
    ThetaBranch.ExteriorPrime R.A :=
  ⟨p.val, ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩

def digitLift (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) : 𝓞 F :=
  (ThetaDigitAverage.residueLifts (RowPrime R m)).lift p (d p)

def rationalDigit (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) : F :=
  -(digitLift R m d p : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A (rowExterior R m p)) : F)

lemma digitLift_residue (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) :
    Ideal.Quotient.mk p.val.asIdeal (digitLift R m d p) = d p :=
  ThetaDigitAverage.ResidueLifts.residue_lift _ _ _

lemma digitParameter_at_row (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d) =
      algebraMap F (p.val.adicCompletion F) (rationalDigit R m d p) := by
  simp only [digitParameter, map_sum]
  rw [Finset.sum_eq_single p]
  · rw [DedekindZetaZeroFree.KPRationalAdelicSplitting.eval_localAdele, Pi.single_eq_same]
    simp only [rationalDigit, digitLift, map_div₀, map_neg,
      IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F)]
    rfl
  · intro q hq hqp
    apply Pi.single_eq_of_ne
    exact fun he => hqp (Subtype.ext he.symm)
  · intro hp
    exact False.elim (hp (Finset.mem_univ p))

lemma digitParameter_off_row (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : KPFinitePlace F)
    (hp : p ∉ RowPrime R m) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p) (digitParameter R m d) = 0 := by
  simp only [digitParameter, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  apply Pi.single_eq_of_ne
  exact fun he => hp (he.symm ▸ q.property)

lemma zero_digit_integral (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hd : d p = 0) :
    algebraMap F (p.val.adicCompletion F) (rationalDigit R m d p) ∈ KPTameCompact.O F p.val := by
  apply completion_integer_of_valuation_le_one
  have hs : digitLift R m d p ∈ p.val.asIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp ((digitLift_residue R m d p).trans hd)
  have hv := DigitMasks.valuation_le_exp_neg_one
    ((p.val.valuation_lt_one_iff_mem (K := F) _).mpr hs)
  change p.val.valuation F (-((digitLift R m d p : 𝓞 F) : F) /
    (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A (rowExterior R m p)) : F)) ≤ 1
  have hg := DigitMasks.generator_valuation R (rowExterior R m p)
  change p.val.valuation F _ = WithZero.exp (-1 : ℤ) at hg
  rw [map_div₀, Valuation.map_neg, hg]
  exact (div_le_one₀ (by simp)).mpr hv

lemma nonzero_digitLift (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hd : d p ≠ 0) :
    (digitLift R m d p : F) ≠ 0 := by
  have hs : digitLift R m d p ∉ p.val.asIdeal := by
    intro h
    exact hd ((digitLift_residue R m d p).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  intro h
  have hz : digitLift R m d p = 0 := Subtype.ext h
  exact hs (hz ▸ p.val.asIdeal.zero_mem)

lemma nonzero_digit_valuation (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hd : d p ≠ 0) :
    p.val.valuation F (rationalDigit R m d p) = WithZero.exp (1 : ℤ) := by
  have hs : digitLift R m d p ∉ p.val.asIdeal := by
    intro h
    exact hd ((digitLift_residue R m d p).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  have hg := DigitMasks.generator_valuation R (rowExterior R m p)
  change p.val.valuation F _ = WithZero.exp (-1 : ℤ) at hg
  simp only [rationalDigit, map_div₀, Valuation.map_neg,
    p.val.valuation_eq_one_iff_notMem.mpr hs, hg, one_div, ← WithZero.exp_neg, neg_neg]

lemma nonzero_digit_inverse_integral (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hd : d p ≠ 0) :
    algebraMap F (p.val.adicCompletion F) ((rationalDigit R m d p)⁻¹) ∈ KPTameCompact.O F p.val := by
  apply completion_integer_of_valuation_le_one
  rw [map_inv₀, nonzero_digit_valuation R m d p hd, ← WithZero.exp_neg,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField IsDedekindDomain
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

lemma exteriorDigitValue_eq_slot (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : ThetaBranch.ExteriorPrime R.A) :
    exteriorDigitValue R D m x d p = OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
       KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d))) := by
  rw [exteriorDigitValue, OrbitExpansion.reverseTuple_exterior]
  have h := DedekindZetaZeroFree.KPRationalAdelicSplitting.eval_localIdele F (Sum.inr p.val) (Sum.inr p.val)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
  simp only [Pi.mulSingle_eq_same] at h
  change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val)).toMonoidHom
    (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) = _ at h
  exact congrArg (fun z => OrbitExpansion.exteriorSlotValue R D p.val
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d)))) h

lemma exterior_diagonal_slot (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    OrbitExpansion.exteriorSlotValue R D p.val
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) = D.exteriorValue R p x := by
  unfold SourceFactorization.exteriorValue
  have h := DedekindZetaZeroFree.KPRationalAdelicSplitting.eval_localIdele F (Sum.inr p.val) (Sum.inr p.val)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
  simp only [Pi.mulSingle_eq_same] at h
  change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val)).toMonoidHom
    (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) = _ at h
  exact congrArg (fun z => OrbitExpansion.exteriorSlotValue R D p.val
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z)) h.symm

lemma exteriorDigitValue_off_row (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : ThetaBranch.ExteriorPrime R.A)
    (hp : p.val ∉ RowPrime R m) :
    exteriorDigitValue R D m x d p = D.exteriorValue R p x := by
  rw [exteriorDigitValue_eq_slot, digitParameter_off_row R m d p.val hp]
  have h := exterior_integral_digit_value R D p
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) 0
  simpa only [ZeroMemClass.coe_zero] using h.trans (exterior_diagonal_slot R D p x)

lemma exteriorDigitValue_zero (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hp : d p = 0) :
    exteriorDigitValue R D m x d (rowExterior R m p) = D.exteriorValue R (rowExterior R m p) x := by
  rw [exteriorDigitValue_eq_slot]
  have he := digitParameter_at_row R m d p
  change KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr (rowExterior R m p).val)
    (digitParameter R m d) = _ at he
  rw [he]
  have h := exterior_integral_digit_value R D (rowExterior R m p)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
    ⟨_, zero_digit_integral R m d p hp⟩
  exact h.trans (exterior_diagonal_slot R D _ x)

def digitUnit (m : ThetaReflectionData.Row R.A) (d : ThetaDigitAverage.Dig (RowPrime R m))
    (p : RowPrime R m) (hp : d p ≠ 0) : Fˣ :=
  Units.mk0 (rationalDigit R m d p) (div_ne_zero (neg_ne_zero.mpr (nonzero_digitLift R m d p hp))
    (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A (rowExterior R m p))).ne_zero)

lemma exteriorDigitValue_nonzero_norm (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hp : d p ≠ 0) :
    ‖exteriorDigitValue R D m x d (rowExterior R m p)‖ =
      ‖D.exteriorValue R (rowExterior R m p) (x * -((digitUnit R m d p hp)⁻¹ ^ 2))‖ := by
  let H := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom (digitUnit R m d p hp)
  have hi : (H⁻¹ : p.val.adicCompletion F) ∈ KPTameCompact.O F p.val := by
    simpa only [H, digitUnit, Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0,
      map_inv₀, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using nonzero_digit_inverse_integral R m d p hp
  have h := exterior_nonintegral_digit_norm R D (rowExterior R m p)
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) H hi
  rw [exteriorDigitValue_eq_slot]
  have he := digitParameter_at_row R m d p
  change KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr (rowExterior R m p).val)
    (digitParameter R m d) = _ at he
  rw [he]
  have hr : Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
      (x * -((digitUnit R m d p hp)⁻¹ ^ 2)) =
      Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x * -(H⁻¹ ^ 2) := by
    apply Units.ext
    simp only [Units.coe_map, Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      map_mul, map_neg, map_pow, map_inv₀, H]
  rw [← hr] at h
  have hs := exterior_diagonal_slot R D (rowExterior R m p) (x * -((digitUnit R m d p hp)⁻¹ ^ 2))
  dsimp only [rowExterior] at hs h ⊢
  rw [hs] at h
  simpa only [H, digitUnit, Units.coe_map, Units.val_mk0,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using h
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField IsDedekindDomain
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)

lemma spherical_symbol_norm (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    ‖ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x)‖ = 1 := by
  unfold ThetaBranch.symbol
  let u := (isUnit_iff_ne_zero.mpr (ThetaBranch.unitResidue_ne_zero p.val _
    (ThetaBranch.localUnit_order R.A R.probe.allowed p x))).unit
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((ThetaBranch.residueCharacter R.A R.σ p).apply_mem_rootsOfUnity u)
  simpa only [MulChar.coe_equivToUnitHom, u, IsUnit.unit_spec] using h

lemma spherical_norm_le_one (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    ‖ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x‖ ≤ 1 := by
  rw [ThetaBranch.sphericalFactor, norm_mul, norm_zpow, spherical_symbol_norm R, one_zpow, mul_one]
  have hQ : (1 : ℝ) ≤ Fintype.card (DHCubic.Residue F p.val) := by
    exact_mod_cast Fintype.card_pos (α := DHCubic.Residue F p.val)
  have hg := DedekindZetaZeroFree.ThetaPhaseSeparation.norm_gaussTwo R.A R.σ (Characters.psi R) (Characters.primitive R) p
  unfold ThetaBranch.gaussTwo at hg
  unfold sexticSphericalCoefficient
  split_ifs with hn h0 h1
  · norm_num
  · rw [norm_zpow, Complex.norm_natCast]
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_one_of_one_le_of_nonpos hQ
    exact_mod_cast neg_nonpos.mpr (Int.ediv_nonneg (by omega) (by norm_num : (0 : ℤ) ≤ 3))
  · rw [norm_mul, norm_mul, hg, mul_one, norm_zpow, Complex.norm_natCast,
      norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_one₀
    · rw [← Real.rpow_intCast]
      apply Real.rpow_le_one_of_one_le_of_nonpos hQ
      exact_mod_cast neg_nonpos.mpr (Int.ediv_nonneg (by omega) (by norm_num : (0 : ℤ) ≤ 3))
    · positivity
    · exact (inv_le_one₀ (by positivity)).mpr ((Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hQ))
  · norm_num

include E in
lemma exteriorValue_norm_le_one (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    ‖D.exteriorValue R p x‖ ≤ 1 := by
  rw [E.rational_exact]
  exact spherical_norm_le_one R p x

include E in
lemma exteriorValue_zero_of_order_neg (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ)
    (hx : ThetaBranch.order p.val x < 0) : D.exteriorValue R p x = 0 := by
  rw [E.rational_exact]
  simp only [ThetaBranch.sphericalFactor, sexticSphericalCoefficient, ite_eq_left hx, zero_mul]

lemma digitUnit_order (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hp : d p ≠ 0) :
    ThetaBranch.order p.val (digitUnit R m d p hp) = -1 := by
  simp only [ThetaBranch.order, digitUnit, Units.val_mk0, nonzero_digit_valuation R m d p hp,
    WithZero.log_exp]

lemma digit_shift_order (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : RowPrime R m) (hp : d p ≠ 0) :
    ThetaBranch.order p.val (x * -((digitUnit R m d p hp)⁻¹ ^ 2)) = ThetaBranch.order p.val x + 2 := by
  rw [DedekindZetaZeroFree.ThetaBranch.ord_mul]
  have hn (z : Fˣ) : ThetaBranch.order p.val (-z) = ThetaBranch.order p.val z := by
    simp only [ThetaBranch.order, Units.val_neg, Valuation.map_neg]
  rw [hn, ← zpow_natCast, DedekindZetaZeroFree.ThetaBranch.ord_zpow, ← zpow_neg_one, DedekindZetaZeroFree.ThetaBranch.ord_zpow,
    digitUnit_order R m d p hp]
  ring

include E in
lemma exteriorDigitValue_norm_le_one (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : ThetaBranch.ExteriorPrime R.A) :
    ‖exteriorDigitValue R D m x d p‖ ≤ 1 := by
  by_cases hp : p.val ∈ RowPrime R m
  · let q : RowPrime R m := ⟨p.val, hp⟩
    have he : rowExterior R m q = p := Subtype.ext rfl
    rw [← he]
    by_cases hd : d q = 0
    · rw [exteriorDigitValue_zero R D m x d q hd]
      exact exteriorValue_norm_le_one R D E _ _
    · rw [exteriorDigitValue_nonzero_norm R D m x d q hd]
      exact exteriorValue_norm_le_one R D E _ _
  · rw [exteriorDigitValue_off_row R D m x d p hp]
    exact exteriorValue_norm_le_one R D E p x

include E in
lemma exteriorDigitValue_zero_below (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (p : ThetaBranch.ExteriorPrime R.A)
    (hx : ThetaBranch.order p.val x < if p.val ∈ RowPrime R m then -2 else 0) :
    exteriorDigitValue R D m x d p = 0 := by
  by_cases hp : p.val ∈ RowPrime R m
  · rw [ite_eq_left hp] at hx
    let q : RowPrime R m := ⟨p.val, hp⟩
    have he : rowExterior R m q = p := Subtype.ext rfl
    rw [← he]
    by_cases hd : d q = 0
    · rw [exteriorDigitValue_zero R D m x d q hd]
      exact exteriorValue_zero_of_order_neg R D E _ _ (by dsimp [rowExterior, q]; omega)
    · apply norm_eq_zero.mp
      rw [exteriorDigitValue_nonzero_norm R D m x d q hd,
        exteriorValue_zero_of_order_neg R D E, norm_zero]
      change ThetaBranch.order q.val _ < 0
      rw [digit_shift_order R]
      dsimp [q]
      omega
  · rw [ite_eq_right hp] at hx
    rw [exteriorDigitValue_off_row R D m x d p hp]
    exact exteriorValue_zero_of_order_neg R D E p x hx
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField IsDedekindDomain
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)

def digitExterior (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) : ℂ := ∏ᶠ p, exteriorDigitValue R D m x d p

lemma digitExterior_finite (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) :
    Function.HasFiniteMulSupport (exteriorDigitValue R D m x d) :=
  (reverseTuple_period R D 1 x 1 m d).1

include E in
lemma digitExterior_norm_le_one (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) : ‖digitExterior R D m x d‖ ≤ 1 := by
  have ht := finprod_eq_prod_of_mulSupport_subset (f := exteriorDigitValue R D m x d)
    (s := (digitExterior_finite R D m x d).toFinset)
    (by intro p hp; exact (digitExterior_finite R D m x d).mem_toFinset.mpr hp)
  rw [digitExterior, ht]
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun p _ => exteriorDigitValue_norm_le_one R D E m x d p)

include E in
lemma digitExterior_order_lower (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (hx : digitExterior R D m x d ≠ 0)
    (p : ThetaBranch.ExteriorPrime R.A) :
    (if p.val ∈ RowPrime R m then -2 else 0) ≤ ThetaBranch.order p.val x := by
  by_contra hn
  have hz := exteriorDigitValue_zero_below R D E m x d p (by omega)
  exact hx (finprod_eq_zero _ p hz (digitExterior_finite R D m x d))

lemma valuation_eq_exp_order (p : KPFinitePlace F) (x : Fˣ) :
    p.valuation F (x : F) = WithZero.exp (-ThetaBranch.order p x) := by
  simpa only [ThetaBranch.order, neg_neg] using
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr x.ne_zero)).symm

include E in
lemma digitExterior_row_square_integral (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (hx : digitExterior R D m x d ≠ 0) :
    ((ThetaReflectionData.rowUnit R.A m ^ 2 * x : Fˣ) : F) ∈ R.A.R := by
  intro p hp
  have he := digitExterior_order_lower R D E m x d hx ⟨p, hp⟩
  have hn : 0 ≤ ThetaBranch.order p (ThetaReflectionData.rowUnit R.A m) := by
    have hm := m.val.property p hp
    change p.valuation F (ThetaReflectionData.rowUnit R.A m : F) ≤ 1 at hm
    rw [valuation_eq_exp_order] at hm
    have := WithZero.exp_le_one_iff.mp hm
    omega
  have htotal : 0 ≤ 2 * ThetaBranch.order p (ThetaReflectionData.rowUnit R.A m) + ThetaBranch.order p x := by
    by_cases hr : p ∈ RowPrime R m
    · have hv := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp hr).2
      change p.valuation F (ThetaReflectionData.rowUnit R.A m : F) < 1 at hv
      rw [valuation_eq_exp_order] at hv
      have := WithZero.exp_lt_one_iff.mp hv
      rw [ite_eq_left hr] at he
      change -2 ≤ ThetaBranch.order p x at he
      omega
    · rw [ite_eq_right hr] at he
      change 0 ≤ ThetaBranch.order p x at he
      omega
  rw [valuation_eq_exp_order, DedekindZetaZeroFree.ThetaBranch.ord_mul, ← zpow_natCast, DedekindZetaZeroFree.ThetaBranch.ord_zpow]
  apply WithZero.exp_le_one_iff.mpr
  norm_num at *
  omega
end DedekindZetaZeroFree.OrbitFrequencies
end
