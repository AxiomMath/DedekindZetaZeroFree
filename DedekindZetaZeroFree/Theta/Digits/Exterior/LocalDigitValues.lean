module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.NonzeroDigitEvaluation

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localAdele → eval_localAdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)

abbrev RowPrime (m : ThetaReflectionData.Row R.A) :=
  {p // p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property}

abbrev exteriorRowPrime (m : ThetaReflectionData.Row R.A) (p : RowPrime R m) : ThetaBranch.ExteriorPrime R.A :=
  ⟨p.val, ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩

def localDigitValue (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F) : ℂ :=
  C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
      KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
      KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (-algebraMap (𝓞 F) (p.val.adicCompletion F) s /
          algebraMap F (p.val.adicCompletion F)
            (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))
    (C.factorization.references (Sum.inr p.val)))

theorem parameter_at_row (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : RowPrime R m) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d) =
      -algebraMap (𝓞 F) (p.val.adicCompletion F)
        ((ThetaDigitAverage.residueLifts _).lift p (d p)) /
        algebraMap F (p.val.adicCompletion F)
          (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A (exteriorRowPrime R m p)) : F) := by
  simp only [digitParameter, map_sum, eval_localAdele]
  rw [Finset.sum_eq_single p]
  · rw [eval_localAdele]
    simp only [Pi.single_eq_same]
  · intro q _ hq
    apply Pi.single_eq_of_ne
    intro he
    exact hq (Subtype.ext he.symm)
  · simp

theorem factor_at_row (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : RowPrime R m) :
    ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d (exteriorRowPrime R m p) =
      localDigitValue R C (exteriorRowPrime R m p) x ((ThetaDigitAverage.residueLifts _).lift p (d p)) := by
  rw [digit_word]
  have hp := parameter_at_row R m d p
  change KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr (exteriorRowPrime R m p).val)
    (digitParameter R m d) = _ at hp
  rw [hp]
  rfl

theorem zero_localDigit (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F)
    (hs : Ideal.Quotient.mk p.val.asIdeal s = 0) :
    localDigitValue R C p x s = ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x := by
  have hm : s ∈ p.val.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hs
  have hv : p.val.valuation F (s : F) < 1 := (p.val.valuation_lt_one_iff_mem s).mpr hm
  let z := -algebraMap (𝓞 F) (p.val.adicCompletion F) s /
    algebraMap F (p.val.adicCompletion F)
      (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)
  have hz : z ∈ p.val.adicCompletionIntegers F := by
    change Valued.v z ≤ 1
    have he : z = algebraMap F (p.val.adicCompletion F)
      (-(s : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) := by
      simp [z, ← IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F)]
    rw [he]
    change Valued.v (algebraMap F (p.val.adicCompletion F)
      (-(s : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F))) ≤ 1
    change Valued.v ((-(s : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F) : F) : p.val.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe, map_div₀, Valuation.map_neg,
      DigitMasks.generator_valuation R p]
    apply (div_le_one₀ (by simp)).mpr
    exact DigitMasks.valuation_le_exp_neg_one hv
  have hf := (C.factorization.spherical_reference p.val p.property).2
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z)
    (exterior_integral_root_mem_compact R p ⟨z,hz⟩)
  change exteriorImageAction R C.toJointHaarFactorizedSources p
    (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z)
    (C.factorization.references (Sum.inr p.val)) = C.factorization.references (Sum.inr p.val) at hf
  unfold localDigitValue
  change C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
    (_ * _ * KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z) _) = _
  simp only [map_mul, Module.End.mul_apply]
  rw [hf, weyl_fixed R C p, ← exterior_diagonal_eq_standard_lift]
  exact C.exterior.rational_exact p x

theorem nonzero_localDigit (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F)
    (hs : Ideal.Quotient.mk p.val.asIdeal s ≠ 0) :
    localDigitValue R C p x s =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
        (ThetaBranch.order p.val x + 2) *
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x) ^
        (4 + 2 * (ThetaBranch.order p.val x + 2)) *
      ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal s) ^ (4 : ℕ) *
      (if ThetaBranch.order p.val x + 2 = 0 then
        Characters.psi R p
          (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x) /
            Ideal.Quotient.mk p.val.asIdeal s) else 1) := by
  have hm : s ∉ p.val.asIdeal := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hsn : (s : F) ≠ 0 := by
    exact_mod_cast (fun h => hm (h ▸ p.val.asIdeal.zero_mem) : s ≠ 0)
  let V := Units.mk0 (s : F) hsn
  have hv : ThetaBranch.order p.val V = 0 := by
    simp [ThetaBranch.order, V, p.val.valuation_eq_one_iff_notMem.mpr hm]
  have hr := reduction_integral p.val s hm
  have hh := nonzero_value R C p x V hv
  unfold ThetaBranch.symbol at hh
  rw [hr] at hh
  exact hh

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
