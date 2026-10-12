module

public import DedekindZetaZeroFree.Theta.Periods.ExteriorCompactInvariance
public import DedekindZetaZeroFree.Theta.Digits.RationalMaskFrequencies
public import DedekindZetaZeroFree.Metaplectic.Kubota.SixthPowerTorusRootCongruence
public import DedekindZetaZeroFree.Theta.Digits.SUnitReindexingCongruence

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField IsDedekindDomain
open scoped Classical BigOperators
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localAdele → eval_localAdele
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming integral_iff → integral_iff
open _root_.DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction.ArithmeticCongruence renaming loc → loc
open _root_.DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction.ArithmeticCongruence renaming loc_val → loc_val
open _root_.DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction.ArithmeticCongruence renaming loc_int → loc_int
open _root_.DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction.ArithmeticCongruence renaming loc_ideal → loc_ideal
open _root_.DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction.ArithmeticCongruence renaming digit_diff → digit_diff

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def exteriorUnit (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) (u : R.A.U) :
    (KPTameCompact.O F p)ˣ := Units.map (loc R.A p hp) (R.A.unitEquiv u)

theorem exteriorUnit_inclusion (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) (u : R.A.U) :
    KPTameCompact.unitInclusion F p (exteriorUnit R p hp u) =
      Units.map (algebraMap F (p.adicCompletion F)) u.val := by
  apply Units.ext
  rfl

theorem digitParameter_arch (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (w : InfinitePlace F) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w) (digitParameter R m d) = 0 := by
  rw [digitParameter, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  change (0 : InfiniteAdeleRing F) w = 0
  rfl

theorem digitParameter_S (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : KPFinitePlace F) (hp : p ∈ R.A.Sf) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p) (digitParameter R m d) = 0 := by
  simp only [digitParameter, map_sum, eval_localAdele]
  apply Finset.sum_eq_zero
  intro q _
  apply Pi.single_eq_of_ne
  intro h
  have he : p = q.val := h
  exact ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp q.property).1
    (he ▸ hp)

theorem digit_lift_congruence (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaDigitAverage.rowPrimes R.A m.val m.property) :
    let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
    let L := ThetaDigitAverage.residueLifts (ThetaDigitAverage.rowPrimes R.A m.val m.property)
    let g : F := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A ⟨p.val, hp⟩)
    (-algebraMap (𝓞 F) (p.val.adicCompletion F) (L.lift p (digitReindex R m u d p)) / algebraMap F _ g) -
      (algebraMap F (p.val.adicCompletion F) (u.val : F)) ^ 6 *
        (-algebraMap (𝓞 F) (p.val.adicCompletion F) (L.lift p (d p)) / algebraMap F _ g) ∈
          KPTameCompact.O F p.val := by
  letI : ValuativeRel (p.val.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F p.val
  letI : (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  dsimp only
  let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
  let L := ThetaDigitAverage.residueLifts (ThetaDigitAverage.rowPrimes R.A m.val m.property)
  let z : R.A.R := algebraMap (𝓞 F) R.A.R (L.lift p (digitReindex R m u d p)) -
    (R.A.unitEquiv u : R.A.R) ^ 6 * algebraMap (𝓞 F) R.A.R (L.lift p (d p))
  have hz : z ∈ Ideal.map (algebraMap (𝓞 F) R.A.R) p.val.asIdeal :=
    digit_diff R.A u _
      (fun q hq => ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp hq).1) d p
  have hzO := loc_ideal R.A p.val hp z hz
  have hzlt : Valued.v ((loc R.A p.val hp z : KPTameCompact.O F p.val) : p.val.adicCompletion F) < 1 := by
    rw [KPTameCompact.p, KPLocalCube.maximalIdeal, IsLocalRing.mem_maximalIdeal] at hzO
    have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hzO
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (p.val.adicCompletion F))
      (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.mp hv
  let g : F := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A ⟨p.val, hp⟩)
  have hg : Valued.v (algebraMap F (p.val.adicCompletion F) g) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (g : p.val.adicCompletion F) = _
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact generator_valuation R ⟨p.val, hp⟩
  have hint : -((loc R.A p.val hp z : KPTameCompact.O F p.val) : p.val.adicCompletion F) /
      algebraMap F (p.val.adicCompletion F) g ∈ KPTameCompact.O F p.val := by
    apply (ValuativeRel.isEquiv (ValuativeRel.valuation (p.val.adicCompletion F))
      (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one.mpr
    rw [map_div₀, Valuation.map_neg, hg]
    apply (div_le_one₀ (by simp)).mpr
    exact valuation_le_exp_neg_one hzlt
  convert hint using 1
  have he : ((loc R.A p.val hp z : KPTameCompact.O F p.val) : p.val.adicCompletion F) =
      algebraMap (𝓞 F) (p.val.adicCompletion F) (L.lift p (digitReindex R m u d p)) -
        (algebraMap F (p.val.adicCompletion F) (u.val : F)) ^ 6 *
          algebraMap (𝓞 F) (p.val.adicCompletion F) (L.lift p (d p)) := by
    rw [show z = algebraMap (𝓞 F) R.A.R (L.lift p (digitReindex R m u d p)) -
      (R.A.unitEquiv u : R.A.R) ^ 6 * algebraMap (𝓞 F) R.A.R (L.lift p (d p)) from rfl,
      map_sub, map_mul, map_pow]
    change (↑(loc R.A p.val hp (algebraMap (𝓞 F) R.A.R (L.lift p (digitReindex R m u d p)))) :
      p.val.adicCompletion F) -
      (↑(loc R.A p.val hp (R.A.unitEquiv u : R.A.R)) : p.val.adicCompletion F) ^ 6 *
        (↑(loc R.A p.val hp (algebraMap (𝓞 F) R.A.R (L.lift p (d p)))) : p.val.adicCompletion F) = _
    rw [loc_int, loc_int, loc_val]
    rfl
  rw [he]
  ring

theorem digitParameter_congruence (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : KPFinitePlace F) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p) (digitParameter R m (digitReindex R m u d)) -
      (algebraMap F (p.adicCompletion F) (u.val : F)) ^ 6 *
        KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p) (digitParameter R m d) ∈ KPTameCompact.O F p := by
  simp only [digitParameter, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, eval_localAdele]
  apply (KPTameCompact.O F p).sum_mem
  intro q _
  by_cases he : p = q.val
  · subst p
    change _ ∈ KPTameCompact.O F q.val
    have hz (x : q.val.adicCompletion F) :
        KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr q.val)
          (KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) x) = x := by
      change Pi.single q.val x q.val = x
      exact Pi.single_eq_same _ _
    rw [hz, hz]
    exact digit_lift_congruence R m u d q
  · have hz (x : q.val.adicCompletion F) :
        KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p)
          (KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) x) = 0 := by
      change Pi.single q.val x p = 0
      exact Pi.single_eq_of_ne he _
    rw [hz, hz]
    simp

end DedekindZetaZeroFree.DigitMasks

end
