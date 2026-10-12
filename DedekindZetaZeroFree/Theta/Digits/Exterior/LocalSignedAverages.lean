module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.LocalDigitValues

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)

theorem rowExponent_eq (m : ThetaReflectionData.Row R.A) (p : ThetaBranch.ExteriorPrime R.A) :
    ThetaDigitAverage.rowExponent R.A m.val p.val = ThetaBranch.rowIndex R.A m p.val := by
  have hv : p.val.valuation F (m.val : F) ≤ 1 := m.val.property p.val p.property
  have hnz : p.val.valuation F (m.val : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (ThetaReflectionData.rowUnit R.A m).ne_zero
  rw [← WithZero.exp_log hnz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
  apply Fin.ext
  simp only [ThetaDigitAverage.rowExponent, ThetaBranch.rowIndex, ThetaBranch.order,
    ThetaReflectionData.rowUnit, Units.val_mk0]
  omega

theorem local_average (m : ThetaReflectionData.Row R.A) (x : Fˣ) (p : RowPrime R m) :
    (∑ v : ThetaDigitAverage.Residue p.val,
      sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ (exteriorRowPrime R m p))
        (Characters.psi R (exteriorRowPrime R m p)) (ThetaDigitAverage.rowExponent R.A m.val p.val) v *
      localDigitValue R C (exteriorRowPrime R m p) x ((ThetaDigitAverage.residueLifts _).lift p v)) =
    sexticReflectedDigitModel (ThetaBranch.residueCharacter R.A R.σ (exteriorRowPrime R m p))
      (Characters.psi R (exteriorRowPrime R m p)) (ThetaBranch.rowIndex R.A m p.val)
      (ThetaBranch.order p.val x + 2)
      (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed (exteriorRowPrime R m p) x)) := by
  have hj : ThetaDigitAverage.rowExponent R.A m.val p.val = ThetaBranch.rowIndex R.A m p.val :=
    rowExponent_eq R m (exteriorRowPrime R m p)
  rw [hj]
  let q := exteriorRowPrime R m p
  let L := ThetaDigitAverage.residueLifts (ThetaDigitAverage.rowPrimes R.A m.val m.property)
  have hL (v : ThetaDigitAverage.Residue p.val) : Ideal.Quotient.mk q.val.asIdeal (L.lift p v) = v :=
    L.residue_lift p v
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ThetaDigitAverage.Residue p.val))]
  rw [zero_localDigit R C q x (L.lift p 0) (hL 0)]
  have hn (v : ThetaDigitAverage.Residue p.val) (hv : v ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val)) :
      localDigitValue R C q x (L.lift p v) =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ q) (Characters.psi R q)
        (ThetaBranch.order p.val x + 2) *
      ThetaBranch.symbol R.A R.σ q (ThetaBranch.localUnit R.A R.probe.allowed q x) ^
        (4 + 2 * (ThetaBranch.order p.val x + 2)) *
      ThetaBranch.residueCharacter R.A R.σ q v ^ (4 : ℕ) *
      (if ThetaBranch.order p.val x + 2 = 0 then
        Characters.psi R q
          (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed q x) / v) else 1) := by
    have hh := nonzero_localDigit R C q x (L.lift p v) (by rw [hL]; exact Finset.ne_of_mem_erase hv)
    rw [hL] at hh
    exact hh
  change (∑ v ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val),
    sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ q) (Characters.psi R q)
      (ThetaBranch.rowIndex R.A m p.val) v * localDigitValue R C q x (L.lift p v)) + _ = _
  rw [Finset.sum_congr rfl (fun v hv => congrArg
    (fun z => sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ q) (Characters.psi R q)
      (ThetaBranch.rowIndex R.A m p.val) v * z) (hn v hv))]
  unfold sexticReflectedDigitModel sexticReflectedNonzeroDigits
  have hz : ThetaBranch.order p.val x + 2 - 2 = ThetaBranch.order p.val x := by omega
  rw [hz]
  unfold ThetaBranch.sphericalFactor ThetaBranch.symbol
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  ring

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
