module

public import DedekindZetaZeroFree.Eisenstein.Induction.TorusCovariance
public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.RationalCovariance
open KPGlobalTorusFiniteStages KPGlobalTorusPeriodizationInverse
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 theorem scalar_torus (r : KPGlobalCenterRationalCharacter.R F ζ hζ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    RawSource.scalarValue F ζ hζ P C (r.val.val*g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      RawSource.scalarValue F ζ hζ P C g := by
  unfold RawSource.scalarValue
  rw [SourceTorusCovariance.quotient_torus, map_smul, unitaryPeriodization_intertwines]
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
    ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ)) *
    (unitaryPeriodization F ζ hζ P (RawSource.quotientValue F ζ hζ P C g)).val.val (1*r.val) = _
  rw [one_mul]
  let f := unitaryPeriodization F ζ hζ P (RawSource.quotientValue F ζ hζ P C g)
  have hc := f.val.property r 1
  change f.val.val (r.val*1) = (rationalUnitCharacter F ζ hζ r : ℂ)*f.val.val 1 at hc
  rw [mul_one] at hc
  rw [hc]
  have hr := KPGlobalCenterRationalCharacter.nu_positive F ζ hζ r.val
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hchar : (rationalUnitCharacter F ζ hζ r : ℂ) =
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) /
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ) := by
    change ((rationalUnitValue F ζ hζ r : ℂˣ) : ℂ) = _
    simp [rationalUnitValue, Units.val_div_eq_div_val,
      KPGlobalCenterRationalCharacter.positiveComplex]
  rw [hchar]
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) := by
    unfold KPGlobalTorusFunctionData.deltaHalf KPGlobalExceptionalParameter.realLogPower
    have hpos : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hd]
  field_simp
  rfl

 theorem scalar_upper (y : KPAdeles F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    RawSource.scalarValue F ζ hζ P C (KPGlobalTorusFunctionData.N F ζ hζ y*g) =
      RawSource.scalarValue F ζ hζ P C g := by
  unfold RawSource.scalarValue
  rw [RawSource.quotientValue_upper]

 theorem covariance (r : KPGlobalCenterRationalCharacter.R F ζ hζ)
    (y : KPAdeles F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    RawSource.scalarValue F ζ hζ P C ((r.val.val*KPGlobalTorusFunctionData.N F ζ hζ y)*g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2+0) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      RawSource.scalarValue F ζ hζ P C g := by
  rw [mul_assoc, scalar_torus, scalar_upper]
  simp

end DedekindZetaZeroFree.EisensteinReferenceSections.RationalCovariance

end
