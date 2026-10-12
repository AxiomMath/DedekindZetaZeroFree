module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.BruhatEvaluation
public import DedekindZetaZeroFree.Theta.Whittaker.UnitDiagonalCovariance

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_spec → reduction_spec
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_mul → reduction_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_pow → reduction_pow
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

 theorem val_eq_one (p : KPFinitePlace F) (x : Fˣ) (hx : ThetaBranch.order p x = 0) :
    Valued.v (algebraMap F (p.adicCompletion F) x.val) = 1 := by
  change Valued.v ((x.val : F) : p.adicCompletion F) = 1
  rw [HeightOneSpectrum.adicCompletion.valued_coe]
  have hn := (Valuation.ne_zero_iff (p.valuation F)).mpr x.ne_zero
  rw [← WithZero.exp_log hn]
  have hh : WithZero.log (p.valuation F x.val) = 0 := by
    unfold ThetaBranch.order at hx
    omega
  simp [hh]

 theorem rational_unit (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ)
    (hx : ThetaBranch.order p.val x = 0) :
    ∃ u : KPHilbert.LocalIntegerUnits F p.val,
      KPHilbert.integerUnitInclusion F p.val u = Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x := by
  apply ExteriorWhittakerValues.UnitCovarianceCompletion.exists_integerUnit_of_valuation_one
  letI : (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  apply ((ValuativeRel.isEquiv (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ)))
    (valuation (p.val.adicCompletion F))).eq_one_iff_eq_one).mp
  exact val_eq_one p.val x hx

 theorem residue_norm_approx (p : KPFinitePlace F) (x : Fˣ) (hx : ThetaBranch.order p x = 0) :
    ∃ t : 𝓞 F, ‖algebraMap F (p.adicCompletion F) x.val - algebraMap (𝓞 F) (p.adicCompletion F) t‖ < 1 ∧
      Ideal.Quotient.mk p.asIdeal t = ThetaBranch.unitResidue p x := by
  have hv : p.valuation F x.val = 1 := by
    have hh := val_eq_one p x hx
    change Valued.v ((x.val : F) : p.adicCompletion F) = 1 at hh
    rwa [HeightOneSpectrum.adicCompletion.valued_coe] at hh
  obtain ⟨t, ht, hr⟩ := DigitMasks.rational_residue_approx p x hv.le
  refine ⟨t, ?_, hr⟩
  have hh : Valued.v (algebraMap F (p.adicCompletion F) (t.val - x.val)) < 1 := by
    change Valued.v (((t.val - x.val : F)) : p.adicCompletion F) < 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact ht
  rw [map_sub] at hh
  have hn := Valued.toNormedField.norm_lt_one_iff.mpr hh
  rw [norm_sub_rev] at hn
  exact hn

 theorem rational_character (hR : RootAligned R) (p : ThetaBranch.ExteriorPrime R.A)
    (x : Fˣ) (hx : ThetaBranch.order p.val x = 0)
    (u : KPHilbert.LocalIntegerUnits F p.val)
    (hu : KPHilbert.integerUnitInclusion F p.val u = Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) :
    (KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12
      (KPHilbert.residueSixCharacter F p.val R.A.zeta12 R.A.primitive_zeta12 (ExteriorWhittakerValues.exterior_good_six p) u) : ℂ) =
      ThetaBranch.residueCharacter R.A R.σ p (ThetaBranch.unitResidue p.val x) := by
  obtain ⟨t, ht, hr⟩ := residue_norm_approx p.val x hx
  rw [← hr]
  apply ExteriorWhittakerValues.UnitCovarianceCompletion.unit_phase_of_norm_sub_lt_one R hR p u t
  have he := congrArg Units.val hu
  change (u : p.val.adicCompletion F) = algebraMap F (p.val.adicCompletion F) x.val at he
  rw [he]
  exact ht

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
