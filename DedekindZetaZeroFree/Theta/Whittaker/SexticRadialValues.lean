module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalUnitCovariance
public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalTraceAndResidueTransport
public import DedekindZetaZeroFree.Theta.Whittaker.NonnegativeRadialValues

@[expose] public section

noncomputable section
open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ShellArithmetic
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem radialValue_eq_sextic (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A)
    [Fintype (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer)]
    (e : ℤ) :
    ActualShellValues.radialValue F p.val
      (KPExteriorUnitShellIntegrals.g (residueChi R p) (residuePsi R p) 2) e =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p)
        (MomentSources.Characters.psi R p) e := by
  let q : ℕ := Fintype.card (DHCubic.Residue F p.val)
  have hc : KPLocalPrincipalSeries.residueCardinality (p.val.adicCompletion F) = q := by
    change Nat.card (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer) = _
    rw [Nat.card_congr (residueEquiv R p).symm.toEquiv, Nat.card_eq_fintype_card]
  have hc' : Fintype.card (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer) = q := by
    rw [← Nat.card_eq_fintype_card]
    exact hc
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hint (n : ℤ) : ActualSpherical.QPower F p.val (n : ℝ) = (q : ℂ) ^ n := by
    unfold ActualSpherical.QPower
    rw [hc, Real.rpow_eq_pow, Real.rpow_intCast, Complex.ofReal_zpow]
    simp only [Complex.ofReal_natCast]
  have hhalf : ActualSpherical.QPower F p.val (-(1 / 2 : ℝ)) =
      (Real.sqrt (q : ℝ) : ℂ)⁻¹ := by
    unfold ActualSpherical.QPower
    rw [hc, Real.rpow_eq_pow, Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  have hadd (n : ℤ) : ActualSpherical.QPower F p.val (-(n : ℝ) - (1 / 2 : ℝ)) =
      (q : ℂ) ^ (-n) * (Real.sqrt (q : ℝ) : ℂ)⁻¹ := by
    have he : -(n : ℝ) - (1 / 2 : ℝ) = ((-n : ℤ) : ℝ) + -(1 / 2 : ℝ) := by push_cast; ring
    rw [he]
    change (Real.rpow _ (_ + _) : ℂ) = _
    rw [hc, Real.rpow_eq_pow, Real.rpow_add hq, Complex.ofReal_mul]
    rw [Real.rpow_intCast, Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow,
      Complex.ofReal_zpow, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hg : KPExteriorUnitShellIntegrals.g (residueChi R p) (residuePsi R p) 2 =
      (Real.sqrt (q : ℝ) : ℂ)⁻¹ *
        gaussSum (ThetaBranch.residueCharacter R.A R.σ p ^ 2) (MomentSources.Characters.psi R p) := by
    unfold KPExteriorUnitShellIntegrals.g KPExteriorUnitShellIntegrals.qPower
    rw [hc', Real.rpow_eq_pow, Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
    have hh : (residueChi R p) ^ (2 : ℤ) = (residueChi R p) ^ (2 : ℕ) := by norm_cast
    rw [hh, gauss_two_transport]
  unfold ActualShellValues.radialValue sexticSphericalCoefficient
  split_ifs with he h0 h1
  · rfl
  · simpa only [Int.cast_neg] using hint (-(e / 3))
  · rw [hadd, hg]
  · rfl

theorem negativeGenerator_value (R : PrincipalMellin.ActualRecipe S η)
    (hR : MomentSources.RootAligned R) {N : MomentSources.TraceHaarTransport R}
    (C : MomentSources.JointHaarFactorizedSources R N) (p : ThetaBranch.ExteriorPrime R.A) (e : ℕ) :
    ThetaExpansion.exteriorWhittakerValue R C p ((-ThetaExpansion.exteriorCompletionGenerator R p) ^ (e : ℤ)) =
      ThetaExpansion.exteriorWhittakerValue R C p (ThetaExpansion.exteriorCompletionGenerator R p ^ (e : ℤ)) := by
  let u : (p.val.adicCompletion F)ˣ := (-1) ^ e
  let t : 𝓞 F := (-1) ^ e
  have ht : ‖(u : p.val.adicCompletion F) -
      algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1 := by
    simp [u, t]
  have hu : valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1 := by
    simp [u]
  have hh := ThetaExpansion.exterior_whittaker_value_unit_covariance R hR C p (e : ℤ) u t ht hu
  have hc : ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal t) ^ (2 * (e : ℤ)) = 1 := by
    have hneg : ThetaBranch.residueCharacter R.A R.σ p (-1) ^ 2 = 1 := by
      rw [pow_two, ← map_mul]
      simp
    have hpow : (ThetaBranch.residueCharacter R.A R.σ p (-1) ^ e) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm e 2, pow_mul, hneg, one_pow]
    simp only [t, map_pow, map_neg, map_one]
    rw [zpow_mul, zpow_ofNat, hpow, one_zpow]
  rw [hc, mul_one] at hh
  have he : (-ThetaExpansion.exteriorCompletionGenerator R p) ^ (e : ℤ) =
      ThetaExpansion.exteriorCompletionGenerator R p ^ (e : ℤ) * u := by
    have hn : -ThetaExpansion.exteriorCompletionGenerator R p = (-1) * ThetaExpansion.exteriorCompletionGenerator R p := by
      apply Units.ext
      simp
    rw [hn, mul_zpow]
    simp only [zpow_natCast, u]
    exact mul_comm _ _
  rw [he]
  exact hh

end DedekindZetaZeroFree.ExteriorWhittakerValues.ShellArithmetic

end
