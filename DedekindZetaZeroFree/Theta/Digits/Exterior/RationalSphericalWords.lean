module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.TameRationalPhases

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)

theorem integral_of_order_nonneg (p : KPFinitePlace F) (x : Fˣ) (hx : 0 ≤ ThetaBranch.order p x) :
    algebraMap F (p.adicCompletion F) x.val ∈ KPTameCompact.O F p := by
  letI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  apply (ValuativeRel.isEquiv (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))
    (valuation (p.adicCompletion F))).le_one_iff_le_one.mp
  change Valued.v ((x.val : F) : p.adicCompletion F) ≤ 1
  rw [HeightOneSpectrum.adicCompletion.valued_coe]
  have hn := (Valuation.ne_zero_iff (p.valuation F)).mpr x.ne_zero
  rw [← WithZero.exp_log hn, ← WithZero.exp_zero, WithZero.exp_le_exp]
  unfold ThetaBranch.order at hx
  omega

theorem rational_word_value (p : ThetaBranch.ExteriorPrime R.A) (x H : Fˣ)
    (hH : ThetaBranch.order p.val H < 0) :
    C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (algebraMap F (p.val.adicCompletion F) H.val))
      (C.factorization.references (Sum.inr p.val))) =
    (ResidueTrace.localTraceCharacter p.val (algebraMap F (p.val.adicCompletion F) (x.val * H.val⁻¹)) : ℂ) *
      KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom (-(H⁻¹ ^ 2))) *
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p (x * (-(H⁻¹ ^ 2))) := by
  let M := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
  have hi : ((M H)⁻¹).val ∈ KPTameCompact.O F p.val := by
    rw [← map_inv]
    exact integral_of_order_nonneg p.val H⁻¹ (by rw [order_inv]; omega)
  have hb := bruhat_value R C p (M x) (M H) hi
  have he : -( (M H)⁻¹ ^ 2) = M (-(H⁻¹ ^ 2)) := by
    apply Units.ext
    simp [M]
  rw [he, ← map_mul] at hb
  have hw : exteriorWhittakerValue R C.toJointHaarFactorizedSources p (M (x * -(H⁻¹ ^ 2))) =
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p (x * -(H⁻¹ ^ 2)) :=
    C.exterior.rational_exact p _
  rw [hw] at hb
  have hp : (M x).val * ((M H)⁻¹).val =
      algebraMap F (p.val.adicCompletion F) (x.val * H.val⁻¹) := by
    simp [M]
  rw [hp] at hb
  exact hb

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
