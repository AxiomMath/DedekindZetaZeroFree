module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.AdditiveFrequencies

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

theorem nonzero_value (p : ThetaBranch.ExteriorPrime R.A) (x V : Fˣ)
    (hV : ThetaBranch.order p.val V = 0) :
    C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (-algebraMap F (p.val.adicCompletion F) V.val /
            algebraMap F (p.val.adicCompletion F)
              (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))
      (C.factorization.references (Sum.inr p.val))) =
    sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
      (ThetaBranch.order p.val x + 2) *
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x) ^
        (4 + 2 * (ThetaBranch.order p.val x + 2)) *
      ThetaBranch.symbol R.A R.σ p V ^ (4 : ℕ) *
      (if ThetaBranch.order p.val x + 2 = 0 then
        Characters.psi R p
          (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x) /
            ThetaBranch.unitResidue p.val V) else 1) := by
  let g := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
  let H := -V / g
  have hc := digit_coordinates R p x V hV
  dsimp only at hc
  have hword := rational_word_value R C p x H (by rw [hc.1]; norm_num)
  have he : algebraMap F (p.val.adicCompletion F) H.val =
      -algebraMap F (p.val.adicCompletion F) V.val / algebraMap F (p.val.adicCompletion F) g.val := by
    simp [H]
  rw [he] at hword
  rw [hword, mul_assoc, nonzero_spherical R C.aligned p x V hV]
  by_cases hneg : ThetaBranch.order p.val x + 2 < 0
  · simp [sexticSphericalCoefficient, hneg]
  · rw [additive_digit R p x V hV (by omega)]
    ring

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
