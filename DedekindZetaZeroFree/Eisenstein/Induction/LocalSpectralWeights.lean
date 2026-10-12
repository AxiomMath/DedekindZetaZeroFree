module

public import DedekindZetaZeroFree.Metaplectic.Iwasawa.LocalLogarithmicHeights
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.RationalFiberSlices

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPAdelicCoverRestrictedProduct ThetaExpansion KPGlobalTorusFiniteStages
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def awayHeight (q : KPFinitePlace F) (g : Raw R.A) : ℝ :=
  ∑ᶠ (v) (_ : v ≠ Sum.inr q), rawLocalLog R P C g v

theorem rawLocalLog_local_left (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) (g : Raw R.A)
    (v : KPHilbert.Place F) (hv : v ≠ Sum.inr q) :
    rawLocalLog R P C (localToRestricted F ζ hζ (Sum.inr q) a * g) v =
      rawLocalLog R P C g v := by
  have he : (localToRestricted F ζ hζ (Sum.inr q) a * g) v = g v := by
    simp only [RestrictedProduct.mul_apply, localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_eq_of_ne hv, one_mul]
  cases v <;> dsimp only [rawLocalLog] <;> rw [he]

theorem awayHeight_local_left (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) (g : Raw R.A) :
    awayHeight R P C q (localToRestricted F ζ hζ (Sum.inr q) a * g) =
      awayHeight R P C q g := by
  unfold awayHeight
  apply finsum_congr
  intro v
  apply finsum_congr
  intro hv
  exact rawLocalLog_local_left R P C q a g v hv

theorem height_eq_local_add_away (q : KPFinitePlace F) (g : Raw R.A) :
    iwasawaLogHeight R (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
      rawLocalLog R P C g (Sum.inr q) + awayHeight R P C q g := by
  rw [(rawLocalLog_finite_and_height R P C g).2]
  exact (add_finsum_cond_ne (Sum.inr q)
    (rawLocalLog_finite_and_height R P C g).1).symm

theorem spectralWeight_local_left (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) (g : Raw R.A) (s : ℂ) :
    Complex.exp (s * (iwasawaLogHeight R (scalarQuotient F ζ hζ
      (amalgamation F ζ hζ (localToRestricted F ζ hζ (Sum.inr q) a * g))) : ℂ)) =
      Complex.exp (s * (awayHeight R P C q g : ℂ)) *
        Complex.exp (s * (Real.log (LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q)
          (finiteIntegralIwasawa R P C q)
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (a * g (Sum.inr q)))) : ℂ)) := by
  rw [height_eq_local_add_away R P C q, awayHeight_local_left R P C q a g,
    Complex.ofReal_add, mul_add, Complex.exp_add, mul_comm]
  simp only [rawLocalLog, RestrictedProduct.mul_apply, localToRestricted,
    RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
    Pi.mulSingle_eq_same]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
