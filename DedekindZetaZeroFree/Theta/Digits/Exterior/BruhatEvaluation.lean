module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.FiniteSupport
public import DedekindZetaZeroFree.Metaplectic.Weil.LiftedBruhatWordEvaluation

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

theorem bruhat_value (p : ThetaBranch.ExteriorPrime R.A)
    (y H : (p.val.adicCompletion F)ˣ)
    (hH : ((H⁻¹ : (p.val.adicCompletion F)ˣ) : p.val.adicCompletion F) ∈ KPTameCompact.O F p.val) :
    C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) H.val)
      (C.factorization.references (Sum.inr p.val))) =
    (ResidueTrace.localTraceCharacter p.val (y.val * (H⁻¹).val) : ℂ) *
      KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)) *
      exteriorWhittakerValue R C.toJointHaarFactorizedSources p (y * (-(H⁻¹ ^ 2))) := by
  let A := KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
  let NN := KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
  have hn : A y * NN (H⁻¹).val = NN (y.val * (H⁻¹).val) * A y := by
    dsimp [A, NN]
    rw [KPCorrectedBruhatLifts.quotient_upper_diagonal]
    rw [mul_div_cancel_left₀ _ y.ne_zero]
  have hword : A y * KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) * NN H.val =
      NN (y.val * (H⁻¹).val) * (A y * A (-(H⁻¹ ^ 2))) *
        KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (H⁻¹).val := by
    rw [mul_assoc, KPCorrectedBruhatLifts.quotient_weyl_upper]
    rw [← mul_assoc, ← mul_assoc, hn]
    simp only [mul_assoc]
    rfl
  have hh := representation_bruhat (exteriorImageAction R C.toJointHaarFactorizedSources p)
    (C.factorization.ell (Sum.inr p.val)) (C.factorization.references (Sum.inr p.val))
    (A y) (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) (NN H.val)
    (NN (y.val * (H⁻¹).val)) (A (-(H⁻¹ ^ 2)))
    (KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (H⁻¹).val)
    (KPPGLLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)) ^ 2))
    (A (y * (-(H⁻¹ ^ 2))))
    (ResidueTrace.localTraceCharacter p.val (y.val * (H⁻¹).val) : ℂ)
    (KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)))
    hword (lower_fixed R C p ⟨_, hH⟩)
    (exterior_whittaker_equivariance R C.toJointHaarFactorizedSources p (y.val * (H⁻¹).val))
    (KPPGLLocalCover.A_mul F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)))
    (KPRankOneShellRepair.actualCanonicalImage_ordinary_genuine F R.A.zeta12
      R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
      (C.factorization.finiteData p.val).inducing.polarization
      (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer _)
  rw [hh]
  unfold exteriorWhittakerValue
  rw [exterior_diagonal_eq_standard_lift]

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
