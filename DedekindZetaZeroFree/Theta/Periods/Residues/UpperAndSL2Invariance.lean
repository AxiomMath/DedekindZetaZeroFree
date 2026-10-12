module

public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.AutomorphyAndEigenvalue
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ComplexRootGeneration
public import DedekindZetaZeroFree.Theta.Whittaker.FourierVanishingAndRootInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open KPLiteralPeriod
open _root_.DedekindZetaZeroFree.KPLiteralPeriod renaming complexSL2_upper → complexSL2_upper
open _root_.DedekindZetaZeroFree.KPLiteralPeriod renaming complexSL2_lower → complexSL2_lower
open _root_.DedekindZetaZeroFree.KPLiteralPeriod renaming literal_rationalLift_mk → literal_rationalLift_mk

theorem coreResidue_upper_invariant_of_period_zero (x : V)
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure)
    (hp : ∀ g, KPLiteralRaw.period F ζ hζ ψ μ
      (KPLiteralRaw.rightAction F ζ hζ g (coreResidue R P C x)) = 0) :
    ∀ u g, coreResidue R P C x (KPGlobalTorusFunctionData.N F ζ hζ u * g) =
      coreResidue R P C x g :=
  ((haar_fourier_vanishing_forces_root_invariance F ζ hζ ψ hψ μ hμ
    (coreResidue R P C x) (coreResidue_raw_automorphic R P C x)).2.2.2 hp).1

theorem coreResidue_sl2_invariant_of_upper_invariant (x : V)
    (hu : ∀ u g, coreResidue R P C x (KPGlobalTorusFunctionData.N F ζ hζ u * g) =
      coreResidue R P C x g) (w : InfinitePlace F) :
    ∀ a g, coreResidue R P C x (complexSL2 F ζ hζ w a * g) = coreResidue R P C x g := by
  let θ := coreResidue R P C x
  have hr := coreResidue_regular R P C x
  have hw : ∀ g, θ (KPRationalAdelicSplitting.pglW F ζ hζ * g) = θ g := by
    intro g
    have h := hr.2.1 (Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap F)) g
    rw [literal_rationalLift_mk] at h
    change θ (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (KPStandardLocalRootLifts.weylSwap F)) * g) = θ g at h
    simpa only [KPRationalAdelicSplitting.pglW, KPRationalAdelicSplitting.W_rational] using h
  have hl := KPWildIndependentGenericity.NonzeroPeriod.lower_invariance_of_upper
    F ζ hζ θ hu hw
  exact KPGlobalGenericity.split_root_invariance (complexSL2 F ζ hζ w) θ
    (fun z g => by rw [complexSL2_upper]; exact hu _ g)
    (fun z g => by rw [complexSL2_lower]; exact hl _ g)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
