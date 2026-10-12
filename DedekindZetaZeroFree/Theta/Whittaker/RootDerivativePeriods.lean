module

public import DedekindZetaZeroFree.Theta.Whittaker.ArchimedeanDerivativeMultipliers

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem fourier_firstRootList (dq : Measure (KPAdditiveQuotient F))
    (hHaar : dq.IsAddHaarMeasure) (hprob : dq Set.univ = 1)
    (B : FirstRootCutoffs R) (l : List (InfinitePlace F))
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (y : R.A.G) :
    MomentSources.fourier R dq
      (l.foldr (fun w h => firstRootLocalDerivative R w (B.exponent w) h) f) (diagonal R y) =
      (l.map (fun w => (‖(y.1 w : w.Completion)‖ : ℂ) *
        DHCubic.angular (complexCoordinate y w) ^ B.exponent w)).prod *
          MomentSources.fourier R dq f (diagonal R y) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    have hreg := firstRootList_regular R B l f hf hr
    rw [List.foldr_cons, fourier_firstRootLocalDerivative R dq hHaar hprob _ hreg.1
      hreg.2 w (B.exponent w) (B.sign w), ih]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem fourier_firstRootDerivatives (dq : Measure (KPAdditiveQuotient F))
    (hHaar : dq.IsAddHaarMeasure) (hprob : dq Set.univ = 1)
    (B : FirstRootCutoffs R) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (y : R.A.G) :
    MomentSources.fourier R dq (firstRootDerivatives R B f) (diagonal R y) =
      firstRootMultiplier R B y * MomentSources.fourier R dq f (diagonal R y) := by
  unfold firstRootDerivatives
  rw [fourier_firstRootList R dq hHaar hprob B _ f hf hr]
  unfold firstRootMultiplier
  congr 1
  exact Finset.prod_map_toList _ _

theorem firstRootDerivatives_period (N : TraceHaarTransport R)
    (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R) (J : FirstRootProjected R N A B)
    (v : R.A.UnitQuotient) (y : R.A.G) :
    MomentSources.fourier R J.base.sources.dq
      (firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) (diagonal R y) =
      firstRootMultiplier R J.cutoffs y *
        MomentSources.fourier R J.base.sources.dq (J.base.realization.theta v) (diagonal R y) := by
  have ha := J.base.realization.automorphic v
  exact fourier_firstRootDerivatives R J.base.sources.dq J.base.sources.quotientHaar
    J.base.sources.probability J.cutoffs (J.base.realization.theta v) ha.1 ha.2.1 y

end DedekindZetaZeroFree.RootDerivatives

end
