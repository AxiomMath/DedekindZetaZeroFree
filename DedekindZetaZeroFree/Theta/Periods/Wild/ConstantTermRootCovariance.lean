module

public import DedekindZetaZeroFree.Theta.Periods.Wild.GlobalTensorEvaluation
public import DedekindZetaZeroFree.Theta.Whittaker.Borel.ConstantIntegralInvariance

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance wildCurrentConstantTermDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)

theorem globalMap_regular (z : AmbientTensor F W (fiber D W)) :
    globalMap D W s hW x z ∈ regularResidualFunctions R :=
  D.regular _

theorem globalMap_rational (z : AmbientTensor F W (fiber D W))
    (γ : KPRationalAdelicSplitting.RationalPGL2 F) (g : Group R) :
    globalMap D W s hW x z
      (KPRationalAdelicSplitting.rationalPGLHom F R.A.zeta12 R.A.primitive_zeta12 γ * g) =
      globalMap D W s hW x z g := by
  induction γ using Quotient.inductionOn with
  | h a =>
    change globalMap D W s hW x z
      (KPRationalAdelicSplitting.rationalPGLHom F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.rationalPGLQuotient F a) * g) = _
    rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
    have hh := (globalMap_regular D W s hW x z).2.1 (Matrix.ProjGenLinGroup.mk a) g
    rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed,
      (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting F R.A.zeta12 R.A.primitive_zeta12).on_matrix] at hh
    exact hh

theorem globalMap_root (q : W) (t : q.val.adicCompletion F)
    (z : AmbientTensor F W (fiber D W)) (g : Group R) :
    globalMap D W s hW x (slotMap D W q
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)
        (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t)) z) g =
      globalMap D W s hW x z
        (g * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) t)) := by
  have hh := globalMap_finite D W s hW x q
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t) z g
  simpa only [finite_root_injection (R := R)] using hh

theorem constant_integral_root (q : W) (t : q.val.adicCompletion F)
    (z : AmbientTensor F W (fiber D W))
    (μ : Measure (KPCompactFourier.AdditiveQuotient F)) [μ.IsAddHaarMeasure]
    (b : KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12) :
    (∫ u, KPWildRawSourceConstruction.sourceFiber F R.A.zeta12 R.A.primitive_zeta12 b
      (globalMap D W s hW x (slotMap D W q
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)
          (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t)) z)) u ∂μ) =
    ∫ u, KPWildRawSourceConstruction.sourceFiber F R.A.zeta12 R.A.primitive_zeta12 b
      (globalMap D W s hW x z) u ∂μ := by
  have he := funext (globalMap_root D W s hW x q t z)
  rw [he]
  exact KPWildActualConstantIntegral.integral_right_root_eq F R.A.zeta12 R.A.primitive_zeta12
    μ (globalMap D W s hW x z) (globalMap_rational D W s hW x z) b _
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
