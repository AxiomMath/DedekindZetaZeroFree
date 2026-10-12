module

public import DedekindZetaZeroFree.Theta.Periods.Wild.ConstantIntegralMap
public import DedekindZetaZeroFree.Theta.Periods.Wild.OrdinaryImageVanishing

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance wildCurrentTrivialFrequencyDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)
  (μ : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure μ] [μ.IsAddHaarMeasure]
  (b : KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12)
  (E : Submodule ℂ (JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W
    (character W) (fiber D W) (action D W)))

theorem constant_image_zero (q : W)
    (z : InducedTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) (fiber D W) (action D W) E) :
    constantMap D W s hW x μ b
      (subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
        (depth (R := R) W) (depth_valid (R := R) W) (character W)
        (fiber D W) (action D W) (localData D W) E z) = 0 := by
  exact WildOrdinaryImageFunctional.vanishes F R.A.zeta12 R.A.primitive_zeta12 W
    (depth (R := R) W) (depth_valid (R := R) W) (character W)
    (fiber D W) (action D W) (localData D W) q E
    (constantMap D W s hW x μ b) (by
      intro t u
      exact (congrArg (constantMap D W s hW x μ b)
        (LinearMap.congr_fun (ambient_root_eq_slot D W q t) u)).trans
          (constant_integral_root D W s hW x q t u μ b)) z
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
