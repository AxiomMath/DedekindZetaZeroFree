module

public import DedekindZetaZeroFree.Theta.Periods.Wild.JointPeriodDescent
public import DedekindZetaZeroFree.Theta.Periods.Wild.BorelJointKernel

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentJointForm
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)

def jointForm := Classical.choose (WildCurrentJointPeriod.exists_joint_descent D W s hW x)

theorem jointForm_comp :
    (jointForm D W s hW x).comp
      (tensorQuotient F R.A.zeta12 R.A.primitive_zeta12 W (character W)
        (fiber D W) (action D W)) = WildCurrentJointPeriod.period D W s hW x :=
  Classical.choose_spec (WildCurrentJointPeriod.exists_joint_descent D W s hW x)

theorem kernel_finite_borel
    (a : ProductAffine F R.A.zeta12 R.A.primitive_zeta12 W)
    (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v)
    (e : JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W (character W)
      (fiber D W) (action D W)) (he : jointForm D W s hW x e = 0) :
    WildCurrentJointPeriod.period D W s hW x
      (ambientAction F R.A.zeta12 R.A.primitive_zeta12 W (fiber D W) (action D W) a
        (tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
          (depth (R := R) W) (depth_valid (R := R) W) (character W)
          (fiber D W) (action D W) (localData D W)
          (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))) = 0 :=
  WildJointBorelKernel.full_borel_kernel_zero F R.A.zeta12 R.A.primitive_zeta12 W
    (depth (R := R) W) (depth_valid (R := R) W) (character W)
    (fiber D W) (action D W) (localData D W)
    (WildCurrentJointPeriod.period D W s hW x) (jointForm D W s hW x)
    (jointForm_comp D W s hW x) a f e he
end DedekindZetaZeroFree.FourierContinuation.WildCurrentJointForm

end
