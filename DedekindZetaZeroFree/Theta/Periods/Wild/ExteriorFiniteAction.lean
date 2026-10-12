module

public import DedekindZetaZeroFree.Theta.Periods.Wild.GlobalTensorEvaluation
public import DedekindZetaZeroFree.Theta.Periods.Wild.TameSlotComparison

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
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
  (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) (ho : Sum.inr q ∉ places W)
  (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))

abbrev outsideTuple := Function.update x ⟨Sum.inr q,hq⟩
  (KPRankOneShellRepair.actualCanonicalImageRepresentation F
    R.A.zeta12 R.A.primitive_zeta12 q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
    (D.finiteData q).haar (D.finiteData q).haar_integer
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
    (x ⟨Sum.inr q,hq⟩))

include ho in
theorem outside_finite_pure (y : ∀ r : W, fiber D W r)
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    globalMap D W s hW (outsideTuple D s x q hq a) (PiTensorProduct.tprod ℂ y) g =
    globalMap D W s hW x (PiTensorProduct.tprod ℂ y)
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  rw [globalMap_pure, globalMap_pure]
  rw [WildTameSlotTransport.stageTuple_update_outside D W s x ⟨Sum.inr q,hq⟩ ho]
  have hh := D.finite_intertwining q a s hq (stageTuple D W s x y) g
  simpa only [stageTuple, dif_neg ho] using hh

include ho in
theorem outside_finite (z : AmbientTensor F W (fiber D W))
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    globalMap D W s hW (outsideTuple D s x q hq a) z g =
    globalMap D W s hW x z
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, Pi.smul_apply]
    exact congrArg (fun t : ℂ => c • t) (outside_finite_pure D W s hW x q hq ho a y g)
  | add z w hz hw =>
    simpa only [map_add, Pi.add_apply] using congrArg₂ (fun a b : ℂ => a + b) hz hw
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
