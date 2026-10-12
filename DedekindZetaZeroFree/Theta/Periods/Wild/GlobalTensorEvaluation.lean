module

public import DedekindZetaZeroFree.Theta.Periods.Wild.JointPeriodDescent

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
set_option backward.isDefEq.respectTransparency true
set_option quotPrecheck false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)

def globalMap : AmbientTensor F W (fiber D W) →ₗ[ℂ] Functions R :=
  D.coreMap.comp
    ((RestrictedTensorSimple.stageInclusion _ D.references D.bad s).comp
      ((RestrictedTensorSimple.insert _ (fullFiller D s x)
        (places W) s.val hW).comp (reindex D W).toLinearMap))

theorem globalMap_pure (y : ∀ q : W, fiber D W q) :
    globalMap D W s hW x (PiTensorProduct.tprod ℂ y) =
      D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ (stageTuple D W s x y))) := by
  have hr := reindex_pure_of D W y (placeTuple D W y)
    (fun q => Equiv.piCongrLeft_apply_apply (fun p : places W => actualLocal R D.finiteData p) (placeEquiv W) y q)
  change D.coreMap
    (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (RestrictedTensorSimple.insert _ (fullFiller D s x)
        (places W) s.val hW (reindex D W (PiTensorProduct.tprod ℂ y)))) =
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (stageTuple D W s x y)))
  rw [hr,RestrictedTensorSimple.insert_pure]
  apply congrArg D.coreMap
  apply congrArg (RestrictedTensorSimple.stageInclusion _ D.references D.bad s)
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext p
  by_cases hp : p.val ∈ places W
  · simp [stageTuple,hp]
  · simp [stageTuple,hp,fullFiller,p.property]

theorem globalMap_finite_pure (y : ∀ q : W, fiber D W q) (q : W)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val))
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    globalMap D W s hW x (PiTensorProduct.tprod ℂ
      (Function.update y q ((action D W q)
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a) (y q)))) g =
    globalMap D W s hW x (PiTensorProduct.tprod ℂ y)
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a)) := by
  have ha := globalMap_pure D W s hW x (Function.update y q ((action D W q)
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a) (y q)))
  have hb := globalMap_pure D W s hW x y
  have hu := stageTuple_update D W s hW x y q ((action D W q)
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a) (y q))
  rw [ha, hb, hu]
  have hh := D.finite_intertwining q.val a s (hW (placeEquiv W q).property)
    (stageTuple D W s x y) g
  simpa only [stageTuple_at D W s hW x y q,
    action, WildActualMirabolic.rho] using hh

def slotMap (q : W)
    (a : KPKirillovGenuineSectionCharts.G F R.A.zeta12 R.A.primitive_zeta12 q.val) :
    AmbientTensor F W (fiber D W) →ₗ[ℂ] AmbientTensor F W (fiber D W) :=
  PiTensorProduct.map (Function.update (fun r : W => (LinearMap.id : fiber D W r →ₗ[ℂ] fiber D W r)) q (action D W q a))

set_option backward.isDefEq.respectTransparency false in
theorem slotMap_pure (q : W)
    (a : KPKirillovGenuineSectionCharts.G F R.A.zeta12 R.A.primitive_zeta12 q.val)
    (y : ∀ q : W, fiber D W q) :
    slotMap D W q a (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y q (action D W q a (y q))) := by
  refine (PiTensorProduct.map_tprod (Function.update (fun r : W =>
    (LinearMap.id : fiber D W r →ₗ[ℂ] fiber D W r)) q (action D W q a)) y).trans ?_
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext r
  by_cases hr : r = q
  · subst r; simp only [Function.update_self]
  · simp only [Function.update_of_ne hr, LinearMap.id_apply]

set_option backward.isDefEq.respectTransparency false in
theorem globalMap_finite (q : W)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val))
    (z : AmbientTensor F W (fiber D W))
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    globalMap D W s hW x (slotMap D W q
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a) z) g =
    globalMap D W s hW x z
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, Pi.smul_apply, slotMap_pure]
    exact congrArg (fun z : ℂ => c • z) (globalMap_finite_pure D W s hW x y q a g)
  | add z w hz hw => simpa only [map_add, Pi.add_apply] using congrArg₂ (fun a b : ℂ => a + b) hz hw
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
