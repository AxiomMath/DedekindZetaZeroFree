module

public import DedekindZetaZeroFree.Theta.Periods.Wild.ConstantTermRootCovariance
public import DedekindZetaZeroFree.Theta.Periods.KernelPeriodRealizationAndCoinvariants

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance wildCurrentConstantMapDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)
  (μ : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure μ]
  (b : KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12)

theorem constant_integrable (z : AmbientTensor F W (fiber D W)) :
    Integrable (KPWildRawSourceConstruction.sourceFiber F R.A.zeta12 R.A.primitive_zeta12 b
      (globalMap D W s hW x z)) μ := by
  have hc := KPWildKernelSource.rawBorelRootFiber_continuous F R.A.zeta12 R.A.primitive_zeta12
    (globalMap D W s hW x z) (globalMap_regular D W s hW x z).1
    (globalMap_rational D W s hW x z) b
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def constantMap : AmbientTensor F W (fiber D W) →ₗ[ℂ] ℂ where
  toFun z := ∫ u, KPWildRawSourceConstruction.sourceFiber F R.A.zeta12 R.A.primitive_zeta12 b
    (globalMap D W s hW x z) u ∂μ
  map_add' z w := by
    simp only [map_add, Pi.add_apply]
    exact integral_add (constant_integrable D W s hW x μ b z) (constant_integrable D W s hW x μ b w)
  map_smul' c z := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    exact integral_smul c _

theorem ambient_root_eq_slot (q : W) (t : q.val.adicCompletion F) :
    ambientAction F R.A.zeta12 R.A.primitive_zeta12 W (fiber D W) (action D W)
      (Function.update (1 : ProductAffine F R.A.zeta12 R.A.primitive_zeta12 W) q
        (KPKirillovGenuineSectionCharts.n F R.A.zeta12 R.A.primitive_zeta12 q.val t)) =
    slotMap D W q
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)
        (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t)) := by
  apply congrArg PiTensorProduct.map
  funext r
  by_cases hr : r = q
  · subst r
    simp only [Function.update_self]
    rfl
  · simp only [Function.update_of_ne hr, Pi.one_apply, Subgroup.coe_one, map_one]
    rfl
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
