module

public import DedekindZetaZeroFree.Theta.Periods.Wild.ExteriorFiniteAction

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

include ho in
theorem outside_fourier (z : AmbientTensor F W (fiber D W))
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    fourier R D.sources.dq (globalMap D W s hW (outsideTuple D s x q hq a) z) g =
    fourier R D.sources.dq (globalMap D W s hW x z)
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  unfold MomentSources.fourier
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [outside_finite D W s hW x q hq ho a]
  simp only [mul_assoc]
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
