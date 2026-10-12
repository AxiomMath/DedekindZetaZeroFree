module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteSupportDecomposition

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance finiteRawKernelDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem joint_kernel_finite_raw (D : TensorDetected R N)
    (W : Finset (KPFinitePlace F)) (s : RestrictedTensorSimple.Level D.bad)
    (hW : places W ⊆ s.val) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀ q : KPFinitePlace F, Sum.inr q ∉ places W →
      WildCurrentTameExterior.tameSlot (Sum.inr q))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (harch : ∀ w : InfinitePlace F, a (Sum.inl w) = 1)
    (hb : ∀ q : W, KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q.val) (a (Sum.inr q.val)) ∈
      KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q.val)
    (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v)
    (e : JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W))
    (he : WildCurrentJointForm.jointForm D.toTensorActions W s hW x e = 0) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x
      (tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
        (depth (R := R) W) (depth_valid (R := R) W) (character W)
        (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W)
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))) (rawGlobal (R := R) a) = 0 := by
  have hzero := joint_kernel_raw_borel_word D W s hW x hx (outsideRaw W a)
    (outsideRaw_support W a harch ht) (insideActions W a hb) f e he
  let θ : Functions R := globalMap D.toTensorActions W s hW x
    (tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (depth_valid (R := R) W) (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W)
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))
  have hsame := congrArg (fourier R D.sources.dq θ) (raw_split (R := R) W a hb)
  exact hsame.symm.trans hzero
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
