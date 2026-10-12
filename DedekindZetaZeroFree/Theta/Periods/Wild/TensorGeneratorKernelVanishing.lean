module

public import DedekindZetaZeroFree.Theta.Periods.Wild.ArchimedeanExteriorTransport

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
local instance jointEliminationDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 750000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem linear_zero_of_tensor_generators {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module ℂ (V i)]
    {A B : Type*} [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    (L : ((⨂[ℂ] i, V i) ⊗[ℂ] A) →ₗ[ℂ] B)
    (h : ∀ f e, L (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e) = 0)
    (z : (⨂[ℂ] i, V i) ⊗[ℂ] A) : L z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact L.map_zero
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul f e =>
    induction f using PiTensorProduct.induction_on with
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb, add_zero]
    | smul_tprod c f => simp only [← TensorProduct.smul_tmul', map_smul, h f e, smul_zero]

variable (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)

def jointImage (E : Submodule ℂ (JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (character W) (fiber D.toTensorActions W) (action D.toTensorActions W))) :
    InducedTensor F R.A.zeta12 R.A.primitive_zeta12 W (depth (R := R) W)
      (character W) (fiber D.toTensorActions W) (action D.toTensorActions W) E →ₗ[ℂ] Functions R :=
  (globalMap D.toTensorActions W s hW x).comp
    (subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (depth_valid (R := R) W) (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W) E)

theorem induced_image_zero_of_arch_exterior
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀ q : KPFinitePlace F, Sum.inr q ∉ places W → WildCurrentTameExterior.tameSlot (Sum.inr q))
    (H : JointArchExterior D.toTensorActions W s hW x) (q : W)
    (E : Submodule ℂ (JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (character W) (fiber D.toTensorActions W) (action D.toTensorActions W)))
    (hE : E ≤ (WildCurrentJointForm.jointForm D.toTensorActions W s hW x).ker)
    (z : InducedTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) (fiber D.toTensorActions W) (action D.toTensorActions W) E) :
    jointImage D W s hW x E z = 0 := by
  let L := jointImage D W s hW x E
  change L z = 0
  have hp (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v) (e : E) :
      L (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e) = 0 := by
    apply globalMap_image_zero_of_all_borel D.toTensorActions W s hW x E q
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e)
    intro b
    exact joint_kernel_all_borel_of_arch_exterior D W s hW x hx ht H f e.val (hE e.property) b
  exact linear_zero_of_tensor_generators L hp z

end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
