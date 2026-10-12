module

public import DedekindZetaZeroFree.Theta.Periods.Wild.TensorGeneratorKernelVanishing

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
local instance jointFaithfulnessDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)

theorem detected_coordinates_nonzero
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0) :
    ∀ p, x p ≠ 0 := fun p hp ↦
  hx ((coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s).map_coord_zero p hp)

theorem globalMap_injective_detected
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0) :
    Function.Injective (globalMap D.toTensorActions W s hW x) :=
  (WildCurrentInsertion.insertion_injective D s x (detected_coordinates_nonzero D s x hx)
    (places W) hW).comp (reindex D.toTensorActions W).injective

theorem subspace_pure_fixedCoefficient
    (E : Submodule ℂ (JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (character W) (fiber D.toTensorActions W) (action D.toTensorActions W)))
    (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v) (e : E) :
    subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (depth_valid (R := R) W) (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W) E
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e) =
    KPWildNormalizedCoefficientInsertion.fixedCoefficientMap F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (depth_valid (R := R) W) (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W) f e.val := rfl

theorem jointImage_apply
    (E : Submodule ℂ (JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (character W) (fiber D.toTensorActions W) (action D.toTensorActions W)))
    (z : InducedTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) (fiber D.toTensorActions W) (action D.toTensorActions W) E) :
    jointImage D W s hW x E z = globalMap D.toTensorActions W s hW x
      (subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
        (depth (R := R) W) (depth_valid (R := R) W) (character W)
        (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W) E z) := by
  dsimp only [jointImage, LinearMap.comp_apply]

theorem jointForm_injective_of_arch_exterior
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀ q : KPFinitePlace F, Sum.inr q ∉ places W → WildCurrentTameExterior.tameSlot (Sum.inr q))
    (H : JointArchExterior D.toTensorActions W s hW x) (q : W) :
    Function.Injective (WildCurrentJointForm.jointForm D.toTensorActions W s hW x) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro e he
  have hg := globalMap_injective_detected D W s hW x hx
  let f := Classical.choose (exists_fixed_injective D.toTensorActions W)
  have hi := (Classical.choose_spec (exists_fixed_injective D.toTensorActions W)).2
  let E := (WildCurrentJointForm.jointForm D.toTensorActions W s hW x).ker
  let eE : E := ⟨e, he⟩
  have hz := induced_image_zero_of_arch_exterior D W s hW x hx ht H q E le_rfl
    (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] eE)
  let j := KPWildNormalizedCoefficientInsertion.fixedCoefficientMap F R.A.zeta12 R.A.primitive_zeta12 W
    (depth (R := R) W) (depth_valid (R := R) W) (character W)
    (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W) f
  have hgj : globalMap D.toTensorActions W s hW x (j e) = 0 := by
    have hpin := subspace_pure_fixedCoefficient D W E f eE
    have hzpin := jointImage_apply D W s hW x E (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] eE)
    exact (congrArg (globalMap D.toTensorActions W s hW x) hpin).symm.trans (hzpin.symm.trans hz)
  have hj : j e = 0 := hg (hgj.trans (map_zero _).symm)
  exact hi (hj.trans (map_zero j).symm)
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
