module

public import DedekindZetaZeroFree.Theta.Periods.Wild.TameWordFourierAction

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem globalMap_extend (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s t : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (hst : s.val ⊆ t.val) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (z : AmbientTensor F W (fiber D W)) :
    globalMap D W t (hW.trans hst) (extendTuple D s t x) z =
    globalMap D W s hW x z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul]
    apply congrArg (fun a : Functions R ↦ c • a)
    rw [globalMap_pure, globalMap_pure]
    apply congrArg D.coreMap
    have he : stageTuple D W t (extendTuple D s t x) y =
        extendTuple D s t (stageTuple D W s x y) := by
      funext p
      by_cases hp : p.val ∈ places W
      · simp [stageTuple, extendTuple, hp, hW hp]
      · simp [stageTuple, extendTuple, hp]
    rw [he]
    change RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (PiTensorProduct.tprod ℂ (fun p ↦ if hp : p.val ∈ s.val then
        stageTuple D W s x y ⟨p.val, hp⟩ else D.references p)) = _
    rw [← RestrictedTensorSimple.insert_pure (actualLocal R D.finiteData)
      D.references s.val t.val hst (stageTuple D W s x y)]
    exact Module.DirectLimit.of_f
  | add z w hz hw => simp only [map_add, hz, hw]

theorem enlarged_finite_word_right_kernel (D : TensorDetected R N)
    (W : Finset (KPFinitePlace F)) (s t : RestrictedTensorSimple.Level D.bad)
    (hW : places W ⊆ s.val) (hst : s.val ⊆ t.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (l : List (TameAction D.toTensorActions W t))
    (z : AmbientTensor F W (fiber D.toTensorActions W))
    (hz : WildCurrentJointPeriod.period D.toTensorActions W s hW x z = 0) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x z)
      (wordGroup D.toTensorActions W t l) = 0 := by
  rw [← globalMap_extend D.toTensorActions W s t hW hst x z]
  apply finite_word_right_kernel D W t (hW.trans hst) (extendTuple D.toTensorActions s t x)
  · rw [stage_extend D.toTensorActions s t hst x]
    exact hx
  · rw [period_extend D.toTensorActions W s t hW hst x z]
    exact hz

theorem joint_kernel_enlarged_finite_word (D : TensorDetected R N)
    (W : Finset (KPFinitePlace F)) (s t : RestrictedTensorSimple.Level D.bad)
    (hW : places W ⊆ s.val) (hst : s.val ⊆ t.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (l : List (TameAction D.toTensorActions W t))
    (a : ProductAffine F R.A.zeta12 R.A.primitive_zeta12 W)
    (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v)
    (e : JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W))
    (he : WildCurrentJointForm.jointForm D.toTensorActions W s hW x e = 0) :
    fourier R D.sources.dq
      (globalMap D.toTensorActions W s hW x
        (ambientAction F R.A.zeta12 R.A.primitive_zeta12 W
          (fiber D.toTensorActions W) (action D.toTensorActions W) a
          (tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
            (depth (R := R) W) (depth_valid (R := R) W) (character W)
            (fiber D.toTensorActions W) (action D.toTensorActions W)
            (localData D.toTensorActions W) (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))))
      (wordGroup D.toTensorActions W t l) = 0 := by
  apply enlarged_finite_word_right_kernel D W s t hW hst x hx l
  exact WildCurrentJointForm.kernel_finite_borel D.toTensorActions W s hW x a f e he
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
