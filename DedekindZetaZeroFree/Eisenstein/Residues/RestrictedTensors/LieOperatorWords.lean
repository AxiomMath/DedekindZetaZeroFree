module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RestrictedTensors.VariableSlotOperators

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open LiteralSource MomentSources HCGeneration TensorActionSource
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem stageImageQuotient_variable_slot (H : ∀ q, LocalImageData R q)
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (v : complexCore) :
    stageImageQuotient R P C H s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ (harmonicInverse v))) =
    PiTensorProduct.tprod ℂ (Function.update
      (fun j : s.val => localImageQuotient R P C H j.val (x j)) ⟨Sum.inl w,hw⟩ v) := by
  rw [stageImageQuotient, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j = ⟨Sum.inl w,hw⟩
  · subst j
    simp only [Function.update_self]
    apply Subtype.ext
    exact harmonicInverse_pin v
  · simp only [Function.update_of_ne hj]

theorem stageScalarWord_lie (s : RestrictedTensorSimple.Level (bad R.A P C))
    (b : List (Fin (groupDimension F))) (f : Functions R) :
    stageScalarWord R P C s (b.map StageGenerator.lie) f =
      actualRightWord F R.A.zeta12 R.A.primitive_zeta12 b f := by
  induction b with
  | nil => rfl
  | cons i b ih =>
    change actualRight F R.A.zeta12 R.A.primitive_zeta12 i
      (stageScalarWord R P C s (b.map StageGenerator.lie) f) = _
    rw [ih]
    rfl

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

theorem actualStageWord_eq_image
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (b : List (StageGenerator R P C s)) :
    actualStageWord R P C μ hμ s b =
      stageImageWord R P C (actualImageData R P C μ hμ) s b := by
  induction b with
  | nil => rfl
  | cons i b ih =>
    change (actualStageGenerator R P C μ hμ s i).comp
      (actualStageWord R P C μ hμ s b) = _
    rw [ih]
    rfl

include μ hμ in
theorem restrictedSlot_residue_native_word (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (b : List (Fin (groupDimension F))) :
    ∃ (y : ∀ j : s.val, Plus R.A P C j.val) (a : List ComplexGenerator),
      ∀ v : complexCore,
      actualRightWord F R.A.zeta12 R.A.primitive_zeta12 b
        (coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)) =
      coreResidue R P C (restrictedSlotTensor R.A P C s y w hw (complexWord a v)) := by
  let H := actualImageData R P C μ hμ
  let X := fun j : s.val => localImageQuotient R P C H j.val (x j)
  obtain ⟨Y,a,hY⟩ := stageImageWord_variable_slot R P C H s X w hw b
  let y : ∀ j : s.val, Plus R.A P C j.val := fun j =>
    Classical.choose (localImageQuotient_surjective R P C H j.val (Y j))
  have hy : (fun j : s.val => localImageQuotient R P C H j.val (y j)) = Y := by
    funext j
    exact Classical.choose_spec (localImageQuotient_surjective R P C H j.val (Y j))
  refine ⟨y,a,?_⟩
  intro v
  let u := PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ (harmonicInverse v))
  let u' := PiTensorProduct.tprod ℂ
    (Function.update y ⟨Sum.inl w,hw⟩ (harmonicInverse (complexWord a v)))
  have he : actualStageWord R P C μ hμ s (b.map StageGenerator.lie)
      (sourceStageQuotient R H s.val u) = sourceStageQuotient R H s.val u' := by
    rw [actualStageWord_eq_image]
    change stageImageWord R P C H s (b.map StageGenerator.lie)
      (stageImageQuotient R P C H s u) = stageImageQuotient R P C H s u'
    rw [stageImageQuotient_variable_slot,stageImageQuotient_variable_slot,hy]
    exact hY v
  have hh := actualCoreResidue_stage_word R P C μ hμ N s (b.map StageGenerator.lie)
    (sourceStageQuotient R H s.val u)
  rw [he,actualCoreResidue_source_stage,actualCoreResidue_source_stage,
    stageScalarWord_lie] at hh
  exact hh.symm

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
