module

public import DedekindZetaZeroFree.Theta.Periods.RestrictedTensorIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open LiteralSource MomentSources HCGeneration TensorActionSource KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def actualSlotTensor (s : RestrictedTensorSimple.Level E)
    (x : ∀j : s.val,W j.val) (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    complexCore →ₗ[ℂ] RestrictedTensorSimple.Core W e E :=
  (RestrictedTensorSimple.stageInclusion W e E s).comp
    ((PiTensorProduct.tprod ℂ).toLinearMap x ⟨Sum.inl w,hw⟩)

theorem actualSlot_source_lift (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃y : ∀j : s.val,Plus R.A P C j.val, ∀v : complexCore,
      actualCoreResidue R P C μ hμ N (actualSlotTensor R P C μ hμ s x w hw v) =
      coreResidue R P C (restrictedSlotTensor R.A P C s y w hw v) := by
  let y : ∀j : s.val,Plus R.A P C j.val := fun j =>
    Classical.choose (localImageQuotient_surjective R P C H j.val (x j))
  have hy : (fun j : s.val => localImageQuotient R P C H j.val (y j)) = x := by
    funext j
    exact Classical.choose_spec (localImageQuotient_surjective R P C H j.val (x j))
  refine ⟨y,?_⟩
  intro v
  have he : sourceStageQuotient R H s.val
      (PiTensorProduct.tprod ℂ (Function.update y ⟨Sum.inl w,hw⟩ (harmonicInverse v))) =
      PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ v) := by
    change stageImageQuotient R P C H s _ = _
    exact (stageImageQuotient_variable_slot R P C H s y w hw v).trans
      (congrArg (fun z : ∀j : s.val,W j.val =>
        PiTensorProduct.tprod ℂ (Function.update z ⟨Sum.inl w,hw⟩ v)) hy)
  have hh := actualCoreResidue_source_stage R P C μ hμ N s
    (PiTensorProduct.tprod ℂ (Function.update y ⟨Sum.inl w,hw⟩ (harmonicInverse v)))
  exact (congrArg (fun z : RestrictedTensorSimple.Stage W s.val =>
    actualCoreResidue R P C μ hμ N
      (RestrictedTensorSimple.stageInclusion W e E s z)) he.symm).trans hh

theorem actualSlot_period_lift (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃y : ∀j : s.val,Plus R.A P C j.val, ∀g : Group R, ∀v : complexCore,
      fourier R (KPWildKernelUpperBound.quotientHaar F)
        (actualCoreResidue R P C μ hμ N (actualSlotTensor R P C μ hμ s x w hw v)) g =
      restrictedSlotPeriod R P C s y w hw g v := by
  obtain ⟨y,hy⟩ := actualSlot_source_lift R P C μ hμ N s x w hw
  refine ⟨y,?_⟩
  intro g v
  exact congrArg (fun f => fourier R (KPWildKernelUpperBound.quotientHaar F) f g) (hy v)

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
