module

public import DedekindZetaZeroFree.Theta.Periods.TensorRatiosAndDetection
public import DedekindZetaZeroFree.Metaplectic.Kubota.ArchimedeanPartialProducts

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

open CurrentOutputExtension KPCplxActualImage KPCplxWhittakerUnique

def actualStagePeriod (N : TraceHaarTransport R) (s : RestrictedTensorSimple.Level E)
    (x : ∀j : s.val,W j.val) (g : Group R) : ℂ :=
  fourier R (KPWildKernelUpperBound.quotientHaar F)
    (actualCoreResidue R P C μ hμ N
      (RestrictedTensorSimple.stageInclusion W e E s (PiTensorProduct.tprod ℂ x))) g

theorem actualStage_period_ratio (N : TraceHaarTransport R)

    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) (g : Group R)
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1)
    (M : Theta traceFrequency →L[ℂ] ℂ)
    (hM : M ∈ whittakerSpace traceFrequency traceCharacter)
    (hv0 : M (harmonicInclusion (x ⟨Sum.inl w,hw⟩)) ≠ 0)
    (a : KPCplxCharacterHaar.ComplexPGL2) :
    actualStagePeriod R P C μ hμ N s x (g*projectiveSlot R w a) =
    (M (imageAction traceFrequency a (harmonicInclusion (x ⟨Sum.inl w,hw⟩)))/
      M (harmonicInclusion (x ⟨Sum.inl w,hw⟩)))*actualStagePeriod R P C μ hμ N s x g := by
  simpa [actualStagePeriod,actualSlotTensor,MultilinearMap.toLinearMap_apply] using
    actualSlot_period_ratio R P C μ hμ N  s x w hw g hg M hM (x ⟨Sum.inl w,hw⟩) hv0 a

theorem actualStage_arch_product (N : TraceHaarTransport R)

    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (hw : ∀w : InfinitePlace F, Sum.inl w∈s.val)
    (M : InfinitePlace F → Theta traceFrequency →L[ℂ] ℂ)
    (hM : ∀w, M w ∈ whittakerSpace traceFrequency traceCharacter)
    (hv : ∀w, M w (harmonicInclusion (x ⟨Sum.inl w,hw w⟩)) ≠ 0)
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2)
    (t : Finset (InfinitePlace F)) (g : Group R)
    (hg : ∀w, PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1) :
    actualStagePeriod R P C μ hμ N s x (g*archPartial R t a) =
    (∏w∈t, (M w (imageAction traceFrequency (a w) (harmonicInclusion (x ⟨Sum.inl w,hw w⟩)))/
      M w (harmonicInclusion (x ⟨Sum.inl w,hw w⟩)))) *
      actualStagePeriod R P C μ hμ N s x g := by
  induction t using Finset.induction_on with
  | empty => simp [archPartial_empty]
  | @insert w t hwt ih =>
    have hb : PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12
        (g*archPartial R t a) w = 1 := by
      rw [map_mul]
      rw [Pi.mul_apply,hg w,archPartial_projection_not_mem R t w hwt a,one_mul]
    rw [archPartial_insert R t w hwt a,←mul_assoc,
      actualStage_period_ratio R P C μ hμ N  s x w (hw w) (g*archPartial R t a) hb (M w) (hM w) (hv w) (a w),
      ih,Finset.prod_insert hwt]
    exact (mul_assoc _ _ _).symm

theorem actualStage_arch_background (N : TraceHaarTransport R)

    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (hx : actualStagePeriod R P C μ hμ N s x 1 ≠ 0)
    (hw : ∀w : InfinitePlace F, Sum.inl w∈s.val)
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    ∃c : ℂ, ∀y : ∀j : s.val,W j.val,
      (∀w, y ⟨Sum.inl w,hw w⟩ = x ⟨Sum.inl w,hw w⟩) →
      ∀g : Group R,
      (∀w, PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1) →
      actualStagePeriod R P C μ hμ N s y
        (g*KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 a) =
        c*actualStagePeriod R P C μ hμ N s y g := by
  let M : InfinitePlace F → Theta traceFrequency →L[ℂ] ℂ := fun w =>
    Classical.choose (actualStage_detector R P C μ hμ N  s x hx w (hw w))
  have hM : ∀w, M w ∈ whittakerSpace traceFrequency traceCharacter := fun w =>
    (Classical.choose_spec (actualStage_detector R P C μ hμ N  s x hx w (hw w))).1
  have hv : ∀w, M w (harmonicInclusion (x ⟨Sum.inl w,hw w⟩)) ≠ 0 := fun w =>
    (Classical.choose_spec (actualStage_detector R P C μ hμ N  s x hx w (hw w))).2
  refine ⟨∏w, (M w (imageAction traceFrequency (a w) (harmonicInclusion (x ⟨Sum.inl w,hw w⟩)))/
      M w (harmonicInclusion (x ⟨Sum.inl w,hw w⟩))),?_⟩
  intro y hy g hg
  have hvy : ∀w, M w (harmonicInclusion (y ⟨Sum.inl w,hw w⟩)) ≠ 0 := by
    intro w
    simpa only [hy] using hv w
  simpa only [archPartial_univ,hy] using
    actualStage_arch_product R P C μ hμ N  s y hw M hM hvy a Finset.univ g hg

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
