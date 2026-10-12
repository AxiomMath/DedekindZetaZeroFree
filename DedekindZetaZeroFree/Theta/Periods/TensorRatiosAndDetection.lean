module

public import DedekindZetaZeroFree.Theta.Periods.TensorInsertionAndExtension
public import DedekindZetaZeroFree.Metaplectic.Kubota.DisjointArchimedeanActions
public import DedekindZetaZeroFree.Theta.Whittaker.RestrictedPeriodRatio

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

theorem actualSlot_period_ratio (N : TraceHaarTransport R)

    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) (g : Group R)
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1)
    (M : Theta traceFrequency →L[ℂ] ℂ)
    (hM : M ∈ whittakerSpace traceFrequency traceCharacter)
    (v0 : complexCore) (hv0 : M (harmonicInclusion v0) ≠ 0)
    (a : KPCplxCharacterHaar.ComplexPGL2) :
    fourier R (KPWildKernelUpperBound.quotientHaar F)
      (actualCoreResidue R P C μ hμ N (actualSlotTensor R P C μ hμ s x w hw v0))
      (g*projectiveSlot R w a) =
    (M (imageAction traceFrequency a (harmonicInclusion v0))/M (harmonicInclusion v0))*
      fourier R (KPWildKernelUpperBound.quotientHaar F)
        (actualCoreResidue R P C μ hμ N (actualSlotTensor R P C μ hμ s x w hw v0)) g := by
  obtain ⟨y,hy⟩ := actualSlot_period_lift R P C μ hμ N s x w hw
  have hc : ∀z:ℂ,g*actualMatrixSlot R w (KPCplxCharacterHaar.upperUnipotent z)=
      actualMatrixSlot R w (KPCplxCharacterHaar.upperUnipotent z)*g := by
    intro z
    rw [←projectiveSlot_mk]
    exact (projectiveSlot_commute_of_projection_one R w g hg _).eq
  exact (hy (g*projectiveSlot R w a) v0).trans
    ((restrictedSlotPeriod_background_ratio R N P C  s y w hw g hc M hM v0 hv0 a).trans
      (congrArg (fun z:ℂ => (M (imageAction traceFrequency a (harmonicInclusion v0))/M (harmonicInclusion v0))*z)
        (hy g v0).symm))

theorem actualStage_detector (N : TraceHaarTransport R)

    (s : RestrictedTensorSimple.Level E) (x : ∀j : s.val,W j.val)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F)
      (actualCoreResidue R P C μ hμ N
        (RestrictedTensorSimple.stageInclusion W e E s (PiTensorProduct.tprod ℂ x))) 1 ≠ 0)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃M : Theta traceFrequency →L[ℂ] ℂ,
      M ∈ whittakerSpace traceFrequency traceCharacter ∧
      M (harmonicInclusion (x ⟨Sum.inl w,hw⟩)) ≠ 0 := by
  obtain ⟨y,hy⟩ := actualSlot_period_lift R P C μ hμ N s x w hw
  refine ⟨actualWhittakerExtension R N P C  s y w hw,
    actualWhittakerExtension_mem R N P C  s y w hw,?_⟩
  rw [actualWhittakerExtension_core,←hy]
  simpa [actualSlotTensor,MultilinearMap.toLinearMap_apply] using hx

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
