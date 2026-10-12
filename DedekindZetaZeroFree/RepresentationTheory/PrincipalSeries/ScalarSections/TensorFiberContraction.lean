module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.RootAndTorusCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming referenceStage → referenceStage
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming expand → expand
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming le_expand → le_expand
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming expand_mono → expand_mono
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming expand_tail → expand_tail
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

def productComparison : RestrictedTensorSimple.Core (Fiber A P C) (reference A P C) (bad A P C) →ₗ[ℂ]
    KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  (finiteTensorMap A P C).comp (ScalarAbsorption.absorb
    (A := InfinitePlace F) (LocalFiber F ζ hζ P C) (localReference F ζ hζ P C) C.exceptional)

def rawStageFiber (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A) :
    RestrictedTensorSimple.Stage (Plus A P C) s.val →ₗ[ℂ]
      KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  ((productComparison A P C).comp
    (RestrictedTensorSimple.stageInclusion (Fiber A P C) (reference A P C) (bad A P C) s)).comp
      (PiTensorProduct.map (fun j => localValueMap A P C j.val (g j.val)))

private theorem rawStageFiber_transition (s t : RestrictedTensorSimple.Level (bad A P C))
    (hst : s ≤ t) (g : Raw A)
    (hnew : ∀ v ∈ t.val, v ∉ s.val →
      localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) :
    rawStageFiber A P C t g (RestrictedTensorSimple.transition (Plus A P C)
      (plusReference A P C) (bad A P C) s t hst x) = rawStageFiber A P C s g x := by
  have hm : PiTensorProduct.map (fun j : t.val => localValueMap A P C j.val (g j.val))
      (RestrictedTensorSimple.insert (Plus A P C) (plusReference A P C) s.val t.val hst x) =
      RestrictedTensorSimple.insert (Fiber A P C) (reference A P C) s.val t.val hst
        (PiTensorProduct.map (fun j : s.val => localValueMap A P C j.val (g j.val)) x) := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul]
      congr 1
      rw [RestrictedTensorSimple.insert_pure, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, RestrictedTensorSimple.insert_pure]
      congr 1
      funext j
      by_cases hj : j.val ∈ s.val
      · simp [hj, localValueMap]
      · simpa [hj, localValueMap] using hnew j.val j.property hj
    | add x y hx hy => simp only [map_add, hx, hy]
  unfold rawStageFiber
  simp only [LinearMap.comp_apply, RestrictedTensorSimple.transition]
  rw [hm]
  exact congrArg (productComparison A P C) Module.DirectLimit.of_f

 def stageFiberLift (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A) :
    RestrictedTensorSimple.Stage (Plus A P C) s.val →ₗ[ℂ]
      KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  (rawStageFiber A P C (expand A P C s g) g).comp
    (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C)
      (bad A P C) s (expand A P C s g) (le_expand A P C s g))

 theorem stageFiberLift_transition (s t : RestrictedTensorSimple.Level (bad A P C))
    (hst : s ≤ t) (g : Raw A) (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) :
    stageFiberLift A P C t g (RestrictedTensorSimple.transition (Plus A P C)
      (plusReference A P C) (bad A P C) s t hst x) = stageFiberLift A P C s g x := by
  dsimp only [stageFiberLift, LinearMap.comp_apply]
  rw [(RestrictedTensorSimple.directedSystem (Plus A P C) (plusReference A P C)
    (bad A P C)).map_map hst (le_expand A P C t g)]
  rw [← (RestrictedTensorSimple.directedSystem (Plus A P C) (plusReference A P C)
    (bad A P C)).map_map (le_expand A P C s g) (expand_mono A P C hst g)]
  exact rawStageFiber_transition A P C _ _ (expand_mono A P C hst g) g
    (fun v _ hv => expand_tail A P C s g v hv) _

def rawCoreFiber (g : Raw A) :
    RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C) →ₗ[ℂ]
      KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  Module.DirectLimit.lift ℂ _ _ _ (fun s => stageFiberLift A P C s g)
    (fun s t hst x => stageFiberLift_transition A P C s t hst g x)

theorem rawCoreFiber_stage (s : RestrictedTensorSimple.Level (bad A P C))
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) (g : Raw A)
    (htail : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v) :
    rawCoreFiber A P C g (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) s x) = rawStageFiber A P C s g x := by
  unfold rawCoreFiber RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]
  exact rawStageFiber_transition A P C s _ (le_expand A P C s g) g (fun v _ hv => htail v hv) x

theorem rawCoreValue_fiber (g : Raw A)
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    rawCoreValue A P C g x = rationalEvaluation A
      (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
        (rawCoreFiber A P C g x)) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    change rawCoreValue A P C g (RestrictedTensorSimple.stageInclusion _ _ _ s x) =
      rationalEvaluation A (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
        (rawCoreFiber A P C g (RestrictedTensorSimple.stageInclusion (Plus A P C)
          (plusReference A P C) (bad A P C) s x)))
    let t := expand A P C s g
    have he : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) s x =
        RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) t
          (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C) s t
            (le_expand A P C s g) x) := Module.DirectLimit.of_f.symm
    rw [he, rawCoreFiber_stage A P C t _ g (expand_tail A P C s g)]
    exact rawCoreInsertion_stage A P C t
      (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C) s t
        (le_expand A P C s g) x) g (expand_tail A P C s g)

theorem rawStageFiber_pure (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw A) :
    rawStageFiber A P C s g (PiTensorProduct.tprod ℂ x) =
      (∏ w : s.val.toLeft, localValue A P C (Sum.inl w.val) (g (Sum.inl w.val))
        (x ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) •
      finiteTensorRealization F ζ hζ P C s.val.toRight
        (ScalarAbsorption.rightLevel C.exceptional s).property
        (PiTensorProduct.tprod ℂ (fun q : s.val.toRight =>
          localValue A P C (Sum.inr q.val) (g (Sum.inr q.val))
            (x ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩))) := by
  unfold rawStageFiber productComparison
  simp only [LinearMap.comp_apply, PiTensorProduct.map_tprod, ScalarAbsorption.absorb_stage,
    ScalarAbsorption.stageEquiv_pure, map_smul]
  rw [finiteTensorMap_stage]
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
