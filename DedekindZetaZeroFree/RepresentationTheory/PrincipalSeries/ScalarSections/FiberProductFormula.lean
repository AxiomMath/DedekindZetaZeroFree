module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.TensorFiberContraction

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

def pureSections (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (v : KPHilbert.Place F) : Plus A P C v :=
  if h : v ∈ s.val then x ⟨v, h⟩ else plusReference A P C v

def archValues (f : ∀ v, Plus A P C v) (g : Raw A) : ℂ :=
  ∏ w, localValue A P C (Sum.inl w) (g (Sum.inl w)) (f (Sum.inl w))

def fiberEvaluation (f : ∀ v, Plus A P C v) (g : Raw A) (q : KPFinitePlace F)
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) : ℂ :=
  localUntwistedEvaluation F ζ hζ P C q (localValue A P C (Sum.inr q) (g (Sum.inr q))
    (f (Sum.inr q))) t

private theorem all_arch_mem (s : RestrictedTensorSimple.Level (bad A P C)) (w : InfinitePlace F) :
    Sum.inl w ∈ s.val := s.property (by simp [bad, ScalarAbsorption.fullBad])

theorem rawCoreFiber_pure_formula (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g raw : Raw A)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hg : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = e.val) :
    (rawCoreFiber A P C g (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) s (PiTensorProduct.tprod ℂ x))).val.val e =
      archValues A P C (pureSections A P C s x) g *
        (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (raw (Sum.inl w)).epsilon : ℂ)) *
        ∏ᶠ q, fiberEvaluation A P C (pureSections A P C s x) g q (t q) := by
  rw [rawCoreFiber_stage A P C s _ g hg, rawStageFiber_pure]
  change (∏ w : s.val.toLeft, localValue A P C (Sum.inl w.val) (g (Sum.inl w.val))
      (x ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) * _ = _
  rw [EisensteinReferenceSections.FullTorusFormula.finiteTensorRealization_full_raw_formula F ζ hζ P C
    s.val.toRight (ScalarAbsorption.rightLevel C.exceptional s).property
    (fun q => localValue A P C (Sum.inr q.val) (g (Sum.inr q.val))
      (x ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩)) raw t e ht he]
  have ha : (∏ w : s.val.toLeft, localValue A P C (Sum.inl w.val) (g (Sum.inl w.val))
      (x ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) =
      archValues A P C (pureSections A P C s x) g := by
    have hl : s.val.toLeft = Finset.univ := Finset.eq_univ_of_forall
      (fun w => Finset.mem_toLeft.mpr (all_arch_mem A P C s w))
    have hp : (∏ w : s.val.toLeft, localValue A P C (Sum.inl w.val) (g (Sum.inl w.val))
        (x ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) =
        ∏ w : s.val.toLeft, localValue A P C (Sum.inl w.val) (g (Sum.inl w.val))
          (pureSections A P C s x (Sum.inl w.val)) := by
      apply Finset.prod_congr rfl
      intro w _
      simp only [pureSections, dif_pos (all_arch_mem A P C s w.val)]
    rw [hp]
    exact (Finset.prod_coe_sort s.val.toLeft (fun w => localValue A P C (Sum.inl w)
      (g (Sum.inl w)) (pureSections A P C s x (Sum.inl w)))).trans (by rw [hl]; rfl)
  rw [ha, mul_assoc]
  congr 2
  apply finprod_congr
  intro q
  unfold fiberEvaluation
  congr 1
  by_cases hq : Sum.inr q ∈ s.val
  · simp [pureSections, hq, Finset.mem_toRight.mpr hq]
  · have hn : q ∉ s.val.toRight := fun h => hq (Finset.mem_toRight.mp h)
    simp only [dif_neg hn, pureSections, dif_neg hq]
    exact (hg (Sum.inr q) hq).symm

theorem fiberEvaluation_finiteSupport (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g raw : Raw A)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (hg : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) :
    Function.HasFiniteMulSupport (fun q => fiberEvaluation A P C (pureSections A P C s x) g q (t q)) := by
  have hs := local_evaluation_finiteSupport F ζ hζ P C s.val.toRight
    (ScalarAbsorption.rightLevel C.exceptional s).property
    (fun q => localValue A P C (Sum.inr q.val) (g (Sum.inr q.val))
      (x ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩)) raw t ht
  convert hs using 1
  funext q
  unfold fiberEvaluation
  congr 1
  by_cases hq : Sum.inr q ∈ s.val
  · simp [pureSections, hq, Finset.mem_toRight.mpr hq]
  · have hn : q ∉ s.val.toRight := fun h => hq (Finset.mem_toRight.mp h)
    simp only [dif_neg hn, pureSections, dif_neg hq]
    exact hg (Sum.inr q) hq
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
