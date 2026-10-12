module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ImageQuotientFactors

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPRankOneShellRepair
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "Q" => FiniteQuotientFiber R P C μ hμ
local notation "W" => MomentSources.actualLocal R (actualImageData R P C μ hμ)
local notation "e" => finiteQuotientReference R P C μ hμ
local notation "E" => bad R.A P C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def actualReference (v : KPHilbert.Place F) : W v := actualFactorEquiv R P C μ hμ v (e v)

def actualStageEquiv (t : RestrictedTensorSimple.Level E) :
    RestrictedTensorSimple.Stage Q t.val ≃ₗ[ℂ] RestrictedTensorSimple.Stage W t.val :=
  PiTensorProduct.congr (fun j => actualFactorEquiv R P C μ hμ j.val)

theorem actualStageEquiv_transition (s t : RestrictedTensorSimple.Level E) (hst : s ≤ t) :
    (actualStageEquiv R P C μ hμ t).toLinearMap.comp
      (RestrictedTensorSimple.transition Q e E s t hst) =
    (RestrictedTensorSimple.transition W (actualReference R P C μ hμ) E s t hst).comp
      (actualStageEquiv R P C μ hμ s).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    actualStageEquiv, LinearEquiv.coe_coe, RestrictedTensorSimple.transition,
    RestrictedTensorSimple.insert_pure, PiTensorProduct.congr_tprod]
  congr 1
  funext j
  split_ifs <;> rfl

def actualCoreEquiv : RestrictedTensorSimple.Core Q e E ≃ₗ[ℂ]
    RestrictedTensorSimple.Core W (actualReference R P C μ hμ) E :=
  Module.DirectLimit.congr (fun t => actualStageEquiv R P C μ hμ t)
    (actualStageEquiv_transition R P C μ hμ)

theorem actualCoreEquiv_stage (t : RestrictedTensorSimple.Level E)
    (x : RestrictedTensorSimple.Stage Q t.val) :
    actualCoreEquiv R P C μ hμ (RestrictedTensorSimple.stageInclusion Q e E t x) =
      RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) E t
        (actualStageEquiv R P C μ hμ t x) := by
  unfold actualCoreEquiv
  exact Module.DirectLimit.congr_apply_of
    (fun t : RestrictedTensorSimple.Level E => actualStageEquiv R P C μ hμ t)
    (actualStageEquiv_transition R P C μ hμ) x

def actualCoreResidue (N : MomentSources.TraceHaarTransport R) :
    RestrictedTensorSimple.Core W (actualReference R P C μ hμ) E →ₗ[ℂ]
      MomentSources.Functions R :=
  (finiteCoreResidue R P C μ hμ N).comp (actualCoreEquiv R P C μ hμ).symm.toLinearMap

theorem actualCoreResidue_stage (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level E) (x : RestrictedTensorSimple.Stage Q t.val) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W
      (actualReference R P C μ hμ) E t (actualStageEquiv R P C μ hμ t x)) =
      finiteCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion Q e E t x) := by
  rw [← actualCoreEquiv_stage]
  change finiteCoreResidue R P C μ hμ N
    ((actualCoreEquiv R P C μ hμ).symm ((actualCoreEquiv R P C μ hμ)
      (RestrictedTensorSimple.stageInclusion Q e E t x))) = _
  exact congrArg (finiteCoreResidue R P C μ hμ N)
    ((actualCoreEquiv R P C μ hμ).symm_apply_apply _)

theorem actualCoreResidue_source_stage (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level E) (x : RestrictedTensorSimple.Stage (Plus R.A P C) t.val) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W
      (actualReference R P C μ hμ) E t
      (TensorActionSource.sourceStageQuotient R (actualImageData R P C μ hμ) t.val x)) =
      coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _ t x) := by
  have he : TensorActionSource.sourceStageQuotient R (actualImageData R P C μ hμ) t.val x =
      actualStageEquiv R P C μ hμ t (finiteStageQuotient R P C μ hμ t x) := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul]
      congr 1
      have hs : TensorActionSource.sourceStageQuotient R (actualImageData R P C μ hμ) t.val
          (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ
          (fun j : t.val => TensorActionSource.sourceQuotient R (actualImageData R P C μ hμ) j.val (x j)) :=
        PiTensorProduct.map_tprod _ x
      have hf : finiteStageQuotient R P C μ hμ t (PiTensorProduct.tprod ℂ x) =
          PiTensorProduct.tprod ℂ (fun j : t.val => finiteQuotientMap R P C μ hμ j.val (x j)) :=
        PiTensorProduct.map_tprod _ x
      have hg : actualStageEquiv R P C μ hμ t
          (PiTensorProduct.tprod ℂ (fun j : t.val => finiteQuotientMap R P C μ hμ j.val (x j))) =
          PiTensorProduct.tprod ℂ (fun j : t.val => actualFactorEquiv R P C μ hμ j.val
            (finiteQuotientMap R P C μ hμ j.val (x j))) :=
        PiTensorProduct.congr_tprod _ _
      have hj : (fun j : t.val => TensorActionSource.sourceQuotient R (actualImageData R P C μ hμ) j.val (x j)) =
          (fun j : t.val => actualFactorEquiv R P C μ hμ j.val (finiteQuotientMap R P C μ hμ j.val (x j))) := by
        funext j
        exact (actualFactorEquiv_quotient R P C μ hμ j.val (x j)).symm
      exact hs.trans ((congrArg (PiTensorProduct.tprod ℂ) hj).trans
        (hg.symm.trans (congrArg (actualStageEquiv R P C μ hμ t) hf.symm)))
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [he, actualCoreResidue_stage, ← finiteCoreQuotient_stage, finiteCoreResidue_quotient]

theorem actualCoreResidue_update_finite (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level E) (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (x : ∀ j : t.val, W j.val) (g : MomentSources.Group R) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W
      (actualReference R P C μ hμ) E t
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
        (actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12 q
          (actualImageData R P C μ hμ q).inducing
          (actualImageData R P C μ hμ q).inducing.polarization
          (μ q) (hμ q)
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q,hq⟩))))) g =
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W
      (actualReference R P C μ hμ) E t (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  let y : ∀ j : t.val, Q j.val := fun j => (actualFactorEquiv R P C μ hμ j.val).symm (x j)
  have he : (fun j : t.val => actualFactorEquiv R P C μ hμ j.val (y j)) = x := by
    funext j
    exact (actualFactorEquiv R P C μ hμ j.val).apply_symm_apply _
  have hp : actualStageEquiv R P C μ hμ t (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ x := by rw [actualStageEquiv, PiTensorProduct.congr_tprod, he]
  have ho : actualStageEquiv R P C μ hμ t (PiTensorProduct.tprod ℂ
      (Function.update y ⟨Sum.inr q,hq⟩ (finiteQuotientAction R P C μ hμ q a (y ⟨Sum.inr q,hq⟩)))) =
      PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
        (actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12 q
          (actualImageData R P C μ hμ q).inducing
          (actualImageData R P C μ hμ q).inducing.polarization (μ q) (hμ q)
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q,hq⟩))) := by
    rw [actualStageEquiv, PiTensorProduct.congr_tprod]
    congr 1
    funext j
    by_cases hj : j = ⟨Sum.inr q,hq⟩
    · subst j
      simp only [Function.update_self]
      rw [actualFactorEquiv_finite, congrFun he ⟨Sum.inr q,hq⟩]
      rfl
    · simp only [Function.update_of_ne hj]
      exact congrFun he j
  rw [← hp, ← ho, actualCoreResidue_stage, actualCoreResidue_stage]
  exact finiteCoreResidue_update_finite R P C μ hμ N t q hq a y g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
