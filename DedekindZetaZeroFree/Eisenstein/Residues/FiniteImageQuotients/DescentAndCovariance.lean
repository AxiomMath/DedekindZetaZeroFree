module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.FiniteImageQuotients.ActionCovariance
public import DedekindZetaZeroFree.Eisenstein.Residues.ConstantTerms.UpperCoefficientKernel

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
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Q" => FiniteQuotientFiber R P C μ hμ
local notation "e" => plusReference R.A P C
local notation "E" => bad R.A P C
local notation "V" => Plus R.A P C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem coreResidueUpperLinear_kernel :
    (coreResidueUpperLinear R P C).ker ≤ (coreResidue R P C).ker := by
  intro x hx
  apply coreResidue_eq_zero_of_upper_zero R P C x
  intro g
  exact congrFun hx g

theorem residueStage_finiteQuotient_kernel (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level E) :
    (finiteStageQuotient R P C μ hμ t).ker ≤
      ((coreResidue R P C).comp (RestrictedTensorSimple.stageInclusion V e E t)).ker := by
  intro x hx
  apply coreResidueUpperLinear_kernel R P C
  exact upperStage_finiteQuotient_kernel R P C μ hμ N t hx

def finiteStageResidue (N : MomentSources.TraceHaarTransport R) (t : RestrictedTensorSimple.Level E) :
    RestrictedTensorSimple.Stage Q t.val →ₗ[ℂ] Functions F ζ hζ :=
  ((finiteStageQuotient R P C μ hμ t).ker.liftQ
    ((coreResidue R P C).comp (RestrictedTensorSimple.stageInclusion V e E t))
    (residueStage_finiteQuotient_kernel R P C μ hμ N t)).comp
    ((finiteStageQuotient R P C μ hμ t).quotKerEquivOfSurjective
      (finiteStageQuotient_surjective R P C μ hμ t)).symm.toLinearMap

theorem finiteStageResidue_quotient (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level E) (x : RestrictedTensorSimple.Stage V t.val) :
    finiteStageResidue R P C μ hμ N t (finiteStageQuotient R P C μ hμ t x) =
      coreResidue R P C (RestrictedTensorSimple.stageInclusion V e E t x) := by
  simp only [finiteStageResidue, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

theorem finiteStageResidue_transition (N : MomentSources.TraceHaarTransport R)
    (s t : RestrictedTensorSimple.Level E) (hst : s ≤ t)
    (x : RestrictedTensorSimple.Stage Q s.val) :
    finiteStageResidue R P C μ hμ N t
      (RestrictedTensorSimple.transition Q (finiteQuotientReference R P C μ hμ) E s t hst x) =
      finiteStageResidue R P C μ hμ N s x := by
  obtain ⟨x,rfl⟩ := finiteStageQuotient_surjective R P C μ hμ s x
  rw [← finiteStageQuotient_transition, finiteStageResidue_quotient, finiteStageResidue_quotient]
  exact congrArg (coreResidue R P C) Module.DirectLimit.of_f

def finiteCoreResidue (N : MomentSources.TraceHaarTransport R) :
    RestrictedTensorSimple.Core Q (finiteQuotientReference R P C μ hμ) E →ₗ[ℂ]
      Functions F ζ hζ :=
  Module.DirectLimit.lift ℂ _ _ _ (finiteStageResidue R P C μ hμ N)
    (by intro s t hst x; exact finiteStageResidue_transition R P C μ hμ N s t hst x)

theorem finiteCoreResidue_quotient (N : MomentSources.TraceHaarTransport R)
    (x : RestrictedTensorSimple.Core V e E) :
    finiteCoreResidue R P C μ hμ N (finiteCoreQuotient R P C μ hμ x) = coreResidue R P C x := by
  letI : Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E,le_rfl⟩⟩
  obtain ⟨t,x,rfl⟩ := Module.DirectLimit.exists_of x
  change finiteCoreResidue R P C μ hμ N
    (finiteCoreQuotient R P C μ hμ (RestrictedTensorSimple.stageInclusion V e E t x)) = _
  rw [finiteCoreQuotient_stage]
  unfold finiteCoreResidue RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]
  exact finiteStageResidue_quotient R P C μ hμ N t x

theorem finiteCoreResidue_update_finite (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level E) (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) (x : ∀ j : t.val, Q j.val)
    (g : G F ζ hζ) :
    finiteCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion Q
      (finiteQuotientReference R P C μ hμ) E t
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
        (finiteQuotientAction R P C μ hμ q a (x ⟨Sum.inr q,hq⟩))))) g =
    finiteCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion Q
      (finiteQuotientReference R P C μ hμ) E t (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) := by
  choose y hy using fun j : t.val => finiteQuotientMap_surjective R P C μ hμ j.val (x j)
  have he : (fun j : t.val => finiteQuotientMap R P C μ hμ j.val (y j)) = x := funext hy
  rw [← he, ← finiteStageQuotient_update_finite]
  change finiteCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion Q
    (finiteQuotientReference R P C μ hμ) E t (finiteStageQuotient R P C μ hμ t _)) g = _
  rw [← finiteCoreQuotient_stage, finiteCoreResidue_quotient]
  have hx : PiTensorProduct.tprod ℂ (fun j : t.val => finiteQuotientMap R P C μ hμ j.val (y j)) =
      finiteStageQuotient R P C μ hμ t (PiTensorProduct.tprod ℂ y) :=
    (PiTensorProduct.map_tprod _ _).symm
  rw [hx, ← finiteCoreQuotient_stage, finiteCoreResidue_quotient]
  exact coreResidue_update_finite R P C q a t hq y g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
