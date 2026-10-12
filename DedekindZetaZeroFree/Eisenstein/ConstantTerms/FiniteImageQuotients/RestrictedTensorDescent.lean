module

public import DedekindZetaZeroFree.Eisenstein.Residues.UpperConstantTerm.FiniteTensorQuotient

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
local notation "e" => plusReference R.A P C
local notation "E" => bad R.A P C
local notation "V" => Plus R.A P C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def finiteQuotientReference (v : KPHilbert.Place F) : Q v :=
  finiteQuotientMap R P C μ hμ v (e v)

def finiteStageQuotient (t : RestrictedTensorSimple.Level E) :
    RestrictedTensorSimple.Stage V t.val →ₗ[ℂ] RestrictedTensorSimple.Stage Q t.val :=
  PiTensorProduct.map (fun j : t.val => finiteQuotientMap R P C μ hμ j.val)

theorem finiteStageQuotient_surjective (t : RestrictedTensorSimple.Level E) :
    Function.Surjective (finiteStageQuotient R P C μ hμ t) := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    choose x hx using fun j : t.val => finiteQuotientMap_surjective R P C μ hμ j.val (y j)
    refine ⟨c • PiTensorProduct.tprod ℂ x, ?_⟩
    simp only [finiteStageQuotient, map_smul, PiTensorProduct.map_tprod]
    rw [show (fun j : t.val => finiteQuotientMap R P C μ hμ j.val (x j)) = y from funext hx]
  | add y z hy hz =>
    obtain ⟨x,rfl⟩ := hy
    obtain ⟨w,rfl⟩ := hz
    exact ⟨x+w,map_add _ _ _⟩

theorem finiteStageQuotient_transition (s t : RestrictedTensorSimple.Level E)
    (hst : s ≤ t) (x : RestrictedTensorSimple.Stage V s.val) :
    finiteStageQuotient R P C μ hμ t (RestrictedTensorSimple.transition V e E s t hst x) =
      RestrictedTensorSimple.transition Q (finiteQuotientReference R P C μ hμ) E s t hst
        (finiteStageQuotient R P C μ hμ s x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure,
      finiteStageQuotient, PiTensorProduct.map_tprod]
    congr 1
    congr 1
    funext j
    by_cases hj : j.val ∈ s.val
    · simp [hj]
    · simp [hj, finiteQuotientReference]
  | add x y hx hy => simp only [map_add, hx, hy]

def finiteCoreQuotient : RestrictedTensorSimple.Core V e E →ₗ[ℂ]
    RestrictedTensorSimple.Core Q (finiteQuotientReference R P C μ hμ) E :=
  Module.DirectLimit.lift ℂ _ _ _
    (fun t => (RestrictedTensorSimple.stageInclusion Q (finiteQuotientReference R P C μ hμ) E t).comp
      (finiteStageQuotient R P C μ hμ t))
    (by
      intro s t hst x
      simp only [LinearMap.comp_apply, finiteStageQuotient_transition]
      exact Module.DirectLimit.of_f)

theorem finiteCoreQuotient_stage (t : RestrictedTensorSimple.Level E)
    (x : RestrictedTensorSimple.Stage V t.val) :
    finiteCoreQuotient R P C μ hμ (RestrictedTensorSimple.stageInclusion V e E t x) =
      RestrictedTensorSimple.stageInclusion Q (finiteQuotientReference R P C μ hμ) E t
        (finiteStageQuotient R P C μ hμ t x) := by
  unfold finiteCoreQuotient RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]
  rfl

theorem finiteCoreQuotient_surjective : Function.Surjective (finiteCoreQuotient R P C μ hμ) := by
  letI : Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E,le_rfl⟩⟩
  intro y
  obtain ⟨t,y,rfl⟩ := Module.DirectLimit.exists_of y
  obtain ⟨x,rfl⟩ := finiteStageQuotient_surjective R P C μ hμ t y
  exact ⟨RestrictedTensorSimple.stageInclusion V e E t x,
    finiteCoreQuotient_stage R P C μ hμ t x⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
