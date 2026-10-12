module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.FiniteFiberKernel

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPLocalPrincipalSeries
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
attribute [local irreducible] coreFlatInsertion
set_option backward.isDefEq.respectTransparency true

def coreScatteringLinear (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : G F ζ hζ) :
    V →ₗ[ℂ] ℂ where
  toFun x := coreScattering R P C x s g
  map_add' x y := by
    have he : (fun u : KPAdeles F => (coreFlatInsertion R P C (x+y)).val s
        (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ u * g)) =
        (fun u => (coreFlatInsertion R P C x).val s
          (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ u * g) +
          (coreFlatInsertion R P C y).val s
          (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ u * g)) := by
      funext u
      rw [map_add]
      rfl
    unfold coreScattering
    rw [he]
    exact integral_add (coreScattering_integrable R P C x s hs g)
      (coreScattering_integrable R P C y s hs g)
  map_smul' c x := by
    have he : (fun u : KPAdeles F => (coreFlatInsertion R P C (c • x)).val s
        (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ u * g)) =
        (fun u => c * (coreFlatInsertion R P C x).val s
          (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ u * g)) := by
      funext u
      rw [map_smul]
      rfl
    unfold coreScattering
    rw [he, integral_const_mul]
    rfl

def slotCore (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ t.val) : Plus R.A P C (Sum.inr q) →ₗ[ℂ] V :=
  (RestrictedTensorSimple.stageInclusion _ _ _ t).comp
    ((PiTensorProduct.tprod ℂ).toLinearMap x ⟨Sum.inr q,hq⟩)

@[simp] theorem slotCore_apply (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ t.val) (f : Plus R.A P C (Sum.inr q)) :
    slotCore R P C t x q hq f = RestrictedTensorSimple.stageInclusion _ _ _ t
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩ f)) := rfl

set_option backward.isDefEq.respectTransparency false

def scatteringSlotOutputLinear (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (s : ℂ) (g : Raw R.A) :
    Plus R.A P C (Sum.inr q) →ₗ[ℂ] LocalFiber F ζ hζ P C q where
  toFun := scatteringSlotOutput R P C q μ hμ s g
  map_add' f h := by
    simp only [scatteringSlotOutput, integralSpectralSection, integralCompactProfile, map_add]
    rfl
  map_smul' c f := by
    simp only [scatteringSlotOutput, integralSpectralSection, integralCompactProfile, map_smul]
    rfl

theorem scatteringSlotOutputLinear_ker_le (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ t.val) (g : Raw R.A)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) :
    (scatteringSlotOutputLinear R P C q μ hμ s g).ker ≤
      ((coreScatteringLinear R P C s hs
        (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ g))).comp
            (slotCore R P C t x q hq)).ker := by
  intro f hf
  change scatteringSlotOutput R P C q μ hμ s g f = 0 at hf
  change coreScattering R P C (slotCore R P C t x q hq f) s _ = 0
  rw [slotCore_apply]
  apply coreScattering_slot_kernel R P C N t _ q hq g μ hμ s hs
  simpa only [Function.update_self] using hf

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
