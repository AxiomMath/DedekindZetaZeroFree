module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.FiniteImageQuotients.RestrictedTensorDescent

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

def finiteQuotientAction (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) : Q (Sum.inr q) →ₗ[ℂ] Q (Sum.inr q) :=
  actualCanonicalImageRepresentation F ζ hζ q (C.canonical q) (C.polarization q)
    (μ q) (hμ q) (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a)

theorem finiteQuotientMap_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) (x : V (Sum.inr q)) :
    finiteQuotientMap R P C μ hμ (Sum.inr q) (localFiniteAction R P C q a x) =
      finiteQuotientAction R P C μ hμ q a (finiteQuotientMap R P C μ hμ (Sum.inr q) x) := by
  apply Subtype.ext
  exact actualCanonicalForwardLinear_intertwines F ζ hζ q (C.canonical q)
    (C.polarization q) (μ q) (hμ q) _ x

theorem finiteStageQuotient_update_finite (t : RestrictedTensorSimple.Level E)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) (x : ∀ j : t.val, V j.val) :
    finiteStageQuotient R P C μ hμ t (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
      (localFiniteAction R P C q a (x ⟨Sum.inr q,hq⟩)))) =
      PiTensorProduct.tprod ℂ (Function.update
        (fun j : t.val => finiteQuotientMap R P C μ hμ j.val (x j)) ⟨Sum.inr q,hq⟩
        (finiteQuotientAction R P C μ hμ q a
          (finiteQuotientMap R P C μ hμ (Sum.inr q) (x ⟨Sum.inr q,hq⟩)))) := by
  rw [finiteStageQuotient, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j = ⟨Sum.inr q,hq⟩
  · subst j
    simp only [Function.update_self]
    exact finiteQuotientMap_finite R P C μ hμ q a _
  · simp only [Function.update_of_ne hj]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
