module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalImageFactors

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (M : ∀ q, LocalImageData R q)

abbrev RootPoint (_R : PrincipalMellin.ActualRecipe S η) : KPHilbert.Place F → Type
  | Sum.inl _ => ℂ
  | Sum.inr q => q.adicCompletion F

instance rootPointMeasurable (p : KPHilbert.Place F) : MeasurableSpace (RootPoint R p) := by
  cases p <;> infer_instance

def rootMeasure : ∀ p, Measure (RootPoint R p)
  | Sum.inl _ => KPCplxCharacterHaar.characterHaar (1 : ℂˣ)
  | Sum.inr q => (M q).haar

instance rootMeasureSigmaFinite (p : KPHilbert.Place F) : SigmaFinite (rootMeasure R M p) := by
  cases p with
  | inl w =>
    letI := KPCplxCharacterHaar.characterHaar_isAddHaarMeasure (1 : ℂˣ)
    exact inferInstanceAs (SigmaFinite (KPCplxCharacterHaar.characterHaar (1 : ℂˣ)))
  | inr q => exact inferInstanceAs (SigmaFinite (M q).haar)

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource

end
