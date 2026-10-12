module

public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical
open NumberField MeasureTheory ValuativeRel
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
structure LocalImageData (q : KPFinitePlace F) where
  inducing : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F R.A.zeta12 R.A.primitive_zeta12 q
  haar : Measure (q.adicCompletion F)
  [haar_add : haar.IsAddHaarMeasure]
  haar_integer : haar ((valuation (q.adicCompletion F)).integer : Set (q.adicCompletion F)) = 1
attribute [instance] LocalImageData.haar_add
abbrev actualLocal (M : ∀ q, LocalImageData R q) : KPHilbert.Place F → Type
  | Sum.inl _ => KPGlobalResidualConstruction.complexCore
  | Sum.inr q => KPRankOneShellRepair.actualCanonicalImageModule F R.A.zeta12 R.A.primitive_zeta12
      q (M q).inducing (M q).inducing.polarization (M q).haar (M q).haar_integer
instance actualLocalAdd (M : ∀ q, LocalImageData R q)
    (p : KPHilbert.Place F) : AddCommGroup (actualLocal R M p) := by
  cases p with
  | inl w => exact inferInstanceAs (AddCommGroup KPGlobalResidualConstruction.complexCore)
  | inr q => exact inferInstance
instance actualLocalModule (M : ∀ q, LocalImageData R q)
    (p : KPHilbert.Place F) : Module ℂ (actualLocal R M p) := by
  cases p with
  | inl w => exact inferInstanceAs (Module ℂ KPGlobalResidualConstruction.complexCore)
  | inr q => exact inferInstance
end DedekindZetaZeroFree.MomentSources

end
