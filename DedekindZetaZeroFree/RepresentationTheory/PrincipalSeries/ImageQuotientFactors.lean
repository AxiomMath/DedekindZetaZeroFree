module

public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteImageQuotients.DescentAndCovariance
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.IntegralQuotientActions

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def matchedInducing (q : KPFinitePlace F) :
    KPLocalExceptionalConstruction.CanonicalFiniteInducingData F R.A.zeta12 R.A.primitive_zeta12 q :=
  { C.canonical q with polarization := C.polarization q }

def actualImageData (q : KPFinitePlace F) : MomentSources.LocalImageData R q where
  inducing := matchedInducing R P C q
  haar := μ q
  haar_integer := hμ q

theorem harmonicQuotient_injective : Function.Injective KPLiteralTensor.harmonicQuotient := by
  intro x y h
  apply Subtype.ext
  apply KPCplxActualImageProof.standardIntertwiner_injective (1 : ℂˣ)
  exact congrArg Subtype.val h

def harmonicQuotientEquiv : KPLiteralTensor.harmonicPlus ≃ₗ[ℂ]
    KPGlobalResidualConstruction.complexCore :=
  LinearEquiv.ofBijective KPLiteralTensor.harmonicQuotient
    ⟨harmonicQuotient_injective, KPLiteralTensor.harmonicQuotient_surjective⟩

def actualFactorEquiv (v : KPHilbert.Place F) :
    FiniteQuotientFiber R P C μ hμ v ≃ₗ[ℂ]
      MomentSources.actualLocal R (actualImageData R P C μ hμ) v := by
  cases v with
  | inl w => exact harmonicQuotientEquiv
  | inr q => exact LinearEquiv.refl ℂ _

theorem actualFactorEquiv_quotient (v : KPHilbert.Place F) (f : Plus R.A P C v) :
    actualFactorEquiv R P C μ hμ v (finiteQuotientMap R P C μ hμ v f) =
      TensorActionSource.sourceQuotient R (actualImageData R P C μ hμ) v f := by
  cases v with
  | inl w => rfl
  | inr q => rfl

theorem actualFactorEquiv_finite (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (f : FiniteQuotientFiber R P C μ hμ (Sum.inr q)) :
    actualFactorEquiv R P C μ hμ (Sum.inr q) (finiteQuotientAction R P C μ hμ q a f) =
      actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12 q
        (actualImageData R P C μ hμ q).inducing
        (actualImageData R P C μ hμ q).inducing.polarization
        (actualImageData R P C μ hμ q).haar
        (actualImageData R P C μ hμ q).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
        (actualFactorEquiv R P C μ hμ (Sum.inr q) f) := rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
