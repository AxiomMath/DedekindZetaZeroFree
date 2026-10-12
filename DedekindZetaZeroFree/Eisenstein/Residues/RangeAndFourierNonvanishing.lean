module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.QuotientRange
public import DedekindZetaZeroFree.Eisenstein.Residues.FourierPeriods
public import DedekindZetaZeroFree.Eisenstein.Residues.FlatFourierDetection

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages TensorActionSource ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

theorem coreZeroProfile_surjective : Function.Surjective (coreZeroProfile R P C) := by
  intro v
  obtain ⟨b,hb⟩ := v.property
  obtain ⟨x,hx⟩ := CurrentGlobalSource.quotientCoreEvaluator_source_range R.A P C
    (fullProductCompact R) (full_product_compact_iwasawa R) (asLiteralFlat b)
  refine ⟨x,Subtype.ext ?_⟩
  rw [coreZeroProfile_val,hx]
  exact hb

theorem exists_coreResidue_standard_fourier_one_ne_zero :
    ∃ x : V, MomentSources.fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C x) 1 ≠ 0 := by
  obtain ⟨b,ha,hb⟩ := exists_owned_flat_standard_fourier_ne_zero R P C
  obtain ⟨x,hx⟩ := coreZeroProfile_surjective R P C
    (literalZeroProfileEquiv (full_product_compact_iwasawa R) (b : literalFlatModule (fullProductCompact R)))
  have he : coreResidue R P C x =
      (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared b 0 := by
    change (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue
      (coreZeroProfile R P C x) = _
    rw [hx,LiteralResidueFamily.residue_flat]
  exact ⟨x,he.symm ▸ hb⟩

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
variable (N : MomentSources.TraceHaarTransport R)

theorem exists_actualCoreFourier_one_ne_zero :
    ∃ x, actualCoreFourier R P C μ hμ N 1 x ≠ 0 := by
  obtain ⟨y,hy⟩ := exists_coreResidue_standard_fourier_one_ne_zero R P C
  refine ⟨actualCoreEquiv R P C μ hμ (finiteCoreQuotient R P C μ hμ y),?_⟩
  rw [actualCoreFourier_apply,actualCoreResidue_quotient]
  exact hy
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
