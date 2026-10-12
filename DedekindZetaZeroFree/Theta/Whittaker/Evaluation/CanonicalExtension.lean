module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.CompletedOutputExtension
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactTranslationBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)

include N  in
theorem actualSlot_bound : CompactBound (actualSlot R P C s x w hw) := by
  intro K hK
  obtain ⟨orders,B,hB,h⟩ := restrictedSlot_actual_compact_bound R N P C  s x w hw K hK
  exact ⟨orders,⟨B,hB.le⟩,h⟩

def canonicalOutput (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12) :
    PrincipalSeries negativeParameter →L[ℂ] ℂ :=
  extendedEvaluation (actualSlot R P C s x w hw) (actualSlot_bound R N P C  s x w hw) g

theorem canonicalOutput_core (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)
    (v : complexCore) :
    canonicalOutput R N P C  s x w hw g (smoothInclusion v)=
      LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g :=
  extendedEvaluation_core _ _ g v

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
