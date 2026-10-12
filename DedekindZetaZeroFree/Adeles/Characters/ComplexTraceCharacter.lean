module

public import DedekindZetaZeroFree.Adeles.Characters.StandardAdditiveCharacter
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ComplexCoverImageAction
public import DedekindZetaZeroFree.Adeles.Characters.LocalTraceNontriviality

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Classical
namespace DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource
open NumberField KPReferenceChange.StandardComplexImage
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPInterface.ResidueConstruction.Raw
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F) (w : InfinitePlace F)

def complexLocalPsi : ContinuousAddChar (KPCompletion F (Sum.inr w)) :=
  by
    change ContinuousAddChar (KPHilbert.Completion F (Sum.inl w))
    exact actualLocalPsi F (PrincipalOfKP.standardCharacter F) (Sum.inl w)

theorem complexLocalPsi_trace (x : KPHilbert.Completion F (Sum.inl w)) :
    (complexLocalPsi w).toAddChar x = (archTraceCharacter w x : ℂ) := by
  change (adelicTraceQuotientCharacter F (QuotientAddGroup.mk (Pi.single w x, 0)) : ℂ) = _
  exact congrArg (fun t : Circle => (t : ℂ))
    ((adelicTraceQuotientCharacter_mk F (Pi.single w x, 0)).trans
      (adelicTraceCharacter_arch_single F w x))

end DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource

end
