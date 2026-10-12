module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.CompletionTraceComparison

@[expose] public section

noncomputable section
open scoped NumberField ValuativeRel nonZeroDivisors
open NumberField IsDedekindDomain LocalFieldTheory
open ValuationTheory.DiscreteValuationField

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type) [Field F] [NumberField F]

def baseRaw (v : HeightOneSpectrum (𝓞 F)) :
    CompleteDVF ℚ_[PlaceTraceAdapter.prime F v] :=
  localCompleteDVF ℚ_[PlaceTraceAdapter.prime F v]

def targetRaw (v : HeightOneSpectrum (𝓞 F)) : CompleteDVF (v.adicCompletion F) :=
  chosenLocalExtensionCompleteDVF ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F)

instance valuationHasExtensionRaw (v : HeightOneSpectrum (𝓞 F)) :
    (baseRaw F v).valuation.HasExtension (targetRaw F v).valuation :=
  chosenLocalExtensionCompleteDVF_hasExtension _ _

def codifferentRaw (v : HeightOneSpectrum (𝓞 F)) :
    Submodule (targetRaw F v).valuationSubring (v.adicCompletion F) :=
  RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule
    (baseRaw F v) (targetRaw F v)

def differentRaw (v : HeightOneSpectrum (𝓞 F)) :
    Ideal (targetRaw F v).valuationSubring :=
  RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
    (baseRaw F v) (targetRaw F v)

 theorem integer_mem_targetRaw (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (x : F) ∈
      (targetRaw F v).valuation.valuationSubring := by
  letI : IsIntegralClosure (targetRaw F v).valuationSubring
      (baseRaw F v).valuationSubring (v.adicCompletion F) :=
    chosenLocalExtensionCompleteDVF_isIntegralClosure _ _
  have hx : IsIntegral ℤ (x : F) := (IsIntegralClosure.isIntegral ℤ F x).algebraMap
  have h : IsIntegral ℤ (algebraMap F (v.adicCompletion F) (x : F)) := hx.algebraMap
  have h' := h.tower_top (A := (baseRaw F v).valuationSubring)
  obtain ⟨y, hy⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := (targetRaw F v).valuationSubring)).mp h'
  exact hy ▸ y.property

def integerMap (v : HeightOneSpectrum (𝓞 F)) :
    𝓞 F →+* (targetRaw F v).valuationSubring :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    (targetRaw F v).valuation.valuationSubring (integer_mem_targetRaw F v)

@[simp] theorem integerMap_coe (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    (integerMap F v x : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (x : F) := rfl

end DedekindZetaZeroFree.TraceBaseChange

end
