module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.CompletionTraceComparison
public import DedekindZetaZeroFree.Adeles.Characters.RationalPadicCharacter

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

def localFiniteCharacter (v : HeightOneSpectrum (𝓞 F)) :
    AddChar (v.adicCompletion F) Circle :=
  (rationalPadicCharacter (PlaceTraceAdapter.prime F v)).compAddMonoidHom
    (PlaceTraceAdapter.trace F v).toAddMonoidHom

theorem localFiniteCharacter_apply (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) :
    localFiniteCharacter F v x =
      rationalPadicCharacter (PlaceTraceAdapter.prime F v)
        (PlaceTraceAdapter.trace F v x) := by
  rfl

private theorem continuous_rationalCompletionEquiv_symm
    (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (PlaceTraceAdapter.rationalCompletionEquiv F v).symm := by
  letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ
      (PlaceTraceAdapter.rationalPlace F v)
  have hfun : (PlaceTraceAdapter.rationalCompletionEquiv F v).symm =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
        (PlaceTraceAdapter.rationalPlace F v)).symm.toAlgEquiv.toRingEquiv := by
    ext x; rfl
  rw [hfun]
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
    (PlaceTraceAdapter.rationalPlace F v)).symm.continuous_toFun

private theorem continuous_padicMap (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (PlaceTraceAdapter.padicMap F v) := by
  rw [PlaceTraceAdapter.padicMap]
  exact (finitePlaceAdicCompletionMap_continuous ℚ F
      (PlaceTraceAdapter.rationalPlace F v) ⟨v, rfl⟩).comp
    (continuous_rationalCompletionEquiv_symm F v)

theorem continuous_localFiniteCharacter (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (localFiniteCharacter F v : v.adicCompletion F → Circle) := by
  haveI : ContinuousSMul ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F) := by
    constructor
    change Continuous (fun x : ℚ_[PlaceTraceAdapter.prime F v] ×
      v.adicCompletion F => PlaceTraceAdapter.padicMap F v x.1 * x.2)
    exact ((continuous_padicMap F v).comp continuous_fst).mul continuous_snd
  have htrace : Continuous (PlaceTraceAdapter.trace F v) :=
    (PlaceTraceAdapter.trace F v).continuous_of_finiteDimensional
  exact (continuous_rationalPadicCharacter (PlaceTraceAdapter.prime F v)).comp htrace

theorem localFiniteCharacter_add (v : HeightOneSpectrum (𝓞 F))
    (x y : v.adicCompletion F) :
    localFiniteCharacter F v (x + y) =
      localFiniteCharacter F v x * localFiniteCharacter F v y :=
  AddChar.map_add_eq_mul _ x y

theorem localFiniteCharacter_eq_one_iff (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) :
    localFiniteCharacter F v x = 1 ↔
      PlaceTraceAdapter.trace F v x ∈
        Set.range (fun z : ℤ_[PlaceTraceAdapter.prime F v] =>
          (z : ℚ_[PlaceTraceAdapter.prime F v])) := by
  rw [localFiniteCharacter_apply]
  exact rationalPadicCharacter_eq_one_iff (PlaceTraceAdapter.prime F v) _

theorem localFiniteCharacter_eq_one_of_mem_integers
    (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (ha : a ∈ v.adicCompletionIntegers F) :
    localFiniteCharacter F v a = 1 := by
  rw [localFiniteCharacter_eq_one_iff]
  exact PlaceTraceAdapter.trace_mem_padicIntegers F v a ha

end DedekindZetaZeroFree

end
