module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrdinarySectionCoinvariants
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrbitSectionIsomorphism

@[expose] public section

noncomputable section

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.ActualInput

open scoped NumberField TensorProduct Classical
open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (v : HeightOneSpectrum (RingOfIntegers F))

abbrev standardCharacter := KPKirillovOrbitMapFaithful.ψ F v

theorem standardCharacter_properties :
    IsLocallyConstant (standardCharacter F v) ∧ standardCharacter F v ≠ 1 ∧
    Continuous (standardCharacter F v) ∧
    ∀ b, ‖((standardCharacter F v b : ℂˣ) : ℂ)‖ = 1 := by
  have hlc : IsLocallyConstant (standardCharacter F v) := by
    change IsLocallyConstant (fun x : Multiplicative (v.adicCompletion F) =>
      Circle.toUnits (localFiniteCharacter F v (1 * x.toAdd)))
    simpa only [one_mul, Function.comp_def] using
      ((isLocallyConstant_localFiniteCharacter F v).comp_continuous
        (show Continuous (Multiplicative.toAdd : Multiplicative (v.adicCompletion F) → _)
          from continuous_id)).comp Circle.toUnits
  refine ⟨hlc, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Algebra.trace_surjective
      ℚ_[PlaceTraceAdapter.prime F v] (v.adicCompletion F)
      (((PlaceTraceAdapter.prime F v).1 : ℚ)⁻¹ : ℚ_[PlaceTraceAdapter.prime F v])
    intro h
    have he := congrArg (fun χ => (χ (Multiplicative.ofAdd x) : ℂ)) h
    have hc : localFiniteCharacter F v x = 1 := by
      apply Subtype.ext
      simpa [standardCharacter, KPKirillovOrbitMapFaithful.ψ,
        KPKirillovProjectorGerms.frequencyCharacter] using he
    apply rationalPadicCharacter_inv_prime_ne_one (PlaceTraceAdapter.prime F v)
    simpa only [localFiniteCharacter_apply, PlaceTraceAdapter.trace, hx] using hc
  · apply Continuous.of_coeHom_comp
    change Continuous (fun x : Multiplicative (v.adicCompletion F) =>
      (localFiniteCharacter F v (1 * x.toAdd) : ℂ))
    simpa only [one_mul] using
      (show Continuous (fun x : Multiplicative (v.adicCompletion F) =>
        (localFiniteCharacter F v x.toAdd : ℂ)) from continuous_subtype_val.comp ((continuous_localFiniteCharacter F v).comp
        (show Continuous (Multiplicative.toAdd : Multiplicative (v.adicCompletion F) → _)
          from continuous_id)))
  · intro b
    exact Circle.norm_coe _

variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)

end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.ActualInput

end
