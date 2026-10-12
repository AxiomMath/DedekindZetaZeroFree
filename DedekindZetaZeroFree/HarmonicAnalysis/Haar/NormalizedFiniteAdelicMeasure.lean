module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalCompactOpenAnnihilators
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.DifferentMassProduct
public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.FiniteHaarNormalization

variable (F : Type) [Field F] [NumberField F]

abbrev Adeles := FiniteAdeleRing (𝓞 F) F

instance numberField_countable : Countable F :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

instance integers_countable : Countable (𝓞 F) :=
  Function.Injective.countable RingOfIntegers.coe_injective

instance ideals_countable : Countable (Ideal (𝓞 F)) := by
  classical
  have h : Function.Surjective (fun s : Finset (𝓞 F) =>
      Ideal.span (↑s : Set (𝓞 F))) := by
    intro I
    exact IsNoetherian.noetherian I
  exact h.countable

instance finitePlaces_countable : Countable (HeightOneSpectrum (𝓞 F)) :=
  Function.Injective.countable (fun _ _ h => HeightOneSpectrum.ext h)

instance completion_secondCountable (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  letI : SeparableSpace (v.adicCompletion F) :=
    SeparableSpace.of_denseRange _ (v.denseRange_algebraMap F)
  infer_instance

instance adeles_secondCountable : SecondCountableTopology (Adeles F) := by
  exact KPAdelicTopology.finiteAdeles_secondCountableTopology F

def integralCompact : Set (Adeles F) :=
  Set.range (RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Filter.cofinite)

set_option backward.isDefEq.respectTransparency false in

theorem integralCompact_eq_coordinatewise :
    integralCompact F = {a : Adeles F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  unfold integralCompact
  rw [RestrictedProduct.range_structureMap]
  rfl

def integralSubgroup : AddSubgroup (Adeles F) :=
  KPAdelicTopology.integralAdeles F

@[simp] theorem coe_integralSubgroup :
    (integralSubgroup F : Set (Adeles F)) = integralCompact F := by
  rw [integralCompact_eq_coordinatewise]
  rfl

theorem integralCompact_isOpen : IsOpen (integralCompact F) := by
  rw [← coe_integralSubgroup]
  exact KPAdelicTopology.integralAdeles_isOpen F

theorem integralCompact_isCompact : IsCompact (integralCompact F) := by
  rw [← coe_integralSubgroup]
  exact KPAdelicTopology.integralAdeles_isCompact F

theorem integralCompact_interior_nonempty :
    (interior (integralCompact F)).Nonempty := by
  rw [(integralCompact_isOpen F).interior_eq]
  refine ⟨0, ?_⟩
  rw [← coe_integralSubgroup]
  exact (integralSubgroup F).zero_mem

def K0 : PositiveCompacts (Adeles F) :=
  ⟨⟨integralCompact F, integralCompact_isCompact F⟩,
    integralCompact_interior_nonempty F⟩

@[simp] theorem coe_K0 : (K0 F : Set (Adeles F)) = integralCompact F := rfl

def kappa : ℝ := 1 / Real.sqrt |(NumberField.discr F : ℝ)|

theorem kappa_pos : 0 < kappa F := by
  apply one_div_pos.mpr
  apply Real.sqrt_pos_of_pos
  apply abs_pos.mpr
  exact_mod_cast NumberField.discr_ne_zero F

def measure : Measure (Adeles F) :=
  ENNReal.ofReal (kappa F) • Measure.addHaarMeasure (K0 F)

instance measure_isAddHaarMeasure : (measure F).IsAddHaarMeasure := by
  exact Measure.IsAddHaarMeasure.smul (Measure.addHaarMeasure (K0 F))
    (ENNReal.ofReal_ne_zero_iff.mpr (kappa_pos F)) ENNReal.ofReal_ne_top

instance measure_regular : (measure F).Regular := by
  exact Measure.Regular.smul ENNReal.ofReal_ne_top

instance measure_sigmaFinite : SigmaFinite (measure F) := by
  infer_instance

end DedekindZetaZeroFree.FiniteHaarNormalization

end

section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.FiniteHaarNormalization

variable (F : Type) [Field F] [NumberField F]

theorem finprod_halfNormMass_eq_kappa :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), DifferentMass.halfNormMass F v) = kappa F := by
  exact DifferentMass.finprod_halfNormMass_eq_abs_discr F

theorem measure_integralCompact :
    measure F (integralCompact F) = ENNReal.ofReal (kappa F) := by
  change (ENNReal.ofReal (kappa F) • Measure.addHaarMeasure (K0 F))
    (K0 F : Set (Adeles F)) = _
  rw [Measure.smul_apply, Measure.addHaarMeasure_self, smul_eq_mul, mul_one]

theorem measure_integralCompact_toReal :
    (measure F (integralCompact F)).toReal = kappa F := by
  rw [measure_integralCompact, ENNReal.toReal_ofReal (le_of_lt (kappa_pos F))]

end DedekindZetaZeroFree.FiniteHaarNormalization

end
end
