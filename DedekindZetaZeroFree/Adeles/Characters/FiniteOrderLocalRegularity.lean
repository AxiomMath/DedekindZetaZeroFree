module

public import DedekindZetaZeroFree.Adeles.Characters.RayCharacterCorrectionFactors

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.CorrectionTopology
noncomputable section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]

variable {F : Type} [Field F] [NumberField F]

lemma infinite_embedding_continuous (w : InfinitePlace F) :
    Continuous (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  apply continuous_quot_mk.comp
  apply Continuous.units_map
  change Continuous (fun z : w.Completion =>
    (NumberField.InfiniteAdeleRing.ofCompletion w z, (1 : FiniteAdeleRing (𝓞 F) F)))
  apply Continuous.prodMk _ continuous_const
  change Continuous (fun z : w.Completion => Pi.mulSingle w z)
  fun_prop

lemma finite_embedding_continuous (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) := by
  apply continuous_quot_mk.comp
  apply Continuous.units_map
  change Continuous (fun z : v.adicCompletion F =>
    ((1 : InfiniteAdeleRing F), FiniteAdeleRing.ofAdicCompletion F v z))
  apply Continuous.prodMk continuous_const
  let a := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))
  let f : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      a (Filter.principal {v}ᶜ) := fun z => ⟨Pi.mulSingle v z, by
        rw [Filter.eventually_principal]
        intro w hw
        rw [Pi.mulSingle_eq_of_ne (by simpa using hw)]
        exact one_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr (by
    change Continuous (fun z : v.adicCompletion F => Pi.mulSingle v z)
    fun_prop)
  have hi : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) := by
    simp
  exact (RestrictedProduct.continuous_inclusion hi).comp hf

end
end DedekindZetaZeroFree.SArithmeticData.CorrectionTopology
