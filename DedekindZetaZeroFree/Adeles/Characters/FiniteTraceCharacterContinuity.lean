module

public import DedekindZetaZeroFree.Adeles.Characters.TraceProductFormula

@[expose] public section

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.RepresentationTheory.AdelicTraceCharacterHelpers

variable (F : Type) [Field F] [NumberField F]

theorem finiteCharacter_product_continuous :
    Continuous (fun a : FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, localFiniteCharacter F v (a v)) := by
  classical
  apply RestrictedProduct.continuous_dom.mpr
  intro S hS
  have hfin : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
  have heq : (fun a : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal S) => ∏ᶠ v, localFiniteCharacter F v
      (RestrictedProduct.inclusion _ _ hS a v)) =
      (fun a => ∏ v ∈ hfin.toFinset, localFiniteCharacter F v (a v)) := by
    funext a
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    change v ∈ hfin.toFinset
    rw [Set.Finite.mem_toFinset]
    by_contra h
    have ha := a.2
    have hav : a v ∈ v.adicCompletionIntegers F := (Filter.eventually_principal.mp ha) v (by simpa using h)
    exact hv (localFiniteCharacter_eq_one_of_mem_integers F v (a v) hav)
  change Continuous (fun a => ∏ᶠ v, localFiniteCharacter F v (RestrictedProduct.inclusion _ _ hS a v))
  rw [heq]
  apply continuous_finset_prod
  intro v hv
  exact (continuous_localFiniteCharacter F v).comp (RestrictedProduct.continuous_eval v)

end DedekindZetaZeroFree.RepresentationTheory.AdelicTraceCharacterHelpers

end
