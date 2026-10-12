module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.FiniteSphericalSpan
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.FactorizationThroughSurjections

@[expose] public section

noncomputable section
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.SharedSource
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}

def flatSourcePresentation (Q : AdmissibleFlatSources R) :
    (R.A.UnitQuotient →₀ ℂ) →ₗ[ℂ] flatScalarStage Q :=
  (Finsupp.linearCombination ℂ (fun v => (Q.flat v).val 0)).codRestrict _ (fun c => by
    unfold flatScalarStage
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ c)

theorem flatSourcePresentation_surjective (Q : AdmissibleFlatSources R) :
    Function.Surjective (flatSourcePresentation Q) := by
  intro x
  have hx : x.val ∈ (Finsupp.linearCombination ℂ (fun v => (Q.flat v).val 0)).range := by
    rw [Finsupp.range_linearCombination]
    exact x.property
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, Subtype.ext hc⟩

theorem flatSource_span_descent (Q : AdmissibleFlatSources R)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (b : R.A.UnitQuotient → V)
    (hrel : ∀ c : R.A.UnitQuotient →₀ ℂ,
      (∀ g, ∑ v ∈ c.support, c v * (Q.flat v).val 0 g = 0) →
        ∑ v ∈ c.support, c v • b v = 0) :
    ∃ L : flatScalarStage Q →ₗ[ℂ] V,
      ∀ v, L ⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ = b v := by
  let B := Finsupp.linearCombination ℂ b
  have hker : ∀ c, flatSourcePresentation Q c = 0 → B c = 0 := by
    intro c hc
    have hh : ∀ g, ∑ v ∈ c.support, c v * (Q.flat v).val 0 g = 0 := by
      intro g
      have h := congrArg (fun x : flatScalarStage Q => x.val g) hc
      simpa [flatSourcePresentation, Finsupp.linearCombination_apply, Finsupp.sum] using h
    simpa [B, Finsupp.linearCombination_apply, Finsupp.sum] using hrel c hh
  obtain ⟨L, hL⟩ := KPLiteralResidueDescent.factor_through_surjection
    (flatSourcePresentation Q) (flatSourcePresentation_surjective Q) B hker
  refine ⟨L, fun v => ?_⟩
  have h := hL (Finsupp.single v 1)
  have he : flatSourcePresentation Q (Finsupp.single v 1) =
      ⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ := by
    apply Subtype.ext
    simp [flatSourcePresentation, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [he] at h
  simpa [B, Finsupp.linearCombination_apply, Finsupp.sum] using h

end DedekindZetaZeroFree.SharedSource

end
