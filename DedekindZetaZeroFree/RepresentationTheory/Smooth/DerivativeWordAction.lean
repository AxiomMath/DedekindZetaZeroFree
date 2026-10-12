module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.QuotientDescentAndHolomorphicJets

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualSmoothWordAction
open KPSmoothActualFlowData
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualWordSpatial renaming finitePart_eq → finitePart_eq

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem word_append (v w : List (B F)) (f : X F ζ hζ → ℂ) :
    wordDerivative F ζ hζ (v ++ w) f =
      wordDerivative F ζ hζ v (wordDerivative F ζ hζ w f) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    simp only [List.cons_append, wordDerivative] at *
    rw [ih]

 theorem word_right_covariant (f : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (u : G F ζ hζ) (c : ℂ)
    (hu : ∀ a : GInfinity F, Commute (archimedeanInsertion F ζ hζ a) u)
    (hcov : ∀ g : G F ζ hζ, f (Quotient.mk _ (g * u)) = c * f (Quotient.mk _ g))
    (w : List (B F)) :
    ∀ g : G F ζ hζ, wordDerivative F ζ hζ w f (Quotient.mk _ (g * u)) =
      c * wordDerivative F ζ hζ w f (Quotient.mk _ g) := by
  induction w with
  | nil => exact hcov
  | cons b w ih =>
    intro g
    change deriv (fun t : ℝ => wordDerivative F ζ hζ w f
      (Quotient.mk _ ((g * u) * archimedeanInsertion F ζ hζ (flow F b t)))) 0 = _
    have he : (fun t : ℝ => wordDerivative F ζ hζ w f
        (Quotient.mk _ ((g * u) * archimedeanInsertion F ζ hζ (flow F b t)))) =
        (fun t : ℝ => c * wordDerivative F ζ hζ w f
        (Quotient.mk _ (g * archimedeanInsertion F ζ hζ (flow F b t)))) := by
      funext t
      rw [mul_assoc, (hu (flow F b t)).eq.symm, ← mul_assoc]
      exact ih _
    rw [he]
    exact ((ActualWordLinearity.word_hasDerivAt_flow F ζ hζ f hf w b
      (Quotient.mk _ g)).const_smul c).deriv

theorem word_mem (U : Level F ζ hζ) (w : List (B F)) (f : smoothSpace F ζ hζ U) :
    wordDerivative F ζ hζ w f.val ∈ smoothSpace F ζ hζ U := by
  refine ⟨⟨ActualWordSpatial.word_continuous F ζ hζ U f.val f.property.1
    f.property.2.1 w, fun x => ActualWordLinearity.word_orbit_contDiff
      F ζ hζ f.val f.property.1 w x⟩, ?_, ?_⟩
  · intro g u
    apply ActualWordSpatial.word_right_invariant F ζ hζ f.val u.val _ _ w g
    · intro a
      obtain ⟨v, hv, he⟩ := u.property
      have hfin : v.val ∈ KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ := by
        rw [← finitePart_eq F ζ hζ]
        exact v.property
      rw [← he]
      exact RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a ⟨v.val, hfin⟩
    · exact fun g => f.property.2.1 g u
  · intro g ε
    apply word_right_covariant F ζ hζ f.val f.property.1 _ _ _
      (fun g => f.property.2.2 g ε) w g
    intro a
    exact Subgroup.mem_center_iff.mp
      ((KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ)
        (MonoidHom.mem_range.mpr ⟨ε, rfl⟩)) _

def wordAction (U : Level F ζ hζ) (w : List (B F)) :
    smoothSpace F ζ hζ U →ₗ[ℂ] smoothSpace F ζ hζ U :=
  (ActualWordLinearity.wordLinearMap F ζ hζ (smoothSpace F ζ hζ U)
    (fun f => f.property.1) w).codRestrict (smoothSpace F ζ hζ U) (word_mem F ζ hζ U w)

@[simp] theorem wordAction_value (U : Level F ζ hζ) (w : List (B F))
    (f : smoothSpace F ζ hζ U) (x : X F ζ hζ) :
    (wordAction F ζ hζ U w f).val x = wordDerivative F ζ hζ w f.val x := rfl

end DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualSmoothWordAction

end
