module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.SphericalTruncations

@[expose] public section

namespace DedekindZetaZeroFree.KPExteriorActualJacquetShells

open MeasureTheory
noncomputable section

theorem linearMap_of_eventual_values
    {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : ℕ → U → V)
    (hadd : ∀ R f g, T R (f + g) = T R f + T R g)
    (hsmul : ∀ R (c : ℂ) f, T R (c • f) = c • T R f)
    (hstable : ∀ f, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → T R f = T R₀ f) :
    ∃! J : U →ₗ[ℂ] V, ∀ f, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → T R f = J f := by
  classical
  let bound : U → ℕ := fun f => (hstable f).choose
  let value : U → V := fun f => T (bound f) f
  have hvalue : ∀ f R, bound f ≤ R → T R f = value f := by
    intro f R hR
    exact (hstable f).choose_spec R hR
  let J : U →ₗ[ℂ] V :=
    { toFun := value
      map_add' := by
        intro f g
        let R := max (bound (f + g)) (max (bound f) (bound g))
        rw [← hvalue (f + g) R (by dsimp [R]; omega), hadd,
          hvalue f R (by dsimp [R]; omega), hvalue g R (by dsimp [R]; omega)]
      map_smul' := by
        intro c f
        let R := max (bound (c • f)) (bound f)
        change value (c • f) = c • value f
        rw [← hvalue (c • f) R (by dsimp [R]; omega), hsmul,
          hvalue f R (by dsimp [R]; omega)] }
  refine ⟨J, ?_, ?_⟩
  · intro f
    exact ⟨bound f, hvalue f⟩
  · intro J' hJ'
    apply LinearMap.ext
    intro f
    obtain ⟨R₀, hR₀⟩ := hJ' f
    exact (hR₀ (max R₀ (bound f)) (le_max_left _ _)).symm.trans
      (hvalue f (max R₀ (bound f)) (le_max_right _ _))

theorem linearMap_of_eventual_integrals
    {X U V : Type*} [MeasurableSpace X] [AddCommGroup U] [Module ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (μ : Measure X) (B : ℕ → Set X) (g : U →ₗ[ℂ] (X → V))
    (hint : ∀ R f, IntegrableOn (g f) (B R) μ)
    (hstable : ∀ f, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      (∫ x in B R, g f x ∂μ) = ∫ x in B R₀, g f x ∂μ) :
    ∃! J : U →ₗ[ℂ] V, ∀ f, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      (∫ x in B R, g f x ∂μ) = J f := by
  apply linearMap_of_eventual_values (fun R f => ∫ x in B R, g f x ∂μ)
  · intro R f h
    simp only [map_add, Pi.add_apply]
    exact integral_add (hint R f) (hint R h)
  · intro R c f
    simp only [map_smul, Pi.smul_apply, integral_smul]
  · exact hstable

end
end DedekindZetaZeroFree.KPExteriorActualJacquetShells
