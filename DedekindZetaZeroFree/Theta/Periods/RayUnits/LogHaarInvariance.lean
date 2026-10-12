module

public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain

@[expose] public section

/-
Adapted from
LeanPool/lean-pool, commit `68aa6ee63d20ad76bcc15f595adfc72949991f06`,
`LeanPool/Odlyzko/CompletedZeta/UnitSlabTranslation.lean`.
Copyright (c) 2026 The FLT Project; released under the Apache 2.0 license.
-/

open NumberField MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke

theorem rayUnitPeriodicLogHaarIntegral_translation
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : RayCoset.logHyperplane F → ℂ) (hf : Continuous f)
    (hperiodic : ∀ (γ : RayCoset.rayUnitLogLattice F m)
      (h : RayCoset.logHyperplane F), f (h + (γ : RayCoset.logHyperplane F)) = f h)
    (v : RayCoset.logHyperplane F) :
    (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
      f (h + v) ∂Theta.normalizedLogHaar F) =
      ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        f h ∂Theta.normalizedLogHaar F := by
  classical
  letI := RayCoset.isZLattice_rayUnitLogLattice F m hm
  let L := RayCoset.rayUnitLogLattice F m
  let D := RayCoset.rayUnitHalfOpenDomain F m hm
  let μ := Theta.normalizedLogHaar F
  have hD : IsAddFundamentalDomain L D μ :=
    RayCoset.isAddFundamentalDomain_rayUnitHalfOpenDomain F m hm
  letI : VAddInvariantMeasure L (RayCoset.logHyperplane F) μ := ⟨fun g s hs =>
    (measurePreserving_add_left μ (g : RayCoset.logHyperplane F)).measure_preimage
      hs.nullMeasurableSet⟩
  have hp : ∀ (g : L) h, f (g +ᵥ h) = f h := by
    intro g h
    change f ((g : RayCoset.logHyperplane F) + h) = f h
    rw [add_comm]
    exact hperiodic g h
  let e : RayCoset.logHyperplane F ≃ᵐ RayCoset.logHyperplane F :=
    MeasurableEquiv.addRight v
  have he : MeasurePreserving e μ μ :=
    ⟨e.measurable, by simpa [e] using map_add_right_eq_self μ v⟩
  have hT : IsAddFundamentalDomain L (e '' D) μ := by
    apply hD.image_of_equiv e.toEquiv ?_ (Equiv.refl L) ?_
    · exact (measurePreserving_add_right μ (-v)).quasiMeasurePreserving
    · intro g h
      change ((g : RayCoset.logHyperplane F) + h) + v =
        (g : RayCoset.logHyperplane F) + (h + v)
      exact add_assoc _ _ _
  calc
    _ = ∫ h in e '' D, f h ∂μ :=
      (he.setIntegral_image_emb e.measurableEmbedding f D).symm
    _ = ∫ h in D, f h ∂μ := hT.setIntegral_eq hD hp

end DedekindZetaZeroFree.Hecke
