module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-
The translation change-of-variables and fundamental-domain comparison pattern is adapted
from LeanPool/lean-pool, commit `68aa6ee63d20ad76bcc15f595adfc72949991f06`,
`LeanPool/Odlyzko/CompletedZeta/UnitSlabTranslation.lean`.
Copyright (c) 2026 The FLT Project; released under the Apache 2.0 license.
-/

open MeasureTheory

namespace DedekindZetaZeroFree.Hecke

theorem periodicCubeIntegral_translation {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f)
    (hperiodic : ∀ (z : ι → ℤ) (u : ι → ℝ),
      f (u + fun i => (z i : ℝ)) = f u) :
    ∀ d : ι → ℝ,
      (∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f (u + d)) =
        ∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f u := by
  intro d
  classical
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  let Q := Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hQ : IsAddFundamentalDomain L Q volume := by
    simpa [L, Q, ZSpan.fundamentalDomain_pi_basisFun] using
      ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume := ⟨fun g s hs =>
    (measurePreserving_add_left volume (g : ι → ℝ)).measure_preimage hs.nullMeasurableSet⟩
  have hf : ∀ (g : L) u, f (g +ᵥ u) = f u := by
    intro g u
    have hg := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ g).mp g.prop
    choose z hz using hg
    have heq : (g : ι → ℝ) = fun i => (z i : ℝ) := by
      ext i
      simpa using (hz i).symm
    change f ((g : ι → ℝ) + u) = f u
    rw [heq, add_comm]
    exact hperiodic z u
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.addRight d
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, by simpa [e] using map_add_right_eq_self volume d⟩
  have hT : IsAddFundamentalDomain L (e '' Q) volume := by
    apply hQ.image_of_equiv e.toEquiv ?_ (Equiv.refl L) ?_
    · exact (measurePreserving_add_right volume (-d)).quasiMeasurePreserving
    · intro g x
      change ((g : ι → ℝ) + x) + d = (g : ι → ℝ) + (x + d)
      exact add_assoc _ _ _
  calc
    _ = ∫ u in e '' Q, f u := (he.setIntegral_image_emb e.measurableEmbedding f Q).symm
    _ = ∫ u in Q, f u := hT.setIntegral_eq hQ hf

theorem periodicCubeIntegral_negation {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f)
    (hperiodic : ∀ (z : ι → ℤ) (u : ι → ℝ),
      f (u + fun i => (z i : ℝ)) = f u) :
    (∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f (-u)) =
      ∫ u in Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1), f u := by
  classical
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  let Q := Set.univ.pi (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hQ : IsAddFundamentalDomain L Q volume := by
    simpa [L, Q, ZSpan.fundamentalDomain_pi_basisFun] using
      ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume := ⟨fun g s hs =>
    (measurePreserving_add_left volume (g : ι → ℝ)).measure_preimage hs.nullMeasurableSet⟩
  have hf : ∀ (g : L) u, f (g +ᵥ u) = f u := by
    intro g u
    have hg := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ g).mp g.prop
    choose z hz using hg
    have heq : (g : ι → ℝ) = fun i => (z i : ℝ) := by
      ext i
      simpa using (hz i).symm
    change f ((g : ι → ℝ) + u) = f u
    rw [heq, add_comm]
    exact hperiodic z u
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.neg (ι → ℝ)
  have he : MeasurePreserving e volume volume := Measure.measurePreserving_neg volume
  have hT : IsAddFundamentalDomain L (e '' Q) volume := by
    apply hQ.image_of_equiv e.toEquiv ?_ (Equiv.neg L) ?_
    · exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    · intro g x
      change -(-(g : ι → ℝ) + x) = (g : ι → ℝ) + -x
      simp [add_comm]
  calc
    _ = ∫ u in e '' Q, f u := (he.setIntegral_image_emb e.measurableEmbedding f Q).symm
    _ = ∫ u in Q, f u := hT.setIntegral_eq hQ hf

end DedekindZetaZeroFree.Hecke
