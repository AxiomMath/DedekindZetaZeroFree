module

public import DedekindZetaZeroFree.MeasureTheory.FiniteProductDensity.Fubini

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DedekindZetaZeroFree.FiniteProductDensity

theorem Measure.pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.pi Set.countable_univ fun i _ => hs i),
    Measure.restrict_pi_pi,
    lintegral_fintype_prod_eq_prod'
      (fun i => (hf i).mono_measure (Measure.restrict_le_self (μ := μ i) (s := s i)))]
  exact Finset.prod_congr rfl fun i _ => (withDensity_apply (f i) (hs i)).symm

theorem Measure.pi_withDensity_ofReal {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {g : ∀ i, α i → ℝ} (hg : ∀ i, AEMeasurable (g i) (μ i)) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (g i x))) =
      (Measure.pi μ).withDensity (fun x => ∏ i, ENNReal.ofReal (g i (x i))) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity fun x => ENNReal.ofReal (g i x)) := fun i =>
    SigmaFinite.withDensity_ofReal (g i)
  exact Measure.pi_withDensity μ fun i => (hg i).ennreal_ofReal

end DedekindZetaZeroFree.FiniteProductDensity

end
