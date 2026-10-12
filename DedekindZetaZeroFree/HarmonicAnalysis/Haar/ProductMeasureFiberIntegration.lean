module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal
namespace DedekindZetaZeroFree.NormSheetsProductHaar
noncomputable section

theorem exists_unique_product_haar
    {X Y G : Type*} [Group X] [Group Y] [Group G]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace G]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [IsTopologicalGroup G]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [T2Space X] [T2Space Y] [T2Space G]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace G]
    [BorelSpace X] [BorelSpace Y] [BorelSpace G]
    (e : (X × Y) ≃ₜ* G) (μ : Measure X) [μ.IsHaarMeasure]
    (ρ : Measure G) [ρ.IsHaarMeasure] :
    ∃! ν : Measure Y, ν.IsHaarMeasure ∧ Measure.map e (μ.prod ν) = ρ := by
  classical
  let ν₀ : Measure Y := MeasureTheory.Measure.haar
  let ρ₀ : Measure (X × Y) := Measure.map e.symm ρ
  let c : ℝ≥0 := ρ₀.haarScalarFactor (μ.prod ν₀)
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure ρ₀ (μ.prod ν₀)).ne'
  letI : (c • ν₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hc
  have hscalar : ρ₀ = c • μ.prod ν₀ := Measure.isMulLeftInvariant_eq_smul ρ₀ (μ.prod ν₀)
  have hprod : μ.prod (c • ν₀) = ρ₀ := by
    rw [Measure.prod_smul_right, ← hscalar]
  have hmap : Measure.map e (μ.prod (c • ν₀)) = ρ := by
    rw [hprod]
    exact e.toHomeomorph.toMeasurableEquiv.map_map_symm
  refine ⟨c • ν₀, ⟨inferInstance, hmap⟩, ?_⟩
  rintro ν ⟨hν, hνmap⟩
  letI := hν
  have heq : μ.prod ν = μ.prod (c • ν₀) :=
    e.toHomeomorph.toMeasurableEquiv.map_measurableEquiv_injective (hνmap.trans hmap.symm)
  let K : TopologicalSpace.PositiveCompacts X := Classical.arbitrary _
  have hK0 : μ (K : Set X) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hKtop : μ (K : Set X) ≠ ∞ := K.isCompact.measure_lt_top.ne
  ext s hs
  have hp := congrArg (fun m : Measure (X × Y) => m ((K : Set X) ×ˢ s)) heq
  simp only [Measure.prod_prod] at hp
  exact (ENNReal.mul_right_inj hK0 hKtop).mp hp

theorem integral_fibers
    {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace G]
    (Fiber : X → Type*) [∀ x, MeasurableSpace (Fiber x)]
    (e : (X × Y) ≃ᵐ G) (t : ∀ x, Y ≃ᵐ Fiber x)
    (inclusion : ∀ x, Fiber x → G)
    (hcompat : ∀ x y, inclusion x (t x y) = e (x, y))
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (ρ : Measure G) (hρ : Measure.map e (μ.prod ν) = ρ)
    (g : G → ℂ) (hg : Integrable g ρ) :
    (∀ᵐ x ∂μ, Integrable (fun y : Fiber x => g (inclusion x y))
      (Measure.map (t x) ν)) ∧
    Integrable (fun x => ∫ y : Fiber x, g (inclusion x y) ∂Measure.map (t x) ν) μ ∧
    (∫ y, g y ∂ρ) = ∫ x, (∫ y : Fiber x, g (inclusion x y) ∂Measure.map (t x) ν) ∂μ := by
  have hg' : Integrable (fun p : X × Y => g (e p)) (μ.prod ν) := by
    apply (integrable_map_equiv e g).mp
    simpa [hρ] using hg
  have hfiber (x : X) :
      (∫ y : Fiber x, g (inclusion x y) ∂Measure.map (t x) ν) =
        ∫ y, g (e (x, y)) ∂ν := by
    rw [integral_map_equiv]
    simp only [hcompat]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hg'.prod_right_ae] with x hx
    apply (integrable_map_equiv (t x) _).mpr
    simpa only [Function.comp_def, hcompat] using hx
  · simp_rw [hfiber]
    exact hg'.integral_prod_left
  · rw [← hρ, integral_map_equiv, integral_prod _ hg']
    simp_rw [hfiber]

end
end DedekindZetaZeroFree.NormSheetsProductHaar
