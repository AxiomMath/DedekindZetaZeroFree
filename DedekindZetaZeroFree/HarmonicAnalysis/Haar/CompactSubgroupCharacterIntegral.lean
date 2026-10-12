module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

noncomputable section

open scoped Classical

namespace DedekindZetaZeroFree

open MeasureTheory

theorem compactSubgroup_character_integral
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure]
    (U : AddSubgroup G) (hU : IsCompact (U : Set G))
    (χ : AddChar G Circle) (hχ : Continuous χ) :
    IntegrableOn (fun x : G => (χ x : ℂ)) (U : Set G) μ ∧
      (∫ x in (U : Set G), (χ x : ℂ) ∂μ) =
        if (∀ u ∈ U, χ u = 1) then ((μ (U : Set G)).toReal : ℂ) else 0 := by
  have hf : Continuous (fun x : G => (χ x : ℂ)) := continuous_subtype_val.comp hχ
  refine ⟨hf.continuousOn.integrableOn_compact hU, ?_⟩
  by_cases ht : ∀ u ∈ U, χ u = 1
  · rw [if_pos ht]
    calc
      (∫ x in (U : Set G), (χ x : ℂ) ∂μ) = ∫ _ in (U : Set G), (1 : ℂ) ∂μ :=
        setIntegral_congr_fun hU.measurableSet (fun x hx => by simp [ht x hx])
      _ = ((μ (U : Set G)).toReal : ℂ) := by
        simp [setIntegral_const, Measure.real, Complex.real_smul]
  · rw [if_neg ht]
    obtain ⟨u, hu, hne⟩ : ∃ u ∈ U, χ u ≠ 1 := by simpa using ht
    have hmem (x : G) : u + x ∈ U ↔ x ∈ U :=
      ⟨fun hx => by simpa using U.sub_mem hx hu, fun hx => U.add_mem hu hx⟩
    have htranslate :
        (fun x : G => (U : Set G).indicator (fun y => (χ y : ℂ)) (u + x)) =
          (fun x : G => (χ u : ℂ) * (U : Set G).indicator (fun y => (χ y : ℂ)) x) := by
      funext x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mpr hx),
          AddChar.map_add_eq_mul]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).mp hx)]
    have heq : (χ u : ℂ) * (∫ x in (U : Set G), (χ x : ℂ) ∂μ) =
        ∫ x in (U : Set G), (χ x : ℂ) ∂μ := by
      have h := integral_add_left_eq_self (μ := μ)
        ((U : Set G).indicator (fun y => (χ y : ℂ))) u
      rw [htranslate, integral_const_mul, integral_indicator hU.measurableSet] at h
      exact h
    have hc : (χ u : ℂ) ≠ 1 := fun h => hne (Circle.coe_eq_one.mp h)
    by_contra hI
    exact hc ((mul_eq_right₀ hI).mp heq)

end DedekindZetaZeroFree

end
