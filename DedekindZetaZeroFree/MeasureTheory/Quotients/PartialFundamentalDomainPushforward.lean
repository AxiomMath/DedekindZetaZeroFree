module

public import Mathlib.MeasureTheory.Group.FundamentalDomain

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open MeasureTheory

namespace DedekindZetaZeroFree.KPActualComponentHaarSources.ProductDisintegration

private theorem partial_domain_pushforward_compare
    {Γ Y Z : Type*} [Group Γ] [MulAction Γ Y]
    [MeasurableSpace Y] [MeasurableSpace Z] [Countable Γ]
    [MeasurableConstSMul Γ Y] (μ : Measure Y) [SMulInvariantMeasure Γ Y μ]
    (S D E : Set Y) (hS : MeasurableSet S)
    (hSinv : ∀ γ : Γ, (fun y => γ • y) ⁻¹' S = S)
    (hD : IsFundamentalDomain Γ D (μ.restrict S))
    (hE : IsFundamentalDomain Γ E (μ.restrict S))
    (q : Y → Z) (hq : Measurable q)
    (hqi : ∀ (γ : Γ) y, q (γ • y) = q y) :
    Measure.map q ((μ.restrict S).restrict D) =
      Measure.map q ((μ.restrict S).restrict E) := by
  letI : SMulInvariantMeasure Γ Y (μ.restrict S) := ⟨by
    intro γ T hT
    rw [Measure.restrict_apply (hT.preimage (measurable_const_smul γ)),
      Measure.restrict_apply hT]
    have ht : ((fun y => γ • y) ⁻¹' T) ∩ S =
        (fun y => γ • y) ⁻¹' (T ∩ S) := by
      rw [Set.preimage_inter, hSinv]
    rw [ht, SMulInvariantMeasure.measure_preimage_smul γ (hT.inter hS)]⟩
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply hq hT, Measure.map_apply hq hT,
    Measure.restrict_apply (hT.preimage hq), Measure.restrict_apply (hT.preimage hq)]
  exact hD.measure_set_eq hE (hT.preimage hq) (fun γ => by
    ext y
    simp only [Set.mem_preimage, hqi])

theorem quotient_restrict_of_partial_domain
    {Γ Y Z : Type*} [Group Γ] [MulAction Γ Y]
    [MeasurableSpace Y] [MeasurableSpace Z] [Countable Γ]
    [MeasurableConstSMul Γ Y]
    (μ : Measure Y) [SMulInvariantMeasure Γ Y μ]
    (E : Set Y) (hEm : MeasurableSet E) (hE : IsFundamentalDomain Γ E μ)
    (q : Y → Z) (hq : Measurable q) (hqi : ∀ (γ : Γ) y, q (γ • y) = q y)
    (T : Set Z) (hT : MeasurableSet T)
    (D : Set Y) (hDm : MeasurableSet D) (hDsub : D ⊆ q ⁻¹' T)
    (hD : IsFundamentalDomain Γ D (μ.restrict (q ⁻¹' T))) :
    (Measure.map q (μ.restrict E)).restrict T = Measure.map q (μ.restrict D) := by
  have hS : MeasurableSet (q ⁻¹' T) := hT.preimage hq
  have hSinv : ∀ γ : Γ, (fun y => γ • y) ⁻¹' (q ⁻¹' T) = q ⁻¹' T := by
    intro γ
    ext y
    simp only [Set.mem_preimage]
    rw [hqi γ y]
  have hE' : IsFundamentalDomain Γ E (μ.restrict (q ⁻¹' T)) :=
    hE.mono Measure.absolutelyContinuous_restrict
  have hcmp := partial_domain_pushforward_compare μ (q ⁻¹' T) D E hS hSinv hD hE' q hq hqi
  rw [Measure.restrict_restrict_of_subset hDsub] at hcmp
  rw [Measure.restrict_restrict hEm] at hcmp
  have hmap : (Measure.map q (μ.restrict E)).restrict T =
      Measure.map q (μ.restrict (E ∩ q ⁻¹' T)) := by
    apply Measure.ext
    intro A hA
    rw [Measure.restrict_apply hA, Measure.map_apply hq (hA.inter hT),
      Measure.restrict_apply ((hA.inter hT).preimage hq), Set.preimage_inter,
      Measure.map_apply hq hA, Measure.restrict_apply (hA.preimage hq)]
    congr 1
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hmap]
  exact hcmp.symm

end DedekindZetaZeroFree.KPActualComponentHaarSources.ProductDisintegration

end
