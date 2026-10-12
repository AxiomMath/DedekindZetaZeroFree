module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

namespace DedekindZetaZeroFree
open IsDedekindDomain

theorem exists_ringOfIntegers_adicCompletion_approximation
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F)
    (γ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ a : NumberField.RingOfIntegers F,
      Valued.v (algebraMap (NumberField.RingOfIntegers F) (v.adicCompletion F) a - x) <
        (γ : WithZero (Multiplicative ℤ)) := by
  let δ : WithZero (Multiplicative ℤ) := min (γ : WithZero (Multiplicative ℤ)) 1
  have hδ : δ ≠ 0 := ne_of_gt (lt_min (Units.zero_lt γ) zero_lt_one)
  obtain ⟨t, ht⟩ := v.valuedAdicCompletion_surjective F δ
  let ε := Units.mk0 (Valued.v.restrict t) (by
    intro hz
    exact hδ (ht ▸ (Valued.v.restrict_eq_zero_iff.mp hz)))
  have hball : {y : v.adicCompletion F | Valued.v (y - x) < δ} ∈ nhds x := by
    apply Valued.mem_nhds.mpr
    refine ⟨ε, ?_⟩
    intro y hy
    change Valued.v.restrict (y - x) < Valued.v.restrict t at hy
    simpa [ht] using Valued.v.restrict_lt_iff.mp hy
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap F).mem_nhds hball
  have hy1 : Valued.v (algebraMap F (v.adicCompletion F) y - x) < 1 :=
    lt_of_lt_of_le hy (min_le_right _ _)
  have hyγ : Valued.v (algebraMap F (v.adicCompletion F) y - x) < γ :=
    lt_of_lt_of_le hy (min_le_left _ _)
  have hyint : v.valuation F y ≤ 1 := by
    rw [← v.valuedAdicCompletion_eq_valuation' y]
    change Valued.v (algebraMap F (v.adicCompletion F) y) ≤ 1
    have h := Valued.v.map_add_le hy1.le
      ((v.mem_adicCompletionIntegers _ F).mp hx)
    simpa only [sub_add_cancel] using h
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hyint γ
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap (NumberField.RingOfIntegers F)
      (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) y) < γ := by
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers F) F
      (v.adicCompletion F), ← map_sub]
    exact (v.valuedAdicCompletion_eq_valuation' _).trans_lt ha
  have h := Valued.v.map_add_lt ha' hyγ
  simpa only [sub_add_sub_cancel] using h

theorem denseRange_ringOfIntegers_adicCompletionIntegers
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    DenseRange (algebraMap (NumberField.RingOfIntegers F)
      (v.adicCompletionIntegers F)) := by
  intro x
  rw [mem_closure_iff_nhds']
  intro s hs
  obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ x s).mp hs
  obtain ⟨ε, hε⟩ := Valued.mem_nhds.mp hu
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom ε
  obtain ⟨a, ha⟩ := exists_ringOfIntegers_adicCompletion_approximation F v x x.property γ
  refine ⟨⟨algebraMap (NumberField.RingOfIntegers F) (v.adicCompletionIntegers F) a,
    ⟨a, rfl⟩⟩, hus ?_⟩
  apply hε
  apply Valued.v.restrict_lt_iff_lt_embedding.mpr
  change Valued.v
    ((algebraMap (NumberField.RingOfIntegers F) (v.adicCompletionIntegers F) a :
      v.adicCompletion F) - x) < _
  exact ha
end DedekindZetaZeroFree
