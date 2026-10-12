module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem entire_division_at_zero (q : ℂ → ℂ) (hq : Differentiable ℂ q) (hq0 : q 0 = 0) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s : ℂ, q s = s * u s := by
  refine ⟨dslope q 0, ?_, ?_⟩
  · rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).mpr
      hq.differentiableOn
  · intro s
    have h := sub_smul_dslope_of_zero hq0 s
    simpa using h.symm

end DedekindZetaZeroFree.AbelianQuotient
