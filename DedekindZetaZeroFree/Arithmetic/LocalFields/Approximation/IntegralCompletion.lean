module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

open scoped NumberField Classical Valued WithZero
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
variable {F : Type} [Field F] [NumberField F]

private theorem valuation_algebraMap (p : HeightOneSpectrum (𝓞 F)) (b : F) :
    Valued.v (algebraMap F (p.adicCompletion F) b) = p.valuation F b := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  exact p.valuedAdicCompletion_eq_valuation' b

theorem completion_integer_approximation (p : HeightOneSpectrum (𝓞 F))
    (z : p.adicCompletionIntegers F) (n : ℕ) :
    ∃ a : 𝓞 F, Valued.v (algebraMap F (p.adicCompletion F) (a : F) - z) ≤
      WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  let r : p.adicCompletion F := algebraMap F _ π ^ n
  have hr : Valued.v r = WithZero.exp (-(n : ℤ)) := by
    change Valued.v (algebraMap F (p.adicCompletion F) π ^ n) = _
    rw [map_pow, valuation_algebraMap, hπ]
    simp [← WithZero.exp_nsmul, nsmul_eq_mul]
  have hrz : r ≠ 0 := by
    intro h
    have h' := hr
    rw [h, map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm
  have hbound : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let U : Set (p.adicCompletion F) :=
    {y | (y - (z : p.adicCompletion F)) / r ∈
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).valuationSubring}
  have hU : IsOpen U :=
    (Valued.isOpen_valuationSubring (p.adicCompletion F)).preimage
      ((continuous_id.sub continuous_const).div_const r)
  obtain ⟨b, hb⟩ := (p.denseRange_algebraMap F).exists_mem_open hU
    ⟨z, by simp [U]⟩
  have hbz : Valued.v (algebraMap F (p.adicCompletion F) b - z) ≤ WithZero.exp (-(n : ℤ)) := by
    change Valued.v ((algebraMap F (p.adicCompletion F) b - z) / r) ≤ 1 at hb
    rw [map_div₀, hr] at hb
    exact (div_le_one₀ WithZero.exp_pos).mp hb
  have hbint : p.valuation F b ≤ 1 := by
    rw [← valuation_algebraMap p b]
    have he : algebraMap F (p.adicCompletion F) b =
        (algebraMap F (p.adicCompletion F) b - z) + z := by simp
    rw [he]
    exact (ValuationClass.map_add_le_max _ _ _).trans
      (max_le (hbz.trans hbound) z.property)
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hbint
    (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap F (p.adicCompletion F) (a : F) -
      algebraMap F (p.adicCompletion F) b) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← map_sub, valuation_algebraMap]
    exact ha.le
  have he : algebraMap F (p.adicCompletion F) (a : F) - z =
      (algebraMap F (p.adicCompletion F) (a : F) - algebraMap F (p.adicCompletion F) b) +
      (algebraMap F (p.adicCompletion F) b - z) := by ring
  rw [he]
  exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha' hbz)
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
