module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

open scoped NumberField Classical Valued
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility

theorem valuationInteger_mem_span_iff {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (r x : v.valuationSubring) (hr : (r : K) ≠ 0) :
    x ∈ Ideal.span {r} ↔ v (x : K) ≤ v (r : K) := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    have he := congrArg (fun z : v.valuationSubring => (z : K)) hy
    change (x : K) = (r : K) * (y : K) at he
    rw [he, map_mul]
    exact (mul_le_mul_of_nonneg_left y.property zero_le).trans (by simp)
  · intro hx
    let y : v.valuationSubring := ⟨(x : K) / (r : K), by
      change v ((x : K) / (r : K)) ≤ 1
      rw [map_div₀]
      exact (div_le_one₀ ((v.pos_iff).mpr hr)).mpr hx⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change (x : K) = (r : K) * ((x : K) / (r : K))
    field_simp
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
