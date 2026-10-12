module

public import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.SmoothAnnularWeight

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable section

def initialTheta (F : Type*) [Field F] [NumberField F]
    (v : Ideal (𝓞 F) → ℂ) (X : ℝ) : ℂ :=
  ∑ I ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2 : ℝ) * X)).filter (fun I => I ≠ ⊥),
    (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / X) : ℂ) * v I

theorem initialTheta_summand_eq_zero_of_not_mem
    (F : Type*) [Field F] [NumberField F] (v : Ideal (𝓞 F) → ℂ)
    {X : ℝ} (hX : 0 < X) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hout : I ∉ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2 : ℝ) * X)).filter
      (fun J => J ≠ ⊥)) :
    (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / X) : ℂ) * v I = 0 := by
  have hnorm : (5 / 2 : ℝ) * X < (Ideal.absNorm I : ℝ) := by
    have : ¬ (Ideal.absNorm I : ℝ) ≤ (5 / 2 : ℝ) * X := by
      intro h
      exact hout (Finset.mem_filter.mpr ⟨DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr h, hI⟩)
    exact lt_of_not_ge this
  have hw : DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / X) = 0 :=
    DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_zero_of_ge
      ((le_div_iff₀ hX).mpr hnorm.le)
  simp [hw]

theorem initialTheta_eq_finsum (F : Type*) [Field F] [NumberField F]
    (v : Ideal (𝓞 F) → ℂ) {X : ℝ} (hX : 0 < X) :
    initialTheta F v X = ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I.val : ℝ) / X) : ℂ) * v I.val := by
  let s := (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2 : ℝ) * X)).subtype (fun I => I ≠ ⊥)
  rw [finsum_eq_finsetSum_of_support_subset (s := s)]
  · exact (Finset.sum_subtype_eq_sum_filter
      (fun I => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / X) : ℂ) * v I)).symm
  · intro I hI
    by_contra hout
    apply hI
    apply initialTheta_summand_eq_zero_of_not_mem F v hX I.val I.property
    intro hin
    apply hout
    simpa [s] using (Finset.mem_filter.mp hin).1

def initialGram (F : Type) [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (X : ℝ) (b1 b2 : Ideal (𝓞 F)) : ℂ :=
  initialTheta F (fun I => (Q.χ b1) I * (starRingEnd ℂ) ((Q.χ b2) I)) X

end

end DedekindZetaZeroFree.LargeSieve.Sieve
