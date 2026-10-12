module

public import DedekindZetaZeroFree.CharacterSums.Gauss.Sextic.LocalTable

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.CorrectionFactors.LocalAlgebra
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F] {A : SArithmeticData F} {σ : F →+* ℂ}

theorem chi_norm (p : ExteriorPrime A)
    (x : A.R ⧸ A.extendIdeal (primeIdeal p)) (hx : IsUnit x) :
    ‖chi (σ := σ) p x‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one
    (CanonicalLocalGaussTable.chi_unit_sixth p x hx) (by decide)

theorem generator_residue_unit (J : A.Exterior) (v : A.R)
    (hv : A.Generates J v) (p : ExteriorPrime A) (hnot : ¬p.val.asIdeal ∣ J.val) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) v) := by
  letI : Field (A.R ⧸ A.extendIdeal (primeIdeal p)) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hle : A.extendIdeal J ≤ A.extendIdeal (primeIdeal p) := by
    rw [← hv.2]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  have hle' : J.val ≤ p.val.asIdeal := by
    have hh := Ideal.comap_mono (f := algebraMap (𝓞 F) A.R) hle
    change J.val ≤ (primeIdeal p).val
    simpa only [← Ideal.under_def, SArithmeticData.extendIdeal,
      SIntegerLocalization.under_map_exterior A.Sf J.val J.property.2,
      SIntegerLocalization.under_map_exterior A.Sf (primeIdeal p).val (primeIdeal p).property.2]
      using hh
  exact hnot (Ideal.dvd_iff_le.mpr hle')

end DedekindZetaZeroFree.CorrectionFactors.LocalAlgebra

end
