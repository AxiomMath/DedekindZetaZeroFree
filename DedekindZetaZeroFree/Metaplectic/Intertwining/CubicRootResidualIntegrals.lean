module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalKernelEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RootResidualGeometry

open ValuativeRel MeasureTheory
open scoped Classical

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem unit_mem_integer_iff_exponent_nonneg (u : Kˣ) :
    (u : K) ∈ (valuation K).integer ↔ 0 ≤ KPCubicExpansion.valuationExponent K u := by
  change valuation K (u : K) ≤ 1 ↔ _
  rw [← (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).map_le_map_iff']
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (u : K)) ≤
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K 1 ↔ _
  rw [map_one]
  have hn : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (u : K)) ≠ 0 := by
    simpa using (Units.ne_zero u)
  rw [← WithZero.exp_log hn, WithZero.exp_le_one_iff]
  change WithZero.log _ ≤ 0 ↔ 0 ≤ -WithZero.log _
  omega

theorem exponent_dvd_of_unitCubeClasses
    (u : Kˣ)
    (hu : QuotientGroup.mk' (CubicCharacters.cubes Kˣ) u ∈
      KPTameValuationCoordinates.unitCubeClasses K) :
    3 ∣ KPCubicExpansion.valuationExponent K u := by
  obtain ⟨y, hy, he⟩ := hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hy
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hdiff : (KPRamifiedBeta.unitsInclusion K z * t ^ 3) / u ∈
      CubicCharacters.cubes Kˣ := (QuotientGroup.eq_iff_div_mem).mp he
  obtain ⟨r, hr⟩ := hdiff
  change r ^ 3 = _ at hr
  have hh := congrArg (KPCubicExpansion.valuationExponent K) hr
  have hu0 : KPCubicExpansion.valuationExponent K (KPRamifiedBeta.unitsInclusion K z) = 0 :=
    KPCubicExpansion.valuationExponent_unit z
  simp only [div_eq_mul_inv, KPCubicExpansion.valuationExponent_mul, hu0, zero_add] at hh
  rw [← zpow_natCast r 3, KPCubicExpansion.valuationExponent_zpow,
    ← zpow_natCast t 3, KPCubicExpansion.valuationExponent_zpow,
    ← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow] at hh
  refine ⟨KPCubicExpansion.valuationExponent K t - KPCubicExpansion.valuationExponent K r, ?_⟩
  omega

theorem cubic_cutoffs_eq (n : ℤ) (hn : 3 ∣ n) (i : Fin 3) :
    n ≤ (i.val : ℤ) ↔ n ≤ 0 := by
  obtain ⟨k, rfl⟩ := hn
  have hi := i.isLt
  omega

theorem diagonal_root_residual_mem_integer_iff
    (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ))
    (u : Kˣ) (hu : 3 ∣ KPCubicExpansion.valuationExponent K u) (i : Fin 3) :
    ((π ^ i.val : Kˣ) : K) / (u : K) ∈ (valuation K).integer ↔
      (u : K)⁻¹ ∈ (valuation K).integer := by
  have hp : KPCubicExpansion.valuationExponent K π = 1 := by
    simp [KPCubicExpansion.valuationExponent, hπ]
  have hh (j : ℕ) : KPCubicExpansion.valuationExponent K (π ^ j * u⁻¹) =
      (j : ℤ) - KPCubicExpansion.valuationExponent K u := by
    rw [KPCubicExpansion.valuationExponent_mul,
      ← zpow_natCast π j, KPCubicExpansion.valuationExponent_zpow, hp,
      ← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow]
    ring
  have hz : KPCubicExpansion.valuationExponent K u⁻¹ =
      -KPCubicExpansion.valuationExponent K u := by
    rw [← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow]
    ring
  simp only [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul]
  change ((π ^ i.val * u⁻¹ : Kˣ) : K) ∈ (valuation K).integer ↔
    ((u⁻¹ : Kˣ) : K) ∈ (valuation K).integer
  rw [unit_mem_integer_iff_exponent_nonneg, unit_mem_integer_iff_exponent_nonneg,
    hh, hz]
  have hc := cubic_cutoffs_eq (KPCubicExpansion.valuationExponent K u) hu i
  omega

section Arithmetic
open scoped NumberField
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
  (hP : KPTameJacquetTestDuality.IsTamePolarization F ζ hζ q S P)

include hP

theorem tame_borel_coordinate_exponent_dvd
    (b : KPTameJacquetTestDuality.BL F ζ hζ q S P) :
    3 ∣ KPCubicExpansion.valuationExponent (LocalField F q)
      (S.borel.coordinate (KPTameJacquetTestDuality.retractL F ζ hζ q S P b)) := by
  apply exponent_dvd_of_unitCubeClasses
  change QuotientGroup.mk
    (S.borel.coordinate (KPTameJacquetTestDuality.retractL F ζ hζ q S P b)) ∈ _
  rw [← S.cube_class, ← hP]
  exact ⟨S.heisenberg.π (KPTameJacquetTestDuality.retractL F ζ hζ q S P b),
    (KPTameJacquetTestDuality.retractL F ζ hζ q S P b).property, rfl⟩

theorem relative_diagonal_exponent_dvd
    (b : KPTameJacquetTestDuality.BL F ζ hζ q S P) (u : (LocalField F q)ˣ)
    (hb : S.borel.coordinate (KPTameJacquetTestDuality.retractL F ζ hζ q S P b) =
      u⁻¹ ^ (2 : ℕ)) :
    3 ∣ KPCubicExpansion.valuationExponent (LocalField F q) u := by
  have hd := tame_borel_coordinate_exponent_dvd F ζ hζ q S P hP b
  rw [hb, ← zpow_natCast u⁻¹ 2,
    KPCubicExpansion.valuationExponent_zpow,
    ← zpow_neg_one u, KPCubicExpansion.valuationExponent_zpow] at hd
  obtain ⟨n, hn⟩ := hd
  have hv : KPCubicExpansion.valuationExponent (LocalField F q) u % 3 = 0 := by
    omega
  exact (Int.dvd_iff_emod_eq_zero).mpr hv
end Arithmetic

section Haar
variable [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

theorem integral_integer_translate_of_support
    (φ : K → ℂ) (hφ : Function.support φ ⊆ (valuation K).integer)
    (a : K) (ha : a ∈ (valuation K).integer) :
    (∫ x in (valuation K).integer, φ (x + a) ∂μ) =
      ∫ x in (valuation K).integer, φ x ∂μ := by
  have ho : MeasurableSet ((valuation K).integer : Set K) :=
    (valuation K).isClosed_integer.measurableSet
  have hind : ((valuation K).integer : Set K).indicator φ = φ := by
    funext x
    by_cases hx : x ∈ (valuation K).integer
    · simp [Set.indicator_of_mem, hx]
    · have hf : φ x = 0 := by
        by_contra hf
        exact hx (hφ hf)
      simp [Set.indicator_of_notMem, hx, hf]
  have htrans : ((valuation K).integer : Set K).indicator (fun x => φ (x + a)) =
      fun x => φ (x + a) := by
    funext x
    by_cases hx : x ∈ (valuation K).integer
    · simp [Set.indicator_of_mem, hx]
    · have hf : φ (x + a) = 0 := by
        by_contra hf
        have hs := hφ hf
        have hd := (valuation K).integer.sub_mem hs ha
        exact hx (by simpa using hd)
      simp [Set.indicator_of_notMem, hx, hf]
  rw [← integral_indicator ho, ← integral_indicator ho, htrans, hind]
  exact integral_add_right_eq_self φ a

theorem integral_integer_translate_of_not_mem
    (φ : K → ℂ) (hφ : Function.support φ ⊆ (valuation K).integer)
    (a : K) (ha : a ∉ (valuation K).integer) :
    (∫ x in (valuation K).integer, φ (x + a) ∂μ) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  by_contra hf
  have hs := hφ hf
  have hd := (valuation K).integer.sub_mem hs hx
  apply ha
  simpa using hd

theorem diagonal_root_residual_integral_eq
    (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ))
    (u : Kˣ) (hu : 3 ∣ KPCubicExpansion.valuationExponent K u) (i : Fin 3)
    (φ : K → ℂ) (hφ : Function.support φ ⊆ (valuation K).integer) :
    (∫ x in (valuation K).integer,
      φ (x + ((π ^ i.val : Kˣ) : K) / (u : K)) ∂μ) =
      ∫ x in (valuation K).integer, φ (x + (u : K)⁻¹) ∂μ := by
  have he := diagonal_root_residual_mem_integer_iff K π hπ u hu i
  by_cases h : (u : K)⁻¹ ∈ (valuation K).integer
  · rw [integral_integer_translate_of_support K μ φ hφ _ (he.mpr h),
      integral_integer_translate_of_support K μ φ hφ _ h]
  · rw [integral_integer_translate_of_not_mem K μ φ hφ _ (fun hi => h (he.mp hi)),
      integral_integer_translate_of_not_mem K μ φ hφ _ h]
end Haar

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.RootResidualGeometry

end
