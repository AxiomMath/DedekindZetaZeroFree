module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.InverseRootSupportHaarMass

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPTameJacquetTestDuality

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
include S P

theorem rootLevelSet_isOpen (m : ℕ) (hm : 0 < m) :
    IsOpen (rootLevelSet F ζ hζ q m) := by
  rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hm]
  have hi : IsOpen ((valuation (LocalField F q)).integer : Set (LocalField F q)) :=
    Valuation.isOpen_integer (v := valuation (LocalField F q))
  apply hi.isOpenMap_subtype_val
  exact IsLocalRing.isOpen_maximalIdeal_pow (KPLocalCube.LocalIntegers F q) m

theorem zero_mem_rootLevelSet (m : ℕ) (hm : 0 < m) :
    (0 : LocalField F q) ∈ rootLevelSet F ζ hζ q m := by
  rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hm]
  exact ⟨0, Ideal.zero_mem _, by simp⟩

theorem rootMass_pos (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (m : ℕ) (hm : 0 < m) :
    0 < rootMass F ζ hζ q μ m := by
  have hpos : 0 < μ (rootLevelSet F ζ hζ q m) :=
    (rootLevelSet_isOpen F ζ hζ q S P m hm).measure_pos μ
      ⟨0, zero_mem_rootLevelSet F ζ hζ q S P m hm⟩
  have hfin : μ (rootLevelSet F ζ hζ q m) < ⊤ := by
    apply lt_of_le_of_lt (b := μ ((valuation (LocalField F q)).integer : Set (LocalField F q)))
    · apply measure_mono
      rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hm]
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    · rw [hμ]
      simp
  exact ENNReal.toReal_pos hpos.ne' hfin.ne

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

end
