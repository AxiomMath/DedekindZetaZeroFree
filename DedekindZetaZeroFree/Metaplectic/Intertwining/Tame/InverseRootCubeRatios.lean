module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.InverseRootSupportHaarMass

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.TameInverseRootValueAudit

open scoped NumberField Classical
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPTameJacquetTestDuality

theorem eventual_inverse_root_chart_ratio_cube
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ u w : (KPTameCompact.O F q)ˣ,
      ∀ t : LocalField F q,
      t ∈ rootLevelSet F ζ hζ q m →
      (KPTameCompact.unitInclusion F q w : LocalField F q) =
        (KPTameCompact.unitInclusion F q u : LocalField F q) +
          (π : LocalField F q) * t →
      ∃ y : (LocalField F q)ˣ,
        KPTameCompact.unitInclusion F q w =
          KPTameCompact.unitInclusion F q u * y ^ 3 := by
  obtain ⟨M, hM, hcubes⟩ := KPLocalCube.principal_units_eventually_cubes F q
  refine ⟨M, ?_⟩
  intro m hm u w t ht hw
  have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < M) hm
  rw [KPTameTransposeUnitNumeratorSteps.rootLevelSet_eq_congruence_ideal
    F q ζ hζ S P m hmpos] at ht
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  have hp : valuation (LocalField F q) (π : LocalField F q) ≤ 1 := by
    apply (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q))).mp
    rw [hπ, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let p : KPLocalCube.LocalIntegers F q := ⟨(π : LocalField F q), hp⟩
  let x : KPLocalCube.LocalIntegers F q := p * t₀ * (↑u⁻¹)
  have hx : x ∈ KPLocalCube.maximalIdeal F q ^ m :=
    (KPLocalCube.maximalIdeal F q ^ m).mul_mem_right _
      ((KPLocalCube.maximalIdeal F q ^ m).mul_mem_left _ ht₀)
  obtain ⟨y, hy⟩ := hcubes m hm (1 + (x : LocalField F q)) ⟨x, hx, rfl⟩
  refine ⟨y, ?_⟩
  apply Units.ext
  rw [Units.val_mul, hy]
  have huinv : ((↑u⁻¹ : KPTameCompact.O F q) : LocalField F q) =
      (KPTameCompact.unitInclusion F q u : LocalField F q)⁻¹ :=
    Units.val_inv_eq_inv_val (KPTameCompact.unitInclusion F q u)
  have hu0 : (KPTameCompact.unitInclusion F q u : LocalField F q) ≠ 0 :=
    Units.ne_zero _
  change (KPTameCompact.unitInclusion F q w : LocalField F q) =
    (KPTameCompact.unitInclusion F q u : LocalField F q) *
      (1 + (π : LocalField F q) * (t₀ : LocalField F q) *
        ((↑u⁻¹ : KPTameCompact.O F q) : LocalField F q))
  rw [huinv, hw]
  field_simp
  rfl

end DedekindZetaZeroFree.TameInverseRootValueAudit

end
