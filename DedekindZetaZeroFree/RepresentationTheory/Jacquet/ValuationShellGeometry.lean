module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.SphericalTruncations

@[expose] public section

open scoped NumberField Valued ValuativeRel BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorActualJacquetShellsGeometry

open KPLocalExceptionalConstruction KPExteriorActualJacquetShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private theorem scaled_integer_eq (a : LocalField F v) (ha : a ≠ 0) :
    {x : LocalField F v | ∃ u : (valuation (LocalField F v)).integer,
      x = a * (u : LocalField F v)} =
      {x | valuation (LocalField F v) x ≤ valuation (LocalField F v) a} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, rfl⟩
    rw [map_mul]
    exact mul_le_of_le_one_right (show 0 ≤ valuation (LocalField F v) a from bot_le) u.property
  · intro hx
    have hu : valuation (LocalField F v) (a⁻¹ * x) ≤ 1 := by
      rw [map_mul, map_inv₀]
      exact (inv_mul_le_one₀ ((valuation (LocalField F v)).pos_iff.mpr ha)).mpr hx
    exact ⟨⟨a⁻¹ * x, hu⟩, by simp [ha]⟩

theorem sphericalBall_eq_valuation_ball
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) :
    sphericalBall F v π e =
      {x | valuation (LocalField F v) x ≤
        valuation (LocalField F v) ((π : LocalField F v) ^ e)} := by
  apply scaled_integer_eq
  exact pow_ne_zero _ (uniformizerUnit F v π hπ).ne_zero

theorem isCompact_sphericalBall
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) :
    IsCompact (sphericalBall F v π e) := by
  rw [sphericalBall_eq_valuation_ball F v π hπ e]
  exact IsNonarchimedeanLocalField.isCompact_closedBall _ _

theorem measurableSet_sphericalBall
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) :
    MeasurableSet (sphericalBall F v π e) :=
  (isCompact_sphericalBall F v π hπ e).isClosed.measurableSet

theorem integerUnitShell_eq_valuation_sphere :
    KPTameGauss.integerUnitShell (LocalField F v) =
      {x | valuation (LocalField F v) x = 1} := by
  ext x
  simp only [KPTameGauss.integerUnitShell, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact (Valuation.integer.integers (valuation (LocalField F v))).isUnit_iff_valuation_eq_one.mp hu
  · intro hx
    exact ⟨⟨x, hx.le⟩, rfl,
      (Valuation.integer.integers (valuation (LocalField F v))).isUnit_iff_valuation_eq_one.mpr hx⟩

theorem sphericalShell_eq_valuation_sphere
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) (l : ℤ) :
    sphericalShell F v π e l =
      {x | valuation (LocalField F v) x =
        valuation (LocalField F v) ((π : LocalField F v) ^ ((e : ℤ) - l))} := by
  let a : LocalField F v := (π : LocalField F v) ^ ((e : ℤ) - l)
  have ha : a ≠ 0 := zpow_ne_zero _ (uniformizerUnit F v π hπ).ne_zero
  ext x
  simp only [sphericalShell, Set.mem_setOf_eq]
  rw [integerUnitShell_eq_valuation_sphere F v]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [Set.mem_setOf_eq] at hu
    rw [map_mul, hu, mul_one]
  · intro hx
    refine ⟨a⁻¹ * x, ?_, by simp [a, ha]⟩
    change valuation (LocalField F v) (a⁻¹ * x) = 1
    rw [map_mul, map_inv₀, hx]
    exact inv_mul_cancel₀ ((valuation (LocalField F v)).ne_zero_iff.mpr ha)

theorem isCompact_sphericalShell
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) (l : ℤ) :
    IsCompact (sphericalShell F v π e l) := by
  rw [sphericalShell_eq_valuation_sphere F v π hπ e l]
  apply (IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F v)
    (valuation (LocalField F v) ((π : LocalField F v) ^ ((e : ℤ) - l)))).of_isClosed_subset
  · simpa only [← (valuation (LocalField F v)).restrict_inj] using
      (valuation (LocalField F v)).isClosed_sphere
        ((valuation (LocalField F v)).restrict ((π : LocalField F v) ^ ((e : ℤ) - l)))
  · intro x hx
    exact hx.le

theorem measurableSet_sphericalShell
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) (e : ℕ) (l : ℤ) :
    MeasurableSet (sphericalShell F v π e l) :=
  (isCompact_sphericalShell F v π hπ e l).isClosed.measurableSet

end
end DedekindZetaZeroFree.KPExteriorActualJacquetShellsGeometry
