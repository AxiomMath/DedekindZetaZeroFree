module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicCharacterProjection
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ValuationShellIntegration
public import DedekindZetaZeroFree.Algebra.IntegerGeometricTails

@[expose] public section

section

namespace DedekindZetaZeroFree.KPRankOneTestFunctionMellinPole

open MeasureTheory ValuativeRel
open scoped ValuativeRel WithZero Topology

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def integerBall (π : Kˣ) (n : ℤ) : Set K :=
  {x | ∃ t : 𝒪[K], x = ((π ^ n : Kˣ) : K) * (t : K)}

def IsTailCutoff (φ : K → ℂ) (n₀ : ℤ) : Prop :=
  ∀ y : Kˣ, n₀ ≤ KPCubicExpansion.valuationExponent K y → φ (y : K) = φ 0

def IsSupportCutoff (φ : K → ℂ) (nmin : ℤ) : Prop :=
  ∀ y : Kˣ, KPCubicExpansion.valuationExponent K y < nmin → φ (y : K) = 0

private lemma exponent_nonneg_iff (y : Kˣ) :
    0 ≤ KPCubicExpansion.valuationExponent K y ↔ (y : K) ∈ 𝒪[K] := by
  let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hne : iso (valuation K (y : K)) ≠ 0 := by
    exact (map_ne_zero_iff iso iso.injective).mpr ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  rw [Valuation.mem_integer_iff]
  rw [← map_le_map_iff iso, map_one]
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp only [KPCubicExpansion.valuationExponent]
  dsimp [iso] at *
  omega
private lemma exponent_inv (y : Kˣ) :
    KPCubicExpansion.valuationExponent K y⁻¹ = -KPCubicExpansion.valuationExponent K y := by
  have h := KPCubicExpansion.valuationExponent_mul y y⁻¹
  simpa [KPCubicExpansion.valuationExponent] using h
private lemma ball_units_iff (π y : Kˣ)
    (hπ : valuation K (π : K) = ValuativeRel.uniformizer K) (n : ℤ) :
    (y : K) ∈ integerBall K π n ↔ n ≤ KPCubicExpansion.valuationExponent K y := by
  have hv : KPCubicExpansion.valuationExponent K (y * (π^n)⁻¹) =
      KPCubicExpansion.valuationExponent K y - n := by
    rw [KPCubicExpansion.valuationExponent_mul, exponent_inv,
      KPCubicExpansion.valuationExponent_zpow, KPCubicExpansion.valuationExponent_uniformizer π hπ]
    ring
  constructor
  · rintro ⟨t, ht⟩
    have hm : ((y * (π^n)⁻¹ : Kˣ) : K) ∈ 𝒪[K] := by
      rw [Units.val_mul, ht]
      convert t.property using 1
      rw [mul_comm _ (t : K), mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have h := (exponent_nonneg_iff K _).mpr hm
    rw [hv] at h
    omega
  · intro hn
    have hm : ((y * (π^n)⁻¹ : Kˣ) : K) ∈ 𝒪[K] := by
      apply (exponent_nonneg_iff K _).mp
      rw [hv]
      omega
    refine ⟨⟨_, hm⟩, ?_⟩
    simp [Units.val_mul, mul_assoc, mul_comm, mul_left_comm]
    exact mul_inv_cancel₀ (zpow_ne_zero n π.ne_zero)

private lemma exponent_value (y : Kˣ) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (y : K)) =
      WithZero.exp (-KPCubicExpansion.valuationExponent K y) := by
  have hn : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (y : K)) ≠ 0 := by
    exact (map_ne_zero_iff _ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective).mpr
      ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  simp only [KPCubicExpansion.valuationExponent, neg_neg, WithZero.exp_log hn]
private lemma exists_tail (φ : K → ℂ) (hlc : IsLocallyConstant φ) :
    ∃ n : ℤ, IsTailCutoff K φ n := by
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp (hlc.eventually_eq 0)
  let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hne : iso γ ≠ 0 := (map_ne_zero_iff iso iso.injective).mpr hγ
  refine ⟨-(iso γ).log + 1, ?_⟩
  intro y hy
  apply hsub
  change valuation K (y : K) < γ
  rw [← map_lt_map_iff iso]
  rw [exponent_value K y, ← WithZero.exp_log hne, WithZero.exp_lt_exp]
  omega

private lemma exists_lower (φ : K → ℂ) (hc : HasCompactSupport φ) :
    ∃ n : ℤ, IsSupportCutoff K φ n := by
  let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let U : ℤ → Set K := fun n => {x | valuation K x < iso.symm (WithZero.exp n)}
  have hopen : ∀ n, IsOpen (U n) := by
    intro n
    simpa only [ValuativeRel.restrict_lt_orderMonoidIso, U] using
      (valuation K).isOpen_ball
        ((ValueGroupWithZero.orderMonoidIso (valuation K)) (iso.symm (WithZero.exp n)))
  have hcover : ∀ x ∈ tsupport φ, ∃ n, x ∈ U n := by
    intro x hx
    by_cases hz : x = 0
    · refine ⟨0, ?_⟩
      simp [U, hz]
    · let y := Units.mk0 x hz
      refine ⟨-KPCubicExpansion.valuationExponent K y + 1, ?_⟩
      change valuation K (y : K) < iso.symm _
      rw [← map_lt_map_iff iso, OrderMonoidIso.apply_symm_apply, exponent_value K y,
        WithZero.exp_lt_exp]
      omega
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hopen (fun x hx => Set.mem_iUnion.mpr (hcover x hx))
  obtain ⟨N, hN⟩ := (s.finite_toSet.bddAbove).exists_ge (0 : ℤ)
  refine ⟨-N, ?_⟩
  intro y hy
  by_contra hn
  have hmem : (y : K) ∈ tsupport φ := subset_closure hn
  have hcov := hs hmem
  obtain ⟨n, hn, hxy⟩ := Set.mem_iUnion₂.mp hcov
  have hnN : n ≤ N := hN.2 n hn
  change valuation K (y : K) < iso.symm (WithZero.exp n) at hxy
  rw [← map_lt_map_iff iso, OrderMonoidIso.apply_symm_apply, exponent_value K y,
      WithZero.exp_lt_exp] at hxy
  omega

theorem exists_cutoffs (φ : K → ℂ) (hφlc : IsLocallyConstant φ)
    (hφcs : HasCompactSupport φ) (π : Kˣ)
    (hπ : valuation K (π : K) = ValuativeRel.uniformizer K) :
    ∃ nmin n₀ : ℤ, nmin ≤ n₀ ∧ IsSupportCutoff K φ nmin ∧
      IsTailCutoff K φ n₀ ∧ ∀ x ∈ integerBall K π n₀, φ x = φ 0 := by
  obtain ⟨nl, hl⟩ := exists_lower K φ hφcs
  obtain ⟨nt, ht⟩ := exists_tail K φ hφlc
  refine ⟨nl, max nl nt, le_max_left _ _, hl, ?_, ?_⟩
  · intro y hy
    exact ht y (le_trans (le_max_right _ _) hy)
  · intro x hx
    by_cases hz : x = 0
    · simp [hz]
    · exact ht (Units.mk0 x hz)
        (le_trans (le_max_right _ _) ((ball_units_iff K π (Units.mk0 x hz) hπ _).mp hx))

end
end DedekindZetaZeroFree.KPRankOneTestFunctionMellinPole

end
