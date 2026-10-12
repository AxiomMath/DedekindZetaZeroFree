module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.ActualRowTransfer

theorem log_square_le_rpow (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (1 + Real.log Z) ^ 2 ≤ C * Z ^ η := by
  refine ⟨7 * (1 + η⁻¹) ^ 2, by positivity, ?_⟩
  intro Z hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  set t := Real.log Z with ht
  have ht0 : 0 ≤ t := Real.log_nonneg hZ
  set u := η * t with hu
  have hu0 : 0 ≤ u := mul_nonneg hη.le ht0
  have hexppos : 0 < Real.exp u := Real.exp_pos u

  have hule : u ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  have h1le : 1 ≤ Real.exp u := Real.one_le_exp hu0

  have hsq : u ^ 2 ≤ 4 * Real.exp u := by
    have hhalf : u / 2 ≤ Real.exp (u / 2) := by
      have := Real.add_one_le_exp (u / 2); linarith
    have hpow : (u / 2) ^ 2 ≤ (Real.exp (u / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    have hexp : (Real.exp (u / 2)) ^ 2 = Real.exp u := by
      rw [pow_two, ← Real.exp_add]; ring_nf
    rw [hexp] at hpow
    nlinarith [hpow]
  have hquad : (1 + u) ^ 2 ≤ 7 * Real.exp u := by
    have : (1 + u) ^ 2 = 1 + 2 * u + u ^ 2 := by ring
    rw [this]
    nlinarith [h1le, hule, hsq, hexppos.le]

  have hlin : 1 + t ≤ (1 + η⁻¹) * (1 + u) := by
    have h : (1 + η⁻¹) * (1 + u) - (1 + t) = η * t + η⁻¹ := by
      rw [hu]; field_simp; ring
    nlinarith [h, hη.le, inv_pos.mpr hη, ht0]
  have hstep : (1 + t) ^ 2 ≤ (1 + η⁻¹) ^ 2 * (1 + u) ^ 2 := by
    calc (1 + t) ^ 2 ≤ ((1 + η⁻¹) * (1 + u)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hlin 2
      _ = (1 + η⁻¹) ^ 2 * (1 + u) ^ 2 := by ring
  have hmain : (1 + t) ^ 2 ≤ 7 * (1 + η⁻¹) ^ 2 * Real.exp u := by
    have hfac : (1 + η⁻¹) ^ 2 * (1 + u) ^ 2 ≤ (1 + η⁻¹) ^ 2 * (7 * Real.exp u) :=
      mul_le_mul_of_nonneg_left hquad (by positivity)
    nlinarith [hstep, hfac]
  have hZeta : Real.exp u = Z ^ η := by
    rw [hu, ht, Real.rpow_def_of_pos hZpos]; ring_nf
  rw [hZeta] at hmain
  calc (1 + Real.log Z) ^ 2 = (1 + t) ^ 2 := by rw [ht]
    _ ≤ 7 * (1 + η⁻¹) ^ 2 * Z ^ η := hmain

end DedekindZetaZeroFree.RepresentationTheory.ActualRowTransfer
