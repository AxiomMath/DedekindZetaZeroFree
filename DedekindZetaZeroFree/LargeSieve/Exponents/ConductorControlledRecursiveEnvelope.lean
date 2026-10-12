module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope
public import DedekindZetaZeroFree.LargeSieve.Exponents.NearRegionRecursiveBound
public import DedekindZetaZeroFree.LargeSieve.Exponents.ConductorControlledFarRegionDescent

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

private theorem annularWeight_sieveWeight : SieveWeight DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight where
  smooth := DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_contDiff
  nonneg := DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_nonneg
  one_le := fun t ht => by
    have h := DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_one ht.1 ht.2
    exact le_of_eq h.symm
  zero_outside := fun t ht => by
    rcases lt_or_ge t (1 / 2 : ℝ) with h | h
    · exact DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_zero_of_le (le_of_lt h)
    · have h2 : (5 / 2 : ℝ) ≤ t := by
        by_contra hc
        exact ht ⟨h, le_of_lt (lt_of_not_ge hc)⟩
      exact DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_zero_of_ge h2

theorem recursiveEnvelope_of_core
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hCore : CoreGood Q)
    (α : ℝ) (hα : 1 ≤ α) (hα₂ : α ≤ 2)
    (hExponent : HasSieveExponent F c Q α) :
    DedekindZetaZeroFree.LargeSieve.HasRecursiveEnvelope (B1 F c Q) α := by
  have hW : SieveWeight DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight := annularWeight_sieveWeight
  intro ε hε
  set η : ℝ := ε / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hηle : η ≤ ε := by rw [hηdef]; linarith

  obtain ⟨Cf, hCf0, hfar⟩ :=
    recursion_far_region_core F hF c hc Q hCore DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight hW α hα hα₂
      hExponent η hηpos

  obtain ⟨Cn, hCn0, hnear⟩ := recursion_near_region F c Q α hα hExponent η hηpos
  refine ⟨max Cf Cn + 1, ?_, ?_⟩
  · have h1 := le_max_left Cf Cn
    linarith
  · intro M N hM hN

    set X : ℝ := M + N + N ^ (2 * α - 1) * M ^ (1 - α) with hXdef
    set P : ℝ := (M * N) ^ η with hPdef
    set R : ℝ := (M * N) ^ ε with hRdef
    set δ : ℝ := η / (8 * ↑(max 1 (Nat.ceil (20 / η))) * (α + 1)) with hδdef
    have hXnn : 0 ≤ X := by
      rw [hXdef]
      have h1 : 0 ≤ N ^ (2 * α - 1) := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ M ^ (1 - α) := Real.rpow_nonneg (by linarith) _
      linarith [mul_nonneg h1 h2]
    have hMN1 : 1 ≤ M * N := by nlinarith
    have hCfC : Cf ≤ max Cf Cn + 1 := by
      have h1 := le_max_left Cf Cn
      linarith
    have hCnn : 0 ≤ max Cf Cn + 1 := by linarith
    have hPR : P ≤ R := by
      rw [hPdef, hRdef]
      exact Real.rpow_le_rpow_of_exponent_le hMN1 hηle
    have hPXnn : 0 ≤ P * X := by
      refine mul_nonneg ?_ hXnn
      rw [hPdef]
      exact Real.rpow_nonneg (by linarith) _
    by_cases hcase : M ≤ 2 * N * (M * N) ^ δ
    ·
      have h := hnear M N hM hN hcase
      calc B1 F c Q M N ≤ Cn * P * X := h
        _ = Cn * (P * X) := by ring
        _ ≤ (max Cf Cn + 1) * (P * X) := by
            refine mul_le_mul ?_ le_rfl hPXnn hCnn
            have h1 := le_max_right Cf Cn
            linarith
        _ ≤ (max Cf Cn + 1) * (R * X) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPR hXnn) hCnn
        _ = (max Cf Cn + 1) * R * X := by ring
    ·
      have h := (hfar M N hM hN (le_of_lt (lt_of_not_ge hcase))).1
      calc B1 F c Q M N ≤ Cf * P * X := h
        _ = Cf * (P * X) := by ring
        _ ≤ (max Cf Cn + 1) * (P * X) := mul_le_mul hCfC le_rfl hPXnn hCnn
        _ ≤ (max Cf Cn + 1) * (R * X) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPR hXnn) hCnn
        _ = (max Cf Cn + 1) * R * X := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve
