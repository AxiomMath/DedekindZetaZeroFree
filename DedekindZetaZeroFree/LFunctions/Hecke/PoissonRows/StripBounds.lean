module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConductorNormalization
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConvexityData
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.FixedRowStripBound

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem Lpsi_strip_bound (u : D.Row) (hu : u.u ≠ 1) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ, Scales.wLine - EulerDomain.pad / 2 ≤ w.re →
      w.re ≤ 4 + EulerDomain.pad / 2 → ‖D.Lpsi u w‖ ≤ C * (2 + |w.im|) ^ A := by
  classical
  have hpad : EulerDomain.pad = 1 / 1000000 := rfl
  have hy0 : Scales.wLine = 3 / 25 := rfl
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  obtain ⟨A, hA0, hconv⟩ := convex_normalized F hF
  obtain ⟨C1, hC1, hnorm⟩ := hconv (1 / 100) (by norm_num) (by norm_num)
  obtain ⟨hnpP, -⟩ := RowNonprincipal.inducers_nonprincipal D u hu
  obtain ⟨g, hg, hgs⟩ := RowAnalyticContinuation.exists_entire_numerator D u hu
  obtain ⟨Cr, hCr, hright⟩ := RightHeckeBounds.Lpsi_norm_le_right D (101 / 100) (by norm_num)
  set σs : ℝ := Scales.wLine - EulerDomain.pad / 2 with hσs
  have hσpos : 0 < σs := by rw [hσs, hpad, hy0]; norm_num
  set P : ℝ := ∏ p ∈ EulerDeletion.rowPrimesWithS D u, (1 + (Ideal.absNorm p : ℝ) ^ (-σs))
    with hP
  set Q : ℝ := 1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ) with hQ
  have hQ1 : 1 ≤ Q := by
    have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm (D.inducers u).plus.conductor)
    rw [hQ]; linarith
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.prod_nonneg (fun p _ => by
      have := Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm p) : (0:ℝ) ≤ _) (-σs)
      linarith)
  refine ⟨A, P * C1 * Q + Cr + 1, hA0, by positivity, ?_⟩
  intro w hw1 hw2
  have hY : (1 : ℝ) ≤ (2 + |w.im|) ^ A :=
    Real.one_le_rpow (by linarith [abs_nonneg w.im]) hA0
  have hY0 : (0 : ℝ) ≤ (2 + |w.im|) ^ A := by linarith
  have hPC : 0 ≤ P * C1 * Q := by positivity
  by_cases hcase : w.re ≤ 1 + 1 / 100
  · have hwpos : 0 < w.re := lt_of_lt_of_le hσpos hw1
    have hg_eq := ConvexBridge.entire_eq_mask_mul D u hnpP hg hgs w hwpos
    have hgL := RowAnalyticContinuation.entire_eq_Lpsi D u hu hg hgs w hwpos
    have hN_eq := nonprincipalHeckeEntireContinuation_eq F hF (D.inducers u).plus.conductor
      (D.inducers u).plus.conductor_ne_zero (D.inducers u).plus.character
      (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) w hwpos
    have hmask := (RowHeckeBridge.mask_norm_le D u (D.inducers u).plus σs hσpos w hw1).1
    have hNb := hnorm (D.inducers u).plus.conductor (D.inducers u).plus.conductor_ne_zero
      (D.inducers u).plus.character (D.inducers u).plus.primitive hnpP
      (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) w (by linarith) hcase
    have hQe : Q ^ ((1 + 1 / 100 - w.re) / 2) ≤ Q := by
      have h1 : Q ^ ((1 + 1 / 100 - w.re) / 2) ≤ Q ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 (by
          rw [hσs, hpad, hy0] at hw1; linarith)
      rwa [Real.rpow_one] at h1
    have hnorm_eq : ‖D.Lpsi u w‖ = ‖Detector.finiteEulerDeletionMask F
        (RowHeckeBridge.deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) w‖ *
        ‖nonprincipalHeckeEntireContinuation F (D.inducers u).plus.conductor
          (D.inducers u).plus.character (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP)
          w‖ := by
      rw [← hgL, hg_eq, ← hN_eq, norm_mul]
    rw [hnorm_eq]
    have hNb' : ‖nonprincipalHeckeEntireContinuation F (D.inducers u).plus.conductor
          (D.inducers u).plus.character (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP)
          w‖ ≤ C1 * Q * (2 + |w.im|) ^ A :=
      hNb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQe hC1.le) hY0)
    calc _ ≤ P * (C1 * Q * (2 + |w.im|) ^ A) :=
          mul_le_mul hmask hNb' (norm_nonneg _) hP0
      _ = (P * C1 * Q) * (2 + |w.im|) ^ A := by ring
      _ ≤ (P * C1 * Q + Cr + 1) * (2 + |w.im|) ^ A :=
          mul_le_mul_of_nonneg_right (by linarith) hY0
  · push_neg at hcase
    have h := hright u w (by linarith)
    calc ‖D.Lpsi u w‖ ≤ Cr := by simpa using h
      _ = Cr * 1 := (mul_one _).symm
      _ ≤ Cr * (2 + |w.im|) ^ A := mul_le_mul_of_nonneg_left hY hCr.le
      _ ≤ (P * C1 * Q + Cr + 1) * (2 + |w.im|) ^ A :=
          mul_le_mul_of_nonneg_right (by linarith) hY0

end

end DedekindZetaZeroFree.Quantitative.FixedRowStripBound
