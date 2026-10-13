module

public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.RowCount
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.SubpowerBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Recip

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem recip_bound (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ Uε : ℝ, 2 ≤ Uε ∧ ∀ U : ℝ, Uε ≤ U →
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U →
        ∀ s : ℂ, Scales.goodLine ≤ s.re → |s.im| ≤ 2 * U ^ ρ →
          D.Llam u s ≠ 0 ∧ ‖(D.Llam u s)⁻¹‖ ≤ C * U ^ ε := by
  intro ε hε
  obtain ⟨Cr, hCr, Ur, hUr, hr⟩ :=
    ReciprocalPrimitive.reciprocal_primitive D A_F ρ hA hconv hρ (ε / 2) (by linarith)
  obtain ⟨Cm, hCm, hm⟩ :=
    EulerDeletion.euler_product_bound_with_S D Scales.goodLine (by norm_num [Scales.goodLine]) (ε / 2)
      (by linarith)
  have hxg : (0 : ℝ) < Scales.goodLine := by norm_num [Scales.goodLine]
  refine ⟨Cm * 2 ^ (ε / 2) * Cr, mul_pos (mul_pos hCm (Real.rpow_pos_of_pos (by norm_num) _)) hCr,
    max Ur 2, le_max_right _ _, ?_⟩
  intro U hU u hu hU1 hU2 hexc s hs hIm
  have h2U : 2 ≤ U := le_trans (le_max_right _ _) hU
  have hUr' : Ur ≤ U := le_trans (le_max_left _ _) hU
  have hU0 : 0 < U := by linarith
  have hsre : 0 < s.re := lt_of_lt_of_le hxg hs
  have hq1 : (1 : ℝ) ≤ D.q u := le_trans (by linarith) hU1
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).2
  obtain ⟨g, hg, hgL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A (D.omega u) hnp
  have hg1 : ∀ z : ℂ, 1 < z.re → g z = Detector.idealLSeries F (D.omega u).character z :=
    fun z hz => (hgL z (by linarith [hz])).trans
      (RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (D.omega u) hnp z hz)
  obtain ⟨hgne, hginv⟩ := hr U hUr' u hu hU1 hU2 hexc g hg hg1 s hs hIm
  have hLe : D.Llam u s = Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
      (fun v => (D.omega u).character v.asIdeal) s * g s := by
    rw [RowAnalyticContinuation.Llam_eq_mask_mul_hecke D u hu s hsre, hgL s hsre]
  have hMne := RowHeckeBridge.mask_ne_zero (D.omega u) _ (RowHeckeBridge.deletionSet_finite D u) s hsre
  have hmask := (RowHeckeBridge.mask_norm_le D u (D.omega u) Scales.goodLine hxg s hs).2
  have hP := (hm u hq1).2
  have hPnn : 0 ≤ ∏ p ∈ EulerDeletion.rowPrimesWithS D u,
      (1 - (Ideal.absNorm p : ℝ) ^ (-Scales.goodLine))⁻¹ :=
    le_trans (norm_nonneg _) hmask
  have hq : D.q u ^ (ε / 2) ≤ (2 * U) ^ (ε / 2) :=
    Real.rpow_le_rpow (by linarith) hU2.le (by linarith)
  have h2U' : (2 * U) ^ (ε / 2) = 2 ^ (ε / 2) * U ^ (ε / 2) :=
    Real.mul_rpow (by norm_num) hU0.le
  have hUe : U ^ (ε / 2) * U ^ (ε / 2) = U ^ ε := by
    rw [← Real.rpow_add hU0]; congr 1; ring
  have hUpos : 0 ≤ Cr * U ^ (ε / 2) := mul_nonneg hCr.le (Real.rpow_nonneg hU0.le _)
  refine ⟨?_, ?_⟩
  · rw [hLe]; exact mul_ne_zero hMne hgne
  · rw [hLe, mul_inv, norm_mul]
    calc ‖(Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
          (fun v => (D.omega u).character v.asIdeal) s)⁻¹‖ * ‖(g s)⁻¹‖
        ≤ (∏ p ∈ EulerDeletion.rowPrimesWithS D u,
          (1 - (Ideal.absNorm p : ℝ) ^ (-Scales.goodLine))⁻¹) * (Cr * U ^ (ε / 2)) :=
          mul_le_mul hmask hginv (norm_nonneg _) hPnn
      _ ≤ (Cm * D.q u ^ (ε / 2)) * (Cr * U ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_right hP hUpos
      _ ≤ (Cm * (2 ^ (ε / 2) * U ^ (ε / 2))) * (Cr * U ^ (ε / 2)) := by
          apply mul_le_mul_of_nonneg_right _ hUpos
          exact mul_le_mul_of_nonneg_left (h2U' ▸ hq) hCm.le
      _ = (Cm * 2 ^ (ε / 2) * Cr) * U ^ ε := by rw [← hUe]; ring

theorem recip_card (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      (exceptionalSet D ρ U).Finite ∧
        ((exceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α :=
  Detect.exceptionalSet_card D A_F ρ hA hconv hρ

end

end DedekindZetaZeroFree.Quantitative.Recip
