module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConvexityData
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.DeletionMaskBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.PrimitiveGrowth

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawSharpConvexity31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem plus_sharp_convexity :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ σmin : ℝ, 0 < σmin → σmin ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ σ : ℝ, σmin ≤ σ → σ ≤ 1 → ∀ t : ℝ,
          ‖(RawFixed.FixedData.pkg D).plus u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * (frequencyNorm D.recipe u) ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A_F := by
  obtain ⟨A, hA, H⟩ := RawPrimitiveGrowth31.primPlus_growth D
  refine ⟨A, hA, fun σmin hσmin hσmin1 ε hε => ?_⟩
  obtain ⟨C1, hC1, H1⟩ := H (ε / 2) (by linarith)
  obtain ⟨C2, hC2, H2⟩ := RawDeletionMask31.plus_mask_subpower D σmin (ε / 2) hσmin (by linarith)
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun u hu σ hσ0 hσ1 t => ?_⟩
  have hq1 : (1 : ℝ) ≤ frequencyNorm D.recipe u :=
    RawFrequencyCount.one_le_frequencyNorm D.recipe u
  have hq0 : (0 : ℝ) < frequencyNorm D.recipe u := by linarith
  obtain ⟨g, hg, hgL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A
    (RawFixed.FixedData.primPlus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
  have hgI : ∀ s : ℂ, 1 < s.re →
      g s = Detector.idealLSeries F (RawFixed.FixedData.primPlus D u).character s := by
    intro s hs
    rw [hgL s (by linarith [hs]),
      RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (RawFixed.FixedData.primPlus D u)
        ((RawFixed.FixedData.pkg D).nonprincipal u hu).1 s hs]
  have hwre : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hg1 := H1 u hu (frequencyNorm D.recipe u) hq1 (by linarith) g hg hgI σ (by linarith) hσ1 t
  have hm := (H2 u ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact hσ0)).2.1
  rw [RawHeckeIdentification31.plus_eq_hecke_mul_mask D u hu _ hwre, ← hgL _ hwre, norm_mul]
  have hpow : frequencyNorm D.recipe u ^ ((1 - σ) / 2 + ε / 2) *
      frequencyNorm D.recipe u ^ (ε / 2) = frequencyNorm D.recipe u ^ ((1 - σ) / 2 + ε) := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  have hB : (0 : ℝ) ≤ (2 + |t|) ^ A := by positivity
  refine le_trans (mul_le_mul hg1 hm (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg hq0.le _)) hB)) (le_of_eq ?_)
  rw [← hpow]; ring

theorem plus_sharp_convexity_dyad :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ σmin : ℝ, 0 < σmin → σmin ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ σ : ℝ, σmin ≤ σ → σ ≤ 1 → ∀ t : ℝ,
          ‖(RawFixed.FixedData.pkg D).plus u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A_F := by
  obtain ⟨A, hA, H⟩ := plus_sharp_convexity D
  refine ⟨A, hA, fun σmin hσmin hσmin1 ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H σmin hσmin hσmin1 ε hε
  refine ⟨C * 2 ^ (1 + ε), by positivity, fun u hu U hU hUq hq2 σ hσ0 hσ1 t => ?_⟩
  have hq0 : (0 : ℝ) < frequencyNorm D.recipe u := by linarith
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hexp0 : (0 : ℝ) ≤ (1 - σ) / 2 + ε := by linarith
  have hb := HC u hu σ hσ0 hσ1 t
  have h1 : frequencyNorm D.recipe u ^ ((1 - σ) / 2 + ε) ≤
      2 ^ (1 + ε) * U ^ ((1 - σ) / 2 + ε) := by
    calc frequencyNorm D.recipe u ^ ((1 - σ) / 2 + ε)
        ≤ (2 * U) ^ ((1 - σ) / 2 + ε) :=
          Real.rpow_le_rpow hq0.le (by linarith) hexp0
      _ = 2 ^ ((1 - σ) / 2 + ε) * U ^ ((1 - σ) / 2 + ε) :=
          Real.mul_rpow (by norm_num) hU0
      _ ≤ 2 ^ (1 + ε) * U ^ ((1 - σ) / 2 + ε) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0 _)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hB : (0 : ℝ) ≤ (2 + |t|) ^ A := by positivity
  calc ‖(RawFixed.FixedData.pkg D).plus u ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C * frequencyNorm D.recipe u ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A := hb
    _ ≤ C * (2 ^ (1 + ε) * U ^ ((1 - σ) / 2 + ε)) * (2 + |t|) ^ A := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact mul_le_mul_of_nonneg_left h1 hC.le
    _ = C * 2 ^ (1 + ε) * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A := by ring

theorem minus_detector_line :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character s) →
          ∀ t : ℝ, ‖g (((1 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((99 / 200 : ℝ) + ε) * (2 + |t|) ^ A_F := by
  obtain ⟨A, hA, H⟩ := RawPrimitiveGrowth31.primMinus_growth D
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H ε hε
  refine ⟨C, hC, fun u hu U hU hUq hq2 g hg h t => ?_⟩
  have hb := HC u hu U (by linarith) hq2 g hg h (1 / 100) (by norm_num) (by norm_num) t
  have e : (1 - (1 / 100 : ℝ)) / 2 = 99 / 200 := by norm_num
  rw [e] at hb
  exact hb

theorem minus_primitive_strip :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character s) →
          ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 4 → ∀ t : ℝ,
            ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A_F := by
  obtain ⟨A, hA, H⟩ := RawPrimitiveGrowth31.primMinus_strip_growth D
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H ε hε
  refine ⟨C, hC, fun u hu U hU hUq hq2 g hg h σ h0 h1 t => ?_⟩
  exact HC u hu U (by linarith) hq2 g hg h σ h0 h1 t

theorem plus_strip_growth (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ, Scales.wLine - EulerDomain.pad / 2 ≤ w.re →
      w.re ≤ 4 + EulerDomain.pad / 2 →
      ‖(RawFixed.FixedData.pkg D).plus u w‖ ≤ C * (2 + |w.im|) ^ A := by
  obtain ⟨A, C1, hA, hC1, H1⟩ := RawPrimitiveGrowth31.primPlus_fixed_strip D u hu
  have hq1 : (1 : ℝ) ≤ frequencyNorm D.recipe u :=
    RawFrequencyCount.one_le_frequencyNorm D.recipe u
  have hpos : (0 : ℝ) < Scales.wLine - EulerDomain.pad / 2 := by
    simp only [Scales.wLine, EulerDomain.pad]; norm_num
  obtain ⟨C2, hC2, H2⟩ := RawDeletionMask31.plus_mask_subpower D
    (Scales.wLine - EulerDomain.pad / 2) 1 hpos one_pos
  obtain ⟨g, hg, hgL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A
    (RawFixed.FixedData.primPlus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
  have hgI : ∀ s : ℂ, 1 < s.re →
      g s = Detector.idealLSeries F (RawFixed.FixedData.primPlus D u).character s := by
    intro s hs
    rw [hgL s (by linarith [hs]),
      RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (RawFixed.FixedData.primPlus D u)
        ((RawFixed.FixedData.pkg D).nonprincipal u hu).1 s hs]
  refine ⟨A, C1 * (C2 * frequencyNorm D.recipe u ^ (1 : ℝ)), hA,
    mul_pos hC1 (mul_pos hC2 (Real.rpow_pos_of_pos (by linarith) _)), fun w hw1 hw2 => ?_⟩
  have hwre : 0 < w.re := by linarith
  have hg1 := H1 g hg hgI w (by linarith)
  have hm := (H2 u w (by linarith)).2.1
  rw [RawHeckeIdentification31.plus_eq_hecke_mul_mask D u hu w hwre, ← hgL w hwre, norm_mul]
  refine le_trans (mul_le_mul hg1 hm (norm_nonneg _)
    (mul_nonneg hC1.le (by positivity))) (le_of_eq ?_)
  ring

end

end DedekindZetaZeroFree.Quantitative.RawSharpConvexity31
