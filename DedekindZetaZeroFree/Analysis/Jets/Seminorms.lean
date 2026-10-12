module

public import DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesJets
open KPCplxCharacterHaar Set
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable def jetSup (n : ℕ) (F : ℂ → ℂ) : ℝ :=
  sSup ((fun x : ℂ => ‖iteratedFDeriv ℝ n F x‖) '' Metric.closedBall 0 1)
lemma jetBdd (n : ℕ) (F : ℂ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    BddAbove ((fun x : ℂ => ‖iteratedFDeriv ℝ n F x‖) '' Metric.closedBall 0 1) := by
  exact ((isCompact_closedBall (0 : ℂ) 1).image
    ((hF.continuous_iteratedFDeriv (by simp)).norm)).bddAbove
lemma jetLe (n : ℕ) (F : ℂ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x : ℂ) (hx : x ∈ Metric.closedBall 0 1) : ‖iteratedFDeriv ℝ n F x‖ ≤ jetSup n F := by
  exact le_csSup (jetBdd n F hF) ⟨x, hx, rfl⟩
lemma jetSupLe (n : ℕ) (F : ℂ → ℂ) (r : ℝ)
    (h : ∀ x ∈ Metric.closedBall 0 1, ‖iteratedFDeriv ℝ n F x‖ ≤ r) : jetSup n F ≤ r := by
  apply csSup_le
  · exact ⟨_, 0, by simp, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
lemma jetNonneg (n : ℕ) (F : ℂ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) : 0 ≤ jetSup n F := by
  exact (norm_nonneg _).trans (jetLe n F hF 0 (by simp))
lemma jetZero (n : ℕ) : jetSup n (0 : ℂ → ℂ) = 0 := by
  simp [jetSup, Pi.zero_def, iteratedFDeriv_fun_zero]
lemma jetAdd (n : ℕ) (F G : ℂ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) : jetSup n (F + G) ≤ jetSup n F + jetSup n G := by
  apply jetSupLe
  intro x hx
  rw [iteratedFDeriv_add_apply ((hF.of_le (by simp)).contDiffAt) ((hG.of_le (by simp)).contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add (jetLe n F hF x hx) (jetLe n G hG x hx))
lemma jetNeg (n : ℕ) (F : ℂ → ℂ) : jetSup n (-F) = jetSup n F := by
  simp [jetSup, iteratedFDeriv_neg_apply]
lemma jetSmul (n : ℕ) (F : ℂ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : ℂ) :
    jetSup n (c • F) = ‖c‖ * jetSup n F := by
  apply le_antisymm
  · apply jetSupLe
    intro x hx
    rw [iteratedFDeriv_const_smul_apply ((hF.of_le (by simp)).contDiffAt), norm_smul]
    exact mul_le_mul_of_nonneg_left (jetLe n F hF x hx) (norm_nonneg c)
  · by_cases hc : c = 0
    · simp [hc, jetZero]
    have h : jetSup n F ≤ ‖c⁻¹‖ * jetSup n (c • F) := by
      have hsc : ContDiff ℝ (⊤ : ℕ∞) (c • F) := hF.const_smul c
      calc
        jetSup n F = jetSup n (c⁻¹ • (c • F)) := by simp [smul_smul, hc]
        _ ≤ ‖c⁻¹‖ * jetSup n (c • F) := by
          apply jetSupLe
          intro x hx
          rw [iteratedFDeriv_const_smul_apply ((hsc.of_le (by simp)).contDiffAt), norm_smul]
          exact mul_le_mul_of_nonneg_left (jetLe n (c • F) hsc x hx) (norm_nonneg c⁻¹)
    have := mul_le_mul_of_nonneg_left h (norm_nonneg c)
    simpa [norm_inv, ← mul_assoc, norm_ne_zero_iff.mpr hc] using this
end DedekindZetaZeroFree.KPCplxPrincipalSeriesJets
