module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem rlogrBound_poleClear (H : ℂ → ℂ) (a b w : ℂ)
    (hH : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ s : ℂ, ‖H s‖ ≤
        C * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖))) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ s : ℂ, ‖s * (s - 1) * H s - (s - 1) * a + s * w * b‖ ≤
        C * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C, K, hC, hK, hH⟩ := hH
  refine ⟨C + ‖a‖ + ‖w‖ * ‖b‖, K + 2, by positivity, by positivity, ?_⟩
  intro s
  let t : ℝ := (1 + ‖s‖) * Real.log (2 + ‖s‖)
  have hR : 0 ≤ ‖s‖ := norm_nonneg s
  have hlog : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  have ht : 0 ≤ t := mul_nonneg (by positivity) hlog
  have hlin : 1 + ‖s‖ ≤ Real.exp t := by
    calc
      1 + ‖s‖ ≤ 2 + ‖s‖ := by linarith
      _ = Real.exp (Real.log (2 + ‖s‖)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (by dsimp [t]; nlinarith)
  have hsub : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    simpa only [norm_one, add_comm] using norm_sub_le s (1 : ℂ)
  have hquad : ‖s‖ * ‖s - 1‖ ≤ Real.exp t * Real.exp t := by
    apply mul_le_mul
    · linarith
    · exact hsub.trans hlin
    · exact norm_nonneg _
    · exact (Real.exp_pos _).le
  have hE : Real.exp t ≤ Real.exp ((K + 2) * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hmain : ‖s‖ * ‖s - 1‖ * ‖H s‖ ≤ C * Real.exp ((K + 2) * t) := by
    calc
      _ ≤ (Real.exp t * Real.exp t) * (C * Real.exp (K * t)) := by
        apply mul_le_mul hquad
        · simpa only [t, mul_assoc] using hH s
        · exact norm_nonneg _
        · positivity
      _ = C * Real.exp ((K + 2) * t) := by
        rw [show (K + 2) * t = t + t + K * t by ring, Real.exp_add, Real.exp_add]
        ring
  have ha : ‖s - 1‖ * ‖a‖ ≤ ‖a‖ * Real.exp ((K + 2) * t) := by
    calc
      _ ≤ Real.exp t * ‖a‖ := mul_le_mul_of_nonneg_right (hsub.trans hlin) (norm_nonneg _)
      _ ≤ Real.exp ((K + 2) * t) * ‖a‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hb : ‖s‖ * ‖w‖ * ‖b‖ ≤ (‖w‖ * ‖b‖) * Real.exp ((K + 2) * t) := by
    calc
      _ ≤ Real.exp ((K + 2) * t) * ‖w‖ * ‖b‖ := by
        gcongr
        exact (by linarith : ‖s‖ ≤ Real.exp t).trans hE
      _ = _ := by ring
  calc
    _ ≤ ‖s * (s - 1) * H s‖ + ‖(s - 1) * a‖ + ‖s * w * b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖s‖ * ‖s - 1‖ * ‖H s‖ + ‖s - 1‖ * ‖a‖ + ‖s‖ * ‖w‖ * ‖b‖ := by
      simp only [norm_mul]
    _ ≤ C * Real.exp ((K + 2) * t) + ‖a‖ * Real.exp ((K + 2) * t) +
        (‖w‖ * ‖b‖) * Real.exp ((K + 2) * t) :=
      add_le_add (add_le_add hmain ha) hb
    _ = (C + ‖a‖ + ‖w‖ * ‖b‖) *
        Real.exp ((K + 2) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
      dsimp [t]
      rw [mul_assoc (K + 2)]
      ring

end DedekindZetaZeroFree.Hecke
