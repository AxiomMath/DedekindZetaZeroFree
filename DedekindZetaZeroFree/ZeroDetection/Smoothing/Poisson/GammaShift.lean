module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.MellinIdentity
public import DedekindZetaZeroFree.Analysis.ContourIntegration.GammaShiftNorm

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorShift

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def smoothedSum (F : Type) [Field F] [NumberField F] (U β γ : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ then
      (DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
    else 0

theorem detector_shift :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ β γ : ℝ, DetectorDef.σ₀ ≤ β → β ≤ 1 →
          DetectorDef.IsLZero (D.omega u) ((β : ℂ) + (γ : ℂ) * Complex.I) →
          ‖smoothedSum F U β γ (D.omega u)‖ ≤
            C * U ^ (-(3 / 1250 : ℝ) + ε) * (2 + |γ|) ^ A_F := by
  obtain ⟨A, hA, hshift⟩ := GammaShiftNorm.gamma_shift_norm D
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hshift ε hε
  refine ⟨C, hC, ?_⟩
  intro u hu U hU hUq hUq2 β γ hβ hβ1 hz0
  have hz1 := hz0
  have hnp : ¬ (D.omega u).character.IsPrincipal :=
    (RowNonprincipal.inducers_nonprincipal D u hu).2
  have hσ : DetectorDef.σ₀ = (22 / 25 : ℝ) := rfl
  have hβ22 : (22 / 25 : ℝ) ≤ β := by
    have h := hβ
    rw [hσ] at h
    exact h
  have hU0 : (0 : ℝ) < U := by linarith
  have hU1 : (1 : ℝ) ≤ U := by linarith

  obtain ⟨G, hGdiff, hGL⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A (D.omega u) hnp
  have hGs : ∀ z : ℂ, 1 < z.re →
      G z = Detector.idealLSeries F (D.omega u).character z := by
    intro z hz
    rw [hGL z (by linarith), RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (D.omega u) hnp z hz]
  obtain ⟨hre, g, hgan, hgs, hg0⟩ := hz0
  have hre' : 0 < ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    linarith
  have hGz : G ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
    rw [hGL _ hre', ← RowHeckeBridge.eq_hecke_of_analyticOn D.recipe.A (D.omega u) hnp hgan
      hgs _ hre', hg0]

  have hzc := GammaZeroContour.gamma_zero_contour D u hnp U hU hUq hUq2 G hGdiff hGs β γ hβ hβ1
    hz1 2 (by norm_num) (by norm_num)
  have hbnd := hbound u hu U hU hUq hUq2 G hGdiff hGs β γ hβ hβ1

  obtain ⟨_, _, hid⟩ := DetectorMellin.detector_mellin_identity F U hU (D.omega u) hnp β
    ⟨hβ, hβ1⟩ γ 2 (by norm_num)
  have hS : smoothedSum F U β γ (D.omega u) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, DetectorMellin.mellinIntegrand F U (D.omega u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := hid

  have hcp : ∀ v : ℂ, (U : ℂ) ^ ((DetectorDef.r : ℂ) * v) =
      (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ v := by
    intro v
    rw [Complex.ofReal_cpow hU0.le, ← Complex.cpow_mul]
    all_goals
      rw [← Complex.ofReal_log hU0.le, ← Complex.ofReal_mul, Complex.ofReal_im]
      linarith [Real.pi_pos]
  have hpt : ∀ v : ℂ, 1 < ((β : ℂ) + (γ : ℂ) * Complex.I + v).re →
      DetectorMellin.mellinIntegrand F U (D.omega u) β γ v =
        Complex.Gamma v * (G ((β : ℂ) + (γ : ℂ) * Complex.I + v) *
          DetectorDef.D F U (D.omega u).character ((β : ℂ) + (γ : ℂ) * Complex.I + v)) *
          (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ v := by
    intro v hv
    unfold DetectorMellin.mellinIntegrand
    rw [hGs _ hv, hcp v]
    ring
  have hint_eq : (∫ t : ℝ, DetectorMellin.mellinIntegrand F U (D.omega u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
        (G ((β : ℂ) + (γ : ℂ) * Complex.I + (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          DetectorDef.D F U (D.omega u).character
            ((β : ℂ) + (γ : ℂ) * Complex.I + (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) *
        (((U ^ DetectorDef.r : ℝ)) : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    congr 1
    funext t
    apply hpt
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.mul_im]
    linarith

  have hE : DetectorDef.qExp * (1 - DetectorDef.c) + (1 - DetectorDef.c) / 2 +
      DetectorDef.r * (DetectorDef.c - β) ≤ -(3 / 1250 : ℝ) := by
    simp only [DetectorDef.qExp, DetectorDef.c, DetectorDef.r]
    linarith
  have hpow : U ^ (DetectorDef.qExp * (1 - DetectorDef.c) + (1 - DetectorDef.c) / 2 +
      DetectorDef.r * (DetectorDef.c - β) + ε) ≤ U ^ (-(3 / 1250 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
  have hm : ‖∫ t : ℝ, DetectorMellin.mellinIntegrand F U (D.omega u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * U ^ (-(3 / 1250 : ℝ) + ε) * (2 + |γ|) ^ A := by
    rw [hint_eq.trans hzc.2.2]
    exact (hbnd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)))
  have hπ : (1 : ℝ) ≤ ‖(2 * (Real.pi : ℂ))‖ := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hinv : ‖(2 * (Real.pi : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hπ
  rw [hS, norm_mul]
  calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ t : ℝ, DetectorMellin.mellinIntegrand F U (D.omega u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 1 * ‖∫ t : ℝ, DetectorMellin.mellinIntegrand F U (D.omega u) β γ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hm

end

end DedekindZetaZeroFree.Quantitative.DetectorShift
