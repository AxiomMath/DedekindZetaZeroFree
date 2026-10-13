module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.GammaZeroShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.GammaShiftNorm

noncomputable section

open MeasureTheory Complex DedekindZetaZeroFree NumberField

section GammaMoments

private lemma line_continuous (a : ℝ) (ha : a ∈ Set.Icc (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ))) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  intro n hn
  have hr := congrArg Complex.re hn
  simp at hr
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h] at hr; linarith [ha.2]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    linarith [ha.1]

private lemma uniform_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, a ∈ Set.Icc (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ)) →
    ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
  obtain ⟨M, hM, hbound⟩ := gamma_real_interval_bound (a := 1 / 100) (b := 3) (by norm_num)
  refine ⟨2 * M, by positivity, ?_⟩
  intro a ha t
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hzre : z.re = a := by simp [z]
  have hz : z ≠ 0 := by
    intro he
    have : a = 0 := by simpa [hzre] using congrArg Complex.re he
    linarith [ha.2]
  have hzn : (1 / 2 : ℝ) ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hzre, abs_of_neg (by linarith [ha.2])] at this
    linarith [ha.2]
  have he := gamma_norm_le_real (s := z + 1) (by simp [hzre]; linarith [ha.1])
  have hb := hbound (a + 1) ⟨by linarith [ha.1], by linarith [ha.2]⟩
  simp only [Complex.add_re, Complex.one_re, hzre] at he
  rw [Complex.Gamma_add_one z hz, norm_mul] at he
  have hh := he.trans hb
  have := norm_nonneg (Complex.Gamma z)
  dsimp only [z] at *
  nlinarith

private lemma envelope (A : ℝ) :
    ∃ m : ℕ, A + 2 < (m : ℝ) ∧ ∃ D : ℝ, 0 < D ∧
    ∀ a : ℝ, a ∈ Set.Icc (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ)) →
    ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * (1 + |t|) ^ (-(m : ℝ)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (A + 2)
  obtain ⟨B, hB, hBb⟩ := uniform_bound
  obtain ⟨C, hC, hCb⟩ := detector_sz_gamma_decay (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ))
    (by norm_num) m
  have hp : 0 < (2 : ℝ) ^ (m : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hcanc : (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-(m : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  refine ⟨m, hm, (B + C) * 2 ^ (m : ℝ), by positivity, ?_⟩
  intro a ha t
  have ht : 0 < 1 + |t| := by positivity
  have hn : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
  have hBC : B ≤ B + C := by linarith
  have hCC : C ≤ B + C := by linarith
  by_cases ht1 : |t| ≤ 1
  · have hr : (2 : ℝ) ^ (-(m : ℝ)) ≤ (1 + |t|) ^ (-(m : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht (by linarith) hn
    have hh : 1 ≤ 2 ^ (m : ℝ) * (1 + |t|) ^ (-(m : ℝ)) := by
      calc
        1 = 2 ^ (m : ℝ) * 2 ^ (-(m : ℝ)) := hcanc.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hr hp.le
    calc
      _ ≤ B := hBb a ha t
      _ ≤ B + C := hBC
      _ ≤ (B + C) * (2 ^ (m : ℝ) * (1 + |t|) ^ (-(m : ℝ))) :=
        le_mul_of_one_le_right (by positivity) hh
      _ = _ := by ring
  · have hu : 0 < |t| := by linarith
    have hr : (2 * |t|) ^ (-(m : ℝ)) ≤ (1 + |t|) ^ (-(m : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht (by linarith) hn
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg t)] at hr
    have hh : |t| ^ (-(m : ℝ)) ≤ 2 ^ (m : ℝ) * (1 + |t|) ^ (-(m : ℝ)) := by
      calc
        _ = (2 ^ (m : ℝ) * 2 ^ (-(m : ℝ))) * |t| ^ (-(m : ℝ)) := by rw [hcanc]; ring
        _ = 2 ^ (m : ℝ) * (2 ^ (-(m : ℝ)) * |t| ^ (-(m : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hr hp.le
    calc
      _ ≤ C * |t| ^ (-(m : ℝ)) := hCb a ha t (by linarith)
      _ ≤ C * (2 ^ (m : ℝ) * (1 + |t|) ^ (-(m : ℝ))) := mul_le_mul_of_nonneg_left hh hC.le
      _ ≤ (B + C) * (2 ^ (m : ℝ) * (1 + |t|) ^ (-(m : ℝ))) :=
        mul_le_mul_of_nonneg_right hCC (by positivity)
      _ = _ := by ring

private lemma weighted_bound (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (D a γ : ℝ)
    (hD : 0 < D)
    (he : ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * (1 + |t|) ^ (-(m : ℝ))) :
    ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A ≤
      (D * (2 + |γ|) ^ A) * (1 + |t|) ^ (A - (m : ℝ)) := by
  intro t
  have htri : 2 + |γ + t| ≤ (2 + |γ|) * (1 + |t|) := by
    have := abs_add_le γ t
    have : 0 ≤ |γ| * |t| := mul_nonneg (abs_nonneg γ) (abs_nonneg t)
    nlinarith [abs_nonneg t]
  have hp : (2 + |γ + t|) ^ A ≤ (2 + |γ|) ^ A * (1 + |t|) ^ A := by
    calc
      _ ≤ ((2 + |γ|) * (1 + |t|)) ^ A := Real.rpow_le_rpow (by positivity) htri hA
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  calc
    _ ≤ (D * (1 + |t|) ^ (-(m : ℝ))) * ((2 + |γ|) ^ A * (1 + |t|) ^ A) :=
      mul_le_mul (he t) hp (by positivity) (by positivity)
    _ = (D * (2 + |γ|) ^ A) * ((1 + |t|) ^ A * (1 + |t|) ^ (-(m : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2

theorem gamma_moment_shift (A : ℝ) (hA : 0 ≤ A) :
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ a : ℝ, a ∈ Set.Icc (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ)) → ∀ γ : ℝ,
        Integrable (fun t : ℝ =>
          ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) ∧
        (∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) ≤
          C_A * (2 + |γ|) ^ A := by
  obtain ⟨m, hm, D, hD, he⟩ := envelope A
  let w : ℝ → ℝ := fun t => (1 + |t|) ^ (A - (m : ℝ))
  have hw : Integrable w := by
    have hi := integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (m : ℝ) - A) (by simp; linarith : (Module.finrank ℝ ℝ : ℝ) < (m : ℝ) - A)
    simpa [w, Real.norm_eq_abs, neg_sub] using hi
  have hI : 0 ≤ ∫ t, w t := integral_nonneg (fun t => by dsimp [w]; positivity)
  refine ⟨D * ((∫ t, w t) + 1), by positivity, ?_⟩
  intro a ha γ
  have hb := weighted_bound A hA m D a γ hD (he a ha)
  have hf : Continuous (fun t : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) :=
    (line_continuous a ha).norm.mul
      ((continuous_const.add (continuous_const.add continuous_id).abs).rpow_const
        (fun t => Or.inr hA))
  have hg : Integrable (fun t => (D * (2 + |γ|) ^ A) * w t) := hw.const_mul _
  have hi : Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) := by
    apply hg.mono' hf.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb t
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t, (D * (2 + |γ|) ^ A) * w t := integral_mono hi hg hb
    _ = (D * (2 + |γ|) ^ A) * (∫ t, w t) := integral_const_mul _ _
    _ ≤ (D * (2 + |γ|) ^ A) * ((∫ t, w t) + 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end GammaMoments

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem gamma_shift_norm (D : FixedData S η) :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ z : ℂ, 1 < z.re → g z = Detector.idealLSeries F (D.omega u).character z) →
        ∀ β γ : ℝ, DetectorDef.σ₀ ≤ β → β ≤ 1 →
          ‖∫ t : ℝ,
              Complex.Gamma (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              (g (((β : ℂ) + (γ : ℂ) * Complex.I) +
                    (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
                DetectorDef.D F U (D.omega u).character (((β : ℂ) + (γ : ℂ) * Complex.I) +
                    (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I))) *
              ((U ^ DetectorDef.r : ℝ) : ℂ) ^
                (((DetectorDef.c - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ (DetectorDef.qExp * (1 - DetectorDef.c) + (1 - DetectorDef.c) / 2 +
                DetectorDef.r * (DetectorDef.c - β) + ε) * (2 + |γ|) ^ A_F := by
  obtain ⟨A, hA, hconv⟩ := Convex.convexity_detector_line D
  obtain ⟨Ci, hCi, hinv⟩ := DetectorInverseBound.detector_inverse_bound F
  obtain ⟨CA, hCA, hmom⟩ := gamma_moment_shift A hA
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨Cc, hCc, hc⟩ := hconv ε hε
  refine ⟨Ci * Cc * CA, by positivity, ?_⟩
  intro u hu U hU hUq hUq2 g hg hgs β γ hβ hβ1
  have hcv : DetectorDef.c = 1 / 100 := rfl
  have hσ : DetectorDef.σ₀ = 22 / 25 := rfl
  rw [hσ] at hβ
  have hU0 : 0 < U := by linarith
  set a : ℝ := DetectorDef.c - β with ha
  have haI : a ∈ Set.Icc (-(99 / 100 : ℝ)) (-(87 / 100 : ℝ)) := by
    rw [ha, hcv]; constructor <;> linarith
  obtain ⟨hint, hle⟩ := hmom a haI γ
  set E : ℝ := DetectorDef.qExp * (1 - DetectorDef.c)
  have hpt : ∀ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
      (g (((β : ℂ) + (γ : ℂ) * Complex.I) + ((a : ℂ) + (t : ℂ) * Complex.I)) *
        DetectorDef.D F U (D.omega u).character (((β : ℂ) + (γ : ℂ) * Complex.I) +
          ((a : ℂ) + (t : ℂ) * Complex.I))) *
      ((U ^ DetectorDef.r : ℝ) : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε)) *
        (‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) := by
    intro t
    have hs : ((β : ℂ) + (γ : ℂ) * Complex.I) + ((a : ℂ) + (t : ℂ) * Complex.I) =
        ((1 / 100 : ℝ) : ℂ) + ((γ + t : ℝ) : ℂ) * Complex.I := by
      rw [ha, hcv]; push_cast; ring
    have hs' : ((β : ℂ) + (γ : ℂ) * Complex.I) + ((a : ℂ) + (t : ℂ) * Complex.I) =
        ((DetectorDef.c : ℝ) : ℂ) + ((γ + t : ℝ) : ℂ) * Complex.I := by
      rw [hs, hcv]
    rw [hs']
    have h1 := hc u hu U hU hUq hUq2 g hg hgs (γ + t)
    rw [← hcv] at h1
    have h2 := hinv U hU (γ + t) (D.omega u)
    have hX : ‖((U ^ DetectorDef.r : ℝ) : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
        U ^ (DetectorDef.r * a) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hU0 _)]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self,
        add_zero]
      rw [← Real.rpow_mul hU0.le]
    have hexp : U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε) =
        U ^ E * U ^ ((99 / 200 : ℝ) + ε) * U ^ (DetectorDef.r * a) := by
      rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 1
      rw [hcv]; ring
    rw [hexp, norm_mul, norm_mul, norm_mul, hX]
    have hG := norm_nonneg (Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I))
    have hP : 0 ≤ (2 + |γ + t|) ^ A := by positivity
    have hX0 : 0 ≤ U ^ (DetectorDef.r * a) := by positivity
    calc _ ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
          ((Cc * U ^ ((99 / 200 : ℝ) + ε) * (2 + |γ + t|) ^ A) * (Ci * U ^ E)) *
          U ^ (DetectorDef.r * a) := by
          gcongr
      _ = _ := by ring
  have hmeas : Integrable (fun t : ℝ =>
      (Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε)) *
        (‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A)) :=
    hint.const_mul _
  refine (norm_integral_le_of_norm_le hmeas (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]
  have hK : 0 ≤ Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε) := by
    positivity
  calc _ ≤ (Ci * Cc * U ^ (E + (1 - DetectorDef.c) / 2 + DetectorDef.r * a + ε)) *
        (CA * (2 + |γ|) ^ A) := mul_le_mul_of_nonneg_left hle hK
    _ = _ := by ring
