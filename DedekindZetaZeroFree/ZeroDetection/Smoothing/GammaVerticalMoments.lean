module

public import DedekindZetaZeroFree.Analysis.GammaStripDecay

@[expose] public section

namespace DedekindZetaZeroFree

open MeasureTheory

private lemma admissible_bounds (a : ℝ)
    (ha : a ∈ Set.Icc (-(1 / 2 : ℝ)) (-(124 / 250 : ℝ)) ∪ ({2} : Set ℝ)) :
    -(1/2:ℝ) ≤ a ∧ a ≤ 2 ∧ ∀ n : ℕ, a ≠ -(n:ℝ) := by
  rcases ha with ha | ha
  · refine ⟨ha.1, by linarith [ha.2], ?_⟩
    intro n hn
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : n = 0 ∨ 1 ≤ n := Nat.eq_zero_or_pos n
    rcases hn1 with hn1 | hn1
    · simp [hn1] at hn
      linarith [ha.2]
    · have : (1:ℝ) ≤ n := by exact_mod_cast hn1
      linarith [ha.1]
  · simp only [Set.mem_singleton_iff] at ha
    subst a
    refine ⟨by norm_num, le_rfl, ?_⟩
    intro n hn
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
private lemma line_continuous (a : ℝ)
    (ha : a ∈ Set.Icc (-(1 / 2 : ℝ)) (-(124 / 250 : ℝ)) ∪ ({2} : Set ℝ)) :
    Continuous (fun t : ℝ => Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  intro n hn
  have hr := congrArg Complex.re hn
  simp at hr
  exact (admissible_bounds a ha).2.2 n hr
private lemma uniform_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ,
    a ∈ Set.Icc (-(1 / 2 : ℝ)) (-(124 / 250 : ℝ)) ∪ ({2} : Set ℝ) →
    ∀ t : ℝ, ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B := by
  obtain ⟨M,hM,hbound⟩ := gamma_real_interval_bound (b := 3) (by norm_num : (0:ℝ)<1/2)
  refine ⟨3*M, by positivity, ?_⟩
  intro a ha t
  rcases ha with ha | ha
  · let z : ℂ := (a:ℂ)+(t:ℂ)*Complex.I
    have hzre : z.re = a := by simp [z]
    have hz : z ≠ 0 := by
      intro he
      have : a = 0 := by simpa [hzre] using congrArg Complex.re he
      linarith [ha.2]
    have hzn : (1/3:ℝ) ≤ ‖z‖ := by
      have := Complex.abs_re_le_norm z
      rw [hzre, abs_of_neg (by linarith [ha.2])] at this
      linarith [ha.2]
    have he := gamma_norm_le_real (s := z+1) (by simp [hzre]; linarith [ha.1])
    have hb := hbound (a+1) ⟨by linarith [ha.1], by linarith [ha.2]⟩
    simp only [Complex.add_re, Complex.one_re, hzre] at he
    rw [Complex.Gamma_add_one z hz, norm_mul] at he
    have hh := he.trans hb
    have := norm_nonneg (Complex.Gamma z)
    dsimp only [z] at *
    nlinarith
  · simp only [Set.mem_singleton_iff] at ha
    subst a
    have he := gamma_norm_le_real (s := (2:ℂ)+(t:ℂ)*Complex.I) (by norm_num)
    have hb := hbound 2 (by norm_num)
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.natCast_re] at he
    exact (he.trans hb).trans (by linarith : M ≤ 3*M)

private lemma envelope (A : ℝ) :
    ∃ m : ℕ, A+2 < (m:ℝ) ∧ ∃ D : ℝ, 0 < D ∧
    ∀ a : ℝ, a ∈ Set.Icc (-(1 / 2 : ℝ)) (-(124 / 250 : ℝ)) ∪ ({2} : Set ℝ) →
    ∀ t : ℝ, ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D * (1+|t|)^(-(m:ℝ)) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (A+2)
  obtain ⟨B,hB,hBb⟩ := uniform_bound
  obtain ⟨C,hC,hCb⟩ := detector_sz_gamma_decay (-(1/2:ℝ)) 2 (by norm_num) m
  have hp : 0 < (2:ℝ)^(m:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hcanc : (2:ℝ)^(m:ℝ) * (2:ℝ)^(-(m:ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  refine ⟨m,hm,(B+C)*2^(m:ℝ), by positivity, ?_⟩
  intro a ha t
  have ht : 0 < 1+|t| := by positivity
  have hn : -(m:ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
  have hBC : B ≤ B+C := by linarith
  have hCC : C ≤ B+C := by linarith
  by_cases ht1 : |t| ≤ 1
  · have hr : (2:ℝ)^(-(m:ℝ)) ≤ (1+|t|)^(-(m:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht (by linarith) hn
    have hh : 1 ≤ 2^(m:ℝ)*(1+|t|)^(-(m:ℝ)) := by
      calc
        1 = 2^(m:ℝ)*2^(-(m:ℝ)) := hcanc.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hr hp.le
    calc
      _ ≤ B := hBb a ha t
      _ ≤ B+C := hBC
      _ ≤ (B+C)*(2^(m:ℝ)*(1+|t|)^(-(m:ℝ))) :=
        le_mul_of_one_le_right (by positivity) hh
      _ = _ := by ring
  · have hu : 0 < |t| := by linarith
    have hr : (2*|t|)^(-(m:ℝ)) ≤ (1+|t|)^(-(m:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht (by linarith) hn
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (abs_nonneg t)] at hr
    have hh : |t|^(-(m:ℝ)) ≤ 2^(m:ℝ)*(1+|t|)^(-(m:ℝ)) := by
      calc
        _ = (2^(m:ℝ)*2^(-(m:ℝ)))*|t|^(-(m:ℝ)) := by rw [hcanc]; ring
        _ = 2^(m:ℝ)*(2^(-(m:ℝ))*|t|^(-(m:ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hr hp.le
    calc
      _ ≤ C*|t|^(-(m:ℝ)) := hCb a ⟨(admissible_bounds a ha).1, (admissible_bounds a ha).2.1⟩ t (by linarith)
      _ ≤ C*(2^(m:ℝ)*(1+|t|)^(-(m:ℝ))) := mul_le_mul_of_nonneg_left hh hC.le
      _ ≤ (B+C)*(2^(m:ℝ)*(1+|t|)^(-(m:ℝ))) :=
        mul_le_mul_of_nonneg_right hCC (by positivity)
      _ = _ := by ring

private lemma weighted_bound (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (D a γ : ℝ)
    (hD : 0 < D)
    (he : ∀ t : ℝ, ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D*(1+|t|)^(-(m:ℝ))) :
    ∀ t : ℝ, ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ * (2+|γ+t|)^A ≤
      (D*(2+|γ|)^A) * (1+|t|)^(A-(m:ℝ)) := by
  intro t
  have htri : 2+|γ+t| ≤ (2+|γ|)*(1+|t|) := by
    have := abs_add_le γ t
    have : 0 ≤ |γ| * |t| := mul_nonneg (abs_nonneg γ) (abs_nonneg t)
    nlinarith [abs_nonneg t]
  have hp : (2+|γ+t|)^A ≤ (2+|γ|)^A * (1+|t|)^A := by
    calc
      _ ≤ ((2+|γ|)*(1+|t|))^A := Real.rpow_le_rpow (by positivity) htri hA
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  calc
    _ ≤ (D*(1+|t|)^(-(m:ℝ))) * ((2+|γ|)^A * (1+|t|)^A) :=
      mul_le_mul (he t) hp (by positivity) (by positivity)
    _ = (D*(2+|γ|)^A) * ((1+|t|)^A * (1+|t|)^(-(m:ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2

theorem detector_sz_gamma_moments (A : ℝ) (hA : 0 ≤ A) :
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ a : ℝ, a ∈ Set.Icc (-(1 / 2 : ℝ)) (-(124 / 250 : ℝ)) ∪ ({2} : Set ℝ) →
        ∀ γ : ℝ,
          Integrable (fun t : ℝ =>
            ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
              (2 + |γ + t|) ^ A) ∧
          (∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
              (2 + |γ + t|) ^ A) ≤ C_A * (2 + |γ|) ^ A := by
  obtain ⟨m,hm,D,hD,he⟩ := envelope A
  let w : ℝ → ℝ := fun t => (1+|t|)^(A-(m:ℝ))
  have hw : Integrable w := by
    have hi := integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (m:ℝ)-A) (by simp; linarith : (Module.finrank ℝ ℝ : ℝ) < (m:ℝ)-A)
    simpa [w, Real.norm_eq_abs, neg_sub] using hi
  have hI : 0 ≤ ∫ t, w t := integral_nonneg (fun t => by dsimp [w]; positivity)
  refine ⟨D*((∫ t, w t)+1), by positivity, ?_⟩
  intro a ha γ
  have hb := weighted_bound A hA m D a γ hD (he a ha)
  have hf : Continuous (fun t : ℝ =>
      ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ * (2+|γ+t|)^A) :=
    (line_continuous a ha).norm.mul
      ((continuous_const.add (continuous_const.add continuous_id).abs).rpow_const
        (fun t => Or.inr hA))
  have hg : Integrable (fun t => (D*(2+|γ|)^A)*w t) := hw.const_mul _
  have hi : Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ * (2+|γ+t|)^A) := by
    apply hg.mono' hf.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb t
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t, (D*(2+|γ|)^A)*w t := integral_mono hi hg hb
    _ = (D*(2+|γ|)^A)*(∫ t, w t) := integral_const_mul _ _
    _ ≤ (D*(2+|γ|)^A)*((∫ t, w t)+1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end DedekindZetaZeroFree
