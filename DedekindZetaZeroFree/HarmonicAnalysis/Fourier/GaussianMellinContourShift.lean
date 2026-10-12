module

public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

namespace DedekindZetaZeroFree

section
open Complex MeasureTheory Set
open scoped Real

private theorem weighted_strip (G : ℂ → ℂ) (x a b : ℝ) (hx : 0 < x) (ha : 1 < a) (hab : a < b)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 < s.re})
    (hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc a b, ∀ t : ℝ,
      ‖G ((r : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, (x : ℂ) ^ ((a : ℂ) + t * I) * G ((a : ℂ) + t * I)) =
      (∫ t : ℝ, (x : ℂ) ^ ((b : ℂ) + t * I) * G ((b : ℂ) + t * I)) ∧
    ∀ r ∈ Icc a b, Integrable (fun t : ℝ => (x : ℂ) ^ ((r : ℂ) + t * I) * G ((r : ℂ) + t * I)) := by
  obtain ⟨C, hC, hCb⟩ := hdecay
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_const_rpow hx.ne').continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hpow : ∀ r ∈ Icc a b, x ^ r ≤ B := by
    intro r hr
    exact (le_abs_self _).trans ((hB₀ r hr).trans (le_max_left _ _))
  have hhol : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s * G s) {s : ℂ | 1 < s.re} :=
    (differentiableOn_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).mul hG
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hstrip : comparisonClosedStrip a b ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    exact ha.trans_le hs.1
  have hbound : ∀ s ∈ comparisonClosedStrip a b,
      ‖(x : ℂ) ^ s * G s‖ ≤ (B * (2 * C)) * (1 + |s.im|) ^ (-2 : ℝ) := by
    intro s hs
    have hg : ‖G s‖ ≤ C / (1 + s.im ^ 2) := by
      simpa only [re_add_im] using hCb s.re hs s.im
    have hp : ‖(x : ℂ) ^ s‖ ≤ B := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]
      exact hpow s.re hs
    have hd : C / (1 + s.im ^ 2) ≤ (2 * C) * (1 + |s.im|) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |s.im|), Real.rpow_two, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have habs : |s.im| ^ 2 = s.im ^ 2 := sq_abs _
      nlinarith [sq_nonneg (|s.im| - 1)]
    calc
      ‖(x : ℂ) ^ s * G s‖ = ‖(x : ℂ) ^ s‖ * ‖G s‖ := norm_mul _ _
      _ ≤ B * (C / (1 + s.im ^ 2)) := mul_le_mul hp hg (norm_nonneg _) hB
      _ ≤ B * ((2 * C) * (1 + |s.im|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left hd hB
      _ = _ := by ring
  exact ⟨verticalIntegral_eq_of_strip_decay a b (B * (2 * C)) _ _ hab (by positivity)
      hopen hstrip hhol hbound,
    verticalIntegral_integrable_of_strip_decay a b (B * (2 * C)) _ _ hab (by positivity)
      hopen hstrip hhol hbound⟩
private theorem reflected_line (c t : ℝ) :
    -(((-c : ℝ) : ℂ) + t * I) = (c : ℂ) + (-t : ℝ) * I := by
  push_cast
  ring

private theorem reflected_mellin (G : ℂ → ℂ) (c x : ℝ) :
    mellinInv (-c) (fun z : ℂ => G (-z)) x =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) * G ((c : ℂ) + t * I) := by
  unfold mellinInv
  simp_rw [reflected_line, smul_eq_mul]
  rw [integral_neg_eq_self (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) * G ((c : ℂ) + t * I)) volume]

end

attribute [-instance] instCommCStarAlgebraComplex in

theorem mellin_gaussian_contour_shift
    (G : ℂ → ℂ) (g : ℝ → ℂ)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 < s.re})
    (hdecay : ∀ a b : ℝ, 1 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, ∀ t : ℝ,
        ‖G ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2))
    (hinv : ∀ x : ℝ, 0 < x →
      g x = mellinInv (-2) (fun z : ℂ => G (-z)) x) :
    ∀ c : ℝ, 1 < c → ∀ x : ℝ, 0 < x →
      g x = mellinInv (-c) (fun z : ℂ => G (-z)) x ∧
      MeasureTheory.Integrable (fun t : ℝ =>
        (x : ℂ) ^ (-(((-c : ℝ) : ℂ) + t * Complex.I)) •
          G (-(((-c : ℝ) : ℂ) + t * Complex.I))) := by
  intro c hc x hx
  let a := (1 + min 2 c) / 2
  have hmin : 1 < min 2 c := lt_min (by norm_num) hc
  have ha : 1 < a := by dsimp [a]; linarith
  have ha2 : a < 2 := by have := min_le_left (2 : ℝ) c; dsimp [a]; linarith
  have hac : a < c := by have := min_le_right (2 : ℝ) c; dsimp [a]; linarith
  obtain ⟨heq2, _⟩ := weighted_strip G x a 2 hx ha ha2 hG (hdecay a 2 ha ha2.le)
  obtain ⟨heqc, hi⟩ := weighted_strip G x a c hx ha hac hG (hdecay a c ha hac.le)
  constructor
  · rw [hinv x hx]
    change mellinInv (-(2 : ℝ)) (fun z : ℂ => G (-z)) x = _
    rw [reflected_mellin, reflected_mellin, ← heq2, heqc]
  · simpa only [reflected_line, smul_eq_mul] using (hi c ⟨hac.le, le_rfl⟩).comp_neg

end DedekindZetaZeroFree
