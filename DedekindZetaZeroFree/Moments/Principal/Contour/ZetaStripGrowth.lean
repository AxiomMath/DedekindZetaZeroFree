module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalZetaStripGrowth

open DedekindZetaZeroFree Filter Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem strip_le_four (D : FixedData S η) (a ρ : ℝ) (ha : 0 < a) (ha4 : a ≤ 4)
    (hρ : 0 < ρ) :
    ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ 4 → ρ ≤ ‖s - 1‖ →
      ‖D.zetaSCont s‖ ≤ B * (2 + |s.im|) ^ d :=
  PrincipalNumerator.stripNumerator_bound_away_pole D.recipe a 4 ρ ha ha4 le_rfl hρ

private theorem strip_poly (D : FixedData S η) (a b ρ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hρ : 0 < ρ) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ρ ≤ ‖s - 1‖ →
      ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨K, hK, hKb⟩ := RightHeckeBounds.zetaSCont_norm_le_right D 4 (by norm_num)
  by_cases ha4 : a ≤ 4
  · obtain ⟨B, d, hB, hd, hbd⟩ := strip_le_four D a ρ ha ha4 hρ
    refine ⟨B * 2 ^ d + K, d, by positivity, hd, ?_⟩
    intro s h1 h2 hsep
    have hp : 0 ≤ (1 + |s.im|) ^ d := Real.rpow_nonneg (by positivity) d
    have hone : (1 : ℝ) ≤ (1 + |s.im|) ^ d :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) hd
    by_cases h4 : s.re ≤ 4
    · have h := hbd s h1 h4 hsep
      have hrp : (2 + |s.im|) ^ d ≤ 2 ^ d * (1 + |s.im|) ^ d := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hd
      have h3 : B * (2 + |s.im|) ^ d ≤ B * (2 ^ d * (1 + |s.im|) ^ d) :=
        mul_le_mul_of_nonneg_left hrp hB.le
      have h5 : (B * 2 ^ d + K) * (1 + |s.im|) ^ d
          = B * (2 ^ d * (1 + |s.im|) ^ d) + K * (1 + |s.im|) ^ d := by ring
      have h6 : 0 ≤ K * (1 + |s.im|) ^ d := mul_nonneg hK.le hp
      linarith
    · have h := hKb s (by linarith)
      have h7 : K ≤ K * (1 + |s.im|) ^ d := le_mul_of_one_le_right hK.le hone
      have h8 : 0 ≤ B * 2 ^ d * (1 + |s.im|) ^ d := by positivity
      nlinarith
  · refine ⟨K, 0, hK, le_rfl, ?_⟩
    intro s h1 _ _
    have h := hKb s (by linarith [not_le.mp ha4])
    simpa using h

theorem zetaSCont_strip_polynomial_bound (D : FixedData S η) (a b r : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → r ≤ ‖s - 1‖ →
      ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k :=
  strip_poly D a b r ha hab hr

theorem zetaSCont_high_height_bound (D : FixedData S η) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖D.zetaSCont s‖ ≤ C * |s.im| ^ k := by
  obtain ⟨C, k, hC, hk, h⟩ := strip_poly D a b 1 ha hab one_pos
  refine ⟨C * 2 ^ k, k, by positivity, hk, ?_⟩
  intro s h1 h2 him
  have hsep : 1 ≤ ‖s - 1‖ := by
    have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hx : 0 ≤ |s.im| := abs_nonneg _
  have hle : (1 + |s.im|) ^ k ≤ (2 * |s.im|) ^ k :=
    Real.rpow_le_rpow (by linarith) (by linarith) hk
  rw [Real.mul_rpow (by norm_num) hx] at hle
  have hC' := h s h1 h2 hsep
  calc ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := hC'
    _ ≤ C * (2 ^ k * |s.im| ^ k) := mul_le_mul_of_nonneg_left hle hC.le
    _ = C * 2 ^ k * |s.im| ^ k := by ring

theorem zetaSCont_bound_three_tenths_nine_tenths (D : FixedData S η) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, (3 / 10 : ℝ) ≤ s.re → s.re ≤ 9 / 10 → 1 ≤ |s.im| →
      ‖D.zetaSCont s‖ ≤ C * |s.im| ^ k :=
  zetaSCont_high_height_bound D (3 / 10) (9 / 10) (by norm_num) (by norm_num)

theorem zetaSCont_regularized_holomorphic (D : FixedData S η) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | 0 < s.re} ∧ g 1 = Spectral.RS D ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → g s = (s - 1) * D.zetaSCont s := by
  refine ⟨PrincipalNumerator.finiteDeletionRegularization D.recipe, ?_, ?_, ?_⟩
  · unfold PrincipalNumerator.finiteDeletionRegularization
    apply D.recipe.continuation.R_holo.mul
    apply DifferentiableOn.fun_finset_prod
    intro v hv
    exact ((((differentiable_id.neg).mul_const
      (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
        (D.recipe.target v.asIdeal)).differentiableOn.const_sub 1
  · rfl
  · intro s hs hne
    exact PrincipalNumerator.finiteDeletionRegularization_eq D.recipe s hs hne

private theorem reg_right (D : FixedData S η) (b K : ℝ) (hb0 : 0 < b) (hK : 0 ≤ K)
    (hKb : ∀ s : ℂ, 4 ≤ s.re → ‖D.zetaSCont s‖ ≤ K) (s : ℂ) (h4 : 4 ≤ s.re)
    (hb : s.re ≤ b) :
    ‖(s - 1) * D.zetaSCont s‖ ≤ K * (b + 1) * (1 + |s.im|) := by
  have hnorm : ‖s - 1‖ ≤ (b + 1) * (1 + |s.im|) := by
    have hr : |(s - 1).re| ≤ b + 1 := by
      rw [abs_le]; simp only [Complex.sub_re, Complex.one_re]; constructor <;> linarith
    have h' := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hi : |(s - 1).im| = |s.im| := by simp
    rw [hi] at h'
    nlinarith [abs_nonneg s.im]
  rw [norm_mul]
  have hs1 : ‖s - 1‖ * ‖D.zetaSCont s‖ ≤ ((b + 1) * (1 + |s.im|)) * K :=
    mul_le_mul hnorm (hKb s h4) (norm_nonneg _) (by positivity)
  nlinarith

theorem zetaSCont_regularized_strip_bound (D : FixedData S η) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ 1 →
      ‖(s - 1) * D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨K, hK, hKb⟩ := RightHeckeBounds.zetaSCont_norm_le_right D 4 (by norm_num)
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hbpos : 0 < b + 1 := by linarith
  by_cases ha4 : a ≤ 4
  · obtain ⟨B, d, hB, hd, hbd⟩ :=
      PrincipalNumerator.stripRegularization_bound D.recipe a 4 ha ha4 le_rfl
    refine ⟨B * 2 ^ d + K * (b + 1), d + 1, by positivity, by positivity, ?_⟩
    intro s h1 h2 hne
    have hre : 0 < s.re := lt_of_lt_of_le ha h1
    have hp : 0 ≤ (1 + |s.im|) ^ d := Real.rpow_nonneg (by positivity) d
    have hmono : (1 + |s.im|) ^ d ≤ (1 + |s.im|) ^ (d + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) (by linarith)
    have hp1 : 0 ≤ (1 + |s.im|) ^ (d + 1) := Real.rpow_nonneg (by positivity) _
    have hone : (1 : ℝ) ≤ (1 + |s.im|) ^ (d + 1) :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by linarith)
    have hK0 : 0 ≤ K * (b + 1) := by positivity
    by_cases h4 : s.re ≤ 4
    · have hfd := PrincipalNumerator.finiteDeletionRegularization_eq D.recipe s hre hne
      have h := hbd s h1 h4
      have heq : (s - 1) * D.zetaSCont s
          = PrincipalNumerator.finiteDeletionRegularization D.recipe s := hfd.symm
      rw [heq]
      have hrp : (2 + |s.im|) ^ d ≤ 2 ^ d * (1 + |s.im|) ^ d := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hd
      have h3 : B * (2 + |s.im|) ^ d ≤ B * (2 ^ d * (1 + |s.im|) ^ d) :=
        mul_le_mul_of_nonneg_left hrp hB.le
      have h4' : B * 2 ^ d * (1 + |s.im|) ^ d ≤ B * 2 ^ d * (1 + |s.im|) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      have h5 : (B * 2 ^ d + K * (b + 1)) * (1 + |s.im|) ^ (d + 1)
          = B * 2 ^ d * (1 + |s.im|) ^ (d + 1) + K * (b + 1) * (1 + |s.im|) ^ (d + 1) := by
        ring
      have h6 : 0 ≤ K * (b + 1) * (1 + |s.im|) ^ (d + 1) := mul_nonneg hK0 hp1
      nlinarith
    · have h := reg_right D b K hb0 hK.le (fun s hs => hKb s hs) s (by linarith [not_le.mp h4]) h2
      have hpow : (1 + |s.im|) ≤ (1 + |s.im|) ^ (d + 1) := by
        have := Real.rpow_le_rpow_of_exponent_le (x := 1 + |s.im|)
          (by linarith [abs_nonneg s.im]) (show (1 : ℝ) ≤ d + 1 by linarith)
        simpa using this
      have h7 : K * (b + 1) * (1 + |s.im|) ≤ K * (b + 1) * (1 + |s.im|) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hpow hK0
      have h8 : 0 ≤ B * 2 ^ d * (1 + |s.im|) ^ (d + 1) := by positivity
      have h9 : (B * 2 ^ d + K * (b + 1)) * (1 + |s.im|) ^ (d + 1)
          = B * 2 ^ d * (1 + |s.im|) ^ (d + 1) + K * (b + 1) * (1 + |s.im|) ^ (d + 1) := by
        ring
      nlinarith
  · refine ⟨K * (b + 1), 1, by positivity, by norm_num, ?_⟩
    intro s h1 h2 _
    have h := reg_right D b K hb0 hK.le (fun s hs => hKb s hs) s (by linarith [not_le.mp ha4]) h2
    rw [Real.rpow_one]
    exact h

end DedekindZetaZeroFree.Quantitative.PrincipalZetaStripGrowth
