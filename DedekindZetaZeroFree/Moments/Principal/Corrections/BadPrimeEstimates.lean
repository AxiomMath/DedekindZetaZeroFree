module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.Definitions

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums
open Filter Set Metric

private theorem normal_holomorphic {ι : Type*} (g : ι → Coordinates → ℂ)
    (hg : ∀ i, Differentiable ℂ (g i)) (U : Set Coordinates) (hU : IsOpen U)
    (hM : ∀ K : Set Coordinates, K ⊆ U → IsCompact K →
      ∃ M : ι → ℝ, Summable M ∧ ∀ i x, x ∈ K → ‖g i x‖ ≤ M i) :
    DifferentiableOn ℂ (fun x => ∑' i, g i x) U := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨M, hMs, hMb⟩ := hM (closedBall x r) hsub (isCompact_closedBall x r)
  have hhalf : 0 < r / 2 := by positivity
  have hinside {y : Coordinates} (hy : y ∈ ball x (r / 2)) : y ∈ closedBall x r := by
    exact ball_subset_closedBall (ball_subset_ball (by linarith) hy)
  have hderiv : ∀ i y, y ∈ ball x (r / 2) → ‖fderiv ℂ (g i) y‖ ≤ (4 / r) * M i := by
    intro i y hy
    have hball : ball y (r / 2) ⊆ closedBall x r := by
      intro z hz
      apply mem_closedBall.mpr
      have := dist_triangle z y x
      have hz' := mem_ball.mp hz
      have hy' := mem_ball.mp hy
      linarith
    have hnorm := Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((hg i).differentiableOn : DifferentiableOn ℂ (g i) (ball y (r / 2)))
      (R₂ := 2 * M i) (by
        intro z hz
        apply mem_closedBall.mpr
        calc
          dist (g i z) (g i y) ≤ ‖g i z‖ + ‖g i y‖ := by simpa only [dist_eq_norm_sub] using norm_sub_le (g i z) (g i y)
          _ ≤ 2 * M i := by linarith [hMb i z (hball hz), hMb i y (hinside hy)]) hhalf
    convert hnorm using 1 <;> field_simp <;> ring
  have hs := hasFDerivAt_tsum_of_isPreconnected (hMs.mul_left (4 / r)) isOpen_ball
    (convex_ball x (r / 2)).isPreconnected
    (fun i y _ => (hg i y).hasFDerivAt) hderiv
    (mem_ball_self hhalf)
    (Summable.of_norm_bounded hMs (fun i => hMb i x (mem_closedBall_self hr.le)))
    (mem_ball_self hhalf)
  exact hs.differentiableAt.differentiableWithinAt

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma Q_pos (p : ExteriorPrime A) : 0 < Q p := A.exteriorNorm_pos (primeIdeal p)

private lemma two_le_Q (p : ExteriorPrime A) : 2 ≤ Q p :=
  idealNorm_prime_ge_two (primeIdeal p).val (by simpa [primeIdeal] using p.val.prime)

private lemma norm_qPower (p : ExteriorPrime A) (s : ℂ) :
    ‖qPower p s‖ = (Q p) ^ s.re := by
  rw [qPower, Complex.norm_exp, Real.rpow_def_of_pos (Q_pos p)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private lemma norm_vartheta (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ‖vartheta C p‖ = 1 := by
  rw [vartheta]
  exact Circle.norm_coe _

private lemma norm_gammaTwo (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ‖gammaTwo C p‖ ≤ 1 := by
  rw [gammaTwo]
  exact NormalizedProbe.PrincipalData.norm_idealGauss_le_one A σ hS (primeIdeal p)
    (generator C p) (generator_generates C p) 2

private lemma region_lower (x : Coordinates) (hx : x ∈ Omega) :
    (99799 / 100000 : ℝ) < x.1.re ∧ (299 / 100000 : ℝ) < x.2.1.re ∧
      (15999 / 100000 : ℝ) < x.2.2.re := by
  rcases hx with h | h <;> rcases h with ⟨ha, hb, hc⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

private lemma norm_series_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (e : Fin 2) (l k m : ℕ) (x : Coordinates) :
    ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
      ‖Ctk C p (e.val + 3 * l) k (j.val + 6 * m)‖ *
        (Q p) ^ (-(e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re -
          6 * (m : ℝ) * x.2.2.re) := by
  unfold seriesTerm
  simp only [norm_mul, norm_pow, norm_vartheta, one_pow, mul_one,
    norm_zpow, θ.property, one_zpow, norm_qPower]
  have he : ‖gammaTwo C p‖ ^ e.val ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_gammaTwo C p)
  have hexp : (-(e.val : ℂ) * (1 / 2 + x.1) - (l : ℂ) * (1 + 3 * x.1) -
      (k : ℂ) * x.2.1 - 6 * (m : ℂ) * x.2.2).re =
      -(e.val : ℝ) * (1 / 2 + x.1.re) - (l : ℝ) * (1 + 3 * x.1.re) -
      (k : ℝ) * x.2.1.re - 6 * (m : ℝ) * x.2.2.re := by simp
  rw [hexp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) he) (Real.rpow_nonneg (Q_pos p).le _)

private lemma shell_bound (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (ht : 0 < t) (hk : k ≤ 1) :
    ‖Ctk C p t k J‖ ≤ (Q p) ^ ((t : ℝ) + (k : ℝ) / 2) := by
  interval_cases k
  · simpa only [Nat.cast_zero, zero_div, add_zero, Real.rpow_natCast] using
      norm_Ctk_zero_le C p t J ht
  · simpa using norm_Ctk_one_le C p t J ht

private lemma shell_exponent (e : Fin 2) (l k m : ℕ) (ht : 0 < e.val + 3 * l)
    (hk : k ≤ 1) (x : Coordinates) (hx : x ∈ Omega) :
    ((e.val + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2 - (e.val : ℝ) * (1 / 2 + x.1.re) -
      (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re - 6 * (m : ℝ) * x.2.2.re ≤
      -(1 / 4000 : ℝ) - (l : ℝ) / 4 - (m : ℝ) / 4 := by
  obtain ⟨ha, hb, hc⟩ := region_lower x hx
  have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg _
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have he := e.isLt
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  interval_cases k <;> interval_cases e.val <;> simp only [Nat.cast_zero, Nat.cast_one] at *
  all_goals
    by_cases h : l = 0
    · subst l
      simp only [Nat.cast_zero] at *
      nlinarith
    · have h : (1 : ℝ) ≤ l := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      nlinarith

 def ratio : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ))

private lemma ratio_pos : 0 < ratio := Real.rpow_pos_of_pos (by norm_num) _

private lemma ratio_lt_one : ratio < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

 def weight (i : Fin 2 × ℕ × ℕ × ℕ) : ℝ :=
  4 * ratio ^ i.2.1 * (1 / 2 : ℝ) ^ i.2.2.1 * ratio ^ i.2.2.2

private lemma weight_nonneg (i : Fin 2 × ℕ × ℕ × ℕ) : 0 ≤ weight i := by
  have := ratio_pos
  unfold weight
  positivity

private lemma weight_summable : Summable weight := by
  have := ratio_pos
  have hr : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one ratio_pos.le ratio_lt_one
  have hh : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hkm := hh.mul_of_nonneg hr (fun n => by positivity) (fun n => by positivity)
  have hlkm := hr.mul_of_nonneg hkm (fun n => by positivity) (fun n => by dsimp; positivity)
  have h := (Summable.of_finite : Summable (fun _ : Fin 2 => (4 : ℝ))).mul_of_nonneg hlkm
    (fun _ => by norm_num) (fun n => by dsimp; positivity)
  change Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
    4 * ratio ^ i.2.1 * (1 / 2 : ℝ) ^ i.2.2.1 * ratio ^ i.2.2.2)
  simpa only [mul_assoc] using h

private lemma decay_split (p : ExteriorPrime A) (l m : ℕ) :
    (Q p) ^ (-(1 / 4000 : ℝ) - (l : ℝ) / 4 - (m : ℝ) / 4) ≤
      (Q p) ^ (-(1 / 4000 : ℝ)) * ratio ^ l * ratio ^ m := by
  have hq := Q_pos p
  have hpow (n : ℕ) : (Q p) ^ (-(n : ℝ) / 4) ≤ ratio ^ n := by
    calc
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) / 4) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_Q p) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      _ = ratio ^ n := by
        rw [ratio, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  simp only [sub_eq_add_neg, Real.rpow_add hq, neg_div]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hpow l) (Real.rpow_nonneg hq.le _))
    (by simpa only [neg_div] using hpow m) (Real.rpow_nonneg hq.le _) (by have := ratio_pos; positivity)

private lemma positive_term_bound (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (e : Fin 2) (l k m : ℕ) (ht : 0 < e.val + 3 * l)
    (x : Coordinates) (hx : x ∈ Omega) :
    ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
      (Q p) ^ (-(1 / 4000 : ℝ)) * (weight (e, l, k, m) / 2) := by
  have hr := ratio_pos
  by_cases hk : k ≤ 1
  · have h := (norm_series_le C p j θ e l k m x).trans
      (mul_le_mul_of_nonneg_right (shell_bound C p _ _ _ ht hk)
        (Real.rpow_nonneg (Q_pos p).le _))
    rw [← Real.rpow_add (Q_pos p)] at h
    have h' := Real.rpow_le_rpow_of_exponent_le (x := Q p) (by linarith [two_le_Q p])
      (shell_exponent e l k m ht hk x hx)
    have hex : ((e.val + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2 +
        (-(e.val : ℝ) * (1 / 2 + x.1.re) - (l : ℝ) * (1 + 3 * x.1.re) -
          (k : ℝ) * x.2.1.re - 6 * (m : ℝ) * x.2.2.re) =
        ((e.val + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2 - (e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re - 6 * (m : ℝ) * x.2.2.re := by ring
    rw [hex] at h
    have h'' := h.trans (h'.trans (decay_split p l m))
    interval_cases k <;> unfold weight <;> simp only [pow_zero, pow_one] <;>
      nlinarith [mul_nonneg (mul_nonneg (Real.rpow_nonneg (Q_pos p).le (-(1 / 4000 : ℝ)))
        (pow_nonneg hr.le l)) (pow_nonneg hr.le m)]
  · have hk : 2 ≤ k := by omega
    simp only [seriesTerm, Ctk_eq_zero_of_two_le C p _ _ _ ht hk, mul_zero, zero_mul,
      norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (Q_pos p).le _) (div_nonneg (weight_nonneg _) (by norm_num))

private lemma norm_V_bound (p : ExteriorPrime A) (x : Coordinates) (hx : x ∈ Omega) :
    ‖V p x.2.2‖ ≤ ratio := by
  rw [V, norm_qPower]
  have h := (region_lower x hx).2.2
  have he : (-6 * x.2.2).re ≤ -(1 / 4 : ℝ) := by simp; linarith
  exact (Real.rpow_le_rpow_of_exponent_le (by linarith [two_le_Q p]) he).trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_Q p) (by norm_num))

private lemma zero_term (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (k m : ℕ) (x : Coordinates) :
    seriesTerm C p j θ 0 0 k m x.1 x.2.1 x.2.2 =
      if k = 0 then V p x.2.2 ^ m else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [seriesTerm, Fin.val_zero, pow_zero, Nat.mul_zero, Nat.add_zero,
      Int.ofNat_zero, sub_zero, zero_sub, zpow_zero, one_mul, Ctk_zero_zero, zero_mul,
      sub_self, sub_zero, if_true]
    rw [V, qPower, qPower, ← Complex.exp_nat_mul]
    norm_num only [mul_zero, neg_zero, zpow_zero, one_mul, mul_one, Nat.cast_zero,
      zero_mul, sub_zero, zero_sub]
    congr 1
    push_cast
    ring
  · have hJ : j.val + 6 * m ≠ 0 := by omega
    unfold seriesTerm
    rw [show (0 : Fin 2).val + 3 * 0 = 0 by rfl,
      Ctk_zero_pos C p k _ (Nat.pos_of_ne_zero hk), if_neg hJ]
    simp only [mul_zero, zero_mul, if_neg hk]

private lemma term_bound (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (i : Fin 2 × ℕ × ℕ × ℕ)
    (x : Coordinates) (hx : x ∈ Omega) :
    ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤ weight i / 2 := by
  have hr := ratio_pos
  by_cases ht : 0 < i.1.val + 3 * i.2.1
  · apply (positive_term_bound C p j θ _ _ _ _ ht x hx).trans
    exact mul_le_of_le_one_left (div_nonneg (weight_nonneg _) (by norm_num))
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [two_le_Q p]) (by norm_num))
  · have he : i.1 = 0 := Fin.ext (by simp; omega)
    have hl : i.2.1 = 0 := by omega
    rw [he, hl, zero_term C p j hj θ]
    split_ifs with hk
    · rw [norm_pow]
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_V_bound p x hx) i.2.2.2
      simp only [weight, he, hl, hk, pow_zero, mul_one]
      nlinarith [pow_nonneg hr.le i.2.2.2]
    · simp only [norm_zero]
      exact div_nonneg (weight_nonneg _) (by norm_num)

theorem bad_factor_normal_majorants (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) :
    ∀ K : Set Coordinates, K ⊆ Omega → IsCompact K →
      ∃ M : (Fin 2 × ℕ × ℕ × ℕ) → ℝ, Summable M ∧
        ∀ (i : Fin 2 × ℕ × ℕ × ℕ) (x : Coordinates), x ∈ K →
          ‖(1 - V p x.2.2) *
            seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
            M i := by
  intro K hKO _
  refine ⟨weight, weight_summable, ?_⟩
  intro i x hx
  have hV : ‖1 - V p x.2.2‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖V p x.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by have h := (norm_V_bound p x (hKO hx)).trans ratio_lt_one.le; simp only [norm_one]; linarith
  rw [norm_mul]
  have ht := term_bound C p j hj θ i x (hKO hx)
  nlinarith [norm_nonneg (seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2)]

theorem bad_factor_holomorphic (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) :
    DifferentiableOn ℂ
      (fun x : Coordinates => badFactor C p j θ x.1 x.2.1 x.2.2) Omega := by
  have hg : ∀ i : Fin 2 × ℕ × ℕ × ℕ, Differentiable ℂ
      (fun x : Coordinates => (1 - V p x.2.2) *
        seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2) := by
    intro i
    unfold V seriesTerm qPower
    fun_prop
  have h := normal_holomorphic _ hg Omega isOpen_Omega
    (bad_factor_normal_majorants C p j hj θ)
  simpa only [badFactor, f, tsum_mul_left] using h

 def baseline (p : ExteriorPrime A) (x : Coordinates)
    (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  if i.1 = 0 ∧ i.2.1 = 0 ∧ i.2.2.1 = 0 then V p x.2.2 ^ i.2.2.2 else 0

private lemma remainder_bound (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (x : Coordinates) (hx : x ∈ Omega)
    (i : Fin 2 × ℕ × ℕ × ℕ) :
    ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2 - baseline p x i‖ ≤
      (Q p) ^ (-(1 / 4000 : ℝ)) * (weight i / 2) := by
  by_cases ht : 0 < i.1.val + 3 * i.2.1
  · have hb : baseline p x i = 0 := by
      unfold baseline
      split_ifs with h
      · have := congrArg Fin.val h.1
        simp only [Fin.val_zero] at this
        omega
      · rfl
    rw [hb, sub_zero]
    exact positive_term_bound C p j θ _ _ _ _ ht x hx
  · have he : i.1 = 0 := Fin.ext (by simp; omega)
    have hl : i.2.1 = 0 := by omega
    rw [he, hl, zero_term C p j hj θ]
    simp only [baseline, he, hl, true_and]
    split_ifs <;> simp only [sub_self, norm_zero] <;>
      exact mul_nonneg (Real.rpow_nonneg (Q_pos p).le _) (div_nonneg (weight_nonneg _) (by norm_num))

private lemma baseline_norm_bound (p : ExteriorPrime A) (x : Coordinates) (hx : x ∈ Omega)
    (i : Fin 2 × ℕ × ℕ × ℕ) : ‖baseline p x i‖ ≤ weight i / 2 := by
  have hr := ratio_pos
  unfold baseline
  split_ifs with h
  · rcases h with ⟨he, hl, hk⟩
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_V_bound p x hx) i.2.2.2
    simp only [weight, he, hl, hk, pow_zero, mul_one]
    nlinarith [pow_nonneg hr.le i.2.2.2]
  · simp only [norm_zero]
    exact div_nonneg (weight_nonneg _) (by norm_num)

private lemma baseline_sum (p : ExteriorPrime A) (x : Coordinates) (hx : x ∈ Omega) :
    (1 - V p x.2.2) * (∑' i, baseline p x i) = 1 := by
  have hs : Summable (baseline p x) := Summable.of_norm_bounded
    (weight_summable.div_const 2) (baseline_norm_bound p x hx)
  rw [hs.tsum_prod]
  have hs0 := hs.prod_factor (0 : Fin 2)
  have hs00 := hs0.prod_factor (0 : ℕ)
  simp only [baseline]
  rw [tsum_eq_single (0 : Fin 2)]
  · simp only [ite_true]
    rw [show (∑' c : ℕ × ℕ × ℕ, if True ∧ c.1 = 0 ∧ c.2.1 = 0 then V p x.2.2 ^ c.2.2 else 0) =
      ∑' l : ℕ, ∑' c : ℕ × ℕ, baseline p x (0, l, c) by
        simpa only [baseline, Fin.val_zero] using hs0.tsum_prod]
    simp only [baseline, true_and]
    rw [tsum_eq_single (0 : ℕ)]
    · simp only [ite_true]
      rw [show (∑' c : ℕ × ℕ, if True ∧ c.1 = 0 then V p x.2.2 ^ c.2 else 0) =
        ∑' k : ℕ, ∑' m : ℕ, baseline p x (0, 0, k, m) by
          simpa only [baseline, true_and] using hs00.tsum_prod]
      simp only [baseline, true_and]
      rw [tsum_eq_single (0 : ℕ)]
      · simp only [ite_true]
        exact (summable_geometric_of_norm_lt_one ((norm_V_bound p x hx).trans_lt ratio_lt_one)).one_sub_mul_tsum_pow
      · intro k hk
        simp [hk]
    · intro l hl
      simp [hl]
  · intro e he
    simp [he]

theorem bad_factor_uniform_estimate (C : A.GeneralArithmeticContext σ η hS) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ExteriorPrime A) (j : Fin 6), j.val ≠ 0 →
        ∀ (θ : {θ : ℂ // ‖θ‖ = 1}) (x : Coordinates), x ∈ Omega →
          ‖badFactor C p j θ x.1 x.2.1 x.2.2 - 1‖ ≤
            B * Real.rpow (Q p) (-(1 / 4000 : ℝ)) := by
  refine ⟨1 + ∑' i, weight i, ?_, ?_⟩
  · have h : 0 ≤ ∑' i, weight i := tsum_nonneg weight_nonneg
    linarith
  intro p j hj θ x hx
  let g : (Fin 2 × ℕ × ℕ × ℕ) → ℂ := fun i =>
    seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2
  let r : (Fin 2 × ℕ × ℕ × ℕ) → ℂ := fun i => g i - baseline p x i
  let d : ℝ := (Q p) ^ (-(1 / 4000 : ℝ))
  have hd : 0 ≤ d := Real.rpow_nonneg (Q_pos p).le _
  have hs : Summable g := Summable.of_norm_bounded
    (weight_summable.div_const 2) (term_bound C p j hj θ · x hx)
  have hb : Summable (baseline p x) := Summable.of_norm_bounded
    (weight_summable.div_const 2) (baseline_norm_bound p x hx)
  have hr : Summable (fun i => ‖r i‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (remainder_bound C p j hj θ x hx) ((weight_summable.div_const 2).mul_left d)
  have hid : badFactor C p j θ x.1 x.2.1 x.2.2 - 1 =
      (1 - V p x.2.2) * (∑' i, r i) := by
    rw [show (∑' i, r i) = (∑' i, g i) - (∑' i, baseline p x i) from hs.tsum_sub hb,
      mul_sub, baseline_sum p x hx]
    rfl
  have hV : ‖1 - V p x.2.2‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖V p x.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by have h := (norm_V_bound p x hx).trans ratio_lt_one.le; simp only [norm_one]; linarith
  have ht : ‖∑' i, r i‖ ≤ d * ((∑' i, weight i) / 2) := by
    calc
      _ ≤ ∑' i, ‖r i‖ := norm_tsum_le_tsum_norm hr
      _ ≤ ∑' i, d * (weight i / 2) :=
        hr.tsum_le_tsum (remainder_bound C p j hj θ x hx) ((weight_summable.div_const 2).mul_left d)
      _ = d * ((∑' i, weight i) / 2) := by rw [tsum_mul_left, tsum_div_const]
  rw [hid, norm_mul]
  have hw : 0 ≤ ∑' i, weight i := tsum_nonneg weight_nonneg
  change ‖1 - V p x.2.2‖ * ‖∑' i, r i‖ ≤ (1 + ∑' i, weight i) * d
  nlinarith [norm_nonneg (∑' i, r i)]

end DedekindZetaZeroFree.CorrectionFactors

end
