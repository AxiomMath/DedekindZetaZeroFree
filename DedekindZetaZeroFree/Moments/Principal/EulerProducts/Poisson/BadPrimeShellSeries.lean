module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.ShellMajorants

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.BadPrimeShellSeries

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree.LocalFiniteSums
open DedekindZetaZeroFree.CorrectionFactors (V)
open DedekindZetaZeroFree.Quantitative.EulerShellMargin (shellExponent)
open scoped Classical

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

theorem seriesTerm_eq_zero_of_two_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (e : Fin 2) (l k m : ℕ) (ht : 0 < e.val + 3 * l) (hk : 2 ≤ k) (ξ w z : ℂ) :
    seriesTerm C p j θ e l k m ξ w z = 0 := by
  simp only [seriesTerm, Ctk_eq_zero_of_two_le C p _ _ _ ht hk, mul_zero, zero_mul]

theorem norm_seriesTerm_le_Ctk (C : A.GeneralArithmeticContext σ η hS)
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

theorem norm_Ctk_le_shell (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (ht : 0 < t) (hk : k ≤ 1) :
    ‖Ctk C p t k J‖ ≤ (Q p) ^ ((t : ℝ) + (k : ℝ) / 2) := by
  interval_cases k
  · simpa only [Nat.cast_zero, zero_div, add_zero, Real.rpow_natCast] using
      norm_Ctk_zero_le C p t J ht
  · simpa using norm_Ctk_one_le C p t J ht

theorem norm_seriesTerm_le_rpow_shellExponent (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (e : Fin 2) (l k m : ℕ) (ht : 0 < e.val + 3 * l) (hk : k ≤ 1) (x : Coordinates) :
    ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
      (Q p) ^ shellExponent x.1.re x.2.1.re x.2.2.re e.val k l m := by
  calc ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖
      ≤ ‖Ctk C p (e.val + 3 * l) k (j.val + 6 * m)‖ *
        (Q p) ^ (-(e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re -
          6 * (m : ℝ) * x.2.2.re) := norm_seriesTerm_le_Ctk C p j θ e l k m x
    _ ≤ (Q p) ^ (((e.val + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2) *
        (Q p) ^ (-(e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re -
          6 * (m : ℝ) * x.2.2.re) :=
      mul_le_mul_of_nonneg_right (norm_Ctk_le_shell C p _ _ _ ht hk)
        (Real.rpow_nonneg (Q_pos p).le _)
    _ = (Q p) ^ shellExponent x.1.re x.2.1.re x.2.2.re e.val k l m := by
      rw [← Real.rpow_add (Q_pos p)]
      congr 1
      unfold shellExponent
      push_cast
      ring

theorem seriesTerm_leading (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (k m : ℕ) (ξ w z : ℂ) :
    seriesTerm C p j θ 0 0 k m ξ w z = if k = 0 then V p z ^ m else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [seriesTerm, Fin.val_zero, pow_zero, Nat.mul_zero, Nat.add_zero,
      Int.ofNat_zero, sub_zero, zero_sub, zpow_zero, one_mul, Ctk_zero_zero, zero_mul,
      sub_self, sub_zero, if_true]
    rw [CorrectionFactors.V, qPower, qPower, ← Complex.exp_nat_mul]
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

def weight (ρ : ℝ) (i : Fin 2 × ℕ × ℕ × ℕ) : ℝ :=
  2 * ρ ^ i.2.1 * (1 / 2 : ℝ) ^ i.2.2.1 * ρ ^ i.2.2.2

theorem weight_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (i : Fin 2 × ℕ × ℕ × ℕ) : 0 ≤ weight ρ i := by
  unfold weight
  positivity

theorem weight_summable {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : Summable (weight ρ) := by
  have hr : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one hρ0 hρ1
  have hh : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hkm := hh.mul_of_nonneg hr (fun n => by positivity) (fun n => by positivity)
  have hlkm := hr.mul_of_nonneg hkm (fun n => by positivity) (fun n => by dsimp; positivity)
  have h := (Summable.of_finite : Summable (fun _ : Fin 2 => (2 : ℝ))).mul_of_nonneg hlkm
    (fun _ => by norm_num) (fun n => by dsimp; positivity)
  change Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
    2 * ρ ^ i.2.1 * (1 / 2 : ℝ) ^ i.2.2.1 * ρ ^ i.2.2.2)
  simpa only [mul_assoc] using h

private lemma rpow_le_rho (p : ExteriorPrime A) (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    (Q p) ^ (-(b * n)) ≤ ((2 : ℝ) ^ (-b)) ^ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (Q p) ^ (-(b * n)) ≤ (2 : ℝ) ^ (-(b * n)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_Q p)
          (by nlinarith [mul_nonneg hb hn])
    _ = ((2 : ℝ) ^ (-b)) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring

private lemma decay_split (p : ExteriorPrime A) (a b : ℝ) (hb : 0 ≤ b) (l m : ℕ) :
    (Q p) ^ (-a - b * (l : ℝ) - b * (m : ℝ)) ≤
      (Q p) ^ (-a) * ((2 : ℝ) ^ (-b)) ^ l * ((2 : ℝ) ^ (-b)) ^ m := by
  have hq := Q_pos p
  have h2 : -a - b * (l : ℝ) - b * (m : ℝ) = -a + -(b * l) + -(b * m) := by ring
  rw [h2, Real.rpow_add hq, Real.rpow_add hq]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_rho p b hb l)
    (Real.rpow_nonneg hq.le _)) (rpow_le_rho p b hb m) (Real.rpow_nonneg hq.le _)
    (by positivity)

theorem norm_V_le (p : ExteriorPrime A) (b : ℝ) (hb : 0 ≤ b) (z : ℂ) (hz : b ≤ 6 * z.re) :
    ‖V p z‖ ≤ (2 : ℝ) ^ (-b) := by
  rw [CorrectionFactors.V, norm_qPower]
  have he : (-6 * z).re = -(6 * z.re) := by simp
  rw [he]
  calc (Q p) ^ (-(6 * z.re)) ≤ (2 : ℝ) ^ (-(6 * z.re)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_Q p) (by linarith)
    _ ≤ (2 : ℝ) ^ (-b) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

private lemma rho_pos (b : ℝ) : 0 < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _

private lemma rho_lt_one (b : ℝ) (hb : 0 < b) : (2 : ℝ) ^ (-b) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem norm_seriesTerm_le_weight (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0) (θ : {θ : ℂ // ‖θ‖ = 1})
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (x : Coordinates) (hv : b ≤ 6 * x.2.2.re)
    (hshell : ∀ e k l m : ℕ, e ≤ 1 → k ≤ 1 → 0 < e + 3 * l →
      shellExponent x.1.re x.2.1.re x.2.2.re e k l m ≤ -a - b * (l : ℝ) - b * (m : ℝ))
    (i : Fin 2 × ℕ × ℕ × ℕ) :
    ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
        weight ((2 : ℝ) ^ (-b)) i ∧
      (0 < i.1.val + 3 * i.2.1 →
        ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
          (Q p) ^ (-a) * weight ((2 : ℝ) ^ (-b)) i) := by
  obtain ⟨e, l, k, m⟩ := i
  have hρ := rho_pos b
  have hQa : (Q p) ^ (-a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [two_le_Q p]) (by linarith)
  have hw := weight_nonneg hρ.le (e, l, k, m)
  have hpos : 0 < e.val + 3 * l →
      ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
        (Q p) ^ (-a) * weight ((2 : ℝ) ^ (-b)) (e, l, k, m) := by
    intro ht
    by_cases hk : k ≤ 1
    · have h1 := norm_seriesTerm_le_rpow_shellExponent C p j θ e l k m ht hk x
      have h2 := Real.rpow_le_rpow_of_exponent_le (x := Q p) (by linarith [two_le_Q p])
        (hshell e.val k l m (Nat.lt_succ_iff.mp e.isLt) hk ht)
      have h3 := h1.trans (h2.trans (decay_split p a b hb.le l m))
      have hl := pow_nonneg hρ.le l
      have hm := pow_nonneg hρ.le m
      have hQ0 : 0 ≤ (Q p) ^ (-a) := Real.rpow_nonneg (Q_pos p).le _
      refine h3.trans ?_
      have : ((Q p) ^ (-a) * ((2 : ℝ) ^ (-b)) ^ l * ((2 : ℝ) ^ (-b)) ^ m) ≤
          (Q p) ^ (-a) * weight ((2 : ℝ) ^ (-b)) (e, l, k, m) := by
        unfold weight
        simp only
        interval_cases k <;> simp only [pow_zero, pow_one] <;>
          nlinarith [mul_nonneg (mul_nonneg hQ0 hl) hm]
      exact this
    · have hk2 : 2 ≤ k := by omega
      rw [seriesTerm_eq_zero_of_two_le C p j θ e l k m ht hk2, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (Q_pos p).le _) hw
  refine ⟨?_, hpos⟩
  by_cases ht : 0 < e.val + 3 * l
  · exact (hpos ht).trans (mul_le_of_le_one_left hw hQa)
  · have he : e = 0 := Fin.ext (by simp; omega)
    have hl : l = 0 := by omega
    subst he hl
    rw [seriesTerm_leading C p j hj θ]
    split_ifs with hk
    · subst hk
      rw [norm_pow]
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_V_le p b hb.le _ hv) m
      simp only [weight, pow_zero, mul_one]
      nlinarith [pow_nonneg hρ.le m]
    · simpa using hw

def baseline (p : ExteriorPrime A) (z : ℂ) (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  if i.1 = 0 ∧ i.2.1 = 0 ∧ i.2.2.1 = 0 then V p z ^ i.2.2.2 else 0

theorem baseline_norm_le (p : ExteriorPrime A) (z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hV : ‖V p z‖ ≤ ρ) (i : Fin 2 × ℕ × ℕ × ℕ) : ‖baseline p z i‖ ≤ weight ρ i := by
  unfold baseline
  split_ifs with h
  · rcases h with ⟨he, hl, hk⟩
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg _) hV i.2.2.2
    simp only [weight, he, hl, hk, pow_zero, mul_one]
    nlinarith [pow_nonneg hρ i.2.2.2]
  · simp only [norm_zero]
    exact weight_nonneg hρ i

theorem one_sub_V_mul_tsum_baseline (p : ExteriorPrime A) (z : ℂ) (hV : ‖V p z‖ < 1) :
    (1 - V p z) * (∑' i, baseline p z i) = 1 := by
  have hs : Summable (baseline p z) := by
    refine Summable.of_norm_bounded (weight_summable (norm_nonneg _) hV) ?_
    exact baseline_norm_le p z _ (norm_nonneg _) le_rfl
  rw [hs.tsum_prod]
  have hs0 := hs.prod_factor (0 : Fin 2)
  have hs00 := hs0.prod_factor (0 : ℕ)
  simp only [baseline]
  rw [tsum_eq_single (0 : Fin 2)]
  · simp only [ite_true]
    rw [show (∑' c : ℕ × ℕ × ℕ, if True ∧ c.1 = 0 ∧ c.2.1 = 0 then V p z ^ c.2.2 else 0) =
      ∑' l : ℕ, ∑' c : ℕ × ℕ, baseline p z (0, l, c) by
        simpa only [baseline, Fin.val_zero] using hs0.tsum_prod]
    simp only [baseline, true_and]
    rw [tsum_eq_single (0 : ℕ)]
    · simp only [ite_true]
      rw [show (∑' c : ℕ × ℕ, if True ∧ c.1 = 0 then V p z ^ c.2 else 0) =
        ∑' k : ℕ, ∑' m : ℕ, baseline p z (0, 0, k, m) by
          simpa only [baseline, true_and] using hs00.tsum_prod]
      simp only [baseline, true_and]
      rw [tsum_eq_single (0 : ℕ)]
      · simp only [ite_true]
        exact (summable_geometric_of_norm_lt_one hV).one_sub_mul_tsum_pow
      · intro k hk
        simp [hk]
    · intro l hl
      simp [hl]
  · intro e he
    simp [he]

theorem seriesTerm_majorant_margin (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ρ δ₀ : ℝ), 0 < ρ ∧ ρ < 1 ∧ 0 < δ₀ ∧ Summable (weight ρ) ∧
      ∀ (C : A.GeneralArithmeticContext σ η hS)
        (p : ExteriorPrime A) (j : Fin 6), j.val ≠ 0 → ∀ (θ : {θ : ℂ // ‖θ‖ = 1}),
        ∀ x ∈ OmegaStarMargin δ, ∀ i : Fin 2 × ℕ × ℕ × ℕ,
          ‖V p x.2.2‖ ≤ ρ ∧
          ‖(1 - V p x.2.2) *
            seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤ 2 * weight ρ i ∧
          (0 < i.1.val + 3 * i.2.1 →
            ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
              (Q p) ^ (-δ₀) * weight ρ i) := by
  obtain ⟨δ₀, δ', hδ₀, hδ', hsh⟩ := EulerShellMargin.shellExponent_le_margin δ hδ
  set b : ℝ := min δ' δ with hbdef
  have hb : 0 < b := lt_min hδ' hδ
  have hbδ' : b ≤ δ' := min_le_left _ _
  have hbδ : b ≤ δ := min_le_right _ _
  refine ⟨(2 : ℝ) ^ (-b), δ₀, rho_pos b, rho_lt_one b hb, hδ₀,
    weight_summable (rho_pos b).le (rho_lt_one b hb), ?_⟩
  intro C p j hj θ x hx i
  have hv : b ≤ 6 * x.2.2.re := by
    obtain ⟨_, _, h3, _⟩ := hx
    linarith
  have hshell : ∀ e k l m : ℕ, e ≤ 1 → k ≤ 1 → 0 < e + 3 * l →
      shellExponent x.1.re x.2.1.re x.2.2.re e k l m ≤ -δ₀ - b * (l : ℝ) - b * (m : ℝ) := by
    intro e k l m he hk ht
    have h := hsh x hx e k l m he hk ht
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg (sub_nonneg.mpr hbδ') hl, mul_nonneg (sub_nonneg.mpr hbδ') hm]
  obtain ⟨h1, h2⟩ := norm_seriesTerm_le_weight C p j hj θ δ₀ b hδ₀.le hb x hv hshell i
  have hVn := norm_V_le p b hb.le _ hv
  refine ⟨hVn, ?_, h2⟩
  have hV2 : ‖1 - V p x.2.2‖ ≤ 2 := by
    calc ‖1 - V p x.2.2‖ ≤ ‖(1 : ℂ)‖ + ‖V p x.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        have := rho_lt_one b hb
        simp only [norm_one]; linarith
  rw [norm_mul]
  exact mul_le_mul hV2 h1 (norm_nonneg _) (by norm_num)

theorem seriesTerm_majorant_paddedBoxes :
    ∀ (C : A.GeneralArithmeticContext σ η hS)
      (p : ExteriorPrime A) (j : Fin 6), j.val ≠ 0 → ∀ (θ : {θ : ℂ // ‖θ‖ = 1}),
      ∀ x ∈ paddedBoxes, ∀ i : Fin 2 × ℕ × ℕ × ℕ,
        ‖V p x.2.2‖ ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) ∧
        ‖(1 - V p x.2.2) *
          seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
            2 * weight ((2 : ℝ) ^ (-(1 / 8 : ℝ))) i ∧
        (0 < i.1.val + 3 * i.2.1 →
          ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
            (Q p) ^ (-(1 / 20000 : ℝ)) * weight ((2 : ℝ) ^ (-(1 / 8 : ℝ))) i) := by
  intro C p j hj θ x hx i
  have hb : (0 : ℝ) < 1 / 8 := by norm_num
  have hv : (1 / 8 : ℝ) ≤ 6 * x.2.2.re := by
    simp only [paddedBoxes, paddedBox₁, paddedBox₂, paddedBox₃, box, Set.mem_union,
      Set.mem_setOf_eq] at hx
    simp only [Scales.goodLine, Scales.rightLine, Scales.contourOffset, pad] at hx
    norm_num at hx
    rcases hx with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩ <;> linarith
  have hshell : ∀ e k l m : ℕ, e ≤ 1 → k ≤ 1 → 0 < e + 3 * l →
      shellExponent x.1.re x.2.1.re x.2.2.re e k l m ≤
        -(1 / 20000 : ℝ) - (1 / 8 : ℝ) * (l : ℝ) - (1 / 8 : ℝ) * (m : ℝ) := by
    intro e k l m he hk ht
    have h := EulerShellMargin.shellExponent_le_paddedBoxes x hx e k l m he hk ht
    linarith
  obtain ⟨h1, h2⟩ := norm_seriesTerm_le_weight C p j hj θ (1 / 20000) (1 / 8) (by norm_num) hb x
    hv hshell i
  have hVn := norm_V_le p (1 / 8) hb.le _ hv
  refine ⟨hVn, ?_, h2⟩
  have hV2 : ‖1 - V p x.2.2‖ ≤ 2 := by
    calc ‖1 - V p x.2.2‖ ≤ ‖(1 : ℂ)‖ + ‖V p x.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        have := rho_lt_one (1 / 8) hb
        simp only [norm_one]; linarith
  rw [norm_mul]
  exact mul_le_mul hV2 h1 (norm_nonneg _) (by norm_num)

end

end DedekindZetaZeroFree.Quantitative.BadPrimeShellSeries
