module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.Definitions

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma correction_Q_gt_one (p : ExteriorPrime A) : 1 < Q p := by
  change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val

private lemma correction_Q_ge_two (p : ExteriorPrime A) : 2 ≤ Q p := by
  change 2 ≤ (Ideal.absNorm p.val.asIdeal : ℝ)
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val

private lemma correction_chi_le (p : ExteriorPrime A) (u : A.R) :
    ‖chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u)‖ ≤ 1 := by
  letI := A.exteriorResidue_finite (primeIdeal p)
  letI := Fintype.ofFinite (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ
  by_cases hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u)
  · obtain ⟨v, hv⟩ := hu
    rw [← hv]
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((chi (σ := σ) p).apply_mem_rootsOfUnity v)
    simpa only [MulChar.coe_equivToUnitHom] using h.le
  · simp [MulChar.map_nonunit _ hu]

private lemma correction_eta_le (p : ExteriorPrime A) : ‖η p.val.asIdeal‖ ≤ 1 := by
  by_cases h : η p.val.asIdeal = 0
  · simp [h]
  · exact (RayClassBridge.rayClassCharacter_norm_of_ne_zero F
      (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
      A.modulus A.modulus_ne_zero η p.val.asIdeal h).le

private lemma correction_qPower_norm (p : ExteriorPrime A) (s : ℂ) :
    ‖qPower p s‖ = Real.exp (s.re * Real.log (Q p)) := by
  simp [qPower, Complex.norm_exp]

private lemma correction_norm_V (p : ExteriorPrime A) (z : ℂ) :
    ‖V p z‖ = Real.exp ((-6 * z.re) * Real.log (Q p)) := by
  simp [V, correction_qPower_norm]

private lemma correction_norm_W (p : ExteriorPrime A) (u : A.R) (w : ℂ) :
    ‖W (σ := σ) p u w‖ ≤ Real.exp (-w.re * Real.log (Q p)) := by
  simp only [W, norm_mul, correction_qPower_norm, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (correction_chi_le p u)

private lemma correction_norm_D (p : ExteriorPrime A) (u : A.R) (ξ : ℂ) :
    ‖D (σ := σ) (η := η) p u ξ‖ ≤ Real.exp (-ξ.re * Real.log (Q p)) := by
  simp only [D, norm_mul, norm_star, correction_qPower_norm, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.exp_pos _).le
    (mul_le_one₀ (correction_eta_le p) (norm_nonneg _) (correction_chi_le p u))

private lemma correction_norm_E (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (ξ z : ℂ) :
    ‖E C p ξ z‖ = Real.exp ((4 - 6 * ξ.re - 6 * z.re) * Real.log (Q p)) := by
  have hθ : ‖vartheta C p‖ = 1 := Circle.norm_coe _
  simp only [E, norm_mul, norm_pow, hθ, one_pow, one_mul,
    correction_qPower_norm, correction_norm_V]
  rw [← Real.exp_add]
  congr 1
  simp
  ring

private lemma correction_region (x : Coordinates) (hx : x ∈ Omega) :
    1 / 1000 < 6 * x.2.2.re ∧ 1 / 1000 < x.2.1.re ∧
    1 / 1000 < x.1.re ∧ 1 / 1000 < 6 * x.1.re + 6 * x.2.2.re - 4 := by
  rcases hx with h | h <;> rcases h with ⟨hξ, hw, hz⟩ <;>
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma correction_norms_lt_one (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R) (x : Coordinates) (hx : x ∈ Omega) :
    ‖V p x.2.2‖ < 1 ∧ ‖W (σ := σ) p u x.2.1‖ < 1 ∧
    ‖D (σ := σ) (η := η) p u x.1‖ < 1 ∧ ‖E C p x.1 x.2.2‖ < 1 := by
  obtain ⟨hz, hw, hξ, he⟩ := correction_region x hx
  have hlog := Real.log_pos (correction_Q_gt_one p)
  have hexp : ∀ a : ℝ, a < 0 → Real.exp (a * Real.log (Q p)) < 1 := by
    intro a ha
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos ha hlog)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [correction_norm_V]; exact hexp _ (by linarith)
  · exact (correction_norm_W p u _).trans_lt (hexp _ (by linarith))
  · exact (correction_norm_D p u _).trans_lt (hexp _ (by linarith))
  · rw [correction_norm_E]; exact hexp _ (by linarith)

private lemma correction_decay_exponents (x : Coordinates) (hx : x ∈ Omega) :
    -6 * x.2.2.re - x.2.1.re ≤ -(1 + 1 / 4000 : ℝ) ∧
    -x.1.re - 6 * x.2.2.re ≤ -(1 + 1 / 4000 : ℝ) ∧
    -x.1.re - x.2.1.re ≤ -(1 + 1 / 4000 : ℝ) ∧
    1 - x.1.re - x.2.1.re - 6 * x.2.2.re ≤ -(1 + 1 / 4000 : ℝ) ∧
    4 - 6 * x.1.re - 6 * x.2.2.re ≤ -(1 + 1 / 4000 : ℝ) := by
  rcases hx with h | h <;> rcases h with ⟨hξ, hw, hz⟩ <;>
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

private lemma correction_monomial_bounds (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R) (x : Coordinates) (hx : x ∈ Omega) :
    let t := (Q p) ^ (-(1 + 1 / 4000 : ℝ))
    ‖V p x.2.2‖ * ‖W (σ := σ) p u x.2.1‖ ≤ t ∧
    ‖D (σ := σ) (η := η) p u x.1‖ * ‖V p x.2.2‖ ≤ t ∧
    ‖D (σ := σ) (η := η) p u x.1‖ * ‖W (σ := σ) p u x.2.1‖ ≤ t ∧
    Q p * ‖D (σ := σ) (η := η) p u x.1‖ * ‖W (σ := σ) p u x.2.1‖ * ‖V p x.2.2‖ ≤ t ∧
    ‖E C p x.1 x.2.2‖ ≤ t := by
  obtain ⟨hvw, hdv, hdw, hdwv, he⟩ := correction_decay_exponents x hx
  have hQ := correction_Q_gt_one p
  have hQ0 := (lt_trans zero_lt_one hQ)
  have hlog := (Real.log_pos hQ).le
  have ht : (Q p) ^ (-(1 + 1 / 4000 : ℝ)) =
      Real.exp ((-(1 + 1 / 4000 : ℝ)) * Real.log (Q p)) := by
    rw [Real.rpow_def_of_pos hQ0]; congr 1; (try simp only [Real.log_exp]); ring
  have hm : ∀ a : ℝ, a ≤ -(1 + 1 / 4000 : ℝ) →
      Real.exp (a * Real.log (Q p)) ≤ (Q p) ^ (-(1 + 1 / 4000 : ℝ)) := by
    intro a ha; rw [ht]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hlog)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp ((-6 * x.2.2.re) * Real.log (Q p)) *
          Real.exp (-x.2.1.re * Real.log (Q p)) := by
        rw [correction_norm_V]; gcongr; exact correction_norm_W p u _
      _ = Real.exp ((-6 * x.2.2.re - x.2.1.re) * Real.log (Q p)) := by
        rw [← Real.exp_add]; congr 1; (try simp only [Real.log_exp]); ring
      _ ≤ _ := hm _ hvw
  · calc
      _ ≤ Real.exp (-x.1.re * Real.log (Q p)) *
          Real.exp ((-6 * x.2.2.re) * Real.log (Q p)) := by
        rw [correction_norm_V]; gcongr; exact correction_norm_D p u _
      _ = Real.exp ((-x.1.re - 6 * x.2.2.re) * Real.log (Q p)) := by
        rw [← Real.exp_add]; congr 1; (try simp only [Real.log_exp]); ring
      _ ≤ _ := hm _ hdv
  · calc
      _ ≤ Real.exp (-x.1.re * Real.log (Q p)) *
          Real.exp (-x.2.1.re * Real.log (Q p)) := by
        gcongr
        · exact correction_norm_D p u _
        · exact correction_norm_W p u _
      _ = Real.exp ((-x.1.re - x.2.1.re) * Real.log (Q p)) := by
        rw [← Real.exp_add]; congr 1; (try simp only [Real.log_exp]); ring
      _ ≤ _ := hm _ hdw
  · calc
      _ ≤ Q p * Real.exp (-x.1.re * Real.log (Q p)) *
          Real.exp (-x.2.1.re * Real.log (Q p)) *
          Real.exp ((-6 * x.2.2.re) * Real.log (Q p)) := by
        rw [correction_norm_V]; gcongr
        · exact correction_norm_D p u _
        · exact correction_norm_W p u _
      _ = Real.exp ((1 - x.1.re - x.2.1.re - 6 * x.2.2.re) * Real.log (Q p)) := by
        rw [← Real.exp_log hQ0, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; (try simp only [Real.log_exp]); ring
      _ ≤ _ := hm _ hdwv
  · rw [correction_norm_E]; exact hm _ he

private lemma correction_denominator_gap (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R) (x : Coordinates) (hx : x ∈ Omega) :
    let c := 1 - Real.exp (-(1 / 1000 : ℝ) * Real.log 2)
    c ≤ ‖1 - D (σ := σ) (η := η) p u x.1‖ ∧ c ≤ ‖1 - E C p x.1 x.2.2‖ := by
  obtain ⟨hz, hw, hξ, he⟩ := correction_region x hx
  have hlog : Real.log 2 ≤ Real.log (Q p) :=
    Real.log_le_log (by norm_num) (correction_Q_ge_two p)
  have hm : ∀ a : ℝ, a ≤ -(1 / 1000 : ℝ) →
      Real.exp (a * Real.log (Q p)) ≤ Real.exp (-(1 / 1000 : ℝ) * Real.log 2) := by
    intro a ha
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -(1 / 1000 : ℝ) * Real.log (Q p) :=
        mul_le_mul_of_nonneg_right ha (Real.log_pos (correction_Q_gt_one p)).le
      _ ≤ _ := mul_le_mul_of_nonpos_left hlog (by norm_num)
  have hd := (correction_norm_D (σ := σ) (η := η) p u x.1).trans
    (hm _ (by linarith))
  have he' : ‖E C p x.1 x.2.2‖ ≤ Real.exp (-(1 / 1000 : ℝ) * Real.log 2) := by
    rw [correction_norm_E]; exact hm _ (by linarith)
  have hsub : ∀ a : ℂ, 1 - ‖a‖ ≤ ‖1 - a‖ := by
    intro a; simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) a
  dsimp only
  constructor
  · linarith [hsub (D (σ := σ) (η := η) p u x.1)]
  · linarith [hsub (E C p x.1 x.2.2)]

private lemma correction_numerator_bound (q t : ℝ) (hq : 2 ≤ q) (ht : 0 ≤ t)
    (v w d e : ℂ) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hvw : ‖v‖ * ‖w‖ ≤ t) (hdv : ‖d‖ * ‖v‖ ≤ t)
    (hdw : ‖d‖ * ‖w‖ ≤ t) (hdwv : q * ‖d‖ * ‖w‖ * ‖v‖ ≤ t)
    (he : ‖e‖ ≤ t) :
    ‖-v * w + d * v + d * w - (q : ℂ) * d * w * v +
      ((q : ℂ) - 1) * d * w ^ 2 * v +
      e * ((1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d)‖ ≤ 12 * t := by
  have hq0 : 0 ≤ q := by linarith
  have hqn : ‖(q : ℂ)‖ = q := by simp [Complex.norm_real, abs_of_nonneg hq0]
  have hqi : ‖(q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, hqn]; exact inv_le_one_of_one_le₀ (by linarith)
  have hqm : ‖(q : ℂ) - 1‖ ≤ 2 * q := by
    have h := norm_sub_le (q : ℂ) 1
    rw [hqn, norm_one] at h; linarith
  have hw2 : ‖w ^ 2‖ ≤ 1 := by simpa using (pow_le_one₀ (norm_nonneg w) hw : ‖w‖ ^ 2 ≤ 1)
  have hw2v : ‖w ^ 2 * v‖ ≤ 1 := by
    rw [norm_mul]; exact mul_le_one₀ hw2 (norm_nonneg _) hv
  have hbr : ‖(1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d‖ ≤ 6 := by
    calc
      _ ≤ (1 + ‖(q : ℂ)⁻¹‖) + ‖(q : ℂ)⁻¹‖ * ‖w‖ +
          ‖w ^ 2‖ + ‖w ^ 2 * v‖ + ‖d‖ := by
        calc
          _ ≤ ‖(1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v‖ + ‖d‖ := norm_sub_le _ _
          _ ≤ (‖(1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2‖ + ‖w ^ 2 * v‖) + ‖d‖ := by gcongr; exact norm_add_le _ _
          _ ≤ ((‖(1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w‖ + ‖w ^ 2‖) + ‖w ^ 2 * v‖) + ‖d‖ := by gcongr; exact norm_sub_le _ _
          _ ≤ (((‖1 - (q : ℂ)⁻¹‖ + ‖(q : ℂ)⁻¹ * w‖) + ‖w ^ 2‖) + ‖w ^ 2 * v‖) + ‖d‖ := by gcongr; exact norm_add_le _ _
          _ ≤ _ := by simp only [norm_mul]; gcongr; simpa using norm_sub_le (1 : ℂ) (q : ℂ)⁻¹
      _ ≤ 6 := by
        have hp := mul_le_one₀ hqi (norm_nonneg _) hw
        linarith
  have h5 : ‖((q : ℂ) - 1) * d * w ^ 2 * v‖ ≤ 2 * t := by
    simp only [norm_mul, norm_pow]
    calc
      _ ≤ (2 * q) * ‖d‖ * ‖w‖ ^ 2 * ‖v‖ := by gcongr
      _ = 2 * (q * ‖d‖ * ‖w‖ * ‖v‖) * ‖w‖ := by ring
      _ ≤ 2 * t * 1 := by gcongr
      _ = _ := by ring
  have h6 : ‖e * ((1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d)‖ ≤ 6 * t := by
    rw [norm_mul]
    calc
      _ ≤ t * 6 := mul_le_mul he hbr (norm_nonneg _) ht
      _ = _ := by ring
  calc
    _ ≤ ‖-v * w + d * v + d * w - (q : ℂ) * d * w * v + ((q : ℂ) - 1) * d * w ^ 2 * v‖ +
        ‖e * ((1 - (q : ℂ)⁻¹) + (q : ℂ)⁻¹ * w - w ^ 2 + w ^ 2 * v - d)‖ := norm_add_le _ _
    _ ≤ (‖-v * w + d * v + d * w - (q : ℂ) * d * w * v‖ + ‖((q : ℂ) - 1) * d * w ^ 2 * v‖) + 6 * t := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖-v * w + d * v + d * w‖ + ‖(q : ℂ) * d * w * v‖) + 2 * t) + 6 * t := by gcongr; exact norm_sub_le _ _
    _ ≤ (((‖-v * w + d * v‖ + ‖d * w‖) + ‖(q : ℂ) * d * w * v‖) + 2 * t) + 6 * t := by gcongr; exact norm_add_le _ _
    _ ≤ ((((‖-v * w‖ + ‖d * v‖) + ‖d * w‖) + ‖(q : ℂ) * d * w * v‖) + 2 * t) + 6 * t := by gcongr; exact norm_add_le _ _
    _ ≤ 12 * t := by simp only [norm_mul, norm_neg, hqn]; linarith

theorem good_correction_denominators_ne_zero
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (x : Coordinates) (hx : x ∈ Omega) :
    1 - V p x.2.2 ≠ 0 ∧
    1 - W (σ := σ) p u x.2.1 ≠ 0 ∧
    1 - D (σ := σ) (η := η) p u x.1 ≠ 0 ∧
    1 - E C p x.1 x.2.2 ≠ 0 := by
  obtain ⟨hv, hw, hd, he⟩ := correction_norms_lt_one C p u x hx
  have h : ∀ a : ℂ, ‖a‖ < 1 → 1 - a ≠ 0 := by
    intro a ha heq
    have : a = 1 := (sub_eq_zero.mp heq).symm
    simp [this] at ha
  exact ⟨h _ hv, h _ hw, h _ hd, h _ he⟩

set_option maxHeartbeats 1500000 in

theorem good_correction_holomorphic
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u)) :
    DifferentiableOn ℂ (fun x : Coordinates => goodFactor C p u x.1 x.2.1 x.2.2)
      Omega := by
  have hξ : Differentiable ℂ (fun x : Coordinates => x.1) := differentiable_fst
  have hw : Differentiable ℂ (fun x : Coordinates => x.2.1) := differentiable_snd.fst
  have hz : Differentiable ℂ (fun x : Coordinates => x.2.2) := differentiable_snd.snd
  have hv : Differentiable ℂ (fun x : Coordinates => V p x.2.2) := by
    unfold V qPower; fun_prop
  have hw' : Differentiable ℂ (fun x : Coordinates => W (σ := σ) p u x.2.1) := by
    unfold W qPower; fun_prop
  have hd : Differentiable ℂ (fun x : Coordinates => D (σ := σ) (η := η) p u x.1) := by
    unfold D qPower; fun_prop
  have he : Differentiable ℂ (fun x : Coordinates => E C p x.1 x.2.2) := by
    unfold E V qPower; fun_prop
  intro x hx
  obtain ⟨nv, nw, nd, ne⟩ := good_correction_denominators_ne_zero C p u hu x hx
  have hvx := hv x
  have hwx := hw' x
  have hdx := hd x
  have hex := he x
  apply DifferentiableAt.differentiableWithinAt
  unfold goodFactor goodRational
  dsimp only
  fun_prop (disch := assumption)

theorem good_correction_numerator
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (x : Coordinates) (hx : x ∈ Omega) :
    let v := V p x.2.2
    let w := W (σ := σ) p u x.2.1
    let d := D (σ := σ) (η := η) p u x.1
    let e := E C p x.1 x.2.2
    let q : ℂ := Q p
    (1 - e) * (1 - d) * (goodFactor C p u x.1 x.2.1 x.2.2 - 1) =
      -v * w + d * v + d * w - q * d * w * v +
        (q - 1) * d * w ^ 2 * v +
        e * ((1 - q⁻¹) + q⁻¹ * w - w ^ 2 + w ^ 2 * v - d) := by
  obtain ⟨hv, hw, hd, he⟩ := good_correction_denominators_ne_zero C p u hu x hx
  dsimp only
  unfold goodFactor goodRational
  dsimp only
  field_simp
  <;> ring

theorem good_correction_uniform_bound :
    ∃ M : ℝ, 0 < M ∧
      ∀ (F : Type) [Field F] [NumberField F]
        (A : SArithmeticData F) (σ : F →+* ℂ)
        (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
        (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (u : A.R),
        IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u) →
        ∀ x : Coordinates, x ∈ Omega →
          ‖goodFactor C p u x.1 x.2.1 x.2.2 - 1‖ ≤
            M * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) := by
  let c : ℝ := 1 - Real.exp (-(1 / 1000 : ℝ) * Real.log 2)
  have hc : 0 < c := by
    dsimp [c]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have he : Real.exp (-(1 / 1000 : ℝ) * Real.log 2) < 1 :=
      Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by norm_num) hl)
    linarith
  refine ⟨12 / (c * c), by positivity, ?_⟩
  intro F _ _ A σ η hS C p u hu x hx
  have ht : 0 ≤ (Q p) ^ (-(1 + 1 / 4000 : ℝ)) :=
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one (correction_Q_gt_one p)) _).le
  obtain ⟨hv, hw, hd, he⟩ := correction_norms_lt_one C p u x hx
  obtain ⟨hvw, hdv, hdw, hdwv, he'⟩ := correction_monomial_bounds C p u x hx
  have hn := correction_numerator_bound (Q p) _ (correction_Q_ge_two p) ht
    (V p x.2.2) (W (σ := σ) p u x.2.1) (D (σ := σ) (η := η) p u x.1)
    (E C p x.1 x.2.2) hv.le hw.le hd.le hvw hdv hdw hdwv he'
  rw [← good_correction_numerator C p u hu x hx] at hn
  simp only [norm_mul] at hn
  obtain ⟨hdgap, hegap⟩ := correction_denominator_gap C p u x hx
  change c ≤ _ at hdgap hegap
  have hg : c * c ≤ ‖1 - E C p x.1 x.2.2‖ *
      ‖1 - D (σ := σ) (η := η) p u x.1‖ :=
    mul_le_mul hegap hdgap hc.le (norm_nonneg _)
  have hh : (c * c) * ‖goodFactor C p u x.1 x.2.1 x.2.2 - 1‖ ≤
      12 * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) :=
    (mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans hn
  have hc2 : 0 < c * c := mul_pos hc hc
  calc
    _ ≤ (12 * (Q p) ^ (-(1 + 1 / 4000 : ℝ))) / (c * c) :=
      (le_div_iff₀ hc2).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by ring

end DedekindZetaZeroFree.CorrectionFactors

end
