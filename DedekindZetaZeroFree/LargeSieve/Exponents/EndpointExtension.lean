module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormBlocks
public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorNormBounds

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

private lemma one_le_dyadicScale (i : ℕ) : 1 ≤ dyadicScale i := by
  cases i with
  | zero => simp [dyadicScale]
  | succ k => simp only [dyadicScale]; exact one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)

private lemma dyadicScale_nonneg (i : ℕ) : 0 ≤ dyadicScale i :=
  le_trans zero_le_one (one_le_dyadicScale i)

private lemma rpow_one_eq_one (η : ℝ) : Real.rpow (1 : ℝ) η = 1 := by
  rw [Real.rpow_eq_pow, Real.one_rpow]

private lemma rpow_nonneg' (x : ℝ) (hx : 0 ≤ x) (y : ℝ) : 0 ≤ Real.rpow x y := by
  rw [Real.rpow_eq_pow]; exact Real.rpow_nonneg hx y

private lemma one_le_rpow' (x : ℝ) (hx : 1 ≤ x) (y : ℝ) (hy : 0 ≤ y) : 1 ≤ Real.rpow x y := by
  rw [Real.rpow_eq_pow]; exact Real.one_le_rpow hx hy

private lemma rpow_ge_self (x : ℝ) (hx : 1 ≤ x) (a : ℝ) (ha : 1 ≤ a) : x ≤ Real.rpow x a := by
  have h := Real.rpow_le_rpow_of_exponent_le hx ha
  rw [Real.rpow_one] at h
  rwa [← Real.rpow_eq_pow] at h

private lemma card_idealDyadicBlock_le (A : ℝ) (hA1 : 1 ≤ A)
    (hAset : ∀ X : ℝ, 1 ≤ X → ∀ s : Finset (Ideal (𝓞 F)),
      (∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ X) → (s.card : ℝ) ≤ A * X)
    (i : ℕ) : ((idealDyadicBlock F c i).card : ℝ) ≤ A * (2 * dyadicScale i) := by
  cases i with
  | zero =>
    have h1 : ((idealDyadicBlock F c 0).card : ℝ) = 1 := by simp [idealDyadicBlock]
    rw [h1]; simp only [dyadicScale]; linarith
  | succ k =>
    have hk : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := k)
      linarith
    have h := hAset (2 * (2 : ℝ) ^ k) hk
      (paperShell F c ((2 : ℝ) ^ k))
      (fun I hI => ((mem_paperShell F c ((2 : ℝ) ^ k) I).mp hI).2.2.2)
    simpa [idealDyadicBlock, dyadicScale] using h

private lemma mem_block_squarefree (j : ℕ) {b : Ideal (𝓞 F)}
    (hb : b ∈ idealDyadicBlock F c j) : Squarefree b ∧ b ⊔ c = ⊤ := by
  cases j with
  | zero =>
    simp only [idealDyadicBlock, Finset.mem_singleton] at hb
    subst hb
    exact ⟨by rw [show (⊤ : Ideal (𝓞 F)) = 1 by simp]; exact squarefree_one, by simp⟩
  | succ k =>
    have hb' : b ∈ paperShell F c ((2 : ℝ) ^ k) := by simpa [idealDyadicBlock] using hb
    obtain ⟨h1, h2, -, -⟩ := (mem_paperShell F c ((2 : ℝ) ^ k) b).mp hb'
    exact ⟨h1, h2⟩

private lemma norm_row_le_card_mul (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (S : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤) (a : Ideal (𝓞 F)) :
    ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤ (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  have h : ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ≤ ∑ b ∈ S, ‖lam b‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun b hb => ?_))
    rw [norm_mul]
    calc ‖lam b‖ * ‖(Q.χ b) a‖ ≤ ‖lam b‖ * 1 :=
          mul_le_mul_of_nonneg_left (quadraticFamily_norm_le_one Q (hSsf b hb).1 (hSsf b hb).2 a)
            (norm_nonneg _)
      _ = ‖lam b‖ := by ring
  calc ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤ (∑ b ∈ S, ‖lam b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := sq_sum_le_card_mul_sum_sq

private lemma sum_sq_le_card_mul_energy (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (R S : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤) :
    ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
      ≤ (R.card : ℝ) * (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  have hE0 : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := Finset.sum_nonneg (fun b _ => by positivity)
  calc ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
      ≤ ∑ _a ∈ R, (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
        Finset.sum_le_sum (fun a _ => norm_row_le_card_mul Q S lam hSsf a)
    _ = (R.card : ℝ) * ((S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (R.card : ℝ) * (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by ring

private lemma arith_zero_row (C A η α : ℝ) (hA1 : 1 ≤ A) (hC : 2 * A ≤ C) (hη : 0 < η)
    (hα1 : 1 ≤ α) (x : ℝ) (hx1 : 1 ≤ x) (E : ℝ) (hE0 : 0 ≤ E) :
    2 * A * x * E ≤ C * Real.rpow x η * (1 + Real.rpow x α) * E := by
  have hC0 : 0 ≤ C := by linarith
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hX : 1 ≤ Real.rpow x η := one_le_rpow' x hx1 η hη.le
  have hY : x ≤ Real.rpow x α := rpow_ge_self x hx1 α hα1
  have hY0 : 0 ≤ Real.rpow x α := rpow_nonneg' x hx0 α
  have h1Y0 : 0 ≤ 1 + Real.rpow x α := by linarith
  have h1 : 2 * A * x ≤ C * x := mul_le_mul_of_nonneg_right hC hx0
  have h2 : C * x ≤ C * (1 + Real.rpow x α) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have h3 : C * (1 + Real.rpow x α) ≤ C * Real.rpow x η * (1 + Real.rpow x α) := by
    have hCX : C ≤ C * Real.rpow x η := by
      simpa using mul_le_mul_of_nonneg_left hX hC0
    exact mul_le_mul_of_nonneg_right hCX h1Y0
  exact mul_le_mul_of_nonneg_right (le_trans h1 (le_trans h2 h3)) hE0

private lemma arith_zero_col (C A η α : ℝ) (hA1 : 1 ≤ A) (hC : 2 * A ≤ C) (hη : 0 < η)
    (hα1 : 1 ≤ α) (m : ℝ) (hm1 : 1 ≤ m) (E : ℝ) (hE0 : 0 ≤ E) :
    2 * A * m * E ≤ C * Real.rpow m η * (m + 1) * E := by
  have hC0 : 0 ≤ C := by linarith
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  have hX : 1 ≤ Real.rpow m η := one_le_rpow' m hm1 η hη.le
  have hm10 : 0 ≤ m + 1 := by linarith
  have h1 : 2 * A * m ≤ C * m := mul_le_mul_of_nonneg_right hC hm0
  have h2 : C * m ≤ C * (m + 1) := mul_le_mul_of_nonneg_left (by linarith) hC0
  have h3 : C * (m + 1) ≤ C * Real.rpow m η * (m + 1) := by
    have hCX : C ≤ C * Real.rpow m η := by
      simpa using mul_le_mul_of_nonneg_left hX hC0
    exact mul_le_mul_of_nonneg_right hCX hm10
  exact mul_le_mul_of_nonneg_right (le_trans h1 (le_trans h2 h3)) hE0

theorem bilinear_endpoint_exponent_extension
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (i j : ℕ) (R S : Finset (Ideal (𝓞 F))),
        R ⊆ idealDyadicBlock F c i → S ⊆ idealDyadicBlock F c j →
        ∀ lam : Ideal (𝓞 F) → ℂ,
          ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤
            C * Real.rpow (dyadicScale i * dyadicScale j) η *
              (dyadicScale i + Real.rpow (dyadicScale j) α) *
                ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  obtain ⟨A, hA1, -, hAset⟩ := exists_ideal_count_bound_finset F
  intro η hη
  obtain ⟨Cexp, -, hCexpb⟩ := hExponent η hη
  have hα1 : 1 ≤ α := hα.1
  have hC1 : (1 : ℝ) ≤ max (2 * A) Cexp :=
    le_trans (by linarith : (1 : ℝ) ≤ 2 * A) (le_max_left _ _)
  refine ⟨max (2 * A) Cexp, hC1, ?_⟩
  intro i j R S hR hS lam
  rcases i with _ | i' <;> rcases j with _ | j'
  ·
    have hR1 : (R.card : ℝ) ≤ 1 := by
      have hsub : R ⊆ ({⊤} : Finset (Ideal (𝓞 F))) := by simpa [idealDyadicBlock] using hR
      calc (R.card : ℝ) ≤ (({⊤} : Finset (Ideal (𝓞 F))).card : ℝ) :=
            by exact_mod_cast Finset.card_le_card hsub
        _ = 1 := by simp
    have hS1 : (S.card : ℝ) ≤ 1 := by
      have hsub : S ⊆ ({⊤} : Finset (Ideal (𝓞 F))) := by simpa [idealDyadicBlock] using hS
      calc (S.card : ℝ) ≤ (({⊤} : Finset (Ideal (𝓞 F))).card : ℝ) :=
            by exact_mod_cast Finset.card_le_card hsub
        _ = 1 := by simp
    have hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤ := fun b hb => mem_block_squarefree 0 (hS hb)
    have hE0 : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := Finset.sum_nonneg (fun b _ => by positivity)
    have hprod : (R.card : ℝ) * (S.card : ℝ) ≤ 1 :=
      mul_le_one₀ hR1 (Nat.cast_nonneg _) hS1
    have hstep : ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤ 1 * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
      le_trans (sum_sq_le_card_mul_energy Q R S lam hSsf)
        (mul_le_mul_of_nonneg_right hprod hE0)
    rw [one_mul] at hstep
    refine le_trans hstep ?_
    have h2C : (1 : ℝ) ≤ max (2 * A) Cexp * 1 * (1 + 1) := by
      have : (1 : ℝ) ≤ max (2 * A) Cexp := hC1
      nlinarith
    calc ∑ b ∈ S, ‖lam b‖ ^ 2 = 1 * ∑ b ∈ S, ‖lam b‖ ^ 2 := by rw [one_mul]
      _ ≤ (max (2 * A) Cexp * 1 * (1 + 1)) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2C hE0
      _ = max (2 * A) Cexp * Real.rpow (dyadicScale 0 * dyadicScale 0) η *
            (dyadicScale 0 + Real.rpow (dyadicScale 0) α) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
          simp only [dyadicScale, one_mul, rpow_one_eq_one]
  ·
    have hR1 : (R.card : ℝ) ≤ 1 := by
      have hsub : R ⊆ ({⊤} : Finset (Ideal (𝓞 F))) := by simpa [idealDyadicBlock] using hR
      calc (R.card : ℝ) ≤ (({⊤} : Finset (Ideal (𝓞 F))).card : ℝ) :=
            by exact_mod_cast Finset.card_le_card hsub
        _ = 1 := by simp
    have hScard : (S.card : ℝ) ≤ A * (2 * dyadicScale (j' + 1)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hS)
        (card_idealDyadicBlock_le A hA1 hAset (j' + 1))
    have hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤ := fun b hb => mem_block_squarefree (j' + 1) (hS hb)
    have hE0 : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := Finset.sum_nonneg (fun b _ => by positivity)
    have hprod : (R.card : ℝ) * (S.card : ℝ) ≤ 2 * A * dyadicScale (j' + 1) := by
      calc (R.card : ℝ) * (S.card : ℝ) ≤ 1 * (A * (2 * dyadicScale (j' + 1))) :=
            mul_le_mul hR1 hScard (Nat.cast_nonneg _) zero_le_one
        _ = 2 * A * dyadicScale (j' + 1) := by ring
    have hstep : ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
        ≤ 2 * A * dyadicScale (j' + 1) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
      le_trans (sum_sq_le_card_mul_energy Q R S lam hSsf)
        (mul_le_mul_of_nonneg_right hprod hE0)
    refine le_trans hstep ?_
    simp only [dyadicScale, one_mul]
    exact arith_zero_row (max (2 * A) Cexp) A η α hA1 (le_max_left _ _) hη hα1
      (2 ^ j') (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := j')) _ hE0
  ·
    have hS1 : (S.card : ℝ) ≤ 1 := by
      have hsub : S ⊆ ({⊤} : Finset (Ideal (𝓞 F))) := by simpa [idealDyadicBlock] using hS
      calc (S.card : ℝ) ≤ (({⊤} : Finset (Ideal (𝓞 F))).card : ℝ) :=
            by exact_mod_cast Finset.card_le_card hsub
        _ = 1 := by simp
    have hRcard : (R.card : ℝ) ≤ A * (2 * dyadicScale (i' + 1)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hR)
        (card_idealDyadicBlock_le A hA1 hAset (i' + 1))
    have hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤ := fun b hb => mem_block_squarefree 0 (hS hb)
    have hE0 : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := Finset.sum_nonneg (fun b _ => by positivity)
    have hprod : (R.card : ℝ) * (S.card : ℝ) ≤ 2 * A * dyadicScale (i' + 1) := by
      have hb0 : 0 ≤ A * (2 * dyadicScale (i' + 1)) := by
        have hA0 : 0 ≤ A := le_trans zero_le_one hA1
        have := dyadicScale_nonneg (i' + 1)
        positivity
      calc (R.card : ℝ) * (S.card : ℝ) ≤ (A * (2 * dyadicScale (i' + 1))) * 1 :=
            mul_le_mul hRcard hS1 (Nat.cast_nonneg _) hb0
        _ = 2 * A * dyadicScale (i' + 1) := by ring
    have hstep : ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
        ≤ 2 * A * dyadicScale (i' + 1) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
      le_trans (sum_sq_le_card_mul_energy Q R S lam hSsf)
        (mul_le_mul_of_nonneg_right hprod hE0)
    refine le_trans hstep ?_
    simp only [dyadicScale, mul_one, rpow_one_eq_one]
    exact arith_zero_col (max (2 * A) Cexp) A η α hA1 (le_max_left _ _) hη hα1
      (2 ^ i') (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := i')) _ hE0
  ·
    have hR' : R ⊆ paperShell F c (dyadicScale (i' + 1)) := by
      simpa [idealDyadicBlock, dyadicScale] using hR
    have hS' : S ⊆ paperShell F c (dyadicScale (j' + 1)) := by
      simpa [idealDyadicBlock, dyadicScale] using hS
    have hfilt : (paperShell F c (dyadicScale (j' + 1))).filter (fun b => b ∈ S) = S := by
      rw [Finset.filter_mem_eq_inter]
      exact (Finset.inter_eq_right).2 hS'
    have hrow : ∀ a : Ideal (𝓞 F),
        (∑ b ∈ S, lam b * (Q.χ b) a) =
          rowSum Q (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0) a := by
      intro a
      rw [rowSum]
      have hcong : (∑ b ∈ paperShell F c (dyadicScale (j' + 1)),
            (if b ∈ S then lam b else 0) * (Q.χ b) a)
          = ∑ b ∈ paperShell F c (dyadicScale (j' + 1)),
              (if b ∈ S then lam b * (Q.χ b) a else 0) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        by_cases hb : b ∈ S <;> simp [hb]
      rw [hcong, ← Finset.sum_filter, hfilt]
    have henergy : energy F c (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0)
        = ∑ b ∈ S, ‖lam b‖ ^ 2 := by
      rw [energy]
      have hcong : (∑ b ∈ paperShell F c (dyadicScale (j' + 1)),
            ‖(if b ∈ S then lam b else 0 : ℂ)‖ ^ 2)
          = ∑ b ∈ paperShell F c (dyadicScale (j' + 1)), (if b ∈ S then ‖lam b‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        by_cases hb : b ∈ S <;> simp [hb]
      rw [hcong, ← Finset.sum_filter, hfilt]
    have hQ1 : ∑ a ∈ R, ‖rowSum Q (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0) a‖ ^ 2
        ≤ Q1 F c Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1))
            (fun b => if b ∈ S then lam b else 0) := by
      rw [Q1]
      exact Finset.sum_le_sum_of_subset_of_nonneg hR' (fun a _ _ => by positivity)
    have hE0 : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := Finset.sum_nonneg (fun b _ => by positivity)
    have hB1 : Q1 F c Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1))
          (fun b => if b ∈ S then lam b else 0)
        ≤ B1 F c Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1)) *
          energy F c (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0) :=
      Q1_le_B1_mul_energy Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1)) _
    have hexp : B1 F c Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1))
        ≤ Cexp * Real.rpow (dyadicScale (i' + 1) * dyadicScale (j' + 1)) η *
            (dyadicScale (i' + 1) + Real.rpow (dyadicScale (j' + 1)) α) :=
      hCexpb _ _ (one_le_dyadicScale _) (one_le_dyadicScale _)
    have henergy0 : 0 ≤ energy F c (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0) := by
      rw [energy]; exact Finset.sum_nonneg (fun b _ => by positivity)
    have hbound : ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
        ≤ Cexp * Real.rpow (dyadicScale (i' + 1) * dyadicScale (j' + 1)) η *
            (dyadicScale (i' + 1) + Real.rpow (dyadicScale (j' + 1)) α) *
              ∑ b ∈ S, ‖lam b‖ ^ 2 := by
      calc ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
          = ∑ a ∈ R, ‖rowSum Q (dyadicScale (j' + 1))
              (fun b => if b ∈ S then lam b else 0) a‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun a _ => ?_); rw [hrow a]
        _ ≤ Q1 F c Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1))
              (fun b => if b ∈ S then lam b else 0) := hQ1
        _ ≤ B1 F c Q (dyadicScale (i' + 1)) (dyadicScale (j' + 1)) *
              energy F c (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0) := hB1
        _ ≤ (Cexp * Real.rpow (dyadicScale (i' + 1) * dyadicScale (j' + 1)) η *
              (dyadicScale (i' + 1) + Real.rpow (dyadicScale (j' + 1)) α)) *
              energy F c (dyadicScale (j' + 1)) (fun b => if b ∈ S then lam b else 0) :=
              mul_le_mul_of_nonneg_right hexp henergy0
        _ = Cexp * Real.rpow (dyadicScale (i' + 1) * dyadicScale (j' + 1)) η *
              (dyadicScale (i' + 1) + Real.rpow (dyadicScale (j' + 1)) α) *
                ∑ b ∈ S, ‖lam b‖ ^ 2 := by rw [henergy]
    refine le_trans hbound ?_
    have hM0 : 0 ≤ dyadicScale (i' + 1) := dyadicScale_nonneg _
    have hN0 : 0 ≤ dyadicScale (j' + 1) := dyadicScale_nonneg _
    have hA0 : 0 ≤ Real.rpow (dyadicScale (i' + 1) * dyadicScale (j' + 1)) η :=
      rpow_nonneg' _ (mul_nonneg hM0 hN0) η
    have hB0 : 0 ≤ dyadicScale (i' + 1) + Real.rpow (dyadicScale (j' + 1)) α := by
      have := rpow_nonneg' _ hN0 α
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0) hB0) hE0

theorem bilinear_endpoint_exponent_extension_contractions
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (i j : ℕ) (R S : Finset (Ideal (𝓞 F))),
        R ⊆ idealDyadicBlock F c i → S ⊆ idealDyadicBlock F c j →
        ∀ (u v lam : Ideal (𝓞 F) → ℂ),
          (∀ a ∈ R, ‖u a‖ ≤ 1) → (∀ b ∈ S, ‖v b‖ ≤ 1) →
          ∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2 ≤
            C * Real.rpow (dyadicScale i * dyadicScale j) η *
              (dyadicScale i + Real.rpow (dyadicScale j) α) *
                ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  intro η hη
  obtain ⟨C, hC, hmain⟩ := bilinear_endpoint_exponent_extension F c Q α hα hExponent η hη
  refine ⟨C, hC, ?_⟩
  intro i j R S hR hS u v lam hu hv
  have hnorm : ∀ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2
      ≤ ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 := by
    intro a ha
    have hrow : (∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b)
        = u a * (∑ b ∈ S, (lam b * v b) * (Q.χ b) a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_); ring
    rw [hrow, norm_mul]
    have hu' : ‖u a‖ ≤ 1 := hu a ha
    calc (‖u a‖ * ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖) ^ 2
        = ‖u a‖ ^ 2 * ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 := by ring
      _ ≤ 1 * ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hu') (by positivity)
      _ = ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 := by ring
  have henergy_le : ∑ b ∈ S, ‖lam b * v b‖ ^ 2 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := by
    refine Finset.sum_le_sum (fun b hb => ?_)
    rw [norm_mul]
    have hv' : ‖v b‖ ≤ 1 := hv b hb
    calc (‖lam b‖ * ‖v b‖) ^ 2 = ‖lam b‖ ^ 2 * ‖v b‖ ^ 2 := by ring
      _ ≤ ‖lam b‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv') (by positivity)
      _ = ‖lam b‖ ^ 2 := by ring
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hM0 : 0 ≤ dyadicScale i := dyadicScale_nonneg i
  have hN0 : 0 ≤ dyadicScale j := dyadicScale_nonneg j
  have hK0 : 0 ≤ C * Real.rpow (dyadicScale i * dyadicScale j) η *
      (dyadicScale i + Real.rpow (dyadicScale j) α) := by
    have h1 : 0 ≤ Real.rpow (dyadicScale i * dyadicScale j) η :=
      rpow_nonneg' _ (mul_nonneg hM0 hN0) η
    have h2 : 0 ≤ dyadicScale i + Real.rpow (dyadicScale j) α := by
      have := rpow_nonneg' _ hN0 α
      linarith
    exact mul_nonneg (mul_nonneg hC0 h1) h2
  exact le_trans (Finset.sum_le_sum hnorm)
    (le_trans (hmain i j R S hR hS (fun b => lam b * v b))
      (mul_le_mul_of_nonneg_left henergy_le hK0))

end DedekindZetaZeroFree.LargeSieve.Sieve
