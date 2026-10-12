module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.KPThreeShell

noncomputable section
open scoped BigOperators

def basis (j : ℤ) : Fin 3 → ℂ :=
  fun i => if i.val = (j % 3).toNat then 1 else 0

def tameFactor (Q : ℝ) (g₂ g₄ : ℂ) (l : ℕ) : ℂ :=
  if l % 3 = 0 then -(Q⁻¹ : ℝ)
  else if l % 3 = 1 then (Real.rpow Q (-(1 : ℝ) / 2) : ℂ) * g₄
  else (Real.rpow Q (-(1 : ℝ) / 2) : ℂ) * g₂

def shell (Q : ℝ) (g₂ g₄ : ℂ) (e : ℕ) : Fin 3 → ℂ :=
  (Real.rpow Q (-2 * (e : ℝ) / 3) : ℂ) •
    (basis (-(e : ℤ)) +
      (1 - (Q⁻¹ : ℝ) : ℂ) •
        ∑ l ∈ (Finset.range (e + 1)).filter (fun l => 1 ≤ l ∧ 3 ∣ l),
          (Real.rpow Q ((l : ℝ) / 3) : ℂ) • basis (-(e : ℤ) + 2 * (l : ℤ)) +
      ((Real.rpow Q (((e : ℝ) + 1) / 3) : ℂ) * tameFactor Q g₂ g₄ (e + 1)) •
        basis (-(e : ℤ) + 2 * ((e : ℤ) + 1)))

private lemma basis_mod (a b : ℤ) (h : a % 3 = b % 3) : basis a = basis b := by
  unfold basis
  rw [h]
private lemma basis_shift (a l : ℤ) (h : 3 ∣ l) : basis (a + 2*l) = basis a := by
  apply basis_mod
  rcases h with ⟨n, rfl⟩
  omega
def ss (Q : ℝ) (e : ℕ) : ℂ :=
  ∑ l ∈ (Finset.range (e+1)).filter (fun l => 1 ≤ l ∧ 3 ∣ l),
    (Real.rpow Q ((l : ℝ)/3) : ℂ)
private lemma vs (Q : ℝ) (e : ℕ) :
  (∑ l ∈ (Finset.range (e+1)).filter (fun l => 1 ≤ l ∧ 3 ∣ l),
    (Real.rpow Q ((l : ℝ)/3) : ℂ) • basis (-(e : ℤ) + 2*(l : ℤ))) =
    ss Q e • basis (-(e : ℤ)) := by
  rw [ss, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro l hl
  have h : 3 ∣ l := (Finset.mem_filter.mp hl).2.2
  rw [basis_shift _ _ (by exact_mod_cast h)]
private lemma ss_succ (Q : ℝ) (e : ℕ) : ss Q (e+1) = ss Q e +
    if 3 ∣ e+1 then (Real.rpow Q (((e+1 : ℕ) : ℝ)/3) : ℂ) else 0 := by
  simp only [ss, Finset.sum_filter, Finset.sum_range_succ]
  congr 1
  simp
private lemma ss_mod_one (Q : ℝ) (k : ℕ) : ss Q (3*k+1) = ss Q (3*k) := by
  rw [ss_succ]
  have h : ¬3 ∣ 3*k+1 := by omega
  simp [h]
private lemma ss_mod_two (Q : ℝ) (k : ℕ) : ss Q (3*k+2) = ss Q (3*k) := by
  rw [show 3*k+2 = (3*k+1)+1 by omega, ss_succ, ss_mod_one]
  have h : ¬3 ∣ 3*k+1+1 := by omega
  simp [h]
private lemma ss_three (Q : ℝ) (k : ℕ) : ss Q (3*(k+1)) = ss Q (3*k) + (Q : ℂ)^(k+1) := by
  rw [show 3*(k+1) = (3*k+2)+1 by omega, ss_succ, ss_mod_two]
  have h : 3 ∣ 3*k+2+1 := by omega
  simp only [h, ↓reduceIte]
  congr 1
  rw [show (((3*k+2+1 : ℕ) : ℝ)/3) = ((k+1 : ℕ) : ℝ) by push_cast; ring]
  simp only [Real.rpow_eq_pow, Real.rpow_natCast, Complex.ofReal_pow]
private lemma geom (Q : ℝ) (hQ : 1 < Q) (k : ℕ) :
    (1 - (Q⁻¹ : ℝ) : ℂ) * ss Q (3*k) = (Q : ℂ)^k - 1 := by
  have hn : (Q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hQ))
  induction k with
  | zero => simp [ss, Finset.sum_filter]
  | succ k ih =>
    rw [ss_three, mul_add, ih, pow_succ]
    push_cast
    field_simp
    ring
abbrev rp (Q x : ℝ) : ℂ := (Real.rpow Q x : ℂ)
private lemma rp_mul (Q : ℝ) (hQ : 1 < Q) (x y : ℝ) :
    rp Q x * rp Q y = rp Q (x+y) := by
  simp only [rp, Real.rpow_eq_pow, ← Complex.ofReal_mul, ← Real.rpow_add (by linarith : 0 < Q)]
private lemma rp_nat (Q : ℝ) (k : ℕ) : rp Q k = (Q : ℂ)^k := by
  simp [rp]
private lemma shell_residue (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) (k c : ℕ) (hc : c < 3) :
    shell Q g₂ g₄ (3*k+c) =
    rp Q (-2*((3*k+c : ℕ) : ℝ)/3) •
      (rp Q k • basis (-(c : ℤ)) +
      (rp Q ((((3*k+c : ℕ) : ℝ)+1)/3) * tameFactor Q g₂ g₄ (3*k+c+1)) • basis ((c : ℤ)+2)) := by
  have hs : ss Q (3*k+c) = ss Q (3*k) := by
    interval_cases c
    · rfl
    · exact ss_mod_one Q k
    · exact ss_mod_two Q k
  have hb : basis (-((3*k+c : ℕ) : ℤ)) = basis (-(c : ℤ)) := by
    apply basis_mod
    push_cast
    omega
  have hb' : basis (-((3*k+c : ℕ) : ℤ) + 2*(((3*k+c : ℕ) : ℤ)+1)) = basis ((c : ℤ)+2) := by
    apply basis_mod
    push_cast
    omega
  unfold shell
  rw [vs, hs, hb, hb', smul_smul, geom Q hQ k]
  rw [sub_smul, one_smul]
  simp only [add_sub_cancel, rp_nat]
private lemma zero_formula (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) (k : ℕ) :
    shell Q g₂ g₄ (3*k) =
    rp Q (-(k : ℝ)) • basis 0 + (rp Q (-(k : ℝ)-1/6)*g₄) • basis 2 := by
  have hf := shell_residue Q hQ g₂ g₄ k 0 (by omega)
  simp only [add_zero, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Int.cast_ofNat,
    Int.ofNat_zero, neg_zero, zero_add] at hf
  have ht : tameFactor Q g₂ g₄ (3*k+1) = rp Q (-1/2) * g₄ := by
    simp [tameFactor, rp, Nat.add_mod, Nat.mul_mod]
  rw [hf, ht, smul_add, smul_smul, smul_smul]
  rw [rp_mul Q hQ]
  congr 1
  · congr 2
    ring
  · rw [← mul_assoc, rp_mul Q hQ]
    rw [← mul_assoc, rp_mul Q hQ]
    congr 2
    ring
private lemma one_formula (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) (k : ℕ) :
    shell Q g₂ g₄ (3*k+1) =
    rp Q (-(k : ℝ)-2/3) • basis 2 + (rp Q (-(k : ℝ)-1/2)*g₂) • basis 0 := by
  have hf := shell_residue Q hQ g₂ g₄ k 1 (by omega)
  have hb : basis (-1) = basis 2 := by apply basis_mod; norm_num
  have hb' : basis (1+2) = basis 0 := by apply basis_mod; norm_num
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.ofNat_one, hb, hb'] at hf
  have ht : tameFactor Q g₂ g₄ (3*k+1+1) = rp Q (-1/2) * g₂ := by
    simp [tameFactor, rp, Nat.add_mod, Nat.mul_mod]
  rw [hf, ht, smul_add, smul_smul, smul_smul]
  rw [rp_mul Q hQ]
  congr 1
  · congr 2
    ring
  · rw [← mul_assoc, rp_mul Q hQ]
    rw [← mul_assoc, rp_mul Q hQ]
    congr 2
    ring
private lemma two_formula (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) (k : ℕ) :
    shell Q g₂ g₄ (3*k+2) = 0 := by
  have hf := shell_residue Q hQ g₂ g₄ k 2 (by omega)
  have hb : basis (-2) = basis 1 := by apply basis_mod; norm_num
  have hb' : basis (2+2) = basis 1 := by apply basis_mod; norm_num
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hb, hb'] at hf
  have ht : tameFactor Q g₂ g₄ (3*k+2+1) = -(Q⁻¹ : ℝ) := by
    simp [tameFactor, Nat.add_mod, Nat.mul_mod]
  have hi : (Q⁻¹ : ℝ) = Real.rpow Q (-1) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg (by linarith : 0 ≤ Q), Real.rpow_one]
  rw [hf, ht, hi]
  change rp Q _ • (rp Q _ • basis 1 + (rp Q _ * (-rp Q (-1))) • basis 1) = 0
  rw [mul_neg, rp_mul Q hQ]
  have he : (3*(k : ℝ)+2+1)/3+-1 = (k : ℝ) := by ring
  rw [he, neg_smul, add_neg_cancel, smul_zero]
private lemma zero_final (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) :
    shell Q g₂ g₄ 0 = basis 0 + (rp Q (-1/6)*g₄) • basis 2 := by
  convert zero_formula Q hQ g₂ g₄ 0 using 1 <;> norm_num [rp]
private lemma three_final (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) (k : ℕ) :
    shell Q g₂ g₄ (3*k) = rp Q (-(k : ℝ)) • shell Q g₂ g₄ 0 := by
  rw [zero_formula Q hQ, zero_final Q hQ, smul_add, smul_smul]
  rw [← mul_assoc, rp_mul Q hQ]
  congr 2
  congr 1
  ring
private lemma one_final (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) (hg : g₂*g₄=1) (k : ℕ) :
    shell Q g₂ g₄ (3*k+1) = (rp Q (-(k : ℝ)-1/2)*g₂) • shell Q g₂ g₄ 0 := by
  rw [one_formula Q hQ, zero_final Q hQ, smul_add, smul_smul]
  have hm : (rp Q (-(k : ℝ)-1/2)*g₂) * (rp Q (-1/6)*g₄) = rp Q (-(k : ℝ)-2/3) := by
    calc
      _ = (rp Q (-(k : ℝ)-1/2)*rp Q (-1/6))*(g₂*g₄) := by ring
      _ = _ := by rw [hg, mul_one, rp_mul Q hQ]; congr 1; ring
  rw [hm, add_comm]

theorem shell_zero (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ) :
    shell Q g₂ g₄ 0 = basis 0 + ((Real.rpow Q (-(1 : ℝ) / 6) : ℂ) * g₄) • basis 2 := by
  exact zero_final Q hQ g₂ g₄

theorem shell_three_mul (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ)
    (hg : g₂ * g₄ = 1) (k : ℕ) :
    shell Q g₂ g₄ (3 * k) = (Real.rpow Q (-(k : ℝ)) : ℂ) • shell Q g₂ g₄ 0 := by
  exact three_final Q hQ g₂ g₄ k

theorem shell_three_mul_add_one (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ)
    (hg : g₂ * g₄ = 1) (k : ℕ) :
    shell Q g₂ g₄ (3 * k + 1) =
      ((Real.rpow Q (-(k : ℝ) - (1 : ℝ) / 2) : ℂ) * g₂) • shell Q g₂ g₄ 0 := by
  exact one_final Q hQ g₂ g₄ hg k

theorem shell_three_mul_add_two (Q : ℝ) (hQ : 1 < Q) (g₂ g₄ : ℂ)
    (hg : g₂ * g₄ = 1) (k : ℕ) :
    shell Q g₂ g₄ (3 * k + 2) = 0 := by
  exact two_formula Q hQ g₂ g₄ k

end

end DedekindZetaZeroFree.KPThreeShell
