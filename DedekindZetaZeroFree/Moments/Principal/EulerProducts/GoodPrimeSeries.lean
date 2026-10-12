module

public import DedekindZetaZeroFree.CharacterSums.Gauss.PositiveDepthLocalSums
public import DedekindZetaZeroFree.CharacterSums.Gauss.Sextic.WeilCorrection
public import DedekindZetaZeroFree.CharacterSums.Gauss.Sextic.InversePowerProduct

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma good_series_Q_gt_one (p : ExteriorPrime A) : 1 < Q p := by
  change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
private lemma good_series_Ctk_bound (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (t k J : ℕ) : ‖Ctk C p t k J‖ ≤ Q p ^ (t+k) := by
  have hQ := good_series_Q_gt_one p
  have hQ0 : 0 < Q p := lt_trans zero_lt_one hQ
  rcases t with _ | t
  · rcases k with _ | k
    · simp [Ctk_zero_zero]
    · rw [Ctk_zero_pos C p (k+1) J (by omega)]
      split_ifs <;> simp only [norm_one, norm_zero, zero_add]
      · exact one_le_pow₀ hQ.le
      · positivity
  · rcases k with _ | _ | k
    · simpa using norm_Ctk_zero_le C p (t+1) J (by omega)
    · refine (norm_Ctk_one_le C p (t+1) J (by omega)).trans ?_
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hQ.le
      push_cast
      linarith
    · rw [Ctk_eq_zero_of_two_le C p (t+1) (k+2) J (by omega) (by omega)]
      simp only [norm_zero]
      positivity
private lemma good_series_vartheta_norm (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) : ‖vartheta C p‖ = 1 := by
  exact Circle.norm_coe _
private lemma good_series_qPower_norm (p : ExteriorPrime A) (s : ℂ) :
    ‖qPower p s‖ = Real.exp (s.re * Real.log (Q p)) := by
  simp [qPower, Complex.norm_exp]
private lemma good_series_term_bound (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1}) (e : Fin 2) (l k m : ℕ) (ξ w z : ℂ) :
    ‖seriesTerm C p j θ e l k m ξ w z‖ ≤
      (‖gammaTwo C p‖ * Real.exp ((1/2 - ξ.re) * Real.log (Q p))) ^ e.val *
      (Real.exp ((2 - 3 * ξ.re) * Real.log (Q p))) ^ l *
      (Real.exp ((1 - w.re) * Real.log (Q p))) ^ k *
      (Real.exp ((-6 * z.re) * Real.log (Q p))) ^ m := by
  have hQ0 : 0 < Q p := lt_trans zero_lt_one (good_series_Q_gt_one p)
  have hc := good_series_Ctk_bound C p (e.val + 3*l) k (j.val+6*m)
  have hpow : Q p ^ (e.val+3*l+k) =
      Real.exp (((e.val+3*l+k : ℕ) : ℝ) * Real.log (Q p)) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ0]
  unfold seriesTerm
  simp only [norm_mul, norm_pow, norm_zpow, θ.property, one_zpow, good_series_vartheta_norm,
    one_pow, mul_one, good_series_qPower_norm]
  calc
    _ ≤ ‖gammaTwo C p‖ ^ e.val * Q p ^ (e.val+3*l+k) *
        Real.exp ((-(e.val : ℂ) * (1/2+ξ) - (l : ℂ) * (1+3*ξ) -
          (k : ℂ)*w - 6*(m : ℂ)*z).re * Real.log (Q p)) := by
      gcongr
    _ = _ := by
      rw [hpow, mul_pow]
      simp only [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      simp
      push_cast
      ring

theorem good_euler_series_summable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 ξ w z‖) := by
  let a := ‖gammaTwo C p‖ * Real.exp ((1/2 - ξ.re) * Real.log (Q p))
  let b := Real.exp ((2 - 3*ξ.re) * Real.log (Q p))
  let c := Real.exp ((1-w.re) * Real.log (Q p))
  let d := Real.exp ((-6*z.re) * Real.log (Q p))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := (Real.exp_pos _).le
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hlog : 0 < Real.log (Q p) := Real.log_pos (good_series_Q_gt_one p)
  have sb : Summable (fun l : ℕ => b^l) := by
    apply summable_geometric_of_lt_one hb
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) hlog
  have sc : Summable (fun k : ℕ => c^k) := by
    apply summable_geometric_of_lt_one hc
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) hlog
  have sd : Summable (fun m : ℕ => d^m) := by
    apply summable_geometric_of_lt_one hd
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) hlog
  have sa : Summable (fun e : Fin 2 => a^e.val) := (hasSum_fintype _).summable
  have scd := sc.mul_of_nonneg sd (fun _ => pow_nonneg hc _) (fun _ => pow_nonneg hd _)
  have sbcd := sb.mul_of_nonneg scd (fun _ => pow_nonneg hb _) (by intro i; exact mul_nonneg (pow_nonneg hc _) (pow_nonneg hd _))
  have sall := sa.mul_of_nonneg sbcd (fun _ => pow_nonneg ha _) (by intro i; exact mul_nonneg (pow_nonneg hb _) (mul_nonneg (pow_nonneg hc _) (pow_nonneg hd _)))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) sall
  simpa only [a, b, c, d, mul_assoc] using
    good_series_term_bound C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 ξ w z

theorem good_euler_geometric_shell_sum (V W D E q : ℂ) (hE : ‖E‖ < 1) :
    (∑' d : ℕ, (E ^ (d + 1) * ((1 - q⁻¹) / (1 - V) + W) -
      D * E ^ d * (1 + (q - 1) * W * V / (1 - V)))) =
      E / (1 - E) * ((1 - q⁻¹) / (1 - V) + W) -
      D / (1 - E) * (1 + (q - 1) * W * V / (1 - V)) := by
  have sE := summable_geometric_of_norm_lt_one hE
  have sEp : Summable (fun d : ℕ => E ^ (d + 1)) := by
    simpa only [pow_succ] using sE.mul_right E
  rw [(sEp.mul_right _).tsum_sub ((sE.mul_left D).mul_right _),
    tsum_mul_right, tsum_mul_right, tsum_mul_left]
  have hp : (∑' d : ℕ, E ^ (d + 1)) = E / (1 - E) := by
    simp only [pow_succ, tsum_mul_right, tsum_geometric_of_norm_lt_one hE, div_eq_mul_inv]
    ring
  rw [hp, tsum_geometric_of_norm_lt_one hE]
  simp only [div_eq_mul_inv]

open CanonicalLocalGaussTable CanonicalGaussInversePower

private lemma good_strict_tau_period (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (a b : ℤ) (h : a % 6 = b % 6) : tau C p a = tau C p b := by
  unfold tau
  rw [T_eq_finiteField, T_eq_finiteField]
  simp only [SArithmeticData.sexticExponent, h]
private lemma good_strict_shell_six_kzero (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (d m : ℕ) (hd : 0 < d) :
    Ctk C p (6*d) 0 (6*m) =
      if d ≤ m then (Q p : ℂ)^(6*d-1)*((Q p : ℂ)-1) else 0 := by
  rw [Ctk_pos_zero C p _ _ (by omega), T_generator_power]
  have hdvd : (6 : ℤ) ∣ (6*d : ℕ) := by exact ⟨(d : ℤ), by push_cast; ring⟩
  simp only [hdvd, if_true]
  have hle : 6*d-1 ≤ 6*m ↔ d ≤ m := by omega
  by_cases hdm : d ≤ m
  · have hne : 6*m-(6*d-1) ≠ 0 := by omega
    simp [hle, hdm, hne]
  · simp [hle, hdm]
private lemma good_strict_shell_six_kone (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (d m : ℕ) (hd : 0 < d) :
    Ctk C p (6*d) 1 (6*m) =
      if d = m then (Q p : ℂ)^(6*d) else 0 := by
  rw [Ctk_one C p _ _ (by omega), T_generator_power]
  have hndvd : ¬ (6 : ℤ) ∣ (6*d : ℕ) - 1 := by
    rw [Int.dvd_iff_emod_eq_zero]; push_cast; omega
  have htau : tau C p ((6*d : ℕ)-1) = tau C p 5 := by
    apply good_strict_tau_period; push_cast; omega
  simp only [hndvd, if_false, htau]
  by_cases hdm : d = m
  · subst m
    simp only [le_refl, if_true, Nat.sub_self]
    rw [mul_right_comm, tau_one_mul_tau_five, ← pow_succ']
    congr 1; omega
  · by_cases hle : 6*d ≤ 6*m
    · have hne : 6*m-6*d ≠ 0 := by omega
      simp [hdm, hle, hne]
    · simp [hdm, hle]
private lemma good_strict_shell_one_kzero (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (d m : ℕ) :
    Ctk C p (6*d+1) 0 (6*m) =
      if d = m then (Q p : ℂ)^(6*d)*tau C p 1 else 0 := by
  rw [Ctk_pos_zero C p _ _ (by omega), T_generator_power]
  have hndvd : ¬ (6 : ℤ) ∣ (6*d+1 : ℕ) := by
    rw [Int.dvd_iff_emod_eq_zero]; push_cast; omega
  have htau : tau C p (6*d+1 : ℕ) = tau C p 1 := by
    apply good_strict_tau_period; push_cast; omega
  simp only [Nat.add_sub_cancel, hndvd, if_false, htau]
  by_cases hdm : d = m
  · subst m; simp
  · by_cases hle : 6*d ≤ 6*m
    · have hne : 6*m-6*d ≠ 0 := by omega
      simp [hdm, hle, hne]
    · simp [hdm, hle]
private lemma good_strict_shell_one_kone (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (d m : ℕ) :
    Ctk C p (6*d+1) 1 (6*m) =
      if d < m then tau C p 1 * (Q p : ℂ)^(6*d)*((Q p : ℂ)-1) else 0 := by
  rw [Ctk_one C p _ _ (by omega), T_generator_power]
  have hdvd : (6 : ℤ) ∣ (6*d+1 : ℕ)-1 := by
    exact ⟨(d : ℤ), by push_cast; ring⟩
  have hle : 6*d+1 ≤ 6*m ↔ d < m := by omega
  simp only [Nat.add_sub_cancel, hdvd, if_true, hle]
  by_cases hdm : d < m
  · have hne : 6*m-(6*d+1) ≠ 0 := by omega
    simp [hdm, hne]
  · simp [hdm]
private lemma good_strict_shell_odd_zero (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : Fin 2) (d k m : ℕ) : Ctk C p (e.val+3*(2*d+1)) k (6*m) = 0 := by
  have ht : 0 < e.val+3*(2*d+1) := by omega
  have hndvd : ¬ (6 : ℤ) ∣ (e.val+3*(2*d+1) : ℕ) := by
    rw [Int.dvd_iff_emod_eq_zero]; push_cast; omega
  have hndvd' : ¬ (6 : ℤ) ∣ (e.val+3*(2*d+1) : ℕ)-1 := by
    rw [Int.dvd_iff_emod_eq_zero]; push_cast; omega
  push_cast at hndvd hndvd'
  rcases k with _ | _ | k
  · rw [Ctk_pos_zero C p _ _ ht, T_generator_power]
    by_cases hle : e.val+3*(2*d+1)-1 ≤ 6*m
    · have he := e.isLt
      have hne : 6*m-(e.val+3*(2*d+1)-1) ≠ 0 := by omega
      simp [hle, hne, hndvd]
    · simp [hle]
  · rw [Ctk_one C p _ _ ht, T_generator_power]
    by_cases hle : e.val+3*(2*d+1) ≤ 6*m
    · have hne : 6*m-(e.val+3*(2*d+1)) ≠ 0 := by omega
      simp [hle, hne, hndvd']
    · simp [hle]
  · exact Ctk_eq_zero_of_two_le C p _ _ _ ht (by omega)
private lemma good_strict_qp_add (p : ExteriorPrime A) (s t : ℂ) : qPower p (s+t) = qPower p s * qPower p t := by
  unfold qPower; rw [add_mul, Complex.exp_add]
private lemma good_strict_qp_nat_mul (p : ExteriorPrime A) (s : ℂ) (n : ℕ) : qPower p (n*s) = qPower p s ^ n := by
  unfold qPower; rw [mul_assoc, Complex.exp_nat_mul]
private lemma good_strict_qp_nat (p : ExteriorPrime A) (n : ℕ) : qPower p n = (Q p : ℂ)^n := by
  have hQ : 0 < Q p := by
    change 0 < (Ideal.absNorm p.val.asIdeal : ℝ)
    exact_mod_cast lt_trans (by decide : 0 < 1) (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
  rw [show (n : ℂ) = n*(1 : ℂ) by ring, good_strict_qp_nat_mul]
  simp [qPower, ← Complex.ofReal_exp, Real.exp_log hQ]
private lemma good_strict_weight_even (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (hθ6 : θ.val^6 = 1)
    (e : Fin 2) (d k m : ℕ) (ξ w z : ℂ) :
    seriesTerm C p 0 θ e (2*d) k m ξ w z =
      (gammaTwo C p * vartheta C p * θ.val⁻¹ * qPower p (-1/2-ξ))^e.val *
      (vartheta C p^6 * qPower p (-2-6*ξ))^d *
      (θ.val*qPower p (-w))^k * qPower p (-6*z)^m *
      Ctk C p (e.val+6*d) k (6*m) := by
  have hne : θ.val ≠ 0 := by intro h; have := θ.property; simp [h] at this
  have hpow : θ.val ^ ((k : ℤ)-(e.val : ℤ)-3*((2*d : ℕ) : ℤ)) = θ.val^k * (θ.val⁻¹)^e.val := by
    rw [show (k : ℤ)-(e.val : ℤ)-3*((2*d : ℕ) : ℤ) = (k : ℤ)-(e.val : ℤ)-(6:ℤ)*(d:ℤ) by push_cast; ring,
      zpow_sub₀ hne, zpow_sub₀ hne, zpow_natCast, zpow_natCast, zpow_mul,
      zpow_ofNat, hθ6, one_zpow, div_one, div_eq_mul_inv, inv_pow]
  have hq : qPower p (-(e.val : ℂ)*(1/2+ξ)-(2*d : ℕ)*(1+3*ξ)-(k : ℂ)*w-6*(m : ℂ)*z) =
      qPower p (-1/2-ξ)^e.val * qPower p (-2-6*ξ)^d * qPower p (-w)^k * qPower p (-6*z)^m := by
    rw [show -(e.val : ℂ)*(1/2+ξ)-(2*d : ℕ)*(1+3*ξ)-(k : ℂ)*w-6*(m : ℂ)*z =
      ((e.val : ℂ)*(-1/2-ξ)+(d : ℂ)*(-2-6*ξ)+(k : ℂ)*(-w))+(m : ℂ)*(-6*z) by push_cast; ring]
    simp only [good_strict_qp_add, good_strict_qp_nat_mul]
  unfold seriesTerm
  simp only [Fin.val_zero, zero_add, show 3*(2*d)=6*d by omega]
  rw [hpow, hq, pow_add, pow_mul]
  simp only [mul_pow]
  ring
private lemma good_strict_geom_tail (V : ℂ) (hV : ‖V‖ < 1) (d : ℕ) :
    (∑' m : ℕ, if d ≤ m then V^m else 0) = V^d/(1-V) := by
  have hi : Function.Injective (fun n : ℕ => n+d) := by intro a b h; dsimp at h; omega
  have hs : Function.support (fun m : ℕ => if d ≤ m then V^m else 0) ⊆
      Set.range (fun n : ℕ => n+d) := by
    intro m hm
    have hdm : d ≤ m := by by_contra h; simp [h] at hm
    exact ⟨m-d, by dsimp; omega⟩
  rw [← hi.tsum_eq hs]
  simp only [Nat.le_add_left, if_true, pow_add, tsum_mul_right,
    tsum_geometric_of_norm_lt_one hV, div_eq_mul_inv]
  ring
private lemma good_strict_geom_strict_tail (V : ℂ) (hV : ‖V‖ < 1) (d : ℕ) :
    (∑' m : ℕ, if d < m then V^m else 0) = V^(d+1)/(1-V) := by
  simpa only [Nat.succ_le_iff] using good_strict_geom_tail V hV (d+1)
private lemma good_strict_even_shell_sum_zero (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (B W V : ℂ) (hV : ‖V‖ < 1) (d : ℕ) (hd : 0 < d) :
    (∑' k : ℕ, ∑' m : ℕ, B^d*W^k*V^m*Ctk C p (6*d) k (6*m)) =
      (B*(Q p : ℂ)^6*V)^d * ((1-(Q p : ℂ)⁻¹)/(1-V)+W) := by
  have hk (k : ℕ) (hk : 2 ≤ k) :
      (∑' m : ℕ, B^d*W^k*V^m*Ctk C p (6*d) k (6*m)) = 0 := by
    simp_rw [Ctk_eq_zero_of_two_le C p (6*d) k _ (by omega) hk, mul_zero]
    exact tsum_zero
  have hsplit :
      (∑' k : ℕ, ∑' m : ℕ, B^d*W^k*V^m*Ctk C p (6*d) k (6*m)) =
      (∑' m : ℕ, B^d*V^m*Ctk C p (6*d) 0 (6*m)) +
      (∑' m : ℕ, B^d*W*V^m*Ctk C p (6*d) 1 (6*m)) := by
    rw [tsum_eq_sum (s := {0,1}) (by intro k h; apply hk; simp at h; omega)]
    simp
  rw [hsplit]
  simp_rw [good_strict_shell_six_kzero C p d _ hd, good_strict_shell_six_kone C p d _ hd]
  have heq : (∑' m : ℕ, B^d*W*V^m*(if d=m then (Q p : ℂ)^(6*d) else 0)) =
      B^d*W*V^d*(Q p : ℂ)^(6*d) := by
    simp_rw [mul_ite, mul_zero]
    exact tsum_ite_eq' d _
  rw [heq]
  have ht : (∑' m : ℕ, B^d*V^m*(if d ≤ m then (Q p : ℂ)^(6*d-1)*((Q p : ℂ)-1) else 0)) =
      B^d*(Q p : ℂ)^(6*d-1)*((Q p : ℂ)-1)*(V^d/(1-V)) := by
    calc
      _ = ∑' m : ℕ, (B^d*(Q p : ℂ)^(6*d-1)*((Q p : ℂ)-1))*(if d ≤ m then V^m else 0) := by
        congr 1; funext m; split_ifs <;> ring
      _ = _ := by rw [tsum_mul_left, good_strict_geom_tail V hV d]
  rw [ht]
  have hQ : (Q p : ℂ) ≠ 0 := by
    have : 1 < Q p := by
      change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hpow : (Q p : ℂ)^(6*d-1) = (Q p : ℂ)^(6*d) * (Q p : ℂ)⁻¹ := by
    rw [pow_sub₀ _ hQ (by omega), pow_one]
  rw [hpow]
  simp only [mul_pow, ← pow_mul]
  field_simp
  <;> ring
private lemma good_strict_even_shell_sum_one (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (H B W V : ℂ) (hV : ‖V‖ < 1) (d : ℕ) :
    (∑' k : ℕ, ∑' m : ℕ, H*B^d*W^k*V^m*Ctk C p (6*d+1) k (6*m)) =
      H*tau C p 1*(B*(Q p : ℂ)^6*V)^d * (1+((Q p : ℂ)-1)*W*V/(1-V)) := by
  have hk (k : ℕ) (hk : 2 ≤ k) :
      (∑' m : ℕ, H*B^d*W^k*V^m*Ctk C p (6*d+1) k (6*m)) = 0 := by
    simp_rw [Ctk_eq_zero_of_two_le C p (6*d+1) k _ (by omega) hk, mul_zero]
    exact tsum_zero
  rw [tsum_eq_sum (s := {0,1}) (by intro k h; apply hk; simp at h; omega)]
  simp only [Finset.sum_insert (by simp : (0 : ℕ) ∉ {1}), Finset.sum_singleton,
    pow_zero, pow_one, mul_one]
  simp_rw [good_strict_shell_one_kzero C p d _, good_strict_shell_one_kone C p d _]
  have heq : (∑' m : ℕ, H*B^d*V^m*(if d=m then (Q p : ℂ)^(6*d)*tau C p 1 else 0)) =
      H*B^d*V^d*(Q p : ℂ)^(6*d)*tau C p 1 := by
    simp_rw [mul_ite, mul_zero]
    simpa only [mul_assoc] using tsum_ite_eq' d (fun m => H*B^d*V^m*((Q p : ℂ)^(6*d)*tau C p 1))
  rw [heq]
  have ht : (∑' m : ℕ, H*B^d*W*V^m*(if d < m then tau C p 1*(Q p : ℂ)^(6*d)*((Q p : ℂ)-1) else 0)) =
      H*B^d*W*tau C p 1*(Q p : ℂ)^(6*d)*((Q p : ℂ)-1)*(V^(d+1)/(1-V)) := by
    calc
      _ = ∑' m : ℕ, (H*B^d*W*tau C p 1*(Q p : ℂ)^(6*d)*((Q p : ℂ)-1))*(if d < m then V^m else 0) := by
        congr 1; funext m; split_ifs <;> ring
      _ = _ := by rw [tsum_mul_left, good_strict_geom_strict_tail V hV d]
  rw [ht]
  simp only [mul_pow, ← pow_mul, pow_succ, div_eq_mul_inv]
  ring
private lemma good_strict_BQV (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (ξ z : ℂ) :
    (vartheta C p^6*qPower p (-2-6*ξ))*(Q p : ℂ)^6*qPower p (-6*z) =
      vartheta C p^6*qPower p (4-6*ξ)*qPower p (-6*z) := by
  rw [← good_strict_qp_nat p 6]
  rw [mul_assoc (vartheta C p^6), ← good_strict_qp_add]
  congr 2; congr 1; ring
private lemma good_strict_Htau (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (ξ : ℂ) :
    (gammaTwo C p*vartheta C p*θ.val⁻¹*qPower p (-1/2-ξ))*tau C p 1 =
      -(η p.val.asIdeal*star θ.val*qPower p (-ξ)) := by
  have hinv : θ.val⁻¹ = star θ.val := by
    apply inv_eq_of_mul_eq_one_right
    rw [RCLike.star_def, Complex.mul_conj', θ.property]
    norm_num
  rw [show (-1/2-ξ : ℂ) = -1/2+(-ξ) by ring, good_strict_qp_add]
  have hh := CanonicalGaussCorrection.gammaTwo_vartheta_tau_one C p
  calc
    _ = (gammaTwo C p*vartheta C p*tau C p 1*qPower p (-1/2))*θ.val⁻¹*qPower p (-ξ) := by ring
    _ = _ := by rw [hh, hinv]; ring
private lemma good_strict_even_shell_sum_origin (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (W V : ℂ) (hW : ‖W‖ < 1) (hV : ‖V‖ < 1) :
    (∑' k : ℕ, ∑' m : ℕ, W^k*V^m*Ctk C p 0 k (6*m)) = 1/(1-V)+W/(1-W) := by
  have hterm (k m : ℕ) : W^k*V^m*Ctk C p 0 k (6*m) =
      if k=0 then V^m else if m=0 then W^k else 0 := by
    by_cases hk : k=0
    · subst k; simp [Ctk_zero_zero]
    · rw [Ctk_zero_pos C p k _ (Nat.pos_of_ne_zero hk)]
      by_cases hm : m=0 <;> simp [hk, hm]
  have hinner (k : ℕ) : (∑' m : ℕ, W^k*V^m*Ctk C p 0 k (6*m)) =
      if k=0 then 1/(1-V) else W^k := by
    simp_rw [hterm]
    by_cases hk : k=0
    · simp [hk, tsum_geometric_of_norm_lt_one hV, div_eq_mul_inv]
    · simp [hk]
  simp_rw [hinner]
  have hs : Summable (fun k : ℕ => if k=0 then 1/(1-V) else W^k) := by
    exact (summable_geometric_of_norm_lt_one hW).congr_cofinite (by
      filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
      simp [hk])
  rw [hs.tsum_eq_zero_add]
  simp only [if_true, Nat.succ_ne_zero, if_false, pow_succ,
    tsum_mul_right, tsum_geometric_of_norm_lt_one hW, div_eq_mul_inv]
  ring
private lemma good_strict_boundary_norms (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    ‖qPower p (-6*z)‖ < 1 ∧ ‖θ.val*qPower p (-w)‖ < 1 ∧
    ‖vartheta C p^6*qPower p (4-6*ξ)*qPower p (-6*z)‖ < 1 := by
  have hQ : 1 < Q p := by
    change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
  have hn (s : ℂ) : ‖qPower p s‖ = Real.exp (s.re*Real.log (Q p)) := by
    simp [qPower, Complex.norm_exp]
  have hv : ‖vartheta C p‖ = 1 := Circle.norm_coe _
  have hlog := Real.log_pos hQ
  constructor
  · rw [hn]; apply Real.exp_lt_one_iff.mpr
    apply mul_neg_of_neg_of_pos _ hlog; simp; linarith
  constructor
  · rw [norm_mul, θ.property, one_mul, hn]; apply Real.exp_lt_one_iff.mpr
    apply mul_neg_of_neg_of_pos _ hlog; simp; linarith
  · simp only [norm_mul, norm_pow, hv, one_pow, one_mul, hn, ← Real.exp_add]
    apply Real.exp_lt_one_iff.mpr
    simp; nlinarith
private lemma good_strict_ib_evaluation (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (θ : {θ : ℂ // ‖θ‖ = 1})
    (hθ : θ.val = chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    let V := qPower p (-6*z)
    let W := θ.val*qPower p (-w)
    let D := η p.val.asIdeal*star θ.val*qPower p (-ξ)
    let E := vartheta C p^6*qPower p (4-6*ξ)*V
    f C p 0 θ ξ w z = 1/(1-V)+W/(1-W)+
      E/(1-E)*((1-(Q p : ℂ)⁻¹)/(1-V)+W)-
      D/(1-E)*(1+((Q p : ℂ)-1)*W*V/(1-V)) := by
  let V := qPower p (-6*z)
  let W := θ.val*qPower p (-w)
  let D := η p.val.asIdeal*star θ.val*qPower p (-ξ)
  let E := vartheta C p^6*qPower p (4-6*ξ)*V
  let B := vartheta C p^6*qPower p (-2-6*ξ)
  let H := gammaTwo C p*vartheta C p*θ.val⁻¹*qPower p (-1/2-ξ)
  change f C p 0 θ ξ w z = 1/(1-V)+W/(1-W)+
    E/(1-E)*((1-(Q p : ℂ)⁻¹)/(1-V)+W)-D/(1-E)*(1+((Q p : ℂ)-1)*W*V/(1-V))
  obtain ⟨hV,hW,hE⟩ := good_strict_boundary_norms C p θ ξ w z hξ hw hz
  change ‖V‖ < 1 at hV
  change ‖W‖ < 1 at hW
  change ‖E‖ < 1 at hE
  have hθ6 : θ.val^6=1 := by rw [hθ]; exact chi_unit_sixth p _ hu
  have sall := (good_euler_series_summable C p 0 θ ξ w z hξ hw hz).of_norm
  let L (e : Fin 2) (l : ℕ) := ∑' i : ℕ × ℕ, seriesTerm C p 0 θ e l i.1 i.2 ξ w z
  have sL (e : Fin 2) : Summable (L e) := (sall.prod_factor e).prod
  have hprod (e : Fin 2) (l : ℕ) : L e l = ∑' k : ℕ, ∑' m : ℕ, seriesTerm C p 0 θ e l k m ξ w z :=
    ((sall.prod_factor e).prod_factor l).tsum_prod
  have hodd (e : Fin 2) (d : ℕ) : L e (2*d+1)=0 := by
    rw [hprod]
    have ht (k m : ℕ) : seriesTerm C p 0 θ e (2*d+1) k m ξ w z = 0 := by
      unfold seriesTerm
      simp only [Fin.val_zero, zero_add, good_strict_shell_odd_zero C p e d k m, mul_zero, zero_mul]
    simp_rw [ht, tsum_zero]
  have hi : Function.Injective (fun d : ℕ => 2*d) := by intro a b h; dsimp at h; omega
  have heven (e : Fin 2) : (∑' l, L e l) = ∑' d, L e (2*d) := by
    symm; apply hi.tsum_eq
    intro l hl
    change L e l ≠ 0 at hl
    have hmod : l % 2 = 0 := by
      by_contra hn
      have heq : l=2*(l/2)+1 := by omega
      rw [heq, hodd] at hl
      exact hl rfl
    exact ⟨l/2, by dsimp; omega⟩
  have h0 (d : ℕ) (hd : 0 < d) : L 0 (2*d) = E^d*((1-(Q p : ℂ)⁻¹)/(1-V)+W) := by
    rw [hprod]
    simp_rw [good_strict_weight_even C p θ hθ6]
    simp only [Fin.val_zero, pow_zero, one_mul, zero_add]
    rw [good_strict_even_shell_sum_zero C p B W V hV d hd]
    rw [show B*(Q p : ℂ)^6*V = E from good_strict_BQV C p ξ z]
  have h00 : L 0 0 = 1/(1-V)+W/(1-W) := by
    rw [show (0 : ℕ) = 2*0 by omega, hprod]
    simp_rw [good_strict_weight_even C p θ hθ6]
    simp only [Fin.val_zero, pow_zero, one_mul, mul_zero, zero_add]
    exact good_strict_even_shell_sum_origin C p W V hW hV
  have h1 (d : ℕ) : L 1 (2*d) = -D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V)) := by
    rw [hprod]
    simp_rw [good_strict_weight_even C p θ hθ6]
    simp only [Fin.val_one, pow_one]
    simp only [show 1+6*d=6*d+1 by omega]
    rw [good_strict_even_shell_sum_one C p H B W V hV d]
    rw [show B*(Q p : ℂ)^6*V = E from good_strict_BQV C p ξ z,
      show H*tau C p 1 = -D from good_strict_Htau C p θ ξ]
  have s0 : Summable (fun d : ℕ => L 0 (2*d)) := (sL 0).comp_injective hi
  unfold f
  rw [sall.tsum_prod, tsum_fintype, Fin.sum_univ_two]
  rw [(sall.prod_factor 0).tsum_prod, (sall.prod_factor 1).tsum_prod]
  change (∑' l, L 0 l)+(∑' l, L 1 l)=_
  rw [heven 0, heven 1, s0.tsum_eq_zero_add, h00]
  have h0' (d : ℕ) := h0 (d+1) (by omega)
  simp_rw [h0', h1]
  have sE := summable_geometric_of_norm_lt_one hE
  have sEp : Summable (fun d : ℕ => E^(d+1)) := by simpa only [pow_succ] using sE.mul_right E
  have sg := (sE.mul_left D).mul_right (1+((Q p : ℂ)-1)*W*V/(1-V))
  have sp := sEp.mul_right ((1-(Q p : ℂ)⁻¹)/(1-V)+W)
  have hg : (∑' d : ℕ, -D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V))) =
      -(∑' d : ℕ, D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V))) := by
    simp only [neg_mul, tsum_neg]
  rw [hg]
  rw [show (1/(1-V)+W/(1-W)+(∑' d : ℕ, E^(d+1)*((1-(Q p : ℂ)⁻¹)/(1-V)+W)))+
      -(∑' d : ℕ, D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V))) =
      1/(1-V)+W/(1-W)+((∑' d : ℕ, E^(d+1)*((1-(Q p : ℂ)⁻¹)/(1-V)+W))-
        (∑' d : ℕ, D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V)))) by ring]
  rw [← sp.tsum_sub sg, good_euler_geometric_shell_sum V W D E (Q p : ℂ) hE]
  ring

theorem good_euler_series (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (θ : {θ : ℂ // ‖θ‖ = 1})
    (hθ : θ.val = chi (σ := σ) p
      (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    let V := qPower p (-6 * z)
    let W := θ.val * qPower p (-w)
    let D := η p.val.asIdeal * star θ.val * qPower p (-ξ)
    let E := vartheta C p ^ 6 * qPower p (4 - 6 * ξ) * V
    Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖seriesTerm C p 0 θ i.1 i.2.1 i.2.2.1 i.2.2.2 ξ w z‖) ∧
    f C p 0 θ ξ w z =
      1 / (1 - V) + W / (1 - W) +
        E / (1 - E) * ((1 - (Q p : ℂ)⁻¹) / (1 - V) + W) -
        D / (1 - E) * (1 + ((Q p : ℂ) - 1) * W * V / (1 - V)) := by
  dsimp only
  refine ⟨good_euler_series_summable C p 0 θ ξ w z hξ hw hz, ?_⟩
  exact good_strict_ib_evaluation C p u hu θ hθ ξ w z hξ hw hz

end DedekindZetaZeroFree.LocalFiniteSums

end
