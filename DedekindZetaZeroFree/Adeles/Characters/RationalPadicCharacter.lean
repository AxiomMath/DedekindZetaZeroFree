module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.PadicFractionalRepresentatives

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

instance instFactPrimeRationalPadicCharacterNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

def rationalPInverted (p : Nat.Primes) : Subring ℚ :=
  Subring.closure ({((p.1 : ℚ)⁻¹)} : Set ℚ)

theorem existsUnique_padicFractionalPart (p : Nat.Primes) (z : ℚ_[p]) :
    ∃! r : ℚ, r ∈ rationalPInverted p ∧ (0 : ℚ) ≤ r ∧ r < 1 ∧
      z - (r : ℚ_[p]) ∈ Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) := by
  obtain ⟨r, hr, hr0, hr1, hzr⟩ := RationalPadicArithmetic.exists_representative p z
  refine ⟨r, ⟨hr, hr0, hr1, (RationalPadicArithmetic.range_iff_norm p _).mpr hzr⟩, ?_⟩
  intro s hs
  exact RationalPadicArithmetic.unique_representative p z s r
    ⟨hs.1, hs.2.1, hs.2.2.1, (RationalPadicArithmetic.range_iff_norm p _).mp hs.2.2.2⟩
    ⟨hr, hr0, hr1, hzr⟩

def padicFractionalPart (p : Nat.Primes) (z : ℚ_[p]) : ℚ :=
  Classical.choose (existsUnique_padicFractionalPart p z)

theorem padicFractionalPart_spec (p : Nat.Primes) (z : ℚ_[p]) :
    padicFractionalPart p z ∈ rationalPInverted p ∧
      (0 : ℚ) ≤ padicFractionalPart p z ∧ padicFractionalPart p z < 1 ∧
      z - (padicFractionalPart p z : ℚ_[p]) ∈
        Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) := by
  exact (Classical.choose_spec (existsUnique_padicFractionalPart p z)).1

lemma fractionalPart_zero (p : Nat.Primes) : padicFractionalPart p 0 = 0 := by
  symm
  apply (Classical.choose_spec (existsUnique_padicFractionalPart p 0)).2
  exact ⟨(rationalPInverted p).zero_mem, le_rfl, zero_lt_one, ⟨0, by simp⟩⟩

private lemma fractionalPart_integral_difference (p : Nat.Primes) (x y : ℚ_[p])
    (hxy : ‖x-y‖ ≤ 1) : padicFractionalPart p x = padicFractionalPart p y := by
  have hx := padicFractionalPart_spec p x
  have hy := padicFractionalPart_spec p y
  apply RationalPadicArithmetic.unique_representative p x
    (padicFractionalPart p x) (padicFractionalPart p y)
    ⟨hx.1, hx.2.1, hx.2.2.1, (RationalPadicArithmetic.range_iff_norm p _).mp hx.2.2.2⟩
    ⟨hy.1, hy.2.1, hy.2.2.1, ?_⟩
  have he : x - (padicFractionalPart p y : ℚ_[p]) =
      (x-y) + (y - (padicFractionalPart p y : ℚ_[p])) := by ring
  rw [he]
  exact (Padic.nonarchimedean _ _).trans (max_le hxy
    ((RationalPadicArithmetic.range_iff_norm p _).mp hy.2.2.2))

private lemma negative_exp_int (a : ℤ) :
    Circle.exp (-(2 * Real.pi * (a : ℝ))) = 1 := by
  have he : -(2 * Real.pi * (a:ℝ)) = ((-a:ℤ):ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [he, Circle.exp_int_mul_two_pi]

lemma negative_exp_congr (r s : ℚ) (h : ∃ a : ℤ, r-s = a) :
    Circle.exp (-(2 * Real.pi * (r : ℝ))) = Circle.exp (-(2 * Real.pi * (s : ℝ))) := by
  obtain ⟨a, ha⟩ := h
  have ha' : (r:ℝ) = (s:ℝ) + (a:ℝ) := by exact_mod_cast (show r = s + (a:ℚ) by linarith)
  rw [ha']
  have he : -(2 * Real.pi * ((s:ℝ)+(a:ℝ))) =
      -(2 * Real.pi * (s:ℝ)) + -(2 * Real.pi * (a:ℝ)) := by ring
  rw [he, Circle.exp_add, negative_exp_int, mul_one]

lemma fractionalPart_add_mod_int (p : Nat.Primes) (x y : ℚ_[p]) :
    ∃ a : ℤ, padicFractionalPart p (x+y) - (padicFractionalPart p x + padicFractionalPart p y) = a := by
  have hx := padicFractionalPart_spec p x
  have hy := padicFractionalPart_spec p y
  have hs := padicFractionalPart_spec p (x+y)
  apply RationalPadicArithmetic.integral_of_norm_le p _
    ((rationalPInverted p).sub_mem hs.1 ((rationalPInverted p).add_mem hx.1 hy.1))
  have he : ((padicFractionalPart p (x+y) - (padicFractionalPart p x + padicFractionalPart p y) : ℚ) : ℚ_[p]) =
      (x - (padicFractionalPart p x : ℚ_[p])) + (y - (padicFractionalPart p y : ℚ_[p])) -
        ((x+y) - (padicFractionalPart p (x+y) : ℚ_[p])) := by push_cast; ring
  rw [he, sub_eq_add_neg]
  apply (Padic.nonarchimedean _ _).trans
  apply max_le
  · exact (Padic.nonarchimedean _ _).trans (max_le
      ((RationalPadicArithmetic.range_iff_norm p _).mp hx.2.2.2)
      ((RationalPadicArithmetic.range_iff_norm p _).mp hy.2.2.2))
  · rw [norm_neg]; exact (RationalPadicArithmetic.range_iff_norm p _).mp hs.2.2.2

def rationalPadicCharacter (p : Nat.Primes) : AddChar ℚ_[p] Circle where
  toFun z := Circle.exp (-(2 * Real.pi * (padicFractionalPart p z : ℝ)))
  map_zero_eq_one' := by rw [fractionalPart_zero]; simp
  map_add_eq_mul' := by
    intro x y
    rw [negative_exp_congr _ _ (fractionalPart_add_mod_int p x y)]
    push_cast
    rw [show -(2 * Real.pi * ((padicFractionalPart p x : ℝ) + (padicFractionalPart p y : ℝ))) =
      -(2 * Real.pi * (padicFractionalPart p x : ℝ)) + -(2 * Real.pi * (padicFractionalPart p y : ℝ)) by ring,
      Circle.exp_add]

theorem continuous_rationalPadicCharacter (p : Nat.Primes) :
    Continuous (rationalPadicCharacter p : ℚ_[p] → Circle) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have he : (rationalPadicCharacter p : ℚ_[p] → Circle) =ᶠ[nhds z]
      (fun _ => rationalPadicCharacter p z) := by
    filter_upwards [Metric.ball_mem_nhds z (show (0:ℝ) < 1 by norm_num)] with w hw
    change Circle.exp _ = Circle.exp _
    rw [fractionalPart_integral_difference p w z (by
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hw))]
  exact continuousAt_const.congr_of_eventuallyEq he

theorem rationalPadicCharacter_eq_one_iff (p : Nat.Primes) (z : ℚ_[p]) :
    rationalPadicCharacter p z = 1 ↔
      z ∈ Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) := by
  constructor
  · intro h
    change Circle.exp (-(2 * Real.pi * (padicFractionalPart p z : ℝ))) = 1 at h
    obtain ⟨a, ha⟩ := Circle.exp_eq_one.mp h
    have hp := padicFractionalPart_spec p z
    have har : (padicFractionalPart p z : ℝ) = -(a:ℝ) := by
      nlinarith [Real.pi_pos]
    have haq : padicFractionalPart p z = -(a:ℚ) := by exact_mod_cast har
    have ha0 : a ≤ 0 := by exact_mod_cast (show (a:ℚ) ≤ 0 by linarith [hp.2.1])
    have ha1 : (-1:ℤ) < a := by exact_mod_cast (show (-1:ℚ) < a by linarith [hp.2.2.1])
    have haz : a = 0 := by omega
    have hf : padicFractionalPart p z = 0 := by simpa [haz] using haq
    simpa [hf] using hp.2.2.2
  · intro hz
    have hf : padicFractionalPart p z = 0 := by
      rw [← fractionalPart_zero p]
      apply fractionalPart_integral_difference
      simpa using (RationalPadicArithmetic.range_iff_norm p z).mp hz
    change Circle.exp (-(2 * Real.pi * (padicFractionalPart p z : ℝ))) = 1
    simp [hf]

theorem rationalPadicCharacter_inv_prime_ne_one (p : Nat.Primes) :
    rationalPadicCharacter p (((p.1 : ℚ)⁻¹ : ℚ_[p])) ≠ 1 := by
  intro h
  have hn := (RationalPadicArithmetic.range_iff_norm p _).mp
    ((rationalPadicCharacter_eq_one_iff p _).mp h)
  have hp : (1:ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have he : ‖(((p.1:ℚ)⁻¹ : ℚ_[p]))‖ = (p.1:ℝ) := by
    push_cast
    rw [norm_inv, Padic.norm_p, inv_inv]
  rw [he] at hn
  exact (not_le.mpr hp) hn

end DedekindZetaZeroFree

end

section

noncomputable section

namespace DedekindZetaZeroFree

theorem rationalPadicCharacter_of_rationalPInverted (p : Nat.Primes)
    (q : ℚ) (hq : q ∈ rationalPInverted p) :
    rationalPadicCharacter p (q : ℚ_[p]) =
      Circle.exp (-(2 * Real.pi * (q : ℝ))) := by
  change Circle.exp (-(2 * Real.pi * (padicFractionalPart p (q : ℚ_[p]) : ℝ))) = _
  apply negative_exp_congr
  have hs := padicFractionalPart_spec p (q : ℚ_[p])
  apply RationalPadicArithmetic.integral_of_norm_le p _
    ((rationalPInverted p).sub_mem hs.1 hq)
  rw [Rat.cast_sub, norm_sub_rev]
  exact (RationalPadicArithmetic.range_iff_norm p _).mp hs.2.2.2

end DedekindZetaZeroFree

end
end
