module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.RationalPadicArithmetic
variable (p : Nat.Primes)
instance : Fact p.1.Prime := ⟨p.2⟩

lemma denominator_power (q : ℚ)
    (hq : q ∈ Subring.closure ({((p.1 : ℚ)⁻¹)} : Set ℚ)) :
    ∃ n : ℕ, ∃ a : ℤ, q * (p.1 : ℚ)^n = a := by
  induction hq using Subring.closure_induction with
  | mem q hq =>
    simp only [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨1, 1, by simp [p.2.ne_zero]⟩
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨n, a, ha⟩ := ihx
    obtain ⟨m, b, hb⟩ := ihy
    refine ⟨n+m, a*(p.1:ℤ)^m + b*(p.1:ℤ)^n, ?_⟩
    push_cast
    rw [pow_add]
    calc
      (x+y) * ((p.1:ℚ)^n * (p.1:ℚ)^m) =
        (x*(p.1:ℚ)^n)*(p.1:ℚ)^m + (y*(p.1:ℚ)^m)*(p.1:ℚ)^n := by ring
      _ = _ := by rw [ha, hb]
  | neg x hx ih =>
    obtain ⟨n, a, ha⟩ := ih
    exact ⟨n, -a, by simpa using congrArg Neg.neg ha⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨n, a, ha⟩ := ihx
    obtain ⟨m, b, hb⟩ := ihy
    refine ⟨n+m, a*b, ?_⟩
    push_cast
    rw [pow_add]
    calc
      (x*y) * ((p.1:ℚ)^n * (p.1:ℚ)^m) = (x*(p.1:ℚ)^n)*(y*(p.1:ℚ)^m) := by ring
      _ = _ := by rw [ha, hb]

lemma integral_of_norm_le (q : ℚ)
    (hq : q ∈ Subring.closure ({((p.1 : ℚ)⁻¹)} : Set ℚ))
    (hn : ‖(q : ℚ_[p])‖ ≤ 1) : ∃ a : ℤ, q = a := by
  obtain ⟨n, a, ha⟩ := denominator_power p q hq
  have hcast : (q : ℚ_[p]) * (p.1 : ℚ_[p]) ^ n = (a : ℚ_[p]) := by exact_mod_cast ha
  have hn' : ‖(a : ℚ_[p])‖ ≤ (p.1 : ℝ)^(- (n : ℤ)) := by
    rw [← hcast, norm_mul, Padic.norm_p_pow]
    simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg ((p.1 : ℚ_[p])^n))
  obtain ⟨b, hb⟩ := (Padic.norm_int_le_pow_iff_dvd a n).mp hn'
  refine ⟨b, ?_⟩
  have hpr : (p.1 : ℚ)^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  apply (mul_right_cancel₀ hpr)
  rw [ha, hb]
  push_cast
  ring

lemma range_iff_norm (z : ℚ_[p]) :
    z ∈ Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) ↔ ‖z‖ ≤ 1 := by
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨z, h⟩, rfl⟩

lemma exists_representative (z : ℚ_[p]) :
    ∃ r : ℚ, r ∈ Subring.closure ({((p.1 : ℚ)⁻¹)} : Set ℚ) ∧
      0 ≤ r ∧ r < 1 ∧ ‖z - (r : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖z‖ (show (1:ℝ) < p.1 by exact_mod_cast p.2.one_lt)
  have hpR : (0:ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hpQ : (0:ℚ) < p.1 := by exact_mod_cast p.2.pos
  have hp0 : (p.1 : ℚ_[p])^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  have hn' : ‖(p.1 : ℚ_[p])^n * z‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    exact (inv_mul_le_one₀ (by positivity)).mpr hn.le
  let x : ℤ_[p] := ⟨(p.1 : ℚ_[p])^n * z, hn'⟩
  let a : ℕ := x.appr n
  refine ⟨(a : ℚ) / (p.1 : ℚ)^n, ?_, by positivity, ?_, ?_⟩
  · rw [div_eq_mul_inv, ← inv_pow]
    exact Subring.mul_mem _ (natCast_mem _ a)
      (Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) n)
  · apply (div_lt_one (by positivity)).mpr
    exact_mod_cast x.appr_lt n
  · obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp (x.appr_spec n)
    have he' : (p.1 : ℚ_[p])^n * (e : ℚ_[p]) =
        (p.1 : ℚ_[p])^n * z - (a : ℚ_[p]) := by
      have he'' := (congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) he).symm
      change (p.1 : ℚ_[p])^n * (e : ℚ_[p]) = (x : ℚ_[p]) - (a : ℚ_[p]) at he''
      exact he''
    have hz : z - (((a:ℚ) / (p.1:ℚ)^n : ℚ) : ℚ_[p]) = (e : ℚ_[p]) := by
      push_cast
      apply (mul_left_cancel₀ hp0)
      rw [mul_sub, mul_div_cancel₀ _ hp0, he']
    rw [hz]
    exact e.2

lemma unique_representative (z : ℚ_[p]) (r s : ℚ)
    (hr : r ∈ Subring.closure ({((p.1 : ℚ)⁻¹)} : Set ℚ) ∧
      0 ≤ r ∧ r < 1 ∧ ‖z - (r : ℚ_[p])‖ ≤ 1)
    (hs : s ∈ Subring.closure ({((p.1 : ℚ)⁻¹)} : Set ℚ) ∧
      0 ≤ s ∧ s < 1 ∧ ‖z - (s : ℚ_[p])‖ ≤ 1) : r = s := by
  have hn : ‖((r-s : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have he : ((r-s : ℚ) : ℚ_[p]) = (z - (s : ℚ_[p])) - (z - (r : ℚ_[p])) := by push_cast; ring
    rw [he]
    rw [sub_eq_add_neg]
    exact (Padic.nonarchimedean _ _).trans (max_le hs.2.2.2 (by rw [norm_neg]; exact hr.2.2.2))
  obtain ⟨a, ha⟩ := integral_of_norm_le p (r-s) (Subring.sub_mem _ hr.1 hs.1) hn
  have ha0 : (-1:ℤ) < a := by exact_mod_cast (show (-1:ℚ) < (a:ℚ) by rw [← ha]; linarith [hr.2.1, hs.2.2.1])
  have ha1 : a < (1:ℤ) := by exact_mod_cast (show (a:ℚ) < 1 by rw [← ha]; linarith [hr.2.2.1, hs.2.1])
  have : a = 0 := by omega
  rw [this, Int.cast_zero] at ha
  exact sub_eq_zero.mp ha
end DedekindZetaZeroFree.RationalPadicArithmetic

end
