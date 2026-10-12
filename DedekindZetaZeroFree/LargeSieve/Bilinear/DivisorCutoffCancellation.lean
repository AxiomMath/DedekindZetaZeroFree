module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeDivisorsAndPrimeSubsets

@[expose] public section

section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
open SplitData
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

private lemma cutoff_eq_zero_iff (n : R →* ℝ≥0) (K : ℝ) (a : R) :
    cutoff n K a = 0 ↔ K < (n a : ℝ) := by
  simp only [cutoff]
  by_cases h : (n a : ℝ) ≤ K
  · rw [if_pos h]; exact iff_of_false (by norm_num) (by linarith)
  · rw [if_neg h]; exact iff_of_true rfl (not_le.mp h)

private lemma cutoff_eq_one_iff (n : R →* ℝ≥0) (K : ℝ) (a : R) :
    cutoff n K a = 1 ↔ (n a : ℝ) ≤ K := by
  simp only [cutoff]
  by_cases h : (n a : ℝ) ≤ K
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]; exact iff_of_false (by norm_num) h

private lemma zero_le_cutoff (n : R →* ℝ≥0) (K : ℝ) (a : R) : 0 ≤ cutoff n K a := by
  simp only [cutoff]; split <;> norm_num

private lemma cutoff_le_one (n : R →* ℝ≥0) (K : ℝ) (a : R) : cutoff n K a ≤ 1 := by
  simp only [cutoff]; split <;> norm_num

private lemma cutoff_mono (n : R →* ℝ≥0) (K : ℝ) {a b : R}
    (h : (n a : ℝ) ≤ (n b : ℝ)) : cutoff n K b ≤ cutoff n K a := by
  by_cases hb : (n b : ℝ) ≤ K
  · rw [(cutoff_eq_one_iff n K b).mpr hb, (cutoff_eq_one_iff n K a).mpr (le_trans h hb)]
  · have hb0 : cutoff n K b = 0 := (cutoff_eq_zero_iff n K b).mpr (not_le.mp hb)
    rw [hb0]; exact zero_le_cutoff n K a

private lemma mem_divisors_iff {g : R} (hg0 : g ≠ 0) {d : R} :
    d ∈ divisors g ↔ ∃ s ≤ UniqueFactorizationMonoid.factors g, s.prod = d := by
  simp only [divisors, if_neg hg0, Finset.mem_image, Multiset.mem_toFinset, Multiset.mem_powerset]

private lemma one_le_prod_map_of_le_factors (n : R →* ℝ≥0)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    {g : R} {s : Multiset R} (hs : s ≤ UniqueFactorizationMonoid.factors g) :
    (1 : ℝ≥0) ≤ (s.map n).prod := by
  apply Multiset.one_le_prod_of_one_le
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  have hpf : p ∈ UniqueFactorizationMonoid.factors g := Multiset.mem_of_le hs hp
  have hprime : Prime p := UniqueFactorizationMonoid.prime_of_factor p hpf
  have h1 : (1 : ℝ) < (n p : ℝ) := hn p hprime
  exact (NNReal.coe_lt_coe.mp (by simpa using h1)).le

private lemma one_le_n_of_mem_divisors (n : R →* ℝ≥0)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    {g d : R} (hg0 : g ≠ 0) (hd : d ∈ divisors g) : (1 : ℝ≥0) ≤ n d := by
  obtain ⟨s, hs, rfl⟩ := (mem_divisors_iff hg0).mp hd
  rw [MonoidHom.map_multiset_prod]
  exact one_le_prod_map_of_le_factors n hn hs

private lemma n_le_n_of_mem_divisors (n : R →* ℝ≥0)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    {g d : R} (hg0 : g ≠ 0) (hd : d ∈ divisors g) : n d ≤ n g := by
  obtain ⟨s, hs, rfl⟩ := (mem_divisors_iff hg0).mp hd
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hs
  have hfg : (UniqueFactorizationMonoid.factors g).prod = g := by
    obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.factors_prod hg0
    rw [Subsingleton.elim v 1] at hv
    simpa using hv
  have hng : n g = ((UniqueFactorizationMonoid.factors g).map n).prod := by
    conv_lhs => rw [← hfg]
    rw [MonoidHom.map_multiset_prod]
  have hu_le : u ≤ UniqueFactorizationMonoid.factors g := by
    rw [hu]; exact Multiset.le_add_left u s
  rw [hng, hu, Multiset.map_add, Multiset.prod_add, MonoidHom.map_multiset_prod]
  exact le_mul_of_one_le_right' (one_le_prod_map_of_le_factors n hn hu_le)

theorem nonzero_coefficient_annulus (n : R →* ℝ≥0)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    (g : R) (hg0 : g ≠ 0) (K : ℝ) (hK : 0 < K)
    (H : Finset R) (b : R) (hb : boundaryCoefficient n K H g b ≠ 0) :
    K < (n b : ℝ) ∧ (n b : ℝ) ≤ K * (n g : ℝ) ^ 2 := by
  simp only [boundaryCoefficient] at hb
  obtain ⟨h, _hhH, hb1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨d, hd, hb2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb1
  obtain ⟨e, he, hb3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb2
  have hbe : h * d * e = b := by
    by_contra hne
    exact hb3 (by rw [if_neg hne])
  rw [if_pos hbe] at hb3
  have hcut : cutoff n K (h * d) - cutoff n K h ≠ 0 :=
    fun h0 => hb3 (by rw [h0, mul_zero])
  have hne : cutoff n K (h * d) ≠ cutoff n K h := sub_ne_zero.mp hcut
  have hd1 : (1 : ℝ≥0) ≤ n d := one_le_n_of_mem_divisors n hn hg0 hd
  have he1 : (1 : ℝ≥0) ≤ n e := one_le_n_of_mem_divisors n hn hg0 he
  have hdg : n d ≤ n g := n_le_n_of_mem_divisors n hn hg0 hd
  have heg : n e ≤ n g := n_le_n_of_mem_divisors n hn hg0 he
  have hhle_nn : n h ≤ n (h * d) := by rw [map_mul]; exact le_mul_of_one_le_right' hd1
  have hhle : (n h : ℝ) ≤ (n (h * d) : ℝ) := NNReal.coe_le_coe.mpr hhle_nn
  have hle_cut : cutoff n K (h * d) ≤ cutoff n K h := cutoff_mono n K hhle
  have hlt : cutoff n K (h * d) < cutoff n K h := lt_of_le_of_ne hle_cut hne
  have hcuthd0 : cutoff n K (h * d) = 0 := by
    have h1 : cutoff n K (h * d) < 1 := lt_of_lt_of_le hlt (cutoff_le_one n K h)
    have h2 : 0 ≤ cutoff n K (h * d) := zero_le_cutoff n K (h * d)
    omega
  have hKlt : K < (n (h * d) : ℝ) := (cutoff_eq_zero_iff n K (h * d)).mp hcuthd0
  have hnhK : (n h : ℝ) ≤ K := by
    have hpos : 0 < cutoff n K h := lt_of_le_of_lt (zero_le_cutoff n K (h * d)) hlt
    have hle1 : cutoff n K h ≤ 1 := cutoff_le_one n K h
    have h1 : cutoff n K h = 1 := by omega
    exact (cutoff_eq_one_iff n K h).mp h1
  have hnb_eq : (n b : ℝ) = (n (h * d) : ℝ) * (n e : ℝ) := by
    rw [← hbe, map_mul, NNReal.coe_mul]
  have he1r : (1 : ℝ) ≤ (n e : ℝ) := NNReal.coe_le_coe.mpr he1
  have hnd_pos : 0 < (n (h * d) : ℝ) := lt_trans hK hKlt
  refine ⟨?_, ?_⟩
  · calc K < (n (h * d) : ℝ) := hKlt
      _ = (n (h * d) : ℝ) * 1 := (mul_one _).symm
      _ ≤ (n (h * d) : ℝ) * (n e : ℝ) := mul_le_mul_of_nonneg_left he1r (le_of_lt hnd_pos)
      _ = (n b : ℝ) := hnb_eq.symm
  · have hnb_eq2 : (n b : ℝ) = (n h : ℝ) * (n d : ℝ) * (n e : ℝ) := by
      rw [hnb_eq, map_mul, NNReal.coe_mul]
    rw [hnb_eq2]
    have h0nh : 0 ≤ (n h : ℝ) := (n h).coe_nonneg
    have h0nd : 0 ≤ (n d : ℝ) := (n d).coe_nonneg
    have h0ne : 0 ≤ (n e : ℝ) := (n e).coe_nonneg
    have h0ng : 0 ≤ (n g : ℝ) := (n g).coe_nonneg
    have hd_nn : (n d : ℝ) ≤ (n g : ℝ) := NNReal.coe_le_coe.mpr hdg
    have he_nn : (n e : ℝ) ≤ (n g : ℝ) := NNReal.coe_le_coe.mpr heg
    calc (n h : ℝ) * (n d : ℝ) * (n e : ℝ)
        ≤ K * (n g : ℝ) * (n g : ℝ) := by
          apply mul_le_mul
          · exact mul_le_mul hnhK hd_nn h0nd hK.le
          · exact he_nn
          · exact h0ne
          · exact mul_nonneg hK.le h0ng
      _ = K * (n g : ℝ) ^ 2 := by ring

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference

end

section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
open SplitData
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

private lemma abs_moebius_le_one (a : R) : |UniqueFactorizationMonoid.moebius a| ≤ 1 := by
  rw [UniqueFactorizationMonoid.moebius]
  split_ifs with h
  · rw [abs_neg_one_pow]
  · simp

private lemma abs_cutoff_sub_le_one (n : R →* ℝ≥0) (K : ℝ) (a b : R) :
    |cutoff n K a - cutoff n K b| ≤ 1 := by
  simp only [cutoff]
  split_ifs <;> norm_num

private lemma divisors_ne_zero (g : R) (hg0 : g ≠ 0) {d : R} (hd : d ∈ divisors g) :
    d ≠ 0 := by
  rw [divisors] at hd
  split_ifs at hd with hg
  · simp at hd
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    rw [Multiset.mem_toFinset, Multiset.mem_powerset] at hm
    have hdvd : m.prod ∣ g :=
      (Multiset.prod_dvd_prod_of_le hm).trans (UniqueFactorizationMonoid.factors_prod hg).dvd
    intro h0
    rw [h0] at hdvd
    exact hg0 (zero_dvd_iff.mp hdvd)

private lemma inner_sum_norm_le_one (n : R →* ℝ≥0) (K : ℝ) (H : Finset R) (g b : R)
    (hg0 : g ≠ 0) {d e : R} (hd : d ∈ divisors g) (he : e ∈ divisors g) :
    ‖((∑ h ∈ H, if h * d * e = b then
        UniqueFactorizationMonoid.moebius e * (cutoff n K (h * d) - cutoff n K h)
      else 0 : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  set F : R → ℤ := fun h => UniqueFactorizationMonoid.moebius e *
    (cutoff n K (h * d) - cutoff n K h) with hF
  set S := H.filter (fun h => h * d * e = b) with hS
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro h1 h1S h2 h2S
    rw [hS, Finset.mem_filter] at h1S h2S
    have hde : d * e ≠ 0 := mul_ne_zero (divisors_ne_zero g hg0 hd) (divisors_ne_zero g hg0 he)
    have heq : h1 * (d * e) = h2 * (d * e) := by
      rw [← mul_assoc, ← mul_assoc, h1S.2, h2S.2]
    exact mul_right_cancel₀ hde heq
  have hsum : (∑ h ∈ H, (if h * d * e = b then F h else 0)) = ∑ h ∈ S, F h := by
    rw [hS]
    exact (Finset.sum_filter (fun h => h * d * e = b) F).symm
  rw [hsum]
  have hbound : ∀ h ∈ S, ‖((F h : ℤ) : ℂ)‖ ≤ 1 := by
    intro h _
    rw [Complex.norm_intCast, ← Int.cast_abs]
    have : |F h| ≤ 1 := by
      rw [hF]
      simp only
      rw [abs_mul]
      simpa using mul_le_mul (abs_moebius_le_one e)
        (abs_cutoff_sub_le_one n K (h * d) h) (abs_nonneg _) zero_le_one
    exact_mod_cast this
  calc ‖((∑ h ∈ S, F h : ℤ) : ℂ)‖
      = ‖∑ h ∈ S, ((F h : ℤ) : ℂ)‖ := by push_cast; ring_nf
    _ ≤ ∑ h ∈ S, ‖((F h : ℤ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ S, (1 : ℝ) := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

theorem boundary_coefficient_card_bound (n : R →* ℝ≥0) (K : ℝ)
    (H : Finset R) (g : R) (hg0 : g ≠ 0) (b : R) :
    ‖(boundaryCoefficient n K H g b : ℂ)‖ ≤ (divisors g).card ^ 2 := by
  classical
  by_cases hg : g = 0
  · subst hg
    simp [boundaryCoefficient, divisors]
  let F : R → R → R → ℤ := fun h d e =>
    if h * d * e = b then UniqueFactorizationMonoid.moebius e *
      (cutoff n K (h * d) - cutoff n K h) else 0
  have hbc : boundaryCoefficient n K H g b
      = ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g, F h d e := by
    rw [boundaryCoefficient]
  rw [hbc]
  have hrearr : (∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g, F h d e)
      = ∑ d ∈ divisors g, ∑ e ∈ divisors g, ∑ h ∈ H, F h d e := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
  rw [hrearr]
  have hcast : ((∑ d ∈ divisors g, ∑ e ∈ divisors g, ∑ h ∈ H, F h d e : ℤ) : ℂ)
      = ∑ d ∈ divisors g, ∑ e ∈ divisors g, ∑ h ∈ H, ((F h d e : ℤ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  have hle : ∀ d ∈ divisors g, ∀ e ∈ divisors g,
      ‖∑ h ∈ H, ((F h d e : ℤ) : ℂ)‖ ≤ 1 := by
    intro d hd e he
    rw [← Int.cast_sum]
    exact inner_sum_norm_le_one n K H g b hg0 hd he
  calc ‖∑ d ∈ divisors g, ∑ e ∈ divisors g, ∑ h ∈ H, ((F h d e : ℤ) : ℂ)‖
      ≤ ∑ d ∈ divisors g, ‖∑ e ∈ divisors g, ∑ h ∈ H, ((F h d e : ℤ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ divisors g, ∑ e ∈ divisors g, ‖∑ h ∈ H, ((F h d e : ℤ) : ℂ)‖ :=
        Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ divisors g, ∑ e ∈ divisors g, (1 : ℝ) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hle d hd e he))
    _ = (divisors g).card ^ 2 := by simp [pow_two]

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference

end

section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
open SplitData
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

theorem collect_cutoff_triple_sum (n : R →* ℝ≥0) (χ : R →* ℂ)
    (K : ℝ) (H : Finset R) (g : R) :
    (∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
      (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ (h * d * e) *
        ((cutoff n K (h * d) - cutoff n K h : ℤ) : ℂ)) =
    ∑ b ∈ boundaryElements H g,
      (boundaryCoefficient n K H g b : ℂ) * normalizedValue n χ b := by
  classical

  let F : R × (R × R) → ℂ := fun x =>
    (UniqueFactorizationMonoid.moebius x.2.2 : ℂ) * normalizedValue n χ (x.1 * x.2.1 * x.2.2) *
      ((cutoff n K (x.1 * x.2.1) - cutoff n K x.1 : ℤ) : ℂ)

  have hmain : (∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
      (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ (h * d * e) *
        ((cutoff n K (h * d) - cutoff n K h : ℤ) : ℂ))
      = ∑ x ∈ H ×ˢ (divisors g ×ˢ divisors g), F x := by
    refine Eq.trans ?_ (Finset.sum_product (s := H) (t := divisors g ×ˢ divisors g) (f := F)).symm
    refine Finset.sum_congr rfl fun h _ => ?_
    exact (Finset.sum_product (s := divisors g) (t := divisors g) (f := fun y => F (h, y))).symm

  have hfiber : ∀ b : R,
      (∑ x ∈ (H ×ˢ (divisors g ×ˢ divisors g)).filter
        (fun x => x.1 * x.2.1 * x.2.2 = b), F x)
      = (boundaryCoefficient n K H g b : ℂ) * normalizedValue n χ b := by
    intro b
    rw [Finset.sum_filter]
    rw [show (∑ x ∈ H ×ˢ (divisors g ×ˢ divisors g),
          (if x.1 * x.2.1 * x.2.2 = b then F x else 0))
        = ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
            (if h * d * e = b then F (h, (d, e)) else 0) from by
      refine Eq.trans (Finset.sum_product (s := H) (t := divisors g ×ˢ divisors g)
        (f := fun x => if x.1 * x.2.1 * x.2.2 = b then F x else 0)) ?_
      refine Finset.sum_congr rfl fun h _ => ?_
      exact Finset.sum_product (s := divisors g) (t := divisors g)
        (f := fun y => if h * y.1 * y.2 = b then F (h, y) else 0)]
    have hcoeff : (boundaryCoefficient n K H g b : ℂ) * normalizedValue n χ b
        = ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
            (if h * d * e = b then
              ((UniqueFactorizationMonoid.moebius e * (cutoff n K (h * d) - cutoff n K h) : ℤ) : ℂ) *
                normalizedValue n χ b
             else 0) := by
      simp only [boundaryCoefficient]
      push_cast
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [hcoeff]
    refine Finset.sum_congr rfl fun h _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hb : h * d * e = b
    · rw [if_pos hb, if_pos hb]
      show (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ (h * d * e) *
          ((cutoff n K (h * d) - cutoff n K h : ℤ) : ℂ)
        = ((UniqueFactorizationMonoid.moebius e * (cutoff n K (h * d) - cutoff n K h) : ℤ) : ℂ) *
          normalizedValue n χ b
      rw [hb, Int.cast_mul]
      ring
    · rw [if_neg hb, if_neg hb]

  have hRHS : (∑ b ∈ boundaryElements H g,
        (boundaryCoefficient n K H g b : ℂ) * normalizedValue n χ b)
      = ∑ x ∈ H ×ˢ (divisors g ×ˢ divisors g), F x := by
    show (∑ b ∈ (H ×ˢ (divisors g ×ˢ divisors g)).image
        (fun x => x.1 * x.2.1 * x.2.2),
        (boundaryCoefficient n K H g b : ℂ) * normalizedValue n χ b) = _
    rw [Finset.sum_congr rfl (fun b _ => (hfiber b).symm)]
    rw [Finset.sum_fiberwise_eq_sum_filter
      (s := H ×ˢ (divisors g ×ˢ divisors g))
      (t := (H ×ˢ (divisors g ×ˢ divisors g)).image (fun x => x.1 * x.2.1 * x.2.2))
      (g := fun x => x.1 * x.2.1 * x.2.2) (f := F)]
    rw [Finset.filter_true_of_mem (fun x hx => Finset.mem_image_of_mem _ hx)]
  exact hmain.trans hRHS.symm

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference

end

section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
open SplitData
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

private lemma nv_prod (n : R →* ℝ≥0) (χ : R →* ℂ) (S : Finset R) :
    normalizedValue n χ (∏ p ∈ S, p) = ∏ p ∈ S, normalizedValue n χ p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [normalizedValue]
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, normalizedValue_mul, ih, Finset.prod_insert ha]

private lemma prod_one_sub (f : R → ℂ) (P : Finset R) :
    ∏ p ∈ P, (1 - f p) = ∑ S ∈ P.powerset, (-1:ℂ)^S.card * ∏ p ∈ S, f p := by
  rw [show (∏ p ∈ P, (1 - f p)) = ∏ p ∈ P, (1 + (- f p)) by
    apply Finset.prod_congr rfl
    intro p hp
    ring]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_neg]

theorem local_density_euler (n : R →* ℝ≥0) (χ : R →* ℂ)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    (g : R) (hg0 : g ≠ 0) (hg : Squarefree g)
    (hχ : ∀ p : R, Prime p → p ∣ g → χ p ^ 2 = 1) :
    (∑ d ∈ divisors g, normalizedValue n χ d) * moebiusDivisorSum n χ g =
      (density n g : ℂ) := by
  classical
  obtain ⟨hPrime, hprod, hdiv, hinj, hmu, _hmem⟩ :=
    squarefree_divisor_dictionary g hg0 hg
  set P : Finset R := (UniqueFactorizationMonoid.factors g).toFinset with hP
  have hdiv' : divisors g = P.powerset.image (fun S : Finset R => ∏ p ∈ S, p) := hdiv

  have hsum1 : (∑ d ∈ divisors g, normalizedValue n χ d) =
      ∏ p ∈ P, (1 + normalizedValue n χ p) := by
    rw [hdiv', Finset.sum_image hinj]
    rw [Finset.prod_one_add P (f := fun p => normalizedValue n χ p)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [nv_prod]

  have hsum2 : moebiusDivisorSum n χ g = ∏ p ∈ P, (1 - normalizedValue n χ p) := by
    unfold moebiusDivisorSum
    rw [hdiv', Finset.sum_image hinj]
    rw [prod_one_sub (fun p => normalizedValue n χ p) P]
    apply Finset.sum_congr rfl
    intro S hS
    rw [hmu S hS, nv_prod]
    push_cast
    ring
  rw [hsum1, hsum2, ← Finset.prod_mul_distrib]

  have hfac : ∀ p ∈ P, (1 + normalizedValue n χ p) * (1 - normalizedValue n χ p)
      = 1 - 1/(((n p : ℝ) : ℂ)) := by
    intro p hp
    have hpP : Prime p := hPrime p hp
    have hpg : p ∣ g := hprod ▸ Finset.dvd_prod_of_mem (fun q : R => q) hp
    have hchi : χ p ^ 2 = 1 := hχ p hpP hpg
    have hnpos : (0:ℝ) < (n p : ℝ) := lt_trans zero_lt_one (hn p hpP)
    have hs : (((Real.sqrt (n p : ℝ) : ℝ)) : ℂ)^2 = ((n p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hnpos)]
    have hxx : (normalizedValue n χ p)^2 = 1/(((n p : ℝ) : ℂ)) := by
      unfold normalizedValue
      rw [div_pow, hs, hchi]
    rw [show (1 + normalizedValue n χ p) * (1 - normalizedValue n χ p)
        = 1 - (normalizedValue n χ p)^2 by ring, hxx]
  rw [Finset.prod_congr rfl hfac, density, ← hP]
  push_cast
  ring

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference

end

section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
open SplitData
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

private lemma dvd_of_mem_divisors {g d : R} (hg0 : g ≠ 0) (hd : d ∈ divisors g) :
    d ∣ g := by
  rw [SplitData.divisors, if_neg hg0] at hd
  simp only [Finset.mem_image, Multiset.mem_toFinset, Multiset.mem_powerset] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  have hprod : (UniqueFactorizationMonoid.factors g).prod = g :=
    associated_iff_eq.mp (UniqueFactorizationMonoid.factors_prod hg0)
  exact hprod ▸ Multiset.prod_dvd_prod_of_le hs

private lemma squarefree_prod_of_nodup_prime [Nontrivial R] {m : Multiset R}
    (hprime : ∀ p ∈ m, Prime p) (hnd : m.Nodup) : Squarefree m.prod := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (m.prod_ne_zero_of_prime hprime),
    UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime]
  exact hnd

theorem divisor_pair_squarefree_times_square (g : R) (hg0 : g ≠ 0)
    (hg : Squarefree g) (h : R) (hh : Squarefree h) (hhg : IsRelPrime h g)
    (d e : R) (hd : d ∈ divisors g) (he : e ∈ divisors g) :
    ∃ a t : R, Squarefree a ∧ t ∣ g ∧ h * d * e = a * t ^ 2 := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  ·
    exact ⟨0, 0, (fun x _ => (Subsingleton.elim x 1) ▸ isUnit_one),
      (Subsingleton.elim 0 g) ▸ dvd_zero 0, Subsingleton.elim _ _⟩
  · haveI := hnt
    have hdvd : d ∣ g := dvd_of_mem_divisors hg0 hd
    have hevd : e ∣ g := dvd_of_mem_divisors hg0 he
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hg0 hdvd
    have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hg0 hevd

    set m := UniqueFactorizationMonoid.normalizedFactors d with hmdef
    set n := UniqueFactorizationMonoid.normalizedFactors e with hndef
    set P := UniqueFactorizationMonoid.normalizedFactors g with hPdef
    have hm : m.prod = d :=
      associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hd0)
    have hn : n.prod = e :=
      associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors he0)
    have hP : P.prod = g :=
      associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hg0)
    have hPnodup : P.Nodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hg0).mp hg
    have hmP : m ≤ P :=
      (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hd0 hg0).mp hdvd
    have hnP : n ≤ P :=
      (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors he0 hg0).mp hevd
    have hprimeP : ∀ p ∈ P, Prime p := fun p hp =>
      UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    have hXle : (m ∪ n) - (m ∩ n) ≤ P :=
      le_trans (Multiset.sub_le_self _ _) (Multiset.union_le hmP hnP)

    refine ⟨h * ((m ∪ n) - (m ∩ n)).prod, (m ∩ n).prod, ?_, ?_, ?_⟩
    · have hXnodup : ((m ∪ n) - (m ∩ n)).Nodup := Multiset.nodup_of_le hXle hPnodup
      have hXprime : ∀ p ∈ (m ∪ n) - (m ∩ n), Prime p := fun p hp =>
        hprimeP p (Multiset.mem_of_le hXle hp)
      have hXsq : Squarefree ((m ∪ n) - (m ∩ n)).prod :=
        squarefree_prod_of_nodup_prime hXprime hXnodup
      have hXg : ((m ∪ n) - (m ∩ n)).prod ∣ g :=
        hP ▸ Multiset.prod_dvd_prod_of_le hXle
      exact squarefree_mul_iff.mpr ⟨hhg.of_dvd_right hXg, hh, hXsq⟩
    · exact hP ▸ Multiset.prod_dvd_prod_of_le (le_trans Multiset.inter_le_left hmP)
    · have hle : m ∩ n ≤ m ∪ n :=
        le_trans Multiset.inter_le_left Multiset.le_union_left
      have hinter : (m ∪ n) ∩ (m ∩ n) = m ∩ n :=
        le_antisymm Multiset.inter_le_right (Multiset.le_inter hle le_rfl)
      have h2 : (m ∪ n).prod = ((m ∪ n) - (m ∩ n)).prod * (m ∩ n).prod := by
        conv_lhs => rw [← Multiset.sub_add_inter (m ∪ n) (m ∩ n), hinter]
        rw [Multiset.prod_add]
      have h1 : m.prod * n.prod = ((m ∪ n) - (m ∩ n)).prod * (m ∩ n).prod ^ 2 := by
        rw [← Multiset.prod_add, ← Multiset.union_add_inter m n, Multiset.prod_add, h2,
          pow_two]
        ac_rfl
      have key : h * d * e = h * (m.prod * n.prod) := by
        rw [← hm, ← hn]
        ac_rfl
      rw [key, h1]
      ac_rfl

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference

end

section

open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

def divisors (g : R) : Finset R :=
  if g = 0 then ∅ else (UniqueFactorizationMonoid.factors g).powerset.toFinset.image
    Multiset.prod

def normalizedValue (n : R →* (ℝ≥0)) (χ : R →* ℂ) (b : R) : ℂ :=
  χ b / (Real.sqrt (n b : ℝ) : ℂ)

def cutoff (n : R →* (ℝ≥0)) (K : ℝ) (b : R) : ℤ :=
  if (n b : ℝ) ≤ K then 1 else 0

def divisorCutoffSum (n : R →* (ℝ≥0)) (χ : R →* ℂ) (K : ℝ)
    (H : Finset R) (g : R) : ℂ :=
  ∑ h ∈ H, ∑ d ∈ divisors g,
    normalizedValue n χ (h * d) * (cutoff n K (h * d) : ℂ)

def baseCutoffSum (n : R →* (ℝ≥0)) (χ : R →* ℂ) (K : ℝ)
    (H : Finset R) : ℂ :=
  ∑ h ∈ H, normalizedValue n χ h * (cutoff n K h : ℂ)

def moebiusDivisorSum (n : R →* (ℝ≥0)) (χ : R →* ℂ) (g : R) : ℂ :=
  ∑ e ∈ divisors g, (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ e

def density (n : R →* (ℝ≥0)) (g : R) : ℝ :=
  ∏ p ∈ (UniqueFactorizationMonoid.factors g).toFinset, (1 - 1 / (n p : ℝ))

def boundaryElements (H : Finset R) (g : R) : Finset R :=
  (H ×ˢ (divisors g ×ˢ divisors g)).image (fun x => x.1 * x.2.1 * x.2.2)

def boundaryCoefficient (n : R →* (ℝ≥0)) (K : ℝ) (H : Finset R) (g b : R) : ℤ :=
  ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
    if h * d * e = b then
      UniqueFactorizationMonoid.moebius e * (cutoff n K (h * d) - cutoff n K h)
    else 0

private theorem normalizedValue_mul (n : R →* ℝ≥0) (χ : R →* ℂ) (a b : R) :
    normalizedValue n χ (a * b) = normalizedValue n χ a * normalizedValue n χ b :=
  SplitData.normalizedValue_mul n χ a b

theorem main_terms_difference (n : R →* (ℝ≥0)) (χ : R →* ℂ)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    (g : R) (hg0 : g ≠ 0) (hg : Squarefree g)
    (hχ : ∀ p : R, Prime p → p ∣ g → χ p ^ 2 = 1)
    (K : ℝ) (hK : 0 < K) (H : Finset R)
    (hH : ∀ h ∈ H, Squarefree h ∧ IsRelPrime h g) :
    divisorCutoffSum n χ K H g * moebiusDivisorSum n χ g -
      baseCutoffSum n χ K H * (density n g : ℂ) =
    ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
      (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ (h * d * e) *
        ((cutoff n K (h * d) - cutoff n K h : ℤ) : ℂ) := by
  have hfirst : divisorCutoffSum n χ K H g * moebiusDivisorSum n χ g =
      ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
        (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ (h * d * e) *
          (cutoff n K (h * d) : ℂ) := by
    simp only [divisorCutoffSum, moebiusDivisorSum, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    simp only [normalizedValue_mul]
    ring
  have hsecond : baseCutoffSum n χ K H * (density n g : ℂ) =
      ∑ h ∈ H, ∑ d ∈ divisors g, ∑ e ∈ divisors g,
        (UniqueFactorizationMonoid.moebius e : ℂ) * normalizedValue n χ (h * d * e) *
          (cutoff n K h : ℂ) := by
    have heuler : (∑ d ∈ divisors g, normalizedValue n χ d) * moebiusDivisorSum n χ g =
        (density n g : ℂ) := local_density_euler n χ hn g hg0 hg hχ
    rw [← heuler]
    simp only [baseCutoffSum, moebiusDivisorSum, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    simp only [normalizedValue_mul]
    ring
  rw [hfirst, hsecond]
  simp only [← Finset.sum_sub_distrib, Int.cast_sub, mul_sub]

theorem main_terms_difference_collected (n : R →* (ℝ≥0)) (χ : R →* ℂ)
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    (g : R) (hg0 : g ≠ 0) (hg : Squarefree g)
    (hχ : ∀ p : R, Prime p → p ∣ g → χ p ^ 2 = 1)
    (K : ℝ) (hK : 0 < K) (H : Finset R)
    (hH : ∀ h ∈ H, Squarefree h ∧ IsRelPrime h g) :
    divisorCutoffSum n χ K H g * moebiusDivisorSum n χ g -
      baseCutoffSum n χ K H * (density n g : ℂ) =
    ∑ b ∈ boundaryElements H g,
      (boundaryCoefficient n K H g b : ℂ) * normalizedValue n χ b := by
  rw [main_terms_difference n χ hn g hg0 hg hχ K hK H hH]
  exact collect_cutoff_triple_sum n χ K H g

theorem boundary_coefficient_properties (n : R →* (ℝ≥0))
    (hn : ∀ p : R, Prime p → 1 < (n p : ℝ))
    (g : R) (hg0 : g ≠ 0) (hg : Squarefree g)
    (K : ℝ) (hK : 0 < K) (H : Finset R)
    (hH : ∀ h ∈ H, Squarefree h ∧ IsRelPrime h g) (b : R) :
    (boundaryCoefficient n K H g b ≠ 0 →
      K < (n b : ℝ) ∧ (n b : ℝ) ≤ K * (n g : ℝ) ^ 2 ∧
        ∃ a t : R, Squarefree a ∧ t ∣ g ∧ b = a * t ^ 2) ∧
    ‖(boundaryCoefficient n K H g b : ℂ)‖ ≤ (divisors g).card ^ 2 := by
  refine ⟨?_, boundary_coefficient_card_bound n K H g hg0 b⟩
  intro hb
  obtain ⟨hlower, hupper⟩ := nonzero_coefficient_annulus n hn g hg0 K hK H b hb
  refine ⟨hlower, hupper, ?_⟩
  have hex : ∃ h ∈ H, ∃ d ∈ divisors g, ∃ e ∈ divisors g, h * d * e = b := by
    by_contra hnone
    apply hb
    unfold boundaryCoefficient
    apply Finset.sum_eq_zero
    intro h hh
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro e he
    exact if_neg (fun heq => hnone ⟨h, hh, d, hd, e, he, heq⟩)
  obtain ⟨h, hh, d, hd, e, he, rfl⟩ := hex
  exact divisor_pair_squarefree_times_square g hg0 hg h (hH h hh).1 (hH h hh).2
    d e hd he

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference

end
