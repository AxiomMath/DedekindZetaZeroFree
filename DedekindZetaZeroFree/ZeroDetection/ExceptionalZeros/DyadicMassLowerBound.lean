module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.NormDyadicCover
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.ShiftedMellinEstimate

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField BigOperators Classical

private theorem fixed_mass_presentation_eq
    (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F))
    (ω : RayClassCharacter F m) (P Q : NonprincipalRayHeckeData F m ω)
    (s : ℂ) (hs : 0 < s.re) : P.L s = Q.L s := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : IsPreconnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_gt (show IsLinearMap ℝ Complex.re from Complex.reLm.isLinear) 0).isPreconnected
  have hev : P.L =ᶠ[nhds (2 : ℂ)] Q.L := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    exact (P.series z hz).unique (Q.series z hz)
  exact (P.L_holo.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq
    (Q.L_holo.analyticOnNhd ho) hc (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) hev hs

private theorem fixed_mass_summand_bound
    (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ω : RayClassCharacter F m) (U β γ : ℝ) (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    ‖Detector.smoothedDetectorSummand F ω U ((β : ℂ) + Complex.I * (γ : ℂ)) n‖ ≤
      |Detector.truncatedIdealMoebius F U n| * (Ideal.absNorm n : ℝ) ^ (-β) *
        Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) := by
  have hnpos : 0 < Ideal.absNorm n :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  have hw := RayUnitary.ray_character_norm_le_one F m hm ω n
  simp only [Detector.smoothedDetectorSummand, if_pos hn, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos hnpos,
    Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
    zero_add, add_zero, abs_of_pos (Real.exp_pos _)]
  simp only [zero_mul, add_zero]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.exp_pos _).le

private theorem fixed_mass_cover_bound
    (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ω : RayClassCharacter F m) (U β γ : ℝ) (hU : 2 ≤ U) (hβ : 249 / 250 ≤ β)
    (hsmall : ‖Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ))‖ ≤ 1 / 8)
    (htail : |Detector.idealDampedTail F (Detector.truncatedIdealMoebius F) U β| < 1 / 8)
    (hunit : 3 / 4 ≤ Real.exp (-1 / U ^ 10)) :
    (1 / 2 : ℝ) ≤
      ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F
          ((2 : ℝ) ^ detector_sz_dyadicUpper U)).toFinset.filter
          (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U < (Ideal.absNorm n : ℝ)),
        (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
          (Ideal.absNorm n : ℂ) ^ (-(β : ℂ) - Complex.I * (γ : ℂ)) *
          (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) : ℂ)‖ := by
  let K := (Detector.ideals_bounded_norm_finite F
    ((2 : ℝ) ^ detector_sz_dyadicUpper U)).toFinset
  let f := Detector.smoothedDetectorSummand F ω U ((β : ℂ) + Complex.I * (γ : ℂ))
  let t : Ideal (𝓞 F) → ℂ := fun n => if n ∈ K then 0 else f n
  let b : Ideal (𝓞 F) → ℝ := fun n =>
    if n ≠ ⊥ ∧ U ^ 11 < (Ideal.absNorm n : ℝ) then
      |Detector.truncatedIdealMoebius F U n| * (Ideal.absNorm n : ℝ) ^ (-β) *
        Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) else 0
  have hK (n : Ideal (𝓞 F)) : n ∈ K ↔ n ≠ ⊥ ∧
      (Ideal.absNorm n : ℝ) ≤ (2 : ℝ) ^ detector_sz_dyadicUpper U :=
    Set.Finite.mem_toFinset _
  have hc := detector_sz_dyadic_cover U hU
  have hb : Summable b := Detector.ideal_damped_tail_summable F
    (Detector.truncatedIdealMoebius F) (Detector.truncatedIdealMoebius_abs_le F) U β hU (by convert hβ using 1 <;> norm_num)
  have htb (n : Ideal (𝓞 F)) : ‖t n‖ ≤ b n := by
    by_cases hnK : n ∈ K
    · simp only [t, if_pos hnK, norm_zero]
      dsimp [b]; split_ifs <;> positivity
    · by_cases hn : n = ⊥
      · simp [t, hnK, f, hn, Detector.smoothedDetectorSummand, b]
      · have hnorm : (2 : ℝ) ^ detector_sz_dyadicUpper U < (Ideal.absNorm n : ℝ) := by
          by_contra H
          exact hnK ((hK n).2 ⟨hn, le_of_not_gt H⟩)
        have hgt := lt_of_le_of_lt hc.2.2.2.1.2 hnorm
        have hcond : n ≠ ⊥ ∧ U ^ 11 < (Ideal.absNorm n : ℝ) := ⟨hn, hgt⟩
        simp only [t, if_neg hnK, b, if_pos hcond]
        exact fixed_mass_summand_bound F m hm ω U β γ n hn
  have ht : Summable t := hb.of_norm_bounded htb
  have htn : Summable (fun n => ‖t n‖) := summable_norm_iff.mpr ht
  have htbound : ‖∑' n, t n‖ < 1 / 8 := by
    calc
      _ ≤ ∑' n, ‖t n‖ := norm_tsum_le_tsum_norm htn
      _ ≤ ∑' n, b n := htn.tsum_le_tsum htb hb
      _ ≤ |Detector.idealDampedTail F (Detector.truncatedIdealMoebius F) U β| := le_abs_self _
      _ < 1 / 8 := htail
  have hfin : Summable (fun n => if n ∈ K then f n else 0) :=
    summable_of_ne_finset_zero (s := K) (by intro n hn; simp [hn])
  have hdecomp : (∑ n ∈ K, f n) + (∑' n, t n) =
      Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ)) := by
    have hfinsum : (∑' n, if n ∈ K then f n else 0) = ∑ n ∈ K, f n := by
      rw [tsum_eq_sum (s := K) (by intro n hn; simp [hn])]
      exact Finset.sum_congr rfl (fun n hn => if_pos hn)
    rw [← hfinsum, ← hfin.tsum_add ht]
    have heq : (fun n => (if n ∈ K then f n else 0) + t n) = f := by
      funext n; dsimp [t]; split_ifs <;> simp
    rw [heq]
    rfl
  have htopK : (⊤ : Ideal (𝓞 F)) ∈ K := (hK _).2
    ⟨top_ne_bot, by simpa only [Ideal.absNorm_top, Nat.cast_one] using
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ detector_sz_dyadicUpper U)⟩
  have htoplow : ¬ (2 : ℝ) ^ detector_sz_dyadicLower U <
      (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℝ) := by
    simpa only [Ideal.absNorm_top, Nat.cast_one, not_lt] using
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ detector_sz_dyadicLower U)
  have hlow : (∑ n ∈ K.filter (fun n => ¬ (2 : ℝ) ^ detector_sz_dyadicLower U <
      (Ideal.absNorm n : ℝ)), f n) = f ⊤ := by
    apply Finset.sum_eq_single ⊤
    · intro n hn hnt
      obtain ⟨hnK, hnlow⟩ := Finset.mem_filter.mp hn
      have hn0 := ((hK n).1 hnK).1
      have hn1 : 1 < (Ideal.absNorm n : ℝ) := by
        have hp := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0)
        have hne : Ideal.absNorm n ≠ 1 := fun H => hnt (Ideal.absNorm_eq_one_iff.mp H)
        exact_mod_cast (show 1 < Ideal.absNorm n by omega)
      have hz := Detector.truncatedIdealMoebius_eq_zero F U hU n hn0 hn1
        ((le_of_not_gt hnlow).trans hc.2.2.1.1)
      simp [f, Detector.smoothedDetectorSummand, hn0, hz]
    · intro H
      exact (H (Finset.mem_filter.mpr ⟨htopK, htoplow⟩)).elim
  have htop : f ⊤ = (Real.exp (-1 / U ^ 10) : ℂ) := by
    simp [f, Detector.smoothedDetectorSummand, Detector.truncatedIdealMoebius_top F U hU,
      ω.map_top', top_ne_bot, neg_div]
  have hband : (∑ n ∈ K.filter (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
      (Ideal.absNorm n : ℝ)), f n) =
      ∑ n ∈ K.filter (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
        (Ideal.absNorm n : ℝ)),
        (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
          (Ideal.absNorm n : ℂ) ^ (-(β : ℂ) - Complex.I * (γ : ℂ)) *
          (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 := ((hK n).1 (Finset.mem_filter.mp hn).1).1
    simp only [f, Detector.smoothedDetectorSummand, if_pos hn0, neg_add_rev, sub_eq_add_neg]
    rw [add_comm (-(Complex.I * (γ : ℂ))) (-(β : ℂ))]
  have hpart := Finset.sum_filter_add_sum_filter_not K
    (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U < (Ideal.absNorm n : ℝ)) f
  rw [hlow, htop] at hpart
  rw [← hpart] at hdecomp
  have he : (Real.exp (-1 / U ^ 10) : ℂ) =
      Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ)) -
        (∑ n ∈ K.filter (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
          (Ideal.absNorm n : ℝ)), f n) - (∑' n, t n) := by
    linear_combination hdecomp
  have hn := norm_sub_le
    (Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ)) -
      (∑ n ∈ K.filter (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
        (Ideal.absNorm n : ℝ)), f n)) (∑' n, t n)
  rw [← he] at hn
  have hn2 := norm_sub_le
    (Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ)))
    (∑ n ∈ K.filter (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
      (Ideal.absNorm n : ℝ)), f n)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  rw [hband] at hn hn2
  change (1 / 2 : ℝ) ≤ ‖∑ n ∈ K.filter (fun n =>
    (2 : ℝ) ^ detector_sz_dyadicLower U < (Ideal.absNorm n : ℝ)),
      (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-(β : ℂ) - Complex.I * (γ : ℂ)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) : ℂ)‖
  linarith

theorem detector_sz_dyadic_mass_at_bridge
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    let A_F : ℝ := (detector_convexity_bridge F htc C₀ hC₀).choose
    ∀ ρ : ℝ, 0 < ρ → ρ < min (1 / 10) (1 / (A_F + 1)) →
      ∃ U₀ : ℝ, 2 ≤ U₀ ∧
        ∀ U : ℝ, U₀ ≤ U →
          ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ →
            (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
            ∀ ω : RayClassCharacter F 𝔪, ω.IsPrimitive → ¬ ω.IsPrincipal →
              ∀ D : NonprincipalRayHeckeData F 𝔪 ω,
                ∀ β γ : ℝ, β ∈ Set.Icc (249 / 250) 1 →
                  |γ| ≤ 4 * U ^ ρ →
                  D.L ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
                  (1 / 2 : ℝ) ≤
                    ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F
                        ((2 : ℝ) ^ detector_sz_dyadicUpper U)).toFinset.filter
                        (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U <
                          (Ideal.absNorm n : ℝ)),
                      (Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
                        (Ideal.absNorm n : ℂ) ^
                          (-(β : ℂ) - Complex.I * (γ : ℂ)) *
                        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) : ℂ)‖ := by
  dsimp only
  intro ρ hρ hρupper
  obtain ⟨C, hC, hbound⟩ :=
    (detector_sz_shifted_estimate F htc C₀ hC₀).2 ρ hρ hρupper
  obtain ⟨X₀, hX₀, htail⟩ :=
    Detector.truncatedIdealMoebius_tail_uniform F (1 / 8) (by norm_num)
  have hlim : Filter.Tendsto (fun U : ℝ => C * U ^ (-2 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2))
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  refine ⟨max X₀ X₁, hX₀.trans (le_max_left _ _), ?_⟩
  intro U hU m hm hmnorm ω hω hnp D β γ hβ hγ hzero
  have hUX₀ : X₀ ≤ U := (le_max_left _ _).trans hU
  have hU2 : 2 ≤ U := hX₀.trans hUX₀
  have hsre : ((β : ℂ) + Complex.I * (γ : ℂ)).re = β := by simp
  have hcanonical : Detector.canonicalRayHeckeL F htc m hm ω hω
      ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 := by
    rw [Detector.canonicalRayHeckeL, dif_neg hnp]
    rw [fixed_mass_presentation_eq F m ω
      (nonprincipalRayHeckeData F htc m hm ω hω hnp) D
      ((β : ℂ) + Complex.I * (γ : ℂ)) (by rw [hsre]; linarith [hβ.1])]
    exact hzero
  have hsmall := (hbound U hU2 m hm ω hω hnp hmnorm β γ hβ.1 hβ.2
    hcanonical hγ).trans (le_of_lt (hX₁ U ((le_max_right _ _).trans hU)))
  have htailU := htail U hUX₀ β (by convert hβ.1 using 1 <;> norm_num)
  have hunit : 3 / 4 ≤ Real.exp (-1 / U ^ 10) := by
    have hp : (4 : ℝ) ≤ U ^ (10 : ℕ) := by
      calc
        4 ≤ (2 : ℝ) ^ (10 : ℕ) := by norm_num
        _ ≤ U ^ (10 : ℕ) := pow_le_pow_left₀ (by norm_num) hU2 _
    have hdiv : 1 / U ^ (10 : ℕ) ≤ (1 / 4 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hp
    have hexp := Real.one_sub_le_exp_neg (1 / U ^ (10 : ℕ))
    rw [← neg_div] at hexp
    linarith
  exact fixed_mass_cover_bound F m hm ω U β γ hU2 hβ.1 hsmall htailU hunit

end
end DedekindZetaZeroFree
