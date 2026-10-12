module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.NormDyadicCover
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.AntitoneWeightedPrefixes
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorBoundsAndDampedTails

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField BigOperators Classical

private theorem prefix_max {ι : Type*} (S : Finset ι) (r : ι → ℝ) (a : ι → ℂ)
    (N T : ℝ) (hNT : N ≤ T) :
    ∃ y ∈ Set.Icc N T, ∀ z ∈ Set.Icc N T,
      ‖∑ i ∈ S.filter (fun i => r i ≤ z), a i‖ ≤
      ‖∑ i ∈ S.filter (fun i => r i ≤ y), a i‖ := by
  let Q : Set (Finset ι) := {q | ∃ y ∈ Set.Icc N T, q = S.filter (fun i => r i ≤ y)}
  have hQ : Q.Finite := by
    apply (S.powerset.finite_toSet).subset
    rintro q ⟨y, hy, rfl⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hQne : Q.Nonempty := ⟨S.filter (fun i => r i ≤ N), N, ⟨le_rfl, hNT⟩, rfl⟩
  obtain ⟨q, ⟨y, hy, rfl⟩, hmax⟩ := Set.exists_max_image Q
    (fun q => ‖∑ i ∈ q, a i‖) hQ hQne
  exact ⟨y, hy, fun z hz => hmax _ ⟨z, hz, rfl⟩⟩

private theorem dyadic_partition {ι : Type*} (S : Finset ι) (r : ι → ℝ) (f : ι → ℂ)
    (l k : ℕ) (hlk : l ≤ k) :
    (∑ i ∈ S.filter (fun i => (2:ℝ)^l < r i ∧ r i ≤ (2:ℝ)^k), f i) =
    ∑ j ∈ Finset.Ico l k, ∑ i ∈ S.filter
      (fun i => (2:ℝ)^j < r i ∧ r i ≤ (2:ℝ)^(j+1)), f i := by
  induction k with
  | zero =>
    have : l = 0 := by omega
    subst l
    simp only [Finset.Ico_self, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hi
    exact False.elim (not_lt_of_ge hhi hlo)
  | succ k ih =>
    by_cases heq : l = k+1
    · subst l
      simp only [Finset.Ico_self, Finset.sum_empty]
      apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hi
      exact False.elim (not_lt_of_ge hhi hlo)
    have hl : l ≤ k := by omega
    rw [Finset.sum_Ico_succ_top hl, ← ih hl]
    have hp : (2:ℝ)^l ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
    have hu : (2:ℝ)^k ≤ (2:ℝ)^(k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [← Finset.sum_union]
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hi, hlo, hhi⟩
        by_cases h : r i ≤ (2:ℝ)^k
        · exact Or.inl ⟨hi, hlo, h⟩
        · exact Or.inr ⟨hi, lt_of_not_ge h, hhi⟩
      · rintro (⟨hi, hlo, hhi⟩ | ⟨hi, hlo, hhi⟩)
        · exact ⟨hi, hlo, hhi.trans hu⟩
        · exact ⟨hi, lt_of_le_of_lt hp hlo, hhi⟩
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      simp only [Finset.mem_filter] at hi hj
      exact (not_lt_of_ge hi.2.2) hj.2.1

private theorem cpow_weight (q β γ U : ℝ) (hq : 0 < q) :
    (q:ℂ)^ (-(β:ℂ) - Complex.I * (γ:ℂ)) * (Real.exp (-q/U^10):ℂ) =
      (q:ℂ)^ (-(249/250:ℂ) - Complex.I * (γ:ℂ)) *
        (detector_sz_normWeight U β q : ℂ) := by
  have hr : ((q.rpow (249 / 250 - β) : ℝ) : ℂ) =
      (q : ℂ) ^ ((249 / 250 - β : ℝ) : ℂ) := Complex.ofReal_cpow hq.le _
  rw [detector_sz_normWeight, Complex.ofReal_mul, hr]
  rw [← mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast hq.ne')]
  congr 2
  push_cast
  ring

private theorem ideal_prefix_eq (F : Type) [Field F] [NumberField F]
    (K N T y : ℝ) (hy : y ≤ T) (hT : T ≤ K) :
    (((Detector.ideals_bounded_norm_finite F K).toFinset.filter
      (fun n => N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ T)).filter
      (fun n => (Ideal.absNorm n : ℝ) ≤ y)) =
    (Detector.ideals_bounded_norm_finite F y).toFinset.filter
      (fun n => N < (Ideal.absNorm n : ℝ)) := by
  ext n
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨⟨hn, _⟩, hlo, _⟩, hhi⟩
    exact ⟨⟨hn, hhi⟩, hlo⟩
  · rintro ⟨⟨hn, hhi⟩, hlo⟩
    exact ⟨⟨⟨hn, hhi.trans (hy.trans hT)⟩, hlo, hhi.trans hy⟩, hhi⟩

theorem detector_sz_prefix_extraction (F : Type) [Field F] [NumberField F]
    (U β γ : ℝ) (b : Ideal (𝓞 F) → ℂ)
    (hU : 2 ≤ U) (hβ : 249 / 250 ≤ β)
    (hmass : (1 / 2 : ℝ) ≤
      ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F
          ((2 : ℝ) ^ detector_sz_dyadicUpper U)).toFinset.filter
          (fun n => (2 : ℝ) ^ detector_sz_dyadicLower U < (Ideal.absNorm n : ℝ)),
        b n * (Ideal.absNorm n : ℂ) ^ (-(β : ℂ) - Complex.I * (γ : ℂ)) *
          (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ 10) : ℂ)‖) :
    ∃ j ∈ detector_sz_dyadicIndices U,
      ∃ y ∈ Set.Icc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)),
        1 / (32 * (1 + Real.log U)) ≤
          ‖∑ n ∈ (Detector.ideals_bounded_norm_finite F y).toFinset.filter
              (fun n => (2 : ℝ) ^ j < (Ideal.absNorm n : ℝ)),
            b n * (Ideal.absNorm n : ℂ) ^
              (-(249 / 250 : ℂ) - Complex.I * (γ : ℂ))‖ := by
  let K := (2:ℝ)^detector_sz_dyadicUpper U
  let S := (Detector.ideals_bounded_norm_finite F K).toFinset
  let r : Ideal (𝓞 F) → ℝ := fun n => (Ideal.absNorm n : ℝ)
  let a : Ideal (𝓞 F) → ℂ := fun n => b n * (Ideal.absNorm n : ℂ) ^
    (-(249/250:ℂ) - Complex.I * (γ:ℂ))
  let f : Ideal (𝓞 F) → ℂ := fun n => b n * (Ideal.absNorm n : ℂ) ^
    (-(β:ℂ) - Complex.I * (γ:ℂ)) * (Real.exp (-r n / U^10):ℂ)
  let J := detector_sz_dyadicIndices U
  let c := 1 / (32 * (1 + Real.log U))
  obtain ⟨hlk, hmem, _, _, _, _, hcard⟩ := detector_sz_dyadic_cover U hU
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hc : 0 < c := by dsimp [c]; positivity
  by_contra hno
  have hblock : ∀ j ∈ J,
      ‖∑ n ∈ S.filter (fun n => (2:ℝ)^j < r n ∧ r n ≤ (2:ℝ)^(j+1)), f n‖ < c := by
    intro j hj
    have hjk : j+1 ≤ detector_sz_dyadicUpper U := by
      have := (hmem j).mp hj
      omega
    have hT : (2:ℝ)^(j+1) ≤ K := pow_le_pow_right₀ (by norm_num) hjk
    have hNT : (2:ℝ)^j ≤ (2:ℝ)^(j+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    let B := S.filter (fun n => (2:ℝ)^j < r n ∧ r n ≤ (2:ℝ)^(j+1))
    obtain ⟨y, hy, hmax⟩ := prefix_max B r a ((2:ℝ)^j) ((2:ℝ)^(j+1)) hNT
    have heq : B.filter (fun n => r n ≤ y) =
        (Detector.ideals_bounded_norm_finite F y).toFinset.filter
          (fun n => (2:ℝ)^j < r n) := ideal_prefix_eq F K _ _ y hy.2 hT
    have hsmall : ‖∑ n ∈ B.filter (fun n => r n ≤ y), a n‖ < c := by
      apply lt_of_not_ge
      intro h
      apply hno
      refine ⟨j, hj, y, hy, ?_⟩
      simpa only [heq] using h
    have hbound := detector_sz_normWeight_prefix_bound B r a U β
      ((2:ℝ)^j) ((2:ℝ)^(j+1))
      (‖∑ n ∈ B.filter (fun n => r n ≤ y), a n‖)
      hU hβ (one_le_pow₀ (by norm_num)) hNT
      (fun n hn => (Finset.mem_filter.mp hn).2) (norm_nonneg _) hmax
    have hident : (∑ n ∈ B, f n) =
        ∑ n ∈ B, a n * (detector_sz_normWeight U β (r n):ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hp : 0 < r n := lt_trans (by positivity) (Finset.mem_filter.mp hn).2.1
      have hw := cpow_weight (r n) β γ U hp
      simp only [r, Complex.ofReal_natCast] at hw
      dsimp [f, a, r]
      rw [mul_assoc, hw, ← mul_assoc]
    exact (hident ▸ hbound).trans_lt hsmall
  have hfilter : S.filter (fun n => (2:ℝ)^detector_sz_dyadicLower U < r n) =
      S.filter (fun n => (2:ℝ)^detector_sz_dyadicLower U < r n ∧ r n ≤ K) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hlo⟩
      have hnk : n ≠ ⊥ ∧ r n ≤ K := by
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn
      exact ⟨hn, hlo, hnk.2⟩
    · rintro ⟨hn, hlo, _⟩; exact ⟨hn, hlo⟩
  have hpart := dyadic_partition S r f (detector_sz_dyadicLower U)
    (detector_sz_dyadicUpper U) hlk.le
  have hmass' : (1/2:ℝ) ≤
      ‖∑ j ∈ J, ∑ n ∈ S.filter (fun n => (2:ℝ)^j < r n ∧ r n ≤ (2:ℝ)^(j+1)), f n‖ := by
    change (1/2:ℝ) ≤ ‖∑ j ∈ Finset.Ico (detector_sz_dyadicLower U)
      (detector_sz_dyadicUpper U), ∑ n ∈ S.filter
        (fun n => (2:ℝ)^j < r n ∧ r n ≤ (2:ℝ)^(j+1)), f n‖
    rw [← hpart]
    change (1/2:ℝ) ≤ ‖∑ n ∈ S.filter
      (fun n => (2:ℝ)^detector_sz_dyadicLower U < r n ∧ r n ≤ K), f n‖
    rw [← hfilter]
    exact hmass
  have hJ : J.Nonempty := by
    exact ⟨detector_sz_dyadicLower U, (hmem _).mpr ⟨le_rfl, hlk⟩⟩
  have hsum : (∑ j ∈ J,
      ‖∑ n ∈ S.filter (fun n => (2:ℝ)^j < r n ∧ r n ≤ (2:ℝ)^(j+1)), f n‖) <
      (J.card:ℝ) * c := by
    calc
      _ < ∑ j ∈ J, c := Finset.sum_lt_sum_of_nonempty hJ hblock
      _ = _ := by simp
  have hhalf : (J.card:ℝ) * c ≤ 1/2 := by
    dsimp [c]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (1 + Real.log U))).mpr
    change (detector_sz_dyadicIndices U).card ≤ (1/2:ℝ) * (32 * (1 + Real.log U))
    nlinarith
  have hn := norm_sum_le J (fun j => ∑ n ∈ S.filter
    (fun n => (2:ℝ)^j < r n ∧ r n ≤ (2:ℝ)^(j+1)), f n)
  linarith

end
end DedekindZetaZeroFree
