module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.NormalProductConvergence
public import DedekindZetaZeroFree.Moments.Principal.Corrections.SmallPrimeSubpowerBounds

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem H_u_uniform_subpower_bound
    (C : A.GeneralArithmeticContext σ η hS) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ (U : Frequency C) (x : Coordinates) (hx : x ∈ Omega),
      ‖H_u C U x.1 x.2.1 x.2.2 (multipliable_localFactor C U x hx)‖ ≤
        Cε * (A.exteriorNorm U.ideal) ^ ε := by
  classical
  open LocalFiniteSums in
  obtain ⟨M, hM, hg⟩ := good_correction_uniform_bound
  obtain ⟨B, hB, hb⟩ := bad_factor_uniform_estimate C
  obtain ⟨K, hK, hsmall⟩ := fixed_small_prime_subpower F A.cS B (1 / 4000) ε
    hB.le (by norm_num) hε
  let g : LocalFiniteSums.ExteriorPrime A → ℝ := fun p =>
    M * LocalFiniteSums.Q p ^ (-(1 + 1 / 4000 : ℝ))
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg hM.le (Real.rpow_nonneg (by
      simp [LocalFiniteSums.Q, SArithmeticData.exteriorNorm, idealNorm]) _)
  have hgs : Summable g := by
    let e : LocalFiniteSums.ExteriorPrime A → NonzeroIdeal F :=
      fun p => ⟨p.val.asIdeal, p.val.ne_bot⟩
    have he : Function.Injective e := by
      intro p q hpq
      apply Subtype.ext
      apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      exact congrArg Subtype.val hpq
    have hh := ((ideal_norm_rpow_summable F (1 + 1 / 4000) (by norm_num)).comp_injective he).mul_left M
    convert hh using 1
    rfl
  refine ⟨Real.exp (∑' p, g p) * K, mul_pos (Real.exp_pos _) hK, ?_⟩
  intro U x hx
  have hloc : ∀ p : LocalFiniteSums.ExteriorPrime A,
      ‖localFactor C U p x.1 x.2.1 x.2.2‖ ≤
        Real.exp (g p) * (if (U.j p).val = 0 then 1 else
          1 + B * LocalFiniteSums.Q p ^ (-(1 / 4000 : ℝ))) := by
    intro p
    have hn (a : ℂ) : ‖a‖ ≤ ‖a - 1‖ + 1 := by
      simpa [norm_sub_rev, add_comm] using norm_le_insert 1 a
    by_cases hj : (U.j p).val = 0
    · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) U.u) := by
        have hs := U.unitPart_spec p
        have he : U.u = U.unitPart p := by simpa [hj] using hs.1
        rw [he]
        exact hs.2
      simp only [localFactor, hj, if_true, mul_one]
      exact (hn _).trans ((add_le_add_left
        (hg F A σ η hS C p U.u hu x hx) 1).trans (by
          simpa [g, add_comm] using Real.add_one_le_exp (g p)))
    · simp only [localFactor, hj, if_false]
      have hm := (hn _).trans (add_le_add_left (hb p (U.j p) hj (U.theta p) x hx) 1)
      apply (hm.trans_eq (add_comm _ _)).trans
      exact le_mul_of_one_le_left (by
        have hq : 0 ≤ LocalFiniteSums.Q p := by
          simp [LocalFiniteSums.Q, SArithmeticData.exteriorNorm, idealNorm]
        exact add_nonneg zero_le_one (mul_nonneg hB.le (Real.rpow_nonneg hq _)))
        (Real.one_le_exp_iff.mpr (hg0 p))
  have hfinite : ∀ s : Finset (LocalFiniteSums.ExteriorPrime A),
      ‖∏ p ∈ s, localFactor C U p x.1 x.2.1 x.2.2‖ ≤
        (Real.exp (∑' p, g p) * K) * A.exteriorNorm U.ideal ^ ε := by
    intro s
    let t := s.filter (fun p => (U.j p).val ≠ 0)
    let b : Ideal (𝓞 F) → ℝ := fun p => 1 + B * idealNorm p ^ (-(1 / 4000 : ℝ))
    have hb1 : ∀ p, 1 ≤ b p := by
      intro p
      have hp : 0 ≤ idealNorm p := by unfold idealNorm; positivity
      dsimp [b]
      nlinarith [Real.rpow_nonneg hp (-(1 / 4000 : ℝ))]
    have hinj : Function.Injective (fun p : LocalFiniteSums.ExteriorPrime A => p.val.asIdeal) := by
      intro p q hpq
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq)
    have ht : t.image (fun p => p.val.asIdeal) ⊆ idealPrimeSupport U.ideal.val := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have hj := (Finset.mem_filter.mp hq).2
      simp only [Frequency.j, idealPrimeExponent] at hj
      simpa only [idealPrimeSupport, Multiset.mem_toFinset] using
        Multiset.count_ne_zero.mp hj
    have hbad : (∏ p ∈ s, if (U.j p).val = 0 then 1 else
        1 + B * LocalFiniteSums.Q p ^ (-(1 / 4000 : ℝ))) ≤
        K * A.exteriorNorm U.ideal ^ ε := by
      calc
        _ = ∏ p ∈ t, b p.val.asIdeal := by
          rw [Finset.prod_ite]
          simp [t, b, LocalFiniteSums.Q, LocalFiniteSums.primeIdeal,
            SArithmeticData.exteriorNorm]
        _ = ∏ p ∈ t.image (fun p => p.val.asIdeal), b p :=
          (Finset.prod_image (fun p _ q _ h => hinj h)).symm
        _ ≤ ∏ p ∈ idealPrimeSupport U.ideal.val, b p := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ ht
          · intro p _; exact zero_le_one.trans (hb1 p)
          · intro p _ _; exact hb1 p
        _ ≤ K * A.exteriorNorm U.ideal ^ ε := hsmall U.ideal
    calc
      _ ≤ ∏ p ∈ s, ‖localFactor C U p x.1 x.2.1 x.2.2‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ p ∈ s, Real.exp (g p) * (if (U.j p).val = 0 then 1 else
          1 + B * LocalFiniteSums.Q p ^ (-(1 / 4000 : ℝ))) :=
        Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => hloc p)
      _ = Real.exp (∑ p ∈ s, g p) * (∏ p ∈ s, if (U.j p).val = 0 then 1 else
          1 + B * LocalFiniteSums.Q p ^ (-(1 / 4000 : ℝ))) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      _ ≤ Real.exp (∑' p, g p) * (K * A.exteriorNorm U.ideal ^ ε) := by
        apply mul_le_mul
        · exact Real.exp_le_exp.mpr (hgs.sum_le_tsum s (fun p _ => hg0 p))
        · exact hbad
        · exact Finset.prod_nonneg (fun p _ => by
            split_ifs
            · norm_num
            · have hq : 0 ≤ LocalFiniteSums.Q p := by
                simp [LocalFiniteSums.Q, SArithmeticData.exteriorNorm, idealNorm]
              positivity)
        · exact (Real.exp_pos _).le
      _ = _ := by ring
  unfold H_u
  apply le_of_tendsto' (multipliable_localFactor C U x hx).hasProd.norm
  intro s
  simpa only [norm_prod] using hfinite s

end DedekindZetaZeroFree.CorrectionFactors

end
