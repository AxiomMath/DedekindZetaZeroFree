module

public import DedekindZetaZeroFree.LFunctions.Hecke.KummerConductorStripBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.EulerCorrectionAndQuotientContinuation
public import DedekindZetaZeroFree.Moments.Principal.Numerator.RightHalfPlaneBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.LeftNumeratorBound
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem plus_continuation_uniform_strip_bound
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus : Frequency R → ℂ → ℂ)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re})
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ (u : Frequency R) (s : ℂ), u ≠ principalFrequency R →
        1 ≤ frequencyNorm R u → 3 / 1000 ≤ s.re → s.re ≤ 4 →
        ‖plus u s‖ ≤ B * (frequencyNorm R u) ^ (1 / 2 + ε) *
          (2 + |s.im|) ^ A := by
  obtain ⟨A, hA, hbound⟩ := RightBound.continued_plus_strip_bound
    R U plus hU hplus hplusSeries (3 / 1000) 4 (by norm_num) (by norm_num)
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨B, hB, hBε⟩ := hbound ε hε
  exact ⟨B, hB, fun u s hu hq hs₁ hs₂ =>
    hBε u hu hq s (by
      simp only [comparisonClosedStrip, Set.mem_setOf_eq]; exact ⟨hs₁, hs₂⟩)⟩

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.LeftNumeratorBound

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.LeftNumeratorBound
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem raw_correction_uniform_subpower_bound
    (C : A.GeneralArithmeticContext σ η hS) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (U : AllRowEuler.InitialSeparation.RawFrequency A) (ξ w z : ℂ),
        (ξ, w, z) ∈ CorrectionFactors.Omega →
        ‖AllRowEuler.InitialSeparation.correctionProduct C U ξ w z‖ ≤
          B * (A.exteriorNorm U.ideal) ^ ε := by
  classical
  open LocalFiniteSums in
  obtain ⟨M, hM, hg⟩ := CorrectionFactors.good_correction_uniform_bound
  obtain ⟨B, hB, hb⟩ := CorrectionFactors.bad_factor_uniform_estimate C
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
  intro U ξ w z hx
  have hloc : ∀ p : LocalFiniteSums.ExteriorPrime A,
      ‖AllRowEuler.InitialSeparation.localCorrection C U p ξ w z‖ ≤
        Real.exp (g p) * (if (U.j p).val = 0 then 1 else
          1 + B * LocalFiniteSums.Q p ^ (-(1 / 4000 : ℝ))) := by
    intro p
    have hn (a : ℂ) : ‖a‖ ≤ ‖a - 1‖ + 1 := by
      simpa [norm_sub_rev, add_comm] using norm_le_insert 1 a
    by_cases hj : (U.j p).val = 0
    · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (LocalFiniteSums.primeIdeal p)) U.u) := by
        have hs := U.unitPart_spec C p
        have he : U.u = U.unitPart C p := by simpa [hj] using hs.1
        rw [he]
        exact hs.2
      simp only [AllRowEuler.InitialSeparation.localCorrection, hj, if_true, mul_one]
      exact (hn _).trans ((add_le_add_left
        (hg F A σ η hS C p U.u hu (ξ, w, z) hx) 1).trans (by
          simpa [g, add_comm] using Real.add_one_le_exp (g p)))
    · simp only [AllRowEuler.InitialSeparation.localCorrection, hj, if_false]
      have hm := (hn _).trans (add_le_add_left (hb p (U.j p) hj (U.theta C p) (ξ, w, z) hx) 1)
      apply (hm.trans_eq (add_comm _ _)).trans
      exact le_mul_of_one_le_left (by
        have hq : 0 ≤ LocalFiniteSums.Q p := by
          simp [LocalFiniteSums.Q, SArithmeticData.exteriorNorm, idealNorm]
        exact add_nonneg zero_le_one (mul_nonneg hB.le (Real.rpow_nonneg hq _)))
        (Real.one_le_exp_iff.mpr (hg0 p))
  have hfinite : ∀ s : Finset (LocalFiniteSums.ExteriorPrime A),
      ‖∏ p ∈ s, AllRowEuler.InitialSeparation.localCorrection C U p ξ w z‖ ≤
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
      simp only [AllRowEuler.InitialSeparation.RawFrequency.j, idealPrimeExponent] at hj
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
      _ ≤ ∏ p ∈ s, ‖AllRowEuler.InitialSeparation.localCorrection C U p ξ w z‖ :=
        Finset.norm_prod_le _ _
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
  apply le_of_tendsto'
    (AllRowEuler.InitialSeparation.raw_correction_multipliable C U (ξ, w, z) hx).hasProd.norm
  intro s
  simpa only [norm_prod] using hfinite s

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.LeftNumeratorBound

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.LeftNumeratorBound
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F}

theorem raw_frequency_norm_eq
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    (FiniteTransform.exteriorNorm A.R.toSubring U.u : ℝ) =
      A.exteriorNorm U.ideal := by
  change (Nat.card (A.R ⧸ Ideal.span {U.u}) : ℝ) = _
  rw [U.generates.2, A.exteriorResidue_card]
  rfl

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.LeftNumeratorBound

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

variable (R : PrincipalMellin.ActualRecipe S η)
  (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
  (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
  (plus minus : Frequency R → ℂ → ℂ)

theorem actual_left_numerator_bound
    (hC : R.probe.correction = C.correction)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re})
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s) :
    ∃ A_F : ℝ, 0 ≤ A_F ∧
      ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 < B ∧
        ∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
          1 ≤ frequencyNorm R u →
          ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
          w.re = 3 / 1000 → z.re = 2 / 5 →
          ‖numerator R C U plus u ξ w z‖ ≤
            B * (frequencyNorm R u) ^ (1 / 2 + δ) *
            (2 + |ξ.im|) ^ A_F * (2 + |w.im|) ^ A_F * (2 + |z.im|) ^ A_F := by
  obtain ⟨A, hA, hplusBound⟩ :=
    LeftNumeratorBound.plus_continuation_uniform_strip_bound
        R U plus hU hplus hplusSeries
  obtain ⟨Bz, hBz, hL⟩ := PrincipalNumerator.rightHalfPlane_bound R 2 (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨Bp, hBp, hp⟩ := hplusBound (δ / 2) hhalf
  obtain ⟨Bc, hBc, hc⟩ :=
    LeftNumeratorBound.raw_correction_uniform_subpower_bound C (δ / 2) hhalf
  refine ⟨Bz * Bp * Bc, mul_pos (mul_pos hBz hBp) hBc, ?_⟩
  intro u ξ w z hu hq hξ hw hz
  have hqpos : 0 < frequencyNorm R u := lt_of_lt_of_le zero_lt_one hq
  have hnorm : R.A.exteriorNorm (U u).ideal = frequencyNorm R u := by
    rw [← LeftNumeratorBound.raw_frequency_norm_eq (U u), hU u]
    rfl
  have hΩ : (ξ, w, z) ∈ CorrectionFactors.Omega := by
    apply Set.mem_union_left
    change (499 / 500 : ℝ) - 1 / 100000 < ξ.re ∧
      (3 / 1000 : ℝ) - 1 / 100000 < w.re ∧
      (2 / 5 : ℝ) - 1 / 100000 < z.re
    have hξlo : (499 / 500 : ℝ) ≤ ξ.re := hξ.1
    constructor
    · linarith
    constructor <;> linarith
  have hLz : ‖R.L (6 * z)‖ ≤ Bz := by
    apply hL
    norm_num [Complex.mul_re, hz]
  have hpw := hp u w hu hq (by linarith) (by linarith)
  have hcorr := hc (U u) ξ w z hΩ
  rw [hnorm] at hcorr
  have hx : 1 ≤ (2 + |ξ.im|) ^ A :=
    Real.one_le_rpow (by linarith [abs_nonneg ξ.im]) hA
  have hzh : 1 ≤ (2 + |z.im|) ^ A :=
    Real.one_le_rpow (by linarith [abs_nonneg z.im]) hA
  have hprod : ‖numerator R C U plus u ξ w z‖ ≤
      (Bz * Bp * Bc) * (frequencyNorm R u) ^ (1 / 2 + δ) *
        (2 + |w.im|) ^ A := by
    calc
      _ = ‖R.L (6 * z)‖ * ‖plus u w‖ *
          ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖ := by
        simp only [numerator, norm_mul]
      _ ≤ Bz * (Bp * (frequencyNorm R u) ^ (1 / 2 + δ / 2) *
          (2 + |w.im|) ^ A) * (Bc * (frequencyNorm R u) ^ (δ / 2)) := by
        gcongr
      _ = (Bz * Bp * Bc) * (frequencyNorm R u) ^ (1 / 2 + δ) *
          (2 + |w.im|) ^ A := by
        have he : (1 / 2 + δ / 2) + δ / 2 = (1 / 2 + δ : ℝ) := by ring
        have hpow : (frequencyNorm R u) ^ (1 / 2 + δ) =
            (frequencyNorm R u) ^ (1 / 2 + δ / 2) *
              (frequencyNorm R u) ^ (δ / 2) := by
          calc
            _ = (frequencyNorm R u) ^ ((1 / 2 + δ / 2) + δ / 2) := by rw [he]
            _ = _ := Real.rpow_add hqpos _ _
        rw [hpow]
        ring
  calc
    _ ≤ (Bz * Bp * Bc) * (frequencyNorm R u) ^ (1 / 2 + δ) *
        (2 + |w.im|) ^ A := hprod
    _ ≤ ((Bz * Bp * Bc) * (frequencyNorm R u) ^ (1 / 2 + δ) *
        (2 + |w.im|) ^ A) * ((2 + |ξ.im|) ^ A * (2 + |z.im|) ^ A) := by
      apply le_mul_of_one_le_right (by positivity)
      exact one_le_mul_of_one_le_of_one_le hx hzh
    _ = _ := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
