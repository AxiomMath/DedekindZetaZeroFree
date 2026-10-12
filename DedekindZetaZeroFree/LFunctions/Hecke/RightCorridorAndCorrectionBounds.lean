module

public import DedekindZetaZeroFree.LFunctions.Hecke.EulerCorrectionAndQuotientContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.KummerConductorStripBounds
public import DedekindZetaZeroFree.Moments.Principal.Numerator.RightHalfPlaneBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]

theorem raw_minus_reciprocal_bound
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (U : AllRowEuler.InitialSeparation.RawFrequency A) (ξ : ℂ), a ≤ ξ.re →
        ‖(AllRowEuler.InitialSeparation.minusL σ η U ξ)⁻¹‖ ≤ B := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a)),
    Real.exp_pos _, ?_⟩
  intro U ξ hξ
  have hξ1 : 1 < ξ.re := ha.trans_le hξ
  have hc := AllRowEuler.InitialSeparation.raw_minus_isCoefficient (A := A) (σ := σ) (η := η) U
  have hexp := HeckeLogProof.exp_eulerLog (cS := A.cS)
    (AllRowEuler.InitialSeparation.minusExteriorCoefficient σ η U) hc ξ hξ1
  rw [AllRowEuler.InitialSeparation.minusL, InitialSeparatedEuler.dirichletSeries, ← hexp,
    norm_inv, Complex.norm_exp, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr
    (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
      (HeckeLogProof.eulerLog_norm_le _ hc a ha ξ hξ))

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound
noncomputable section
open scoped Classical
open scoped NumberField
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem rawRow_majorant_summable (M : ℝ) :
    Summable (fun p : ExteriorPrime A =>
      M * (Q p) ^ (-(1 + 1 / 4000 : ℝ))) := by
  let i : ExteriorPrime A → {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} :=
    fun p => ⟨p.val, by
      intro hp
      have he := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
      simp only [sup_idem] at he
      exact p.val.isPrime.ne_top he⟩
  have hi : Function.Injective i := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r : {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} => r.val) h
  have hs := (summable_exterior_prime_norm_rpow F A.Sf (1 + 1 / 4000) (by norm_num)).comp_injective hi
  simpa [Function.comp_def, i, Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
    using hs.mul_left M

theorem raw_correction_subpower_bound
    (C : A.GeneralArithmeticContext σ η hS) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (U : AllRowEuler.InitialSeparation.RawFrequency A)
        (x : CorrectionFactors.Coordinates), x ∈ CorrectionFactors.Omega →
        ‖AllRowEuler.InitialSeparation.correctionProduct C U x.1 x.2.1 x.2.2‖ ≤
          B * (A.exteriorNorm U.ideal) ^ ε := by
  classical
  open LocalFiniteSums in
  obtain ⟨M, hM, hg⟩ := CorrectionFactors.good_correction_uniform_bound
  obtain ⟨B, hB, hb⟩ := CorrectionFactors.bad_factor_uniform_estimate C
  obtain ⟨K, hK, hsmall⟩ := fixed_small_prime_subpower F A.cS B (1 / 4000) ε
    hB.le (by norm_num) hε
  let g : ExteriorPrime A → ℝ := fun p => M * Q p ^ (-(1 + 1 / 4000 : ℝ))
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg hM.le (Real.rpow_nonneg (by
      simp [Q, SArithmeticData.exteriorNorm, idealNorm]) _)
  have hgs : Summable g := rawRow_majorant_summable (A := A) M
  refine ⟨Real.exp (∑' p, g p) * K, mul_pos (Real.exp_pos _) hK, ?_⟩
  intro U x hx
  have hloc : ∀ p : ExteriorPrime A,
      ‖AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2‖ ≤
        Real.exp (g p) * (if (U.j p).val = 0 then 1 else
          1 + B * Q p ^ (-(1 / 4000 : ℝ))) := by
    intro p
    have hn (a : ℂ) : ‖a‖ ≤ ‖a - 1‖ + 1 := by
      simpa [norm_sub_rev, add_comm] using norm_le_insert 1 a
    by_cases hj : (U.j p).val = 0
    · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
        have hs := U.unitPart_spec C p
        have he : U.u = U.unitPart C p := by simpa [hj] using hs.1
        rw [he]
        exact hs.2
      simp only [AllRowEuler.InitialSeparation.localCorrection, hj, if_true, mul_one]
      exact (hn _).trans ((add_le_add_left
        (hg F A σ η hS C p U.u hu x hx) 1).trans (by
          simpa [g, add_comm] using Real.add_one_le_exp (g p)))
    · simp only [AllRowEuler.InitialSeparation.localCorrection, hj, if_false]
      have hm := (hn _).trans (add_le_add_left (hb p (U.j p) hj (U.theta C p) x hx) 1)
      apply (hm.trans_eq (add_comm _ _)).trans
      exact le_mul_of_one_le_left (by
        have hq : 0 ≤ Q p := by
          simp [Q, SArithmeticData.exteriorNorm, idealNorm]
        exact add_nonneg zero_le_one (mul_nonneg hB.le (Real.rpow_nonneg hq _)))
        (Real.one_le_exp_iff.mpr (hg0 p))
  have hfinite : ∀ s : Finset (ExteriorPrime A),
      ‖∏ p ∈ s, AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2‖ ≤
        (Real.exp (∑' p, g p) * K) * A.exteriorNorm U.ideal ^ ε := by
    intro s
    let t := s.filter (fun p => (U.j p).val ≠ 0)
    let b : Ideal (𝓞 F) → ℝ := fun p => 1 + B * idealNorm p ^ (-(1 / 4000 : ℝ))
    have hb1 : ∀ p, 1 ≤ b p := by
      intro p
      have hp : 0 ≤ idealNorm p := by unfold idealNorm; positivity
      dsimp [b]
      nlinarith [Real.rpow_nonneg hp (-(1 / 4000 : ℝ))]
    have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) := by
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
        1 + B * Q p ^ (-(1 / 4000 : ℝ))) ≤
        K * A.exteriorNorm U.ideal ^ ε := by
      calc
        _ = ∏ p ∈ t, b p.val.asIdeal := by
          rw [Finset.prod_ite]
          simp [t, b, Q, primeIdeal, SArithmeticData.exteriorNorm]
        _ = ∏ p ∈ t.image (fun p => p.val.asIdeal), b p :=
          (Finset.prod_image (fun p _ q _ h => hinj h)).symm
        _ ≤ ∏ p ∈ idealPrimeSupport U.ideal.val, b p := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ ht
          · intro p _; exact zero_le_one.trans (hb1 p)
          · intro p _ _; exact hb1 p
        _ ≤ K * A.exteriorNorm U.ideal ^ ε := hsmall U.ideal
    calc
      _ ≤ ∏ p ∈ s, ‖AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ p ∈ s, Real.exp (g p) * (if (U.j p).val = 0 then 1 else
          1 + B * Q p ^ (-(1 / 4000 : ℝ))) :=
        Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => hloc p)
      _ = Real.exp (∑ p ∈ s, g p) * (∏ p ∈ s, if (U.j p).val = 0 then 1 else
          1 + B * Q p ^ (-(1 / 4000 : ℝ))) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      _ ≤ Real.exp (∑' p, g p) * (K * A.exteriorNorm U.ideal ^ ε) := by
        apply mul_le_mul
        · exact Real.exp_le_exp.mpr (hgs.sum_le_tsum s (fun p _ => hg0 p))
        · exact hbad
        · exact Finset.prod_nonneg (fun p _ => by
            split_ifs
            · norm_num
            · have hq : 0 ≤ Q p := by
                simp [Q, SArithmeticData.exteriorNorm, idealNorm]
              positivity)
        · exact (Real.exp_pos _).le
      _ = _ := by ring
  unfold AllRowEuler.InitialSeparation.correctionProduct
  apply le_of_tendsto'
    ((AllRowEuler.InitialSeparation.raw_correction_multipliable C U x hx).hasProd.norm)
  intro s
  simpa only [norm_prod] using hfinite s

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound

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

theorem actual_right_corridor_bound
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
    ∃ d : ℝ, 0 ≤ d ∧ ∀ δ : ℝ, 0 < δ →
      ∃ B : ℝ, 0 < B ∧ ∀ u : Frequency R, u ≠ principalFrequency R →
        1 ≤ frequencyNorm R u → ∀ ξ w z : ℂ,
        ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
        w ∈ comparisonClosedStrip (3 / 1000) 4 →
        z ∈ comparisonClosedStrip (2 / 5) 2 →
        ‖euler R C U plus minus u ξ w z‖ ≤
          B * (frequencyNorm R u) ^ (1 / 2 + δ) * (2 + |w.im|) ^ d := by
  obtain ⟨d, hd, hP⟩ := RightBound.continued_plus_strip_bound
    R U plus hU hplus hplusSeries (3 / 1000) 4 (by norm_num) (by norm_num)
  obtain ⟨L, hL, hLB⟩ := PrincipalNumerator.rightHalfPlane_bound R (12 / 5) (by norm_num)
  have hσ : 1 < comparisonSigma₁ := by
    norm_num [comparisonSigma₁, comparisonDelta]
  obtain ⟨M, hM, hMB⟩ := RightBound.raw_minus_reciprocal_bound
    R.A R.σ R.target comparisonSigma₁ hσ
  refine ⟨d, hd, ?_⟩
  intro δ hδ
  obtain ⟨P, hPpos, hPB⟩ := hP (δ / 2) (by linarith)
  obtain ⟨H, hH, hHB⟩ := RightBound.raw_correction_subpower_bound C
    (δ / 2) (by linarith)
  refine ⟨L * P * H * M, by positivity, ?_⟩
  intro u hu hq ξ w z hξ hw hz
  have hξlo : comparisonSigma₁ ≤ ξ.re := hξ.1
  have hwlo : (3 / 1000 : ℝ) ≤ w.re := hw.1
  have hzlo : (2 / 5 : ℝ) ≤ z.re := hz.1
  have hΩ : (ξ, w, z) ∈ CorrectionFactors.Omega := by
    apply Or.inl
    change (499 / 500 : ℝ) - 1 / 100000 < ξ.re ∧
      (3 / 1000 : ℝ) - 1 / 100000 < w.re ∧
      (2 / 5 : ℝ) - 1 / 100000 < z.re
    have : (499 / 500 : ℝ) - 1 / 100000 < comparisonSigma₁ := by
      norm_num [comparisonSigma₁, comparisonDelta]
    exact ⟨this.trans_le hξlo, by linarith, by linarith⟩
  have hn : R.A.exteriorNorm (U u).ideal = frequencyNorm R u := by
    unfold frequencyNorm FiniteTransform.exteriorNorm
    rw [← hU u]
    change R.A.exteriorNorm (U u).ideal =
      (Nat.card (R.A.R ⧸ Ideal.span {(U u).u}) : ℝ)
    rw [(U u).generates.2, R.A.exteriorResidue_card]
    rfl
  have hLb : ‖R.L (6 * z)‖ ≤ L := hLB _ (by
    norm_num [Complex.mul_re]
    linarith)
  have hPb := hPB u hu hq w hw
  have hHb := hHB (U u) (ξ, w, z) hΩ
  simp only at hHb
  rw [hn] at hHb
  have hMb : ‖(minus u ξ)⁻¹‖ ≤ M := by
    rw [hminusSeries u ξ (hσ.trans_le hξlo)]
    exact hMB (U u) ξ hξlo
  have hqpos : 0 < frequencyNorm R u := lt_of_lt_of_le zero_lt_one hq
  have hpower : (frequencyNorm R u) ^ (1 / 2 + δ / 2) *
      (frequencyNorm R u) ^ (δ / 2) = (frequencyNorm R u) ^ (1 / 2 + δ) := by
    rw [← Real.rpow_add hqpos]
    congr 1
    ring
  calc
    ‖euler R C U plus minus u ξ w z‖ =
        ‖R.L (6 * z)‖ * ‖plus u w‖ *
          ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖ *
          ‖(minus u ξ)⁻¹‖ := by
      simp only [euler, numerator, div_eq_mul_inv, norm_mul]
    _ ≤ L * (P * (frequencyNorm R u) ^ (1 / 2 + δ / 2) * (2 + |w.im|) ^ d) *
        (H * (frequencyNorm R u) ^ (δ / 2)) * M := by
      apply mul_le_mul _ hMb (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hHb (norm_nonneg _) (by positivity)
      exact mul_le_mul hLb hPb (norm_nonneg _) hL.le
    _ = (L * P * H * M) * (frequencyNorm R u) ^ (1 / 2 + δ) *
        (2 + |w.im|) ^ d := by
      rw [← hpower]
      ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
