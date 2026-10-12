module

public import DedekindZetaZeroFree.LFunctions.Hecke.EulerCorrectionAndQuotientContinuation
public import DedekindZetaZeroFree.Moments.Principal.Numerator.RightHalfPlaneBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.FarEulerBounds
noncomputable section
set_option maxHeartbeats 800000
open scoped Classical NumberField

variable {F : Type} [Field F] [NumberField F]

theorem raw_plus_rightHalfPlane_bound
    (A : SArithmeticData F) (σ : F →+* ℂ) (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (U : AllRowEuler.InitialSeparation.RawFrequency A) (w : ℂ), a ≤ w.re →
        ‖AllRowEuler.InitialSeparation.plusL σ U w‖ ≤ B := by
  have hinj : Function.Injective
      (fun I : A.Exterior => (⟨I.val, I.property.1⟩ : NonzeroIdeal F)) := by
    intro I J h
    exact Subtype.ext (congrArg (fun J : NonzeroIdeal F => J.val) h)
  have hbase : Summable (fun I : A.Exterior => (idealNorm I.val) ^ (-a)) := by
    have h := (ideal_norm_rpow_summable F a ha).comp_injective hinj
    exact h
  refine ⟨(∑' I : A.Exterior, (idealNorm I.val) ^ (-a)) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ ∑' I : A.Exterior, (idealNorm I.val) ^ (-a) :=
      tsum_nonneg (fun I =>
        Real.rpow_nonneg (le_trans zero_le_one (idealNorm_ge_one I.val I.property.1)) _)
    linarith
  · intro U w hw
    have hcoeff : ExteriorIdealEuler.IsCoefficient
        (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U) :=
      AllRowEuler.InitialSeparation.raw_plus_isCoefficient U
    have hsum : Summable (fun I : A.Exterior =>
        ‖ExteriorIdealEuler.summand
          (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U) w I‖) :=
      ExteriorIdealEuler.summable_norm_summand _ hcoeff w (by linarith)
    have hle1 : ‖AllRowEuler.InitialSeparation.plusL σ U w‖ ≤
        ∑' I : A.Exterior, ‖ExteriorIdealEuler.summand
          (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U) w I‖ := by
      rw [AllRowEuler.InitialSeparation.plusL, InitialSeparatedEuler.dirichletSeries]
      exact norm_tsum_le_tsum_norm hsum
    have hle2 : (∑' I : A.Exterior, ‖ExteriorIdealEuler.summand
          (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U) w I‖) ≤
        ∑' I : A.Exterior, (idealNorm I.val) ^ (-a) := by
      refine Summable.tsum_le_tsum (fun I => ?_) hsum hbase
      refine (ExteriorIdealEuler.norm_summand_le _ hcoeff w I).trans ?_
      exact Real.rpow_le_rpow_of_exponent_le (idealNorm_ge_one I.val I.property.1)
        (by rw [neg_le_neg_iff]; exact hw)
    calc
      ‖AllRowEuler.InitialSeparation.plusL σ U w‖ ≤
          ∑' I : A.Exterior, ‖ExteriorIdealEuler.summand
            (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U) w I‖ := hle1
      _ ≤ ∑' I : A.Exterior, (idealNorm I.val) ^ (-a) := hle2
      _ ≤ (∑' I : A.Exterior, (idealNorm I.val) ^ (-a)) + 1 := by linarith

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.FarEulerBounds

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.FarEulerBounds
noncomputable section
open scoped Classical NumberField

set_option maxHeartbeats 1000000

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_far_quotient_regularity
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus minus : Frequency R → ℂ → ℂ)
    (hplus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re})
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (hLcont : ContinuousOn (fun z : ℂ => R.L (6 * z)) {z : ℂ | 2 / 5 < z.re})
    (hLdiff : DifferentiableOn ℂ (fun z : ℂ => R.L (6 * z)) {z : ℂ | 2 / 5 < z.re})
    (hCorrectionCont : ∀ u : Frequency R,
      ContinuousOn (fun x : CorrectionFactors.Coordinates =>
        AllRowEuler.InitialSeparation.correctionProduct C (U u) x.1 x.2.1 x.2.2)
        CorrectionFactors.Omega)
    (hCorrectionDiff : ∀ (u : Frequency R) (ξ w : ℂ),
      DifferentiableOn ℂ
        (fun z : ℂ => AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z)
        {z : ℂ | (ξ, w, z) ∈ CorrectionFactors.Omega}) :
    (∀ u : Frequency R, u ≠ principalFrequency R →
      ContinuousOn
        (fun p : ℝ × ℝ × ℂ => euler R C U plus minus u
          ((4 : ℂ) + (p.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (p.2.1 : ℂ) * Complex.I) p.2.2)
        {p : ℝ × ℝ × ℂ | 2 / 5 < p.2.2.re}) ∧
    (∀ (u : Frequency R) (tξ tw : ℝ), u ≠ principalFrequency R →
      DifferentiableOn ℂ
        (fun z : ℂ => euler R C U plus minus u ((4 : ℂ) + (tξ : ℂ) * Complex.I)
          ((4 : ℂ) + (tw : ℂ) * Complex.I) z)
        {z : ℂ | 2 / 5 < z.re}) := by
  constructor
  · intro u hu
    set s : Set (ℝ × ℝ × ℂ) := {p | (2 / 5 : ℝ) < p.2.2.re} with hs
    set g : ℝ × ℝ × ℂ → CorrectionFactors.Coordinates :=
      fun p => (((4 : ℂ) + (p.1 : ℂ) * Complex.I), ((4 : ℂ) + (p.2.1 : ℂ) * Complex.I), p.2.2)
      with hgdef
    have hg : ContinuousOn g s := by fun_prop
    have hgmap : Set.MapsTo g s CorrectionFactors.Omega := by
      intro p hp
      have hp' : (2 / 5 : ℝ) < p.2.2.re := by simpa only [hs, Set.mem_setOf_eq] using hp
      refine Or.inl ⟨?_, ?_, ?_⟩
      · simp only [hgdef, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
        norm_num
      · simp only [hgdef, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
        norm_num
      · simp only [hgdef]
        linarith
    have hξre : ∀ p : ℝ × ℝ × ℂ, (((4 : ℂ) + (p.1 : ℂ) * Complex.I)).re = 4 := by
      intro p; simp [Complex.add_re, Complex.mul_re]
    have hwre : ∀ p : ℝ × ℝ × ℂ, (((4 : ℂ) + (p.2.1 : ℂ) * Complex.I)).re = 4 := by
      intro p; simp [Complex.add_re, Complex.mul_re]
    have hLc : ContinuousOn (fun p : ℝ × ℝ × ℂ => R.L (6 * p.2.2)) s :=
      hLcont.comp' (by fun_prop) (fun p hp => hp)
    have hpc : ContinuousOn (fun p : ℝ × ℝ × ℂ => plus u ((4 : ℂ) + (p.2.1 : ℂ) * Complex.I)) s :=
      (hplus u hu).continuousOn.comp' (by fun_prop)
        (fun p _ => by rw [Set.mem_setOf_eq, hwre p]; norm_num)
    have hcc : ContinuousOn
        (fun p : ℝ × ℝ × ℂ =>
          AllRowEuler.InitialSeparation.correctionProduct C (U u)
            (g p).1 (g p).2.1 (g p).2.2) s :=
      (hCorrectionCont u).comp' hg hgmap
    have hnumc := (hLc.mul hpc).mul hcc
    have hdenc : ContinuousOn (fun p : ℝ × ℝ × ℂ => minus u ((4 : ℂ) + (p.1 : ℂ) * Complex.I)) s :=
      (hminus u hu).continuousOn.comp' (by fun_prop)
        (fun p _ => by rw [Set.mem_setOf_eq, hξre p]; norm_num)
    have hdenne : ∀ p ∈ s, minus u ((4 : ℂ) + (p.1 : ℂ) * Complex.I) ≠ 0 := by
      intro p hp
      rw [hminusSeries u ((4 : ℂ) + (p.1 : ℂ) * Complex.I) (by rw [hξre p]; norm_num)]
      exact AllRowEuler.InitialSeparation.raw_minusL_ne_zero (U u) _ (by rw [hξre p]; norm_num)
    simpa only [euler, numerator, hgdef, Pi.mul_def, Pi.div_def] using
      hnumc.div hdenc hdenne
  · intro u tξ tw hu
    set s : Set ℂ := {z | (2 / 5 : ℝ) < z.re} with hs
    set ξ : ℂ := (4 : ℂ) + (tξ : ℂ) * Complex.I with hξdef
    set w : ℂ := (4 : ℂ) + (tw : ℂ) * Complex.I with hwdef
    have hξre : ξ.re = 4 := by rw [hξdef]; simp [Complex.add_re, Complex.mul_re]
    have hwre : w.re = 4 := by rw [hwdef]; simp [Complex.add_re, Complex.mul_re]
    have hcorr : DifferentiableOn ℂ
        (fun z : ℂ => AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z) s :=
      (hCorrectionDiff u ξ w).mono
        (fun z hz => by
          have hz' : (2 / 5 : ℝ) < z.re := by simpa only [hs, Set.mem_setOf_eq] using hz
          refine Or.inl ⟨?_, ?_, ?_⟩
          · rw [hξre]; norm_num
          · rw [hwre]; norm_num
          · linarith)
    have hprod : DifferentiableOn ℂ
        (fun z : ℂ => R.L (6 * z) * plus u w *
          AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z) s :=
      (hLdiff.mul (differentiableOn_const _)).mul hcorr
    simpa [euler, numerator, hξdef, hwdef] using hprod.div_const (minus u ξ)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.FarEulerBounds

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.FarEulerBounds
noncomputable section
open scoped Classical NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_far_quotient_subpower_bound
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus minus : Frequency R → ℂ → ℂ)
    (hNorm : ∀ u : Frequency R, R.A.exteriorNorm (U u).ideal = frequencyNorm R u)
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (hLBound : ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 12 ≤ s.re → ‖R.L s‖ ≤ B)
    (hplusBound : ∃ B : ℝ, 0 < B ∧
      ∀ (V : AllRowEuler.InitialSeparation.RawFrequency R.A) (w : ℂ), w.re = 4 →
        ‖AllRowEuler.InitialSeparation.plusL R.σ V w‖ ≤ B)
    (hminusInvBound : ∃ B : ℝ, 0 < B ∧
      ∀ (V : AllRowEuler.InitialSeparation.RawFrequency R.A) (ξ : ℂ), ξ.re = 4 →
        ‖(AllRowEuler.InitialSeparation.minusL R.σ R.target V ξ)⁻¹‖ ≤ B)
    (hCorrectionBound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ (V : AllRowEuler.InitialSeparation.RawFrequency R.A)
        (x : CorrectionFactors.Coordinates), x ∈ CorrectionFactors.Omega →
        ‖AllRowEuler.InitialSeparation.correctionProduct C V x.1 x.2.1 x.2.2‖ ≤
          B * (R.A.exteriorNorm V.ideal) ^ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ (u : Frequency R) (tξ tw : ℝ) (z : ℂ), 2 ≤ z.re →
        ‖euler R C U plus minus u ((4 : ℂ) + (tξ : ℂ) * Complex.I)
          ((4 : ℂ) + (tw : ℂ) * Complex.I) z‖ ≤ B * (frequencyNorm R u) ^ ε := by
  intro ε hε
  obtain ⟨BL, hBLpos, hBL⟩ := hLBound
  obtain ⟨Bp, hBppos, hBp⟩ := hplusBound
  obtain ⟨Bm, hBmpos, hBm⟩ := hminusInvBound
  obtain ⟨Bc, hBcpos, hBc⟩ := hCorrectionBound ε hε
  refine ⟨BL * Bp * Bc * Bm, by positivity, ?_⟩
  intro u tξ tw z hz
  set ξ : ℂ := (4 : ℂ) + (tξ : ℂ) * Complex.I with hξdef
  set w : ℂ := (4 : ℂ) + (tw : ℂ) * Complex.I with hwdef
  have hξre : ξ.re = 4 := by simp [hξdef]
  have hwre : w.re = 4 := by simp [hwdef]
  have hzre : 12 ≤ (6 * z).re := by
    have h6 : (6 * z).re = 6 * z.re := by
      rw [Complex.mul_re]; simp
    rw [h6]; linarith
  have hξ1 : 1 < ξ.re := by rw [hξre]; norm_num
  have hw1 : 1 < w.re := by rw [hwre]; norm_num
  have hL : ‖R.L (6 * z)‖ ≤ BL := hBL (6 * z) hzre
  have hp : ‖plus u w‖ ≤ Bp := by
    rw [hplusSeries u w hw1]; exact hBp (U u) w hwre
  have hm : ‖(minus u ξ)⁻¹‖ ≤ Bm := by
    rw [hminusSeries u ξ hξ1]; exact hBm (U u) ξ hξre
  have hx : (ξ, w, z) ∈ CorrectionFactors.Omega := by
    refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [hξre]; norm_num
    · rw [hwre]; norm_num
    · linarith
  have hc : ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖ ≤
      Bc * (frequencyNorm R u) ^ ε := by
    have h := hBc (U u) (ξ, w, z) hx
    simpa [hNorm u] using h
  have hprod : ‖R.L (6 * z)‖ * ‖plus u w‖ * ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖
      ≤ BL * Bp * (Bc * (frequencyNorm R u) ^ ε) := by
    have h1 : ‖R.L (6 * z)‖ * ‖plus u w‖ ≤ BL * Bp :=
      mul_le_mul hL hp (norm_nonneg _) hBLpos.le
    have h2 : BL * Bp * ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖
        ≤ BL * Bp * (Bc * (frequencyNorm R u) ^ ε) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    calc ‖R.L (6 * z)‖ * ‖plus u w‖ *
          ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖
        ≤ BL * Bp * ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ BL * Bp * (Bc * (frequencyNorm R u) ^ ε) := h2
  have hnum : ‖numerator R C U plus u ξ w z‖ ≤ BL * Bp * (Bc * (frequencyNorm R u) ^ ε) := by
    rw [numerator]
    calc ‖R.L (6 * z) * plus u w *
          AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖
        = ‖R.L (6 * z)‖ * ‖plus u w‖ *
          ‖AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ BL * Bp * (Bc * (frequencyNorm R u) ^ ε) := hprod
  rw [euler]
  calc ‖numerator R C U plus u ξ w z / minus u ξ‖
      = ‖numerator R C U plus u ξ w z‖ * ‖(minus u ξ)⁻¹‖ := by
        rw [norm_div, norm_inv, div_eq_mul_inv]
    _ ≤ (BL * Bp * (Bc * (frequencyNorm R u) ^ ε)) * Bm :=
        mul_le_mul hnum hm (norm_nonneg _)
          (mul_nonneg (mul_nonneg hBLpos.le hBppos.le)
            (mul_nonneg hBcpos.le (Real.rpow_nonneg (Nat.cast_nonneg _) ε)))
    _ = (BL * Bp * Bc * Bm) * (frequencyNorm R u) ^ ε := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.FarEulerBounds

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical NumberField
open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]

section Raw

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem raw_good_cofinite (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    ∀ᶠ p : ExteriorPrime A in Filter.cofinite, (U.j p).val = 0 := by
  apply Filter.eventually_cofinite.mpr
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective
  simpa [AllRowEuler.InitialSeparation.RawFrequency.j, idealPrimeExponent,
    Multiset.count_eq_zero] using
    (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).finite_toSet.preimage
      hinj.injOn

private theorem raw_good_unit (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (p : ExteriorPrime A)
    (hp : (U.j p).val = 0) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
  have hs := AllRowEuler.InitialSeparation.RawFrequency.unitPart_spec C U p
  rw [hs.1, hp, pow_zero, one_mul]
  exact hs.2

private theorem raw_correction_majorant_summable (M : ℝ) :
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

private theorem raw_localCorrection_differentiableOn
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (p : ExteriorPrime A) :
    DifferentiableOn ℂ
      (fun x : CorrectionFactors.Coordinates =>
        AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2)
      CorrectionFactors.Omega := by
  by_cases hj : (U.j p).val = 0
  · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) :=
      raw_good_unit C U p hj
    simpa only [AllRowEuler.InitialSeparation.localCorrection, if_pos hj] using
      CorrectionFactors.good_correction_holomorphic C p U.u hu
  · simpa only [AllRowEuler.InitialSeparation.localCorrection, if_neg hj] using
      CorrectionFactors.bad_factor_holomorphic C p (U.j p) hj
        (AllRowEuler.InitialSeparation.RawFrequency.theta C U p)

private theorem raw_correctionProduct_uniformlyOn
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (K : Set CorrectionFactors.Coordinates) (hK : IsCompact K)
    (hKO : K ⊆ CorrectionFactors.Omega) :
    HasProdUniformlyOn
      (fun (p : ExteriorPrime A) (x : CorrectionFactors.Coordinates) =>
        AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2)
      (fun x : CorrectionFactors.Coordinates =>
        ∏' p : ExteriorPrime A,
          AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2) K := by
  obtain ⟨M, hM, hbound⟩ := CorrectionFactors.good_correction_uniform_bound
  have hb : ∀ᶠ p : ExteriorPrime A in Filter.cofinite, ∀ x ∈ K,
      ‖AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2 - 1‖ ≤
        M * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) := by
    filter_upwards [raw_good_cofinite U] with p hp
    intro x hx
    simpa [AllRowEuler.InitialSeparation.localCorrection, hp] using
      hbound F A σ η hS C p U.u (raw_good_unit C U p hp) x (hKO hx)
  have hcts : ∀ p : ExteriorPrime A,
      ContinuousOn (fun x : CorrectionFactors.Coordinates =>
        AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2 - 1) K := by
    intro p
    exact ((raw_localCorrection_differentiableOn C U p).continuousOn.mono hKO).sub
      continuousOn_const
  simpa only [add_sub_cancel] using
    (raw_correction_majorant_summable (A := A) M).hasProdUniformlyOn_one_add hK hb hcts

private theorem raw_correctionProduct_locallyUniformlyOn
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    HasProdLocallyUniformlyOn
      (fun (p : ExteriorPrime A) (x : CorrectionFactors.Coordinates) =>
        AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2)
      (fun x : CorrectionFactors.Coordinates =>
        ∏' p : ExteriorPrime A,
          AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2)
      CorrectionFactors.Omega :=
  hasProdLocallyUniformlyOn_of_forall_compact CorrectionFactors.isOpen_Omega
    (fun K hKO hK => raw_correctionProduct_uniformlyOn C U K hK hKO)

private theorem raw_correctionProduct_continuousOn
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    ContinuousOn
      (fun x : CorrectionFactors.Coordinates =>
        ∏' p : ExteriorPrime A,
          AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2)
      CorrectionFactors.Omega := by
  apply (raw_correctionProduct_locallyUniformlyOn C U).continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro s
  exact continuousOn_finsetProd s fun p _ =>
    (raw_localCorrection_differentiableOn C U p).continuousOn

private theorem raw_correctionProduct_slice_differentiableOn
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (e : ℂ → CorrectionFactors.Coordinates) (he : Differentiable ℂ e) :
    DifferentiableOn ℂ
      (fun t : ℂ => ∏' p : ExteriorPrime A,
        AllRowEuler.InitialSeparation.localCorrection C U p (e t).1 (e t).2.1 (e t).2.2)
      (e ⁻¹' CorrectionFactors.Omega) := by
  have hlim := (raw_correctionProduct_locallyUniformlyOn C U).comp e
    (fun _ ht => ht) he.continuous.continuousOn
  apply hlim.differentiableOn
  · apply Filter.Eventually.of_forall
    intro s
    simpa only [Finset.prod_fn, Function.comp_apply] using
      (DifferentiableOn.finset_prod (u := s) fun p _ =>
        (raw_localCorrection_differentiableOn C U p).comp he.differentiableOn (fun _ ht => ht))
  · exact CorrectionFactors.isOpen_Omega.preimage he.continuous

private theorem raw_correctionProduct_differentiableOn_z
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (ξ w : ℂ) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∏' p : ExteriorPrime A,
        AllRowEuler.InitialSeparation.localCorrection C U p ξ w z)
      {z : ℂ | (ξ, w, z) ∈ CorrectionFactors.Omega} :=
  raw_correctionProduct_slice_differentiableOn C U (fun z => (ξ, w, z))
    ((differentiable_const ξ).prodMk ((differentiable_const w).prodMk differentiable_id))

private theorem raw_correctionProduct_uniform_subpower_bound
    (C : A.GeneralArithmeticContext σ η hS) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (U : AllRowEuler.InitialSeparation.RawFrequency A)
        (x : CorrectionFactors.Coordinates) (hx : x ∈ CorrectionFactors.Omega),
        ‖AllRowEuler.InitialSeparation.correctionProduct C U x.1 x.2.1 x.2.2‖ ≤
          Cε * (A.exteriorNorm U.ideal) ^ ε := by
  classical
  obtain ⟨M, hM, hg⟩ := CorrectionFactors.good_correction_uniform_bound
  obtain ⟨B, hB, hb⟩ := CorrectionFactors.bad_factor_uniform_estimate C
  obtain ⟨K, hK, hsmall⟩ := fixed_small_prime_subpower F A.cS B (1 / 4000) ε
    hB.le (by norm_num) hε
  let g : ExteriorPrime A → ℝ := fun p => M * (Q p) ^ (-(1 + 1 / 4000 : ℝ))
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg hM.le (Real.rpow_nonneg (by
      simp [Q, SArithmeticData.exteriorNorm, idealNorm]) _)
  have hgs : Summable g := by
    let e : ExteriorPrime A → NonzeroIdeal F :=
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
  have hloc : ∀ p : ExteriorPrime A,
      ‖AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2‖ ≤
        Real.exp (g p) * (if (U.j p).val = 0 then 1 else
          1 + B * (Q p) ^ (-(1 / 4000 : ℝ))) := by
    intro p
    have hn (a : ℂ) : ‖a‖ ≤ ‖a - 1‖ + 1 := by
      simpa [norm_sub_rev, add_comm] using norm_le_insert 1 a
    by_cases hj : (U.j p).val = 0
    · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) :=
        raw_good_unit C U p hj
      simp only [AllRowEuler.InitialSeparation.localCorrection, hj, if_true, mul_one]
      exact (hn _).trans ((add_le_add_left
        (hg F A σ η hS C p U.u hu x hx) 1).trans (by
          simpa [g, add_comm] using Real.add_one_le_exp (g p)))
    · simp only [AllRowEuler.InitialSeparation.localCorrection, hj, if_false]
      have hm := (hn _).trans (add_le_add_left
        (hb p (U.j p) hj (AllRowEuler.InitialSeparation.RawFrequency.theta C U p) x hx) 1)
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
        1 + B * (Q p) ^ (-(1 / 4000 : ℝ))) ≤
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
          1 + B * (Q p) ^ (-(1 / 4000 : ℝ))) :=
        Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => hloc p)
      _ = Real.exp (∑ p ∈ s, g p) * (∏ p ∈ s, if (U.j p).val = 0 then 1 else
          1 + B * (Q p) ^ (-(1 / 4000 : ℝ))) := by
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
  rw [AllRowEuler.InitialSeparation.correctionProduct]
  apply le_of_tendsto' (AllRowEuler.InitialSeparation.raw_correction_multipliable C U x hx).hasProd.norm
  intro s
  simpa only [norm_prod] using hfinite s

end Raw

section Actual

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem raw_generator_quotient_norm (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) :
    (FiniteTransform.exteriorNorm R.A.R.toSubring U.u : ℝ) = R.A.exteriorNorm U.ideal := by
  change (Nat.card (R.A.R ⧸ Ideal.span {U.u}) : ℝ) = _
  rw [U.generates.2, R.A.exteriorResidue_card]
  rfl

private theorem raw_minusL_inv_bound (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) (ξ : ℂ) (hξ : ξ.re = 4) :
    ‖(AllRowEuler.InitialSeparation.minusL R.σ R.target U ξ)⁻¹‖ ≤
      Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-(4 : ℝ))) := by
  have hlog : Complex.exp (HeckeLogProof.eulerLog
        (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U) ξ) =
      AllRowEuler.InitialSeparation.minusL R.σ R.target U ξ := by
    rw [HeckeLogProof.exp_eulerLog
      (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U)
      (AllRowEuler.InitialSeparation.raw_minus_isCoefficient (σ := R.σ) U) ξ
      (by rw [hξ]; norm_num)]
    rfl
  rw [← hlog, ← Complex.exp_neg, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h := HeckeLogProof.eulerLog_norm_le
    (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U)
    (AllRowEuler.InitialSeparation.raw_minus_isCoefficient (σ := R.σ) U) 4 (by norm_num) ξ
    (by rw [hξ])
  rw [Complex.neg_re]
  exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h

private theorem actual_L_differentiableOn (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.L {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  apply R.continuation.L_holo.mul
  apply DifferentiableOn.fun_finset_prod
  intro v hv
  exact ((((differentiable_id.neg).mul_const
    (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
      (R.target v.asIdeal)).differentiableOn.const_sub 1

private theorem six_mul_mem (z : ℂ) (hz : 2 / 5 < z.re) :
    6 * z ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]; norm_num; linarith
  · intro h
    have h2 : (6 * z).re = 1 := by rw [h]; simp
    rw [Complex.mul_re] at h2; norm_num at h2
    linarith

private theorem actual_L_comp_continuousOn (R : PrincipalMellin.ActualRecipe S η) :
    ContinuousOn (fun z : ℂ => R.L (6 * z)) {z : ℂ | 2 / 5 < z.re} :=
  (actual_L_differentiableOn R).continuousOn.comp (by fun_prop) six_mul_mem

private theorem actual_L_comp_differentiableOn (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ (fun z : ℂ => R.L (6 * z)) {z : ℂ | 2 / 5 < z.re} :=
  (actual_L_differentiableOn R).comp (by fun_prop) six_mul_mem

variable (R : PrincipalMellin.ActualRecipe S η)
  (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
  (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
  (plus minus : Frequency R → ℂ → ℂ)

theorem actual_far_euler_inputs
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
    (∀ u : Frequency R, u ≠ principalFrequency R →
      ContinuousOn
        (fun p : ℝ × ℝ × ℂ => euler R C U plus minus u
          ((4 : ℂ) + (p.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (p.2.1 : ℂ) * Complex.I) p.2.2)
        {p : ℝ × ℝ × ℂ | 2 / 5 < p.2.2.re}) ∧
    (∀ (u : Frequency R) (tξ tw : ℝ), u ≠ principalFrequency R →
      DifferentiableOn ℂ
        (fun z : ℂ => euler R C U plus minus u ((4 : ℂ) + (tξ : ℂ) * Complex.I)
          ((4 : ℂ) + (tw : ℂ) * Complex.I) z)
        {z : ℂ | 2 / 5 < z.re}) ∧
    (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ (u : Frequency R) (tξ tw : ℝ) (z : ℂ), u ≠ principalFrequency R →
        1 ≤ frequencyNorm R u → z.re ∈ Set.Icc 2 comparisonR₀ →
        ‖euler R C U plus minus u ((4 : ℂ) + (tξ : ℂ) * Complex.I)
          ((4 : ℂ) + (tw : ℂ) * Complex.I) z‖ ≤ A * (frequencyNorm R u) ^ ε) := by
  obtain ⟨hcont, hdiff⟩ := FarEulerBounds.actual_far_quotient_regularity
    R C U plus minus hplus hminus hminusSeries
    (actual_L_comp_continuousOn R) (actual_L_comp_differentiableOn R)
    (fun u => raw_correctionProduct_continuousOn C (U u))
    (fun u ξ w => raw_correctionProduct_differentiableOn_z C (U u) ξ w)
  refine ⟨hcont, hdiff, ?_⟩
  have hNorm : ∀ u : Frequency R,
      R.A.exteriorNorm (U u).ideal = frequencyNorm R u := by
    intro u
    rw [← raw_generator_quotient_norm R (U u), hU u]
    rfl
  obtain ⟨Bplus, hBplus, hplusBound⟩ :=
    FarEulerBounds.raw_plus_rightHalfPlane_bound R.A R.σ 4 (by norm_num)
  have hbound := FarEulerBounds.actual_far_quotient_subpower_bound
    R C U plus minus hNorm hplusSeries hminusSeries
    (PrincipalNumerator.rightHalfPlane_bound R 12 (by norm_num))
    ⟨Bplus, hBplus, fun V w hw => hplusBound V w (by rw [hw])⟩
    ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F,
        (idealNorm I.val) ^ (-(4 : ℝ))), Real.exp_pos _, raw_minusL_inv_bound R⟩
    (raw_correctionProduct_uniform_subpower_bound C)
  intro ε hε
  obtain ⟨B, hB, hBbound⟩ := hbound ε hε
  refine ⟨B, hB, ?_⟩
  intro u tξ tw z hu hq hz
  exact hBbound u tξ tw z hz.1

end Actual

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
