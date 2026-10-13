module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.MaskedIdentification
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.DenominatorIdentification
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConductorNormalization

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawPrimitiveGrowth31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem euler_bound (σ0 : ℝ) (hσ0 : 1 < σ0) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : Ideal (𝓞 F)) (_ : m ≠ ⊥) (ω : RayClassCharacter F m) (s : ℂ),
      σ0 ≤ s.re → ‖Detector.idealLSeries F ω s‖ ≤ B := by
  obtain ⟨hsum, hnn, hpos, -⟩ := idealAbsoluteSum_converges F σ0 hσ0
  refine ⟨idealAbsoluteSum F σ0, hpos, fun m hm ω s hs => ?_⟩
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ0 hs
  obtain ⟨hsum', hnn', -, -⟩ := idealAbsoluteSum_converges F s.re hs1
  have hterm : ∀ I : Ideal (𝓞 F),
      ‖(if I ≠ ⊥ then ω I * (Ideal.absNorm I : ℂ) ^ (-s) else 0)‖ ≤ idealAbsoluteWeight F σ0 I := by
    intro I
    by_cases hI : I = ⊥
    · simp [hI, idealAbsoluteWeight]
    · simp only [hI, ne_eq, not_false_eq_true, if_true, norm_mul, idealAbsoluteWeight]
      have hN : 0 < (Ideal.absNorm I : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hI)
      have hN1 : (1 : ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hI)
      have h1 := AbelianQuotient.rayCharacter_norm_le_one F m hm ω I
      have h2 : ‖(Ideal.absNorm I : ℂ) ^ (-s)‖ = (Ideal.absNorm I : ℝ) ^ (-s.re) := by
        rw [show ((Ideal.absNorm I : ℕ) : ℂ) = (((Ideal.absNorm I : ℕ) : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos hN]
        simp
      rw [h2]
      refine le_trans (b := (Ideal.absNorm I : ℝ) ^ (-σ0)) ?_ (by simp)
      calc ‖ω I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re) ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (Ideal.absNorm I : ℝ) ^ (-σ0) := by
            rw [one_mul]
            exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  unfold Detector.idealLSeries
  calc ‖∑' I : Ideal (𝓞 F), (if I ≠ ⊥ then ω I * (Ideal.absNorm I : ℂ) ^ (-s) else 0)‖
      ≤ ∑' I : Ideal (𝓞 F),
          ‖(if I ≠ ⊥ then ω I * (Ideal.absNorm I : ℂ) ^ (-s) else 0)‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum)
    _ ≤ idealAbsoluteSum F σ0 :=
        Summable.tsum_le_tsum hterm
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum) hsum

def heckeData (hF : NumberField.IsTotallyComplex F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) : NonprincipalRayHeckeData F ν.conductor ν.character :=
  nonprincipalRayHeckeData F hF ν.conductor ν.conductor_ne_zero ν.character ν.primitive hν

theorem heckeData_eq (hF : NumberField.IsTotallyComplex F)
    (ν : Detector.PrimitiveFrequencyCharacter F) (hν : ¬ ν.character.IsPrincipal)
    (s : ℂ) (hs : 1 < s.re) :
    (heckeData hF ν hν).L s = Detector.idealLSeries F ν.character s := by
  rw [← ((heckeData hF ν hν).series s hs).tsum_eq]
  unfold Detector.idealLSeries
  refine tsum_congr fun I => ?_
  by_cases h : I = ⊥
  · subst h
    simp [(ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  · simp [h]

theorem entire_eq_continuation (hF : NumberField.IsTotallyComplex F)
    (ν : Detector.PrimitiveFrequencyCharacter F) (hν : ¬ ν.character.IsPrincipal)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) :
    g = nonprincipalHeckeEntireContinuation F ν.conductor ν.character (heckeData hF ν hν) := by
  refine RowHeckeBridge.entire_eq_of_eq_right hg
    (nonprincipalHeckeEntireContinuation_differentiable F hF ν.conductor ν.conductor_ne_zero
      ν.character (heckeData hF ν hν)) fun s hs => ?_
  rw [h s hs, nonprincipalHeckeEntireContinuation_eq F hF ν.conductor ν.conductor_ne_zero
    ν.character (heckeData hF ν hν) s (by linarith), heckeData_eq hF ν hν s hs]

theorem convex_core (hF : NumberField.IsTotallyComplex F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 10 → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (g : ℂ → ℂ), Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ s : ℂ, -d ≤ s.re → s.re ≤ 1 + d →
          ‖g s‖ ≤ C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + d - s.re) / 2) *
            (2 + |s.im|) ^ A := by
  obtain ⟨A, hA, H⟩ := DedekindZetaZeroFree.Quantitative.convex_normalized F hF
  refine ⟨A, hA, fun d hd hd1 => ?_⟩
  obtain ⟨C, hC, HC⟩ := H d hd hd1
  refine ⟨C, hC, fun ν hν g hg h s h1 h2 => ?_⟩
  have hge := entire_eq_continuation hF ν hν hg h
  rw [hge]
  exact HC ν.conductor ν.conductor_ne_zero ν.character ν.primitive hν (heckeData hF ν hν) s h1 h2

theorem rpow_scale {Q U c e : ℝ} (hc : 0 < c) (hU : 1 ≤ U) (hQ1 : 1 ≤ Q) (hQ : Q ≤ c * U)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : Q ^ e ≤ max 1 c * U ^ e := by
  have hU0 : 0 < U := by linarith
  have hQ0 : 0 < Q := by linarith
  have h1 : Q ^ e ≤ (c * U) ^ e := Real.rpow_le_rpow hQ0.le hQ he0
  rw [Real.mul_rpow hc.le hU0.le] at h1
  have h2 : c ^ e ≤ max 1 c := by
    calc c ^ e ≤ (max 1 c) ^ e := Real.rpow_le_rpow hc.le (le_max_right _ _) he0
      _ ≤ (max 1 c) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) he1
      _ = max 1 c := Real.rpow_one _
  calc Q ^ e ≤ c ^ e * U ^ e := h1
    _ ≤ max 1 c * U ^ e := mul_le_mul_of_nonneg_right h2 (by positivity)

theorem primitive_growth (hF : NumberField.IsTotallyComplex F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (U : ℝ), 1 ≤ U → 1 + (Ideal.absNorm ν.conductor : ℝ) ≤ c * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∀ t : ℝ,
          ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A := by
  obtain ⟨A, hA, H⟩ := convex_core hF
  refine ⟨A, hA, fun ε hε c hc => ?_⟩
  have hd : 0 < min ε (1 / 10) := lt_min hε (by norm_num)
  have hd1 : min ε (1 / 10) ≤ 1 / 10 := min_le_right _ _
  have hdε : min ε (1 / 10) ≤ ε := min_le_left _ _
  obtain ⟨C0, hC0, HC⟩ := H (min ε (1 / 10)) hd hd1
  refine ⟨C0 * max 1 c, by positivity, fun ν hν U hU hNU g hg h σ h0 h1 t => ?_⟩
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have key := HC ν hν g hg h ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; linarith)
    (by rw [hre]; linarith)
  rw [hre, him] at key
  have hQ1 : (1 : ℝ) ≤ 1 + (Ideal.absNorm ν.conductor : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ν.conductor)
    linarith
  have hQe := rpow_scale hc hU hQ1 hNU
    (e := (1 + min ε (1 / 10) - σ) / 2) (by linarith) (by linarith)
  have hUe : U ^ ((1 + min ε (1 / 10) - σ) / 2) ≤ U ^ ((1 - σ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hX : 0 ≤ (2 + |t|) ^ A := by positivity
  calc ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + min ε (1 / 10) - σ) / 2) *
          (2 + |t|) ^ A := key
    _ ≤ C0 * (max 1 c * U ^ ((1 - σ) / 2 + ε)) * (2 + |t|) ^ A := by
        have h3 : (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + min ε (1 / 10) - σ) / 2) ≤
            max 1 c * U ^ ((1 - σ) / 2 + ε) :=
          hQe.trans (mul_le_mul_of_nonneg_left hUe (by positivity))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0.le) hX
    _ = C0 * max 1 c * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A := by ring

theorem primitive_strip_growth (hF : NumberField.IsTotallyComplex F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (U : ℝ), 1 ≤ U → 1 + (Ideal.absNorm ν.conductor : ℝ) ≤ c * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 4 → ∀ t : ℝ,
          ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A := by
  obtain ⟨A, hA, H⟩ := convex_core hF
  refine ⟨A, hA, fun ε hε c hc => ?_⟩
  have hd : 0 < min ε (1 / 10) := lt_min hε (by norm_num)
  have hd1 : min ε (1 / 10) ≤ 1 / 10 := min_le_right _ _
  have hdε : min ε (1 / 10) ≤ ε := min_le_left _ _
  obtain ⟨C0, hC0, HC⟩ := H (min ε (1 / 10)) hd hd1
  obtain ⟨B, hB, HB⟩ := euler_bound (F := F) (1 + min ε (1 / 10)) (by linarith)
  refine ⟨C0 * max 1 c + B, by positivity, fun ν hν U hU hNU g hg h σ h0 h1 t => ?_⟩
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hX : 0 ≤ (2 + |t|) ^ A := by positivity
  have hX1 : 1 ≤ (2 + |t|) ^ A :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) hA
  have hU1 : 1 ≤ U ^ ((1 : ℝ) / 10 + ε) := Real.one_le_rpow hU (by linarith)
  have hUX : 0 ≤ U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A := by positivity
  have hsplit : (C0 * max 1 c + B) * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A =
      C0 * max 1 c * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A +
        B * (U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A) := by ring
  by_cases hσ : σ ≤ 1 + min ε (1 / 10)
  · have key := HC ν hν g hg h ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; linarith)
      (by rw [hre]; exact hσ)
    rw [hre, him] at key
    have hQ1 : (1 : ℝ) ≤ 1 + (Ideal.absNorm ν.conductor : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ν.conductor)
      linarith
    have hQe := rpow_scale hc hU hQ1 hNU
      (e := (1 + min ε (1 / 10) - σ) / 2) (by linarith) (by linarith)
    have hUe : U ^ ((1 + min ε (1 / 10) - σ) / 2) ≤ U ^ ((1 : ℝ) / 10 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    have h3 : (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + min ε (1 / 10) - σ) / 2) ≤
        max 1 c * U ^ ((1 : ℝ) / 10 + ε) :=
      hQe.trans (mul_le_mul_of_nonneg_left hUe (by positivity))
    have h4 : C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + min ε (1 / 10) - σ) / 2) *
          (2 + |t|) ^ A ≤ C0 * max 1 c * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A := by
      calc _ ≤ C0 * (max 1 c * U ^ ((1 : ℝ) / 10 + ε)) * (2 + |t|) ^ A :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0.le) hX
        _ = _ := by ring
    have h5 := mul_nonneg hB.le hUX
    linarith
  · push_neg at hσ
    have hgs : g ((σ : ℂ) + (t : ℂ) * Complex.I) =
        Detector.idealLSeries F ν.character ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      h _ (by rw [hre]; linarith [hd])
    have hE := HB ν.conductor ν.conductor_ne_zero ν.character
      ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact hσ.le)
    rw [← hgs] at hE
    have h5 : B ≤ B * (U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A) := by
      have := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hU1 hX1) hB.le
      simpa using this
    have h6 : 0 ≤ C0 * max 1 c * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A := by positivity
    linarith

theorem primitive_fixed_strip (hF : NumberField.IsTotallyComplex F) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal),
        ∃ C : ℝ, 0 < C ∧ ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ s : ℂ, -(1 / 10 : ℝ) ≤ s.re → ‖g s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨A, hA, H⟩ := convex_core hF
  obtain ⟨C0, hC0, HC⟩ := H (1 / 10) (by norm_num) le_rfl
  obtain ⟨B, hB, HB⟩ := euler_bound (F := F) (1 + 1 / 10) (by norm_num)
  refine ⟨A, hA, fun ν hν => ?_⟩
  have hQ1 : (1 : ℝ) ≤ 1 + (Ideal.absNorm ν.conductor : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm ν.conductor)
    linarith
  refine ⟨C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) + B, by positivity,
    fun g hg h s hs => ?_⟩
  have hX : 0 ≤ (2 + |s.im|) ^ A := by positivity
  have hX1 : 1 ≤ (2 + |s.im|) ^ A :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) hA
  have hsplit : (C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) + B) *
      (2 + |s.im|) ^ A = C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) *
        (2 + |s.im|) ^ A + B * (2 + |s.im|) ^ A := by ring
  have hQp : 0 < (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) := by positivity
  by_cases hσ : s.re ≤ 1 + 1 / 10
  · have key := HC ν hν g hg h s (by linarith) hσ
    have h3 : (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + 1 / 10 - s.re) / 2) ≤
        (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    have h4 : C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((1 + 1 / 10 - s.re) / 2) *
        (2 + |s.im|) ^ A ≤
        C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) * (2 + |s.im|) ^ A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0.le) hX
    have h5 := mul_nonneg hB.le hX
    linarith
  · push_neg at hσ
    have hgs : g s = Detector.idealLSeries F ν.character s := h s (by linarith)
    have hE := HB ν.conductor ν.conductor_ne_zero ν.character s hσ.le
    rw [← hgs] at hE
    have h5 : B ≤ B * (2 + |s.im|) ^ A := by
      have := mul_le_mul_of_nonneg_left hX1 hB.le
      simpa using this
    have h6 : 0 ≤ C0 * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((3 : ℝ) / 5) *
        (2 + |s.im|) ^ A := by positivity
    linarith

section Fixed

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

include D in
theorem totallyComplex : NumberField.IsTotallyComplex F :=
  primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12

theorem primPlus_growth :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 1 ≤ U → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primPlus D u).character s) →
          ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∀ t : ℝ,
            ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A := by
  obtain ⟨c, hc, hcond⟩ := RawHeckeIdentification31.plus_conductor_bound D
  obtain ⟨A, hA, H⟩ := primitive_growth (totallyComplex D)
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H ε hε (2 * c) (by positivity)
  refine ⟨C, hC, fun u hu U hU hq g hg h σ h0 h1 t => ?_⟩
  refine HC (RawFixed.FixedData.primPlus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
    U hU ?_ g hg h σ h0 h1 t
  have h2 := hcond u
  have h3 := mul_le_mul_of_nonneg_left hq.le hc.le
  linarith

theorem primMinus_growth :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 1 ≤ U → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character s) →
          ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∀ t : ℝ,
            ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A := by
  obtain ⟨c, hc, hcond⟩ := RawHeckeIdentification31.minus_conductor_bound D
  obtain ⟨A, hA, H⟩ := primitive_growth (totallyComplex D)
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H ε hε (1 + 2 * c) (by positivity)
  refine ⟨C, hC, fun u hu U hU hq g hg h σ h0 h1 t => ?_⟩
  refine HC (RawFixed.FixedData.primMinus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).2
    U hU ?_ g hg h σ h0 h1 t
  have h2 := hcond u
  have h3 := mul_le_mul_of_nonneg_left hq.le hc.le
  nlinarith

theorem primPlus_strip_growth :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 1 ≤ U → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primPlus D u).character s) →
          ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 4 → ∀ t : ℝ,
            ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A := by
  obtain ⟨c, hc, hcond⟩ := RawHeckeIdentification31.plus_conductor_bound D
  obtain ⟨A, hA, H⟩ := primitive_strip_growth (totallyComplex D)
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H ε hε (2 * c) (by positivity)
  refine ⟨C, hC, fun u hu U hU hq g hg h σ h0 h1 t => ?_⟩
  refine HC (RawFixed.FixedData.primPlus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
    U hU ?_ g hg h σ h0 h1 t
  have h2 := hcond u
  have h3 := mul_le_mul_of_nonneg_left hq.le hc.le
  linarith

theorem primMinus_strip_growth :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 1 ≤ U → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character s) →
          ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 4 → ∀ t : ℝ,
            ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A := by
  obtain ⟨c, hc, hcond⟩ := RawHeckeIdentification31.minus_conductor_bound D
  obtain ⟨A, hA, H⟩ := primitive_strip_growth (totallyComplex D)
  refine ⟨A, hA, fun ε hε => ?_⟩
  obtain ⟨C, hC, HC⟩ := H ε hε (1 + 2 * c) (by positivity)
  refine ⟨C, hC, fun u hu U hU hq g hg h σ h0 h1 t => ?_⟩
  refine HC (RawFixed.FixedData.primMinus D u) ((RawFixed.FixedData.pkg D).nonprincipal u hu).2
    U hU ?_ g hg h σ h0 h1 t
  have h2 := hcond u
  have h3 := mul_le_mul_of_nonneg_left hq.le hc.le
  nlinarith

theorem primPlus_fixed_strip (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ g : ℂ → ℂ, Differentiable ℂ g →
      (∀ s : ℂ, 1 < s.re →
        g s = Detector.idealLSeries F (RawFixed.FixedData.primPlus D u).character s) →
      ∀ s : ℂ, -(1 / 10 : ℝ) ≤ s.re → ‖g s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨A, hA, H⟩ := primitive_fixed_strip (totallyComplex D)
  obtain ⟨C, hC, HC⟩ := H (RawFixed.FixedData.primPlus D u)
    ((RawFixed.FixedData.pkg D).nonprincipal u hu).1
  exact ⟨A, C, hA, hC, HC⟩

theorem primMinus_fixed_strip (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ g : ℂ → ℂ, Differentiable ℂ g →
      (∀ s : ℂ, 1 < s.re →
        g s = Detector.idealLSeries F (RawFixed.FixedData.primMinus D u).character s) →
      ∀ s : ℂ, -(1 / 10 : ℝ) ≤ s.re → ‖g s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨A, hA, H⟩ := primitive_fixed_strip (totallyComplex D)
  obtain ⟨C, hC, HC⟩ := H (RawFixed.FixedData.primMinus D u)
    ((RawFixed.FixedData.pkg D).nonprincipal u hu).2
  exact ⟨A, C, hA, hC, HC⟩

end Fixed

end

end DedekindZetaZeroFree.Quantitative.RawPrimitiveGrowth31
