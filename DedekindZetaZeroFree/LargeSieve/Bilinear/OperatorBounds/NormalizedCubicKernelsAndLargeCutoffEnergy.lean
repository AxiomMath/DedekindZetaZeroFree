module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimePoissonExpansion
public import DedekindZetaZeroFree.LargeSieve.Exponents.BilinearErrorOptimization
public import DedekindZetaZeroFree.LargeSieve.Bilinear.MainTermBoundaryIdentity

@[expose] public section

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve.NormalizedKernelProfiles

def normalizedKernelRows (F : Type) [Field F] [NumberField F]
    (c bad : Ideal (𝓞 F)) (M K : ℝ) : Finset (Ideal (𝓞 F)) :=
  (kernelRows F c M K).filter (fun a => a ⊔ bad = ⊤)

def T3normalizedMasked (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (bad : Ideal (𝓞 F)) (W : ℝ → ℝ) (M N K : ℝ)
    (d : Ideal (𝓞 F)) (g : Q.G)
    (U : Finset (Ideal (𝓞 F))) (τ lam : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ u ∈ paperShell F c N, ∑ v ∈ paperShell F c N,
    if u ⊔ v = d ∧ Q.cls u = g ∧ Q.cls v = g then
      (if u ∈ U then τ u * lam u else 0) *
        (starRingEnd ℂ) (if v ∈ U then τ v * lam v else 0) *
        (∑ a ∈ normalizedKernelRows F c bad M K,
          (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
            (Q.χ u) a * (starRingEnd ℂ) ((Q.χ v) a))
    else 0

def B3normalizedMasked (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (bad : Ideal (𝓞 F)) (W : ℝ → ℝ) (M N K : ℝ)
    (d : Ideal (𝓞 F)) (U : Finset (Ideal (𝓞 F)))
    (τ : Ideal (𝓞 F) → ℂ) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
    energy F c N lam ≤ 1 ∧
      x = ‖T3normalizedMasked F c Q bad W M N K d g U τ lam‖})

end DedekindZetaZeroFree.LargeSieve.Sieve.NormalizedKernelProfiles

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

theorem canonical_operator_of_large_cutoff_energy
    {F : Type} [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (α ε A : ℝ) (hα₁ : 1 ≤ α) (hα₂ : α ≤ 2)
    (hε : 0 < ε) (hA : 0 ≤ A)
    (hlarge : ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ K →
      N ^ 2 / M * Real.rpow (M * N) ε ≤ K →
      K ≤ M * Real.rpow (M * N) (-ε) →
      ∀ d : Ideal (𝓞 F), d ≠ ⊥ → Squarefree d → d ⊔ c = ⊤ →
        (Ideal.absNorm d : ℝ) ≤ 2 * N →
        ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
          ‖T3 F c Q W M N K d g lam‖ ≤
            A * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) * energy F c N lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 0 < K →
        N ^ 2 / M * Real.rpow (M * N) ε ≤ K →
        K ≤ M * Real.rpow (M * N) (-ε) →
        ∀ d : Ideal (𝓞 F),
          B3 F c Q W M N K d ≤
            C * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) := by
  have hnonneg (B M N K : ℝ) (hB : 0 ≤ B) (hM : 1 ≤ M)
      (hN : 1 ≤ N) (hK : 0 < K) (d : Ideal (𝓞 F)) :
      0 ≤ B * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
        smallCutoffEnvelope α M N K := by
    unfold smallCutoffEnvelope
    have hM0 : 0 ≤ M := le_trans zero_le_one hM
    have hN0 : 0 ≤ N := le_trans zero_le_one hN
    have hp : 0 ≤ Real.rpow (M * N) ε := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
    have hpK : 0 ≤ Real.rpow K (α - 1 / 2) := Real.rpow_nonneg hK.le _
    positivity
  have hbig : ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ K →
      N ^ 2 / M * Real.rpow (M * N) ε ≤ K →
      K ≤ M * Real.rpow (M * N) (-ε) →
      ∀ d : Ideal (𝓞 F), B3 F c Q W M N K d ≤
        A * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
          smallCutoffEnvelope α M N K := by
    intro M N K hM hN hK hl hupp d
    have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
    have hnn := hnonneg A M N K hA hM hN hK0 d
    unfold B3
    apply csSup_le
    · exact ⟨0, Or.inl rfl⟩
    · intro x hx
      rcases hx with hx | ⟨g, lam, hlam, rfl⟩
      · simpa only [Set.mem_singleton_iff.mp hx] using hnn
      · by_cases hr : ∃ u ∈ paperShell F c N, ∃ v ∈ paperShell F c N,
            u ⊔ v = d
        · obtain ⟨u, hu', v, hv', huv⟩ := hr
          have hu := (mem_paperShell F c N u).mp hu'
          have hd0 : d ≠ ⊥ := by
            intro hd
            have : u = ⊥ := bot_unique (le_sup_left.trans (le_of_eq (huv.trans hd)))
            exact hu.1.ne_zero this
          have hdsf : Squarefree d := huv ▸
            hu.1.squarefree_of_dvd (Ideal.dvd_iff_le.mpr le_sup_left)
          have hdc : d ⊔ c = ⊤ := by
            rw [← huv]
            exact top_unique (hu.2.1 ▸ sup_le_sup_right le_sup_left c)
          have hnorm : Ideal.absNorm d ≤ Ideal.absNorm u :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
              hu.1.ne_zero)) (Ideal.absNorm_dvd_absNorm_of_le (huv ▸ le_sup_left))
          have hdN : (Ideal.absNorm d : ℝ) ≤ 2 * N := by
            have hnormR : (Ideal.absNorm d : ℝ) ≤ (Ideal.absNorm u : ℝ) := by
              exact_mod_cast hnorm
            exact hnormR.trans hu.2.2.2
          have ht := hlarge M N K hM hN hK hl hupp d hd0 hdsf hdc hdN g lam
          change ‖T3 F c Q W M N K d g lam‖ ≤
            A * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              smallCutoffEnvelope α M N K * energy F c N lam at ht
          exact ht.trans ((mul_le_mul_of_nonneg_left hlam hnn).trans_eq (mul_one _))
        · have ht : T3 F c Q W M N K d g lam = 0 := by
            unfold T3
            apply Finset.sum_eq_zero
            intro u hu
            apply Finset.sum_eq_zero
            intro v hv
            have hneq : u ⊔ v ≠ d := fun heq => hr ⟨u, hu, v, hv, heq⟩
            simp only [hneq, false_and, ↓reduceIte]
          simpa [ht] using hnn
  obtain ⟨C, hC, hsmall⟩ := smallCutoff_extend_bound F c Q W hW α ε A
    hα₁ hα₂ hε hA (fun M N hM hN hl hu d _ =>
      hbig M N 1 hM hN le_rfl hl hu d)
  refine ⟨max A C, le_trans hA (le_max_left _ _), ?_⟩
  intro M N K hM hN hK hl hu d
  change B3 F c Q W M N K d ≤
    max A C * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
      smallCutoffEnvelope α M N K
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hp : 0 ≤ Real.rpow (M * N) ε := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
  have hpK : 0 ≤ Real.rpow K (α - 1 / 2) := Real.rpow_nonneg hK.le _
  have henv : 0 ≤ smallCutoffEnvelope α M N K := by
    unfold smallCutoffEnvelope
    positivity
  by_cases hd : d = ⊥
  · subst d
    rw [smallCutoff_B3_bottom]
    exact hnonneg (max A C) M N K (le_trans hA (le_max_left _ _)) hM hN hK ⊥
  · by_cases hK1 : 1 ≤ K
    · exact (hbig M N K hM hN hK1 hl hu d).trans (by
        gcongr
        exact le_max_left A C)
    · exact (hsmall M N K hM hN hK (lt_of_not_ge hK1) hl hu d hd).trans (by
        gcongr
        exact le_max_right A C)

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

open DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

theorem assembly_tail_uniform_small_delta
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (D : AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (hδε : δ ≤ ε / 100) :
    ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
        1 ≤ C.M → 1 ≤ C.N →
        max 1 (C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε) ≤ C.K →
        C.K ≤ C.M * Real.rpow (C.M * C.N) (-ε) →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ‖totalRemainder C‖ ≤ A * energy F c C.N C.lam := by
  exact DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.uniform_remainder_small_delta
    D W ε hε δ hδ hδε

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical
open DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

 def errComb {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c} (C : Context Q) : ℂ :=
  (E1 C 1 true + E2 C 1 true - E3 C 1 true - E4 C 1 true + E5 C 1 true) +
    ∑ B ∈ dyadicScales C,
      (E1 C B + E2 C B - E3 C B - E4 C B + E5 C B)

private theorem norm_five_le (a b c d e : ℂ) :
    ‖a + b - c - d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have hA := norm_add_le (a + b - c - d) e
  have hB := norm_sub_le (a + b - c) d
  have hC := norm_sub_le (a + b) c
  have hD := norm_add_le a b
  linarith

private theorem sevenTermSum_eq_mainDifference_sub_errComb
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c} (C : Context Q) :
    sevenTermSum C = MainBoundary.mainDifference C - errComb C := by
  have hblock : ∀ (B : ℝ) (unit : Bool), sevenTermBlock C B unit =
      (T C B unit - Tprime C B unit) -
        (E1 C B unit + E2 C B unit - E3 C B unit - E4 C B unit + E5 C B unit) := by
    intro B unit; unfold sevenTermBlock; ring
  have hsum : (∑ B ∈ dyadicScales C, sevenTermBlock C B) =
      (∑ B ∈ dyadicScales C, (T C B - Tprime C B)) -
        (∑ B ∈ dyadicScales C,
          (E1 C B + E2 C B - E3 C B - E4 C B + E5 C B)) := by
    simp only [hblock]
    rw [Finset.sum_sub_distrib]
  simp only [sevenTermSum, unitBlock, MainBoundary.mainDifference, errComb]
  rw [hblock 1 true, hsum]
  ring

private theorem norm_errComb_le {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c} (C : Context Q) :
    ‖errComb C‖ ≤
      (‖E1 C 1 true‖ + ‖E2 C 1 true‖ + ‖E3 C 1 true‖ + ‖E4 C 1 true‖ +
        ‖E5 C 1 true‖) +
      ∑ B ∈ dyadicScales C,
        (‖E1 C B‖ + ‖E2 C B‖ + ‖E3 C B‖ + ‖E4 C B‖ + ‖E5 C B‖) := by
  simp only [errComb]
  refine le_trans (norm_add_le _ _) (add_le_add (norm_five_le _ _ _ _ _) ?_)
  calc ‖∑ B ∈ dyadicScales C, (E1 C B + E2 C B - E3 C B - E4 C B + E5 C B)‖
      ≤ ∑ B ∈ dyadicScales C,
          ‖E1 C B + E2 C B - E3 C B - E4 C B + E5 C B‖ := norm_sum_le _ _
    _ ≤ ∑ B ∈ dyadicScales C,
          (‖E1 C B‖ + ‖E2 C B‖ + ‖E3 C B‖ + ‖E4 C B‖ + ‖E5 C B‖) :=
        Finset.sum_le_sum (fun B _ => norm_five_le _ _ _ _ _)

private theorem norm_sevenTermSum_le {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) :
    ‖sevenTermSum C‖ ≤
      ‖MainBoundary.mainDifference C‖ +
      ((‖E1 C 1 true‖ + ‖E2 C 1 true‖ + ‖E3 C 1 true‖ + ‖E4 C 1 true‖ +
          ‖E5 C 1 true‖) +
        ∑ B ∈ dyadicScales C,
          (‖E1 C B‖ + ‖E2 C B‖ + ‖E3 C B‖ + ‖E4 C B‖ + ‖E5 C B‖)) := by
  rw [sevenTermSum_eq_mainDifference_sub_errComb C]
  exact le_trans (norm_sub_le _ _) (add_le_add le_rfl (norm_errComb_le C))

theorem large_cutoff_energy_bound
    {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : AllIndexNormalizedFamilyData Q) (hcore : D.bad = c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    {α : ℝ} (hα₁ : 1 ≤ α) (hα₂ : α ≤ 2)
    (hE : HasSieveExponent F c Q α) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ K →
        N ^ 2 / M * Real.rpow (M * N) ε ≤ K →
        K ≤ M * Real.rpow (M * N) (-ε) →
        ∀ d : Ideal (𝓞 F), d ≠ ⊥ → Squarefree d → d ⊔ c = ⊤ →
          (Ideal.absNorm d : ℝ) ≤ 2 * N →
          ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
            ‖T3 F c Q W M N K d g lam‖ ≤
              A * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
                (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                  Real.sqrt (M / K) * N) * energy F c N lam := by

  set ε' : ℝ := ε / 100 with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, A₁, hδpos, hδlt, hA₁, herr⟩ :=
    bilinear_error_optimization hF Q D hcore W hW hα₁ hα₂ hE ε' hε'
  have hδle : δ ≤ ε / 100 := by
    have hden : (1 : ℝ) ≤ 8 * (α + 1) := by nlinarith [hα₁]
    have h1 : ε' / (8 * (α + 1)) ≤ ε' := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hε'.le]
    have h2 : δ ≤ ε' := le_trans hδlt.le h1
    simpa only [hε'def] using h2
  obtain ⟨A₂, hA₂, hassem⟩ :=
    assembly_tail_uniform_small_delta D W ε hε δ hδpos hδle
  obtain ⟨A₃, hA₃, hdiag⟩ := bilinear_explicit_assembly_diagonal (F := F) (c := c) (Q := Q) W hW
  let κ : ℂ := DedekindZetaZeroFree.LargeSieve.SquareSecondPass.kappa (DedekindZetaZeroFree.LargeSieve.principalHeckeData F hF)
  obtain ⟨A₄, hA₄, hmain⟩ :=
    Sieve.MainBoundary.cancelledMainTerms_le_of_exponent Q D.toNormalizedFamilyData W hW κ
      α hα₁ hα₂ hE ε' hε'
  refine ⟨A₃ + (A₄ + A₁) + A₂, ?_, ?_⟩
  · linarith [hA₃, hA₄.le, hA₁, hA₂.le]
  · intro M N K hM hN hK hlower hupper d hd0 hd hdc hdn g lam
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
    have hMNpos : 0 < M * N := mul_pos hM0 hN0
    have hMN1 : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
    have he'le : ε' ≤ ε := by rw [hε'def]; linarith
    have hrpow_le : Real.rpow (M * N) ε' ≤ Real.rpow (M * N) ε :=
      Real.rpow_le_rpow_of_exponent_le hMN1 he'le
    have hrpow_neg_le : Real.rpow (M * N) (-ε) ≤ Real.rpow (M * N) (-ε') :=
      Real.rpow_le_rpow_of_exponent_le hMN1 (by linarith)
    have hneg1 : Real.rpow (M * N) (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hMN1 (by linarith)
    have hKM : K ≤ M := by
      calc K ≤ M * Real.rpow (M * N) (-ε) := hupper
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hneg1 (by linarith)
        _ = M := mul_one M
    have hnd1 : (1 : ℝ) ≤ (Ideal.absNorm d : ℝ) := by
      have h : Ideal.absNorm d ≠ 0 := fun h0 => hd0 (Ideal.absNorm_eq_zero_iff.mp h0)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

    let C : Context Q :=
      { D := D, core := hcore, hF := hF,
        M := M, N := N, K := K, δ := δ, W := W, hW := hW, d := d, hd0 := hd0,
        hd := hd, hdc := hdc, g := g, lam := lam }

    have hdiagC : ‖T3 F c Q W M N K d g lam -
        offDiagonalT3 Q W M N K d g lam‖ ≤ A₃ * M * energy F c N lam := by
      have h := hdiag C rfl hM hN hKpos
      simpa only [C] using h

    have hassemC : ‖totalRemainder C‖ ≤ A₂ * energy F c N lam := by
      have hmax : max 1 (C.N ^ 2 / C.M * Real.rpow (C.M * C.N) ε) ≤ C.K := by
        have h : max 1 (N ^ 2 / M * Real.rpow (M * N) ε) ≤ K := max_le hK hlower
        simpa only [C] using h
      have hupperC : C.K ≤ C.M * Real.rpow (C.M * C.N) (-ε) := by
        simpa only [C] using hupper
      have hnd1C : 1 ≤ DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.norm C.d := by
        simpa only [C, DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.norm] using hnd1
      have hnd2C : DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.norm C.d ≤ 2 * C.N := by
        simpa only [C, DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.norm] using hdn
      have h := hassem C rfl rfl rfl hM hN hmax hupperC hnd1C hnd2C
      simpa only [C] using h

    have herrC :
        (‖E1 C 1 true‖ + ‖E2 C 1 true‖ + ‖E3 C 1 true‖ + ‖E4 C 1 true‖ +
            ‖E5 C 1 true‖) +
          ∑ B ∈ dyadicScales C,
            (‖E1 C B‖ + ‖E2 C B‖ + ‖E3 C B‖ + ‖E4 C B‖ + ‖E5 C B‖) ≤
        A₁ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N) * energy F c N lam := by
      have hmaxE : max 1 (N ^ 2 / M * Real.rpow (M * N) ε') ≤ K := by
        refine max_le hK ?_
        exact le_trans (mul_le_mul_of_nonneg_left hrpow_le (by positivity)) hlower
      have hupE : K ≤ M * Real.rpow (M * N) (-ε') :=
        le_trans hupper (mul_le_mul_of_nonneg_left hrpow_neg_le (by linarith))
      have h := herr M N K hM hN hmaxE hupE d hd0 hd hdc hdn g lam
      simpa only [C] using h

    have hdc' : d ⊔ D.bad = ⊤ := by rw [hcore]; exact hdc
    have hmainC : ‖Sieve.MainBoundary.cancelledMainTerms Q D.bad W κ M N K d g lam‖ ≤
        A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
          (Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) *
          energy F c N lam :=
      hmain M N K hM hN hK hKM d hd hdc' hdn g lam
    have hmain' : ‖MainBoundary.mainDifference C‖ ≤
        A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
          (Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) *
          energy F c N lam := by
      rw [bilinear_main_boundary_identity C hM hN hK]
      have h := hmainC
      rw [hcore] at h
      exact h

    have hnd4nn : 0 ≤ (Ideal.absNorm d : ℝ) ^ 4 := by positivity
    have hrpowεnn : 0 ≤ Real.rpow (M * N) ε := Real.rpow_nonneg hMNpos.le ε
    have henn : 0 ≤ energy F c N lam := by
      unfold energy
      exact Finset.sum_nonneg (fun b _ => by positivity)
    have henvnn : 0 ≤ M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
        Real.sqrt (M / K) * N := by
      have h1 : 0 ≤ Real.sqrt M * Real.rpow K (α - 1 / 2) :=
        mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg hKpos.le _)
      have h2 : 0 ≤ Real.sqrt (M / K) * N := mul_nonneg (Real.sqrt_nonneg _) hN0.le
      linarith [hM, hN, h1, h2]
    have hsqrt_le : Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N ≤
        M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N := by
      nlinarith [hM, hN]

    have hseven : ‖sevenTermSum C‖ ≤
        (A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N) * energy F c N lam := by
      have hmain'' : ‖MainBoundary.mainDifference C‖ ≤
          A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N) * energy F c N lam := by
        refine le_trans hmain' ?_
        have ha : 0 ≤ A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' :=
          mul_nonneg (mul_nonneg hA₄.le hnd4nn) (Real.rpow_nonneg hMNpos.le ε')
        calc A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
                (Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) *
                energy F c N lam
            = (A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε') *
                (Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) *
                energy F c N lam := by ring
          _ ≤ (A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε') *
                (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                  Real.sqrt (M / K) * N) * energy F c N lam :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le ha) henn
          _ = A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
                (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                  Real.sqrt (M / K) * N) * energy F c N lam := by ring
      calc ‖sevenTermSum C‖ ≤ ‖MainBoundary.mainDifference C‖ +
            ((‖E1 C 1 true‖ + ‖E2 C 1 true‖ + ‖E3 C 1 true‖ + ‖E4 C 1 true‖ +
                ‖E5 C 1 true‖) +
              ∑ B ∈ dyadicScales C,
                (‖E1 C B‖ + ‖E2 C B‖ + ‖E3 C B‖ + ‖E4 C B‖ + ‖E5 C B‖)) :=
            norm_sevenTermSum_le C
        _ ≤ (A₄ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) * energy F c N lam) +
            (A₁ * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) * energy F c N lam) :=
            add_le_add hmain'' herrC
        _ = (A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) * energy F c N lam := by ring

    have hKM' : C.K ≤ C.M := by simpa only [C] using hKM
    have hδ' : 0 < C.δ := by simpa only [C] using hδpos
    have hoff : ‖offDiagonalT3 Q W M N K d g lam‖ ≤
        (A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N) * energy F c N lam + A₂ * energy F c N lam := by
      rw [bilinear_explicit_assembly_identity C hM hN hK hKM' hδ']
      calc ‖sevenTermSum C + totalRemainder C‖ ≤ ‖sevenTermSum C‖ + ‖totalRemainder C‖ :=
            norm_add_le _ _
        _ ≤ ((A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) * energy F c N lam) +
            A₂ * energy F c N lam := add_le_add hseven hassemC

    have hT3 : ‖T3 F c Q W M N K d g lam‖ ≤
        A₃ * M * energy F c N lam +
          ((A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N) * energy F c N lam + A₂ * energy F c N lam) := by
      have hsplit : T3 F c Q W M N K d g lam =
          (T3 F c Q W M N K d g lam - offDiagonalT3 Q W M N K d g lam) +
            offDiagonalT3 Q W M N K d g lam := by ring
      calc ‖T3 F c Q W M N K d g lam‖
          = ‖(T3 F c Q W M N K d g lam - offDiagonalT3 Q W M N K d g lam) +
              offDiagonalT3 Q W M N K d g lam‖ := by conv_lhs => rw [hsplit]
        _ ≤ ‖T3 F c Q W M N K d g lam - offDiagonalT3 Q W M N K d g lam‖ +
              ‖offDiagonalT3 Q W M N K d g lam‖ := norm_add_le _ _
        _ ≤ A₃ * M * energy F c N lam +
              ((A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
                (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                  Real.sqrt (M / K) * N) * energy F c N lam +
                A₂ * energy F c N lam) := add_le_add hdiagC hoff
    refine le_trans hT3 ?_
    have hnd41 : 1 ≤ (Ideal.absNorm d : ℝ) ^ 4 := one_le_pow₀ hnd1
    have hrpow1 : 1 ≤ Real.rpow (M * N) ε := Real.one_le_rpow hMN1 hε.le
    have henv1 : 1 ≤ M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
        Real.sqrt (M / K) * N := by
      have h1 : 0 ≤ Real.sqrt M * Real.rpow K (α - 1 / 2) :=
        mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg hKpos.le _)
      have h2 : 0 ≤ Real.sqrt (M / K) * N := mul_nonneg (Real.sqrt_nonneg _) hN0.le
      linarith [hM, hN, h1, h2]
    have hM_le : M ≤ (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
        (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) := by
      have henvM : M ≤ M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
          Real.sqrt (M / K) * N := by
        have h1 : 0 ≤ Real.sqrt M * Real.rpow K (α - 1 / 2) :=
          mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg hKpos.le _)
        have h2 : 0 ≤ Real.sqrt (M / K) * N := mul_nonneg (Real.sqrt_nonneg _) hN0.le
        linarith [hM, hN, h1, h2]
      calc M ≤ M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N := henvM
        _ ≤ ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε) *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) :=
            le_mul_of_one_le_left henvnn
              (one_le_mul_of_one_le_of_one_le hnd41 hrpow1)
        _ = (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) := by ring
    have ha : A₃ * M * energy F c N lam ≤
        A₃ * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N)) * energy F c N lam :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM_le hA₃) henn
    have hb : (A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) *
          energy F c N lam ≤
        (A₄ + A₁) * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N)) * energy F c N lam := by
      have hA41 : 0 ≤ A₄ + A₁ := by linarith [hA₄.le, hA₁]
      have hinner : (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) ≤
          (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow_le hnd4nn) henvnn
      calc (A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N) * energy F c N lam
          = (A₄ + A₁) * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N)) * energy F c N lam := by ring
        _ ≤ (A₄ + A₁) * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N)) * energy F c N lam :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hA41) henn
    have hc : A₂ * energy F c N lam ≤
        A₂ * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N)) * energy F c N lam := by
      have h1 : 1 ≤ (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N) := by
        have := one_le_mul_of_one_le_of_one_le hnd41 hrpow1
        exact one_le_mul_of_one_le_of_one_le this henv1
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hA₂.le h1) henn
    calc A₃ * M * energy F c N lam +
          ((A₄ + A₁) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε' *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N) * energy F c N lam + A₂ * energy F c N lam)
        ≤ A₃ * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N)) * energy F c N lam +
          ((A₄ + A₁) * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N)) * energy F c N lam +
            A₂ * ((Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
              (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
                Real.sqrt (M / K) * N)) * energy F c N lam) :=
          add_le_add ha (add_le_add hb hc)
      _ = (A₃ + (A₄ + A₁) + A₂) * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N) * energy F c N lam := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

theorem masked_le_canonical
    {F : Type} [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (bad : Ideal (𝓞 F)) (hcore : bad = c)
    (W : ℝ → ℝ) (M N K : ℝ) (d : Ideal (𝓞 F))
    (U : Finset (Ideal (𝓞 F))) (τ : Ideal (𝓞 F) → ℂ)
    (hτ : ∀ u, ‖τ u‖ ≤ 1) :
    NormalizedKernelProfiles.B3normalizedMasked F c Q bad W M N K d U τ ≤
      B3 F c Q W M N K d := by

  have hrows : NormalizedKernelProfiles.normalizedKernelRows F c bad M K = kernelRows F c M K := by
    unfold NormalizedKernelProfiles.normalizedKernelRows
    rw [hcore]
    exact Finset.filter_true_of_mem (fun a ha => (Finset.mem_filter.mp ha).2.2.1)

  have hT : ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
      NormalizedKernelProfiles.T3normalizedMasked F c Q bad W M N K d g U τ lam =
        T3 F c Q W M N K d g (fun u => if u ∈ U then τ u * lam u else 0) := by
    intro g lam
    unfold NormalizedKernelProfiles.T3normalizedMasked T3
    rw [hrows]
  unfold NormalizedKernelProfiles.B3normalizedMasked B3
  refine csSup_le ?_ ?_
  · exact ⟨0, Or.inl rfl⟩
  · rintro x (hx | ⟨g, lam, hlam, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact B3_nonneg Q W M N K d
    · rw [hT g lam]

      have henergy :
          energy F c N (fun u => if u ∈ U then τ u * lam u else 0) ≤ energy F c N lam := by
        unfold energy
        apply Finset.sum_le_sum
        intro b _
        change ‖(if b ∈ U then τ b * lam b else 0)‖ ^ 2 ≤ ‖lam b‖ ^ 2
        by_cases hb : b ∈ U
        · rw [if_pos hb, norm_mul, mul_pow]
          exact mul_le_of_le_one_left (sq_nonneg _)
            (pow_le_one₀ (norm_nonneg _) (hτ b))
        · rw [if_neg hb]
          simp
      have h3 : energy F c N (fun u => if u ∈ U then τ u * lam u else 0) ≤ 1 :=
        henergy.trans hlam
      calc ‖T3 F c Q W M N K d g (fun u => if u ∈ U then τ u * lam u else 0)‖
          ≤ B3 F c Q W M N K d *
              energy F c N (fun u => if u ∈ U then τ u * lam u else 0) :=
            norm_T3_le_B3_mul_energy Q W M N K d g _
        _ ≤ B3 F c Q W M N K d * 1 :=
            mul_le_mul_of_nonneg_left h3 (B3_nonneg Q W M N K d)
        _ = B3 F c Q W M N K d := mul_one _

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreNormalizedEstimate

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open NormalizedKernelProfiles

theorem bilinear_prop51_core_normalized_masked
    {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : AllIndexNormalizedFamilyData Q) (hcore : D.bad = c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    {α : ℝ} (hα₁ : 1 ≤ α) (hα₂ : α ≤ 2)
    (hE : HasSieveExponent F c Q α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 0 < K →
      N ^ 2 / M * Real.rpow (M * N) ε ≤ K →
      K ≤ M * Real.rpow (M * N) (-ε) →
      ∀ (d : Ideal (𝓞 F)) (U : Finset (Ideal (𝓞 F)))
        (τ : Ideal (𝓞 F) → ℂ),
        U ⊆ paperShell F c N → (∀ u, ‖τ u‖ ≤ 1) →
        B3normalizedMasked F c Q D.bad W M N K d U τ ≤
          C * ((Ideal.absNorm d : ℝ) ^ 4) * Real.rpow (M * N) ε *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
              Real.sqrt (M / K) * N) := by
  intro ε hε
  obtain ⟨A, hA, hlarge⟩ :=
    CoreNormalizedEstimate.large_cutoff_energy_bound
       hF Q D hcore W hW hα₁ hα₂ hE ε hε
  obtain ⟨C, hC, hcanonical⟩ :=
    CoreNormalizedEstimate.canonical_operator_of_large_cutoff_energy
      c Q W hW α ε A hα₁ hα₂ hε hA hlarge
  refine ⟨C, hC, ?_⟩
  intro M N K hM hN hK hlower hupper d U τ hU hτ
  exact (CoreNormalizedEstimate.masked_le_canonical
    c Q D.bad hcore W M N K d U τ hτ).trans
      (hcanonical M N K hM hN hK hlower hupper d)

end DedekindZetaZeroFree.LargeSieve.Sieve

end

end
