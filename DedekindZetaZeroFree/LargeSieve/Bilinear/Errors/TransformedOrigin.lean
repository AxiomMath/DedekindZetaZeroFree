module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Coefficients.DivisorRectanglesAndEpsilonEnergyBounds

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

namespace ErrorRectangles

def upperConstant (c : Ideal (𝓞 F)) : ℝ := 8 * max 1 (norm c)

def originRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (rectangles C).filter (fun P => P.1 * P.2 ≤
    upperConstant c * (C.N / Real.sqrt (B * C.M)) *
      Real.rpow (C.M * C.N) C.δ)

def originScore (C : Context Q) (B : ℝ) (P : ℝ × ℝ) : ℝ :=
  Real.sqrt (P.1 * P.2) *
    Real.sqrt (U Q B (C.N / (norm C.d * P.1)) *
      U Q B (C.N / (norm C.d * P.2)))

def originEnvelope (C : Context Q) (B : ℝ) : ℝ :=
  finiteSup (originRectangles C B) (originScore C B)

end ErrorRectangles

theorem quotient_weighted_energy (C : Context Q) (hN : 1 ≤ C.N) :
    (∑ u ∈ C.columns,
      ‖C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)‖ ^ 2) ≤
      (norm C.d / C.N) * Sieve.energy F c C.N C.lam := by
  classical
  have hNpos : 0 < C.N := lt_of_lt_of_le zero_lt_one hN
  have hdpos : 0 < norm C.d := by
    have hd : Ideal.absNorm C.d ≠ 0 := fun h => C.hd0 (Ideal.absNorm_eq_zero_iff.mp h)
    unfold norm
    exact_mod_cast Nat.pos_of_ne_zero hd
  rw [Sieve.energy, Finset.mul_sum]
  apply Finset.sum_le_sum_of_injOn (fun u => C.d * u)
  · intro u hu v hv h
    exact mul_left_cancel₀ C.hd0 h
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨u, hu, rfl⟩
    exact (Finset.mem_filter.mp hu).2.1
  · intro u hu
    have hmem := (Finset.mem_filter.mp hu).2.1
    have hlow := ((Sieve.mem_paperShell F c C.N (C.d * u)).mp hmem).2.2.1
    have hmul : norm (C.d * u) = norm C.d * norm u := by
      simp only [norm, map_mul, Nat.cast_mul]
    change C.N < norm (C.d * u) at hlow
    rw [hmul] at hlow
    have hup : 0 < norm u := by
      have hnonneg : 0 ≤ norm u := by unfold norm; positivity
      nlinarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hup.le]
    have hinv : 1 / norm u ≤ norm C.d / C.N := by
      rw [div_le_div_iff₀ hup hNpos]
      simpa only [one_mul] using hlow.le
    calc
      ‖C.lam (C.d * u)‖ ^ 2 / norm u =
          (1 / norm u) * ‖C.lam (C.d * u)‖ ^ 2 := by ring
      _ ≤ (norm C.d / C.N) * ‖C.lam (C.d * u)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
  · intro b hb hbnot
    exact mul_nonneg (div_nonneg hdpos.le hNpos.le) (sq_nonneg _)

private theorem origin_factorization (C : Context Q) (B : ℝ) (unit : Bool) :
    E2 C B unit = -((C.M : ℂ) * C.origin) * Origin.coefficientForm C B unit := by
  unfold E2 Origin.coefficientForm Context.pairSum
  rw [neg_mul, neg_inj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hv
  · simp only [Finset.mul_sum, Context.prefactor, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro a ha
    ring
  · simp

theorem bilinear_error_origin
    (D : Sieve.AllIndexNormalizedFamilyData Q) (W : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D → C.W = W → C.δ = δ →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ‖E2 C B unit‖ ≤ A * Real.rpow (C.M * C.N * norm C.d) ε *
          C.estimatePrefactor * ErrorRectangles.originEnvelope C B *
          Sieve.energy F c C.N C.lam := by
  intro ε hε
  obtain ⟨H, hH, hbound⟩ := Origin.coefficient_estimate D δ hδ ε hε
  by_cases hex : ∃ C₀ : Context Q, C₀.W = W
  · obtain ⟨C₀, hC₀⟩ := hex
    let R : ℝ := ‖C₀.origin‖ + 1
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨R * H, mul_pos hR hH, ?_⟩
    intro C hCD hCW hCδ B unit hunit hM hN hB hBK hKM hn hnN
    have hM0 : 0 ≤ C.M := by linarith
    have hn0 : 0 ≤ norm C.d := by linarith
    have hN0 : 0 ≤ C.N := by linarith
    have hp0 : 0 ≤ Real.rpow (C.M * C.N * norm C.d) ε :=
      Real.rpow_nonneg (mul_nonneg (mul_nonneg hM0 hN0) hn0) _
    have hsrc : C.source = C₀.source := by
      funext x
      simp only [Context.source, hCW, hC₀]
    have horg : C.origin = C₀.origin := by
      simp only [Context.origin, Context.kappa, hsrc]
    have horgle : ‖C.origin‖ ≤ R := by rw [horg]; dsimp [R]; linarith
    have hform := hbound C hCD hCδ B unit hunit hM hN hB hBK hKM hn hnN
    have he : Origin.weightedEnergy C ≤
        (norm C.d / C.N) * Sieve.energy F c C.N C.lam :=
      quotient_weighted_energy C hN
    have henv := Origin.envelope_nonneg C B
    have hscore : Origin.envelope C B = ErrorRectangles.originEnvelope C B := rfl
    rw [origin_factorization, norm_mul, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
    calc
      C.M * ‖C.origin‖ * ‖Origin.coefficientForm C B unit‖ ≤
          C.M * R * (H * Real.rpow (C.M * C.N * norm C.d) ε *
            Origin.envelope C B * Origin.weightedEnergy C) :=
        mul_le_mul (mul_le_mul_of_nonneg_left horgle hM0) hform
          (norm_nonneg _) (mul_nonneg hM0 hR.le)
      _ ≤ C.M * R * (H * Real.rpow (C.M * C.N * norm C.d) ε *
            Origin.envelope C B *
              ((norm C.d / C.N) * Sieve.energy F c C.N C.lam)) := by
        gcongr
      _ = _ := by rw [hscore, Context.estimatePrefactor]; ring
  · refine ⟨1, zero_lt_one, ?_⟩
    intro C hCD hCW
    exact False.elim (hex ⟨C, hCW⟩)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
