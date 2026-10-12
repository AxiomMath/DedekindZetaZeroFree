module

public import DedekindZetaZeroFree.LargeSieve.Exponents.LocalErrorBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

theorem error_dyadic_internal_exponents
    (ε C0 : ℝ) (hε : 0 < ε) (hC0 : 0 ≤ C0) :
    0 < ε / 64 ∧ 0 < ε / (8 * (C0 + 2)) ∧
      8 * (ε / 64) + (C0 + 2) * (ε / (8 * (C0 + 2))) + ε / 4 ≤ ε := by
  have hpos : 0 < C0 + 2 := by linarith
  have hne : C0 + 2 ≠ 0 := ne_of_gt hpos
  constructor
  · positivity
  constructor
  · positivity
  · have heq : (C0 + 2) * (ε / (8 * (C0 + 2))) = ε / 8 := by
      field_simp
    rw [heq]
    linarith

theorem error_dyadic_sum_of_card_bound
    (α ε A C0 : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hε : 0 < ε) (hA : 0 ≤ A) (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M N K n E : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K → 1 ≤ n →
      K ≤ M → n ≤ 2 * N → 0 ≤ E →
      ∀ {ι : Type*} (J : Finset ι) (B e : ι → ℝ),
      J.card ≤ Vendor.dyadicLength K + 2 →
      (∀ j ∈ J, 1 ≤ B j ∧ B j ≤ K) →
      (∀ j ∈ J, 0 ≤ e j) →
      (∀ j ∈ J, e j ≤
        A * n * Real.rpow (M * N)
          (8 * (ε / 64) + (C0 + 2) * (ε / (8 * (C0 + 2)))) *
          (M + N + Real.sqrt M * Real.rpow (B j) (α - 1 / 2)) * E) →
      ∑ j ∈ J, e j ≤
        C * n ^ (4 : ℕ) * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2)) * E := by
  let η := ε / 4
  let q := 8 * (ε / 64) + (C0 + 2) * (ε / (8 * (C0 + 2)))
  let L := 3 + 1 / (η * Real.log 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hL : 0 ≤ L := by
    have := Vendor.dyadicLength_small_power_constant_pos hη
    dsimp [L]
    linarith
  refine ⟨L * A, mul_nonneg hL hA, ?_⟩
  intro M N K n E hM hN hK hn hKM hnN hE ι J B e hcard hB he heBound
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hMN : 1 ≤ M * N := by nlinarith
  have hRq : 0 ≤ Real.rpow (M * N) q := Real.rpow_nonneg (by positivity) _
  have hRη : 0 ≤ Real.rpow (M * N) η := Real.rpow_nonneg (by positivity) _
  have hRε : 0 ≤ Real.rpow (M * N) ε := Real.rpow_nonneg (by positivity) _
  have hKMN : K ≤ M * N := hKM.trans (le_mul_of_one_le_right hM0 hN)
  have hp : 0 ≤ α - 1 / 2 := by linarith [hα.1]
  have hcount : (J.card : ℝ) ≤ L * Real.rpow (M * N) η := by
    have hc : (J.card : ℝ) ≤ (Vendor.dyadicLength K : ℝ) + 2 := by
      exact_mod_cast hcard
    have hl := Vendor.dyadicLength_small_power hη hK
    have hkpow : 1 ≤ Real.rpow K η := Real.one_le_rpow hK hη.le
    have hkp : Real.rpow K η ≤ Real.rpow (M * N) η :=
      Real.rpow_le_rpow hK0 hKMN hη.le
    have hfirst : (J.card : ℝ) ≤ L * Real.rpow K η := by
      dsimp [L]
      push_cast at hl
      change (Vendor.dyadicLength K : ℝ) + 1 ≤
        (2 + 1 / (η * Real.log 2)) * Real.rpow K η at hl
      rw [Real.rpow_eq_pow] at hkpow hl
      nlinarith
    exact hfirst.trans (mul_le_mul_of_nonneg_left hkp hL)
  let S := M + N + Real.sqrt M * Real.rpow K (α - 1 / 2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hU : 0 ≤ A * n * Real.rpow (M * N) q * S * E := by positivity
  have hsum : (∑ j ∈ J, e j) ≤ (J.card : ℝ) *
      (A * n * Real.rpow (M * N) q * S * E) := by
    calc
      (∑ j ∈ J, e j) ≤ ∑ j ∈ J, (A * n * Real.rpow (M * N) q * S * E) := by
        apply Finset.sum_le_sum
        intro j hj
        apply (heBound j hj).trans
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [S]
        exact add_le_add_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith [(hB j hj).1]) (hB j hj).2 hp)
          (Real.sqrt_nonneg M)) _
      _ = _ := by simp
  have hnp : n ≤ n ^ (4 : ℕ) := by
    calc
      n = n ^ (1 : ℕ) := by simp
      _ ≤ n ^ (4 : ℕ) := pow_le_pow_right₀ hn (by norm_num)
  have hexp : q + η ≤ ε := (error_dyadic_internal_exponents ε C0 hε hC0).2.2
  have hpow : Real.rpow (M * N) q * Real.rpow (M * N) η ≤ Real.rpow (M * N) ε := by
    change (M * N) ^ q * (M * N) ^ η ≤ (M * N) ^ ε
    rw [← Real.rpow_add (by positivity : 0 < M * N)]
    exact Real.rpow_le_rpow_of_exponent_le hMN hexp
  calc
    (∑ j ∈ J, e j) ≤ (L * Real.rpow (M * N) η) *
        (A * n * Real.rpow (M * N) q * S * E) :=
      hsum.trans (mul_le_mul_of_nonneg_right hcount hU)
    _ = (L * A) * n * (Real.rpow (M * N) q * Real.rpow (M * N) η) * S * E := by ring
    _ ≤ (L * A) * n ^ (4 : ℕ) * Real.rpow (M * N) ε * S * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_right _ hS
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnp (mul_nonneg hL hA))
        hpow (by positivity) (by positivity)

theorem bilinear_error_dyadic_sum
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (α : ℝ), α ∈ Set.Icc (1 : ℝ) 2 →
      Sieve.HasSieveExponent F c Q α →
      ∀ (ε : ℝ), 0 < ε →
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K → K ≤ M →
        ∀ (d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥) (hd : Squarefree d)
          (hdc : d ⊔ c = ⊤),
        1 ≤ (Ideal.absNorm d : ℝ) → (Ideal.absNorm d : ℝ) ≤ 2 * N →
        ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
        let C : Context Q := {
          D := D, core := core, hF := hF,
          M := M, N := N, K := K, δ := ε / (8 * (C0 + 2)), W := W, hW := hW,
          d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
        (‖E1 C 1 true‖ + ‖E2 C 1 true‖ + ‖E3 C 1 true‖ +
            ‖E4 C 1 true‖ + ‖E5 C 1 true‖) +
          (∑ B ∈ dyadicScales C,
            (‖E1 C B‖ + ‖E2 C B‖ + ‖E3 C B‖ + ‖E4 C B‖ + ‖E5 C B‖)) ≤
          A * (Ideal.absNorm d : ℝ) ^ (4 : ℕ) * Real.rpow (M * N) ε *
            (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2)) *
            Sieve.energy F c N lam := by
  obtain ⟨C0, hC0, hlocal⟩ :=
    bilinear_error_local_exponent_bound F c Q D core hF W hW
  refine ⟨C0, hC0, ?_⟩
  intro α hα hSieve ε hε
  obtain ⟨hζ, hδ, _⟩ := error_dyadic_internal_exponents ε C0 hε hC0
  obtain ⟨A, hA, hblocks⟩ := hlocal α hα hSieve (ε / 64)
    (ε / (8 * (C0 + 2))) hζ hδ
  obtain ⟨Csum, hCsum, hsum⟩ := error_dyadic_sum_of_card_bound α ε A C0 hα hε hA hC0
  refine ⟨Csum, hCsum, ?_⟩
  intro M N K hM hN hK hKM d hd0 hd hdc hn hnN g lam
  let ctx : Context Q := {
    D := D, core := core, hF := hF,
    M := M, N := N, K := K, δ := ε / (8 * (C0 + 2)), W := W, hW := hW,
    d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
  let mass : ℝ → Bool → ℝ := fun B unit =>
    ‖E1 ctx B unit‖ + ‖E2 ctx B unit‖ + ‖E3 ctx B unit‖ +
      ‖E4 ctx B unit‖ + ‖E5 ctx B unit‖
  let J : Finset (Option ℝ) := insert none ((dyadicScales ctx).image some)
  let B : Option ℝ → ℝ := fun j => j.elim 1 id
  let e : Option ℝ → ℝ := fun j => j.elim (mass 1 true) (fun b => mass b false)
  have hcard : J.card ≤ Vendor.dyadicLength K + 2 := by
    dsimp [J]
    calc
      (insert none ((dyadicScales ctx).image some)).card ≤
          ((dyadicScales ctx).image some).card + 1 := Finset.card_insert_le _ _
      _ ≤ (dyadicScales ctx).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ Vendor.dyadicLength K + 2 := by
        have hc : (dyadicScales ctx).card ≤ Vendor.dyadicLength K := by
          unfold dyadicScales
          exact (Finset.card_image_le).trans (by simp [ctx])
        omega
  have hscale : ∀ b ∈ dyadicScales ctx, 1 ≤ b ∧ b ≤ K := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hjK : j < Vendor.dyadicLength K := by simpa [ctx] using hj
    exact ⟨one_le_pow₀ (by norm_num), (Vendor.pow_lt_of_lt_dyadicLength hK hjK).le⟩
  have hB : ∀ j ∈ J, 1 ≤ B j ∧ B j ≤ K := by
    intro j hj
    cases j with
    | none => exact ⟨le_rfl, hK⟩
    | some b => exact hscale b (by simpa [J] using hj)
  have he : ∀ j ∈ J, 0 ≤ e j := by
    intro j hj
    cases j <;> dsimp [e, mass] <;> positivity
  have hbound : ∀ j ∈ J, e j ≤
      A * (Ideal.absNorm d : ℝ) * Real.rpow (M * N)
        (8 * (ε / 64) + (C0 + 2) * (ε / (8 * (C0 + 2)))) *
        (M + N + Real.sqrt M * Real.rpow (B j) (α - 1 / 2)) *
        Sieve.energy F c N lam := by
    intro j hj
    cases j with
    | none =>
      exact hblocks M N K hM hN hK hKM d hd0 hd hdc hn hnN g lam 1 true
        le_rfl hK (fun _ => rfl)
    | some b =>
      obtain ⟨hb1, hbK⟩ := hB (some b) hj
      exact hblocks M N K hM hN hK hKM d hd0 hd hdc hn hnN g lam b false
        hb1 hbK (by simp)
  have hE : 0 ≤ Sieve.energy F c N lam := by unfold Sieve.energy; positivity
  have hs := hsum M N K (Ideal.absNorm d : ℝ) (Sieve.energy F c N lam)
    hM hN hK hn hKM hnN hE J B e hcard hB he hbound
  have heq : (∑ j ∈ J, e j) = mass 1 true + ∑ b ∈ dyadicScales ctx, mass b false := by
    dsimp [J]
    rw [Finset.sum_insert (by simp), Finset.sum_image]
    · rfl
    · intro a ha b hb hab
      exact Option.some.inj hab
  rw [heq] at hs
  exact hs

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end
