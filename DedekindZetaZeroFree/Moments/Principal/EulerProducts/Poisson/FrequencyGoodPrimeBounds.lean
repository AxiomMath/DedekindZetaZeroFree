module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.NormalConvergence

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawEulerGood31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree.Quantitative.EulerGoodPrime

variable {F : Type} [Field F] [NumberField F]

section Generic

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem goodFactor_sub_one_le_five_terms (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (C : A.GeneralArithmeticContext σ η hS)
      (pr : LocalFiniteSums.ExteriorPrime A) (uu : A.R), ∀ p ∈ OmegaStarMargin δ',
        ‖CorrectionFactors.goodFactor C pr uu p.1 p.2.1 p.2.2 - 1‖ ≤
          C₀ * (LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
            LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) +
            LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
            LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
              LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) +
            LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re)) := by
  have hρ : ((2 : ℝ) ^ δ')⁻¹ < 1 := inv_two_rpow_lt_one δ' hδ'
  have hρ0 : 0 < 1 - ((2 : ℝ) ^ δ')⁻¹ := by linarith
  refine ⟨6 / ((1 - ((2 : ℝ) ^ δ')⁻¹) * (1 - ((2 : ℝ) ^ δ')⁻¹)),
    div_pos (by norm_num) (mul_pos hρ0 hρ0), ?_⟩
  intro C pr uu p hp
  simp only [OmegaStarMargin, Set.mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp
  have hQ2 := Q_ge_two pr
  exact good_bound C pr uu p.1 p.2.1 p.2.2 _ hρ
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))
      (rpow_le_two_inv δ' hδ' _ hQ2 _ (by linarith))

theorem goodFactor_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C : ℝ, 0 < C ∧ ∀ (C' : A.GeneralArithmeticContext σ η hS)
      (pr : LocalFiniteSums.ExteriorPrime A) (uu : A.R), ∀ p ∈ OmegaStarMargin δ',
        ‖CorrectionFactors.goodFactor C' pr uu p.1 p.2.1 p.2.2 - 1‖ ≤
          C * LocalFiniteSums.Q pr ^ (-1 - δ') := by
  obtain ⟨C0, hC0, hspec⟩ := goodFactor_sub_one_le_five_terms (A := A) (σ := σ) (η := η)
    (hS := hS) δ' hδ'
  refine ⟨5 * C0, by linarith, ?_⟩
  intro C' pr uu p hp
  have hQ2 := Q_ge_two pr
  have hQ0 := Q_pos pr
  have hQ1 : (1 : ℝ) ≤ LocalFiniteSums.Q pr := by linarith
  have hm : ∀ a : ℝ, a ≤ -1 - δ' →
      LocalFiniteSums.Q pr ^ a ≤ LocalFiniteSums.Q pr ^ (-1 - δ') :=
    fun a ha => Real.rpow_le_rpow_of_exponent_le hQ1 ha
  have hp' := hp
  simp only [OmegaStarMargin, Set.mem_setOf_eq] at hp'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp'
  have T1 : LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [← Real.rpow_add hQ0]; exact hm _ (by linarith)
  have T2 : LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [← Real.rpow_add hQ0]; exact hm _ (by linarith)
  have T3 : LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [← Real.rpow_add hQ0]; exact hm _ (by linarith)
  have e4 : LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
      LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) =
      LocalFiniteSums.Q pr ^ (1 + (-p.1.re + -p.2.1.re + -(6 * p.2.2.re))) := by
    rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_one]
  have T4 : LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
      LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := by
    rw [e4]; exact hm _ (by linarith)
  have T5 : LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re) ≤
      LocalFiniteSums.Q pr ^ (-1 - δ') := hm _ (by linarith)
  have hS5 : LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
      LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re)) +
      LocalFiniteSums.Q pr ^ (-p.1.re) * LocalFiniteSums.Q pr ^ (-p.2.1.re) +
      LocalFiniteSums.Q pr * (LocalFiniteSums.Q pr ^ (-p.1.re) *
        LocalFiniteSums.Q pr ^ (-p.2.1.re) * LocalFiniteSums.Q pr ^ (-(6 * p.2.2.re))) +
      LocalFiniteSums.Q pr ^ (4 - 6 * p.1.re - 6 * p.2.2.re) ≤
      5 * LocalFiniteSums.Q pr ^ (-1 - δ') := by linarith
  calc _ ≤ _ := hspec C' pr uu p hp
    _ ≤ C0 * (5 * LocalFiniteSums.Q pr ^ (-1 - δ')) := mul_le_mul_of_nonneg_left hS5 hC0.le
    _ = 5 * C0 * LocalFiniteSums.Q pr ^ (-1 - δ') := by ring

end Generic

section Raw

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

open AllRowEuler.InitialSeparation

theorem j_val_eq (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) :
    (U.j pr).val = idealPrimeExponent pr.val.asIdeal U.ideal.val := rfl

theorem j_eq_zero_iff (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) :
    (U.j pr).val = 0 ↔
      pr.val.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors U.ideal.val := by
  rw [j_val_eq D, idealPrimeExponent, Multiset.count_eq_zero]

theorem localCorrection_good_eq (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val = 0)
    (ξ w z : ℂ) :
    AllRowEuler.InitialSeparation.localCorrection D.context U pr ξ w z =
      CorrectionFactors.goodFactor D.context pr U.u ξ w z := by
  unfold AllRowEuler.InitialSeparation.localCorrection
  rw [if_pos hj]

theorem localCorrection_good_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (↑(U.j pr) : ℕ) = (0 : ℕ) → ∀ p ∈ OmegaStarMargin δ',
          ‖AllRowEuler.InitialSeparation.localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-1 - δ) := by
  obtain ⟨C, hC, h⟩ := goodFactor_sub_one_le (A := D.recipe.A) (σ := D.recipe.σ)
    (η := D.recipe.target) (hS := D.recipe.traceBad) δ' hδ'
  refine ⟨C, δ', hC, hδ', ?_⟩
  intro U pr hj p hp
  rw [localCorrection_good_eq D U pr hj]
  exact h D.context pr U.u p hp

theorem localCorrection_good_differentiableOn (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val = 0) :
    DifferentiableOn ℂ
      (fun p : Coordinates =>
        AllRowEuler.InitialSeparation.localCorrection D.context U pr p.1 p.2.1 p.2.2) OmegaStar := by
  refine (DedekindZetaZeroFree.Quantitative.EulerProductAux.goodFactor_differentiableOn_star D.context pr
    U.u).congr ?_
  intro p _
  exact localCorrection_good_eq D U pr hj _ _ _

end Raw

end

end DedekindZetaZeroFree.Quantitative.RawEulerGood31
