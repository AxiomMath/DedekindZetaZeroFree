module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.AllowedRowSieve

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorSieve

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowMaximalSum (U N T : ℝ) (b : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ᶠ u : D.Row,
    if FixedData.Row.u u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
      detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) N T
    else 0

private theorem finite_ideals_absNorm_le (F : Type) [Field F] [NumberField F] (M : ℝ) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le ⌊M⌋₊).subset ?_
  rintro I ⟨-, hI⟩
  exact Nat.le_floor hI

private theorem finsum_ideal_ite (F : Type) [Field F] [NumberField F] {G : Type*} [AddCommMonoid G]
    (M : ℝ) (f : Ideal (𝓞 F) → G) :
    (∑ᶠ J : Ideal (𝓞 F), if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ M then f J else 0) =
      ∑ J ∈ (finite_ideals_absNorm_le F M).toFinset, f J := by
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_ideals_absNorm_le F M).toFinset) ?_]
  · apply Finset.sum_congr rfl
    intro J hJ
    rw [Set.Finite.mem_toFinset] at hJ
    rw [if_pos (show J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ M from hJ)]
  · intro J hJ
    rw [Function.mem_support] at hJ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    exact hJ (if_neg (show ¬ (J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ M) from h))

theorem detector_maximal_sieve :
    ∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N T : ℝ) (b : Ideal (𝓞 F) → ℂ), 2 ≤ U → 2 ≤ N → 1 ≤ T →
        detectorDyadicSupport F b N →
        rowMaximalSum D U N T b ≤
          C * (T + 1) * (N + U ^ 2) * (N * U) ^ ε * Real.log (2 * N) ^ Clog *
            detectorDyadicCoefficientMass F b N := by
  refine ⟨0, le_rfl, fun ε hε => ?_⟩
  obtain ⟨C₀, hC₀, hact⟩ := ActualConductorSieve.actual_conductor_sieve D (ε / 2) (by linarith)
  obtain ⟨C, hC, hgen⟩ := DedekindZetaZeroFree.detector_maximal_sieve F ε C₀ hε hC₀
  refine ⟨C, hC, ?_⟩
  intro U N T b hU hN hT hsupp
  rw [Real.rpow_zero, mul_one]
  have hN0 : 0 ≤ N := by linarith
  have hT0 : (0 : ℝ) ≤ T + 1 := by linarith
  have hK : 0 ≤ C * (T + 1) * (N + U ^ 2) * (N * U) ^ ε *
      detectorDyadicCoefficientMass F b N :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hT0) (add_nonneg hN0 (sq_nonneg U)))
      (Real.rpow_nonneg (mul_nonneg hN0 (by linarith)) ε))
      (detectorDyadicCoefficientMass_nonneg F b N)

  have hSieve : ∀ J : Finset D.Row, (∀ u ∈ J, u ∈ ActualConductorSieve.dyadNonprincipal D U) →
      ∀ (M : ℝ) (c : Ideal (𝓞 F) → ℂ), 2 ≤ M →
        (∀ I, ¬ (I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M) → c I = 0) →
        (∑ u : {x // x ∈ J}, ‖∑ᶠ I : Ideal (𝓞 F),
            if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then c I * (D.omega u.1).character I else 0‖ ^ 2) ≤
          C₀ * (M + U ^ 2) * (M * U) ^ (ε / 2) *
            (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then ‖c I‖ ^ 2 else 0) := by
    intro J hJ M c hM _hc
    have hB : ∀ I ∈ (finite_ideals_absNorm_le F M).toFinset,
        I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M :=
      fun I hI => (Set.Finite.mem_toFinset (finite_ideals_absNorm_le F M)).1 hI
    have hact' := hact U M hU hM J hJ _ hB c
    have e1 : (∑ u : {x // x ∈ J}, ‖∑ᶠ I : Ideal (𝓞 F),
          if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then c I * (D.omega u.1).character I else 0‖ ^ 2) =
        ∑ u ∈ J, ‖∑ I ∈ (finite_ideals_absNorm_le F M).toFinset,
          c I * (D.omega u).character I‖ ^ 2 := by
      rw [← Finset.sum_coe_sort J]
      exact Finset.sum_congr rfl (fun u _ => by rw [finsum_ideal_ite F M])
    have hR : (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then ‖c I‖ ^ 2 else 0) =
        ∑ I ∈ (finite_ideals_absNorm_le F M).toFinset, ‖c I‖ ^ 2 :=
      finsum_ideal_ite F M _
    rw [e1, hR]
    exact hact'

  have hJsum : ∀ J : Finset D.Row, (∀ u ∈ J, u ∈ ActualConductorSieve.dyadNonprincipal D U) →
      ∑ u ∈ J, (if u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (D.omega u).character I) N T else 0) ≤
        C * (T + 1) * (N + U ^ 2) * (N * U) ^ ε * detectorDyadicCoefficientMass F b N := by
    intro J hJ
    have hc : ∀ u ∈ J, (if u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (D.omega u).character I) N T else 0) =
        detectorHeightPrefixMaximum F b (fun I => (D.omega u).character I) N T := by
      intro u hu
      have h1 := hJ u hu
      simp only [ActualConductorSieve.dyadNonprincipal, Set.mem_setOf_eq] at h1
      rw [if_pos h1]
    rw [Finset.sum_congr rfl hc, ← Finset.sum_coe_sort J]
    exact hgen {x // x ∈ J} (fun u => (D.omega u.1).character) U N T b hU hN hT
      (hSieve J hJ) hsupp
  have hdyad : ∀ u : D.Row,
      (if u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (D.omega u).character I) N T else 0) ≠ 0 →
      u ∈ ActualConductorSieve.dyadNonprincipal D U := by
    intro u hu
    by_contra hn
    apply hu
    have hn' : ¬ (u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U) := by
      simpa [ActualConductorSieve.dyadNonprincipal] using hn
    rw [if_neg hn']
  unfold rowMaximalSum
  by_cases hfin : (Function.support fun u : D.Row =>
      if u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (D.omega u).character I) N T else 0).Finite
  · have hsub : Function.support (fun u : D.Row =>
        if u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
          detectorHeightPrefixMaximum F b (fun I => (D.omega u).character I) N T else 0) ⊆
        ↑hfin.toFinset :=
      fun u hu => Finset.mem_coe.2 ((Set.Finite.mem_toFinset hfin).2 hu)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    exact hJsum _ (fun u hu => hdyad u (Function.mem_support.1 ((Set.Finite.mem_toFinset hfin).1 hu)))
  · rw [finsum_of_infinite_support hfin]
    exact hK

end

end DedekindZetaZeroFree.Quantitative.DetectorSieve
