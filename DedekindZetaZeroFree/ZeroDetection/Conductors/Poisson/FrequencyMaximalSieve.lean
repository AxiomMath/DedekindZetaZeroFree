module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.DenominatorIdentification

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDetectorMaximal31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowMaximalSum (U N T : ℝ) (b : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ᶠ u : Frequency D.recipe,
    if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
        frequencyNorm D.recipe u < 2 * U then
      detectorHeightPrefixMaximum F b (fun J => (FixedData.primMinus D u).character J) N T
    else 0

private theorem finite_ideals_absNorm_le (F : Type) [Field F] [NumberField F] (M : ℝ) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le ⌊M⌋₊).subset ?_
  rintro I ⟨-, hI⟩
  exact Nat.le_floor hI

theorem detectorHeightPrefixMaximum_nonneg' (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) :
    0 ≤ detectorHeightPrefixMaximum F b ω N T := by
  unfold detectorHeightPrefixMaximum
  apply Real.sSup_nonneg
  rintro v ⟨t, -, rfl⟩
  unfold detectorPrefixMaximum
  apply Real.sSup_nonneg
  rintro w ⟨y, -, rfl⟩
  positivity

theorem detector_maximal_sieve :
    ∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N T : ℝ) (b : Ideal (𝓞 F) → ℂ), 2 ≤ U → 2 ≤ N → 1 ≤ T →
        detectorDyadicSupport F b N →
        rowMaximalSum D U N T b ≤
          C * (T + 1) * (N + U ^ 2) * (N * U) ^ ε * Real.log (2 * N) ^ Clog *
            detectorDyadicCoefficientMass F b N := by
  refine ⟨0, le_rfl, fun ε hε => ?_⟩
  obtain ⟨C₀, hC₀, hact⟩ :=
    RawDenominatorPackage31.minus_conductor_sieve_finsum D (ε / 2) (by linarith)
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
  have hSieve : ∀ J : Finset (Frequency D.recipe),
      (∀ u ∈ J, U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U) →
      ∀ (M : ℝ) (c : Ideal (𝓞 F) → ℂ), 2 ≤ M →
        (∀ I, ¬ (I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M) → c I = 0) →
        (∑ u : {x // x ∈ J}, ‖∑ᶠ I : Ideal (𝓞 F),
            if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then
              c I * (FixedData.primMinus D u.1).character I else 0‖ ^ 2) ≤
          C₀ * (M + U ^ 2) * (M * U) ^ (ε / 2) *
            (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then ‖c I‖ ^ 2 else 0) := by
    intro J hJ M c hM _hc
    set c' : Ideal (𝓞 F) → ℂ :=
      fun I => if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then c I else 0 with hc'
    have e1 : ∀ u : Frequency D.recipe,
        (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then
            c I * (FixedData.primMinus D u).character I else 0) =
          ∑ᶠ I : Ideal (𝓞 F), c' I * (FixedData.primMinus D u).character I := by
      intro u
      refine finsum_congr fun I => ?_
      simp only [hc']
      split_ifs <;> simp
    have e2 : (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then ‖c I‖ ^ 2 else 0) =
        ∑ᶠ I : Ideal (𝓞 F), ‖c' I‖ ^ 2 := by
      refine finsum_congr fun I => ?_
      simp only [hc']
      split_ifs <;> simp
    have hb' : ∀ I, c' I ≠ 0 → I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M := by
      intro I hI
      by_contra h
      apply hI
      simp only [hc']
      rw [if_neg h]
    calc (∑ u : {x // x ∈ J}, ‖∑ᶠ I : Ideal (𝓞 F),
            if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M then
              c I * (FixedData.primMinus D u.1).character I else 0‖ ^ 2)
        = ∑ u : {x // x ∈ J}, ‖∑ᶠ I : Ideal (𝓞 F),
            c' I * (FixedData.primMinus D u.1).character I‖ ^ 2 :=
          Finset.sum_congr rfl (fun u _ => by rw [e1 u.1])
      _ = ∑ u ∈ J, ‖∑ᶠ I : Ideal (𝓞 F), c' I * (FixedData.primMinus D u).character I‖ ^ 2 :=
          Finset.sum_coe_sort J
            (fun u => ‖∑ᶠ I : Ideal (𝓞 F), c' I * (FixedData.primMinus D u).character I‖ ^ 2)
      _ ≤ C₀ * (M + U ^ 2) * (M * U) ^ (ε / 2) * ∑ᶠ I : Ideal (𝓞 F), ‖c' I‖ ^ 2 :=
          hact U M hU hM J hJ c' hb'
      _ = _ := by rw [e2]
  have hJsum : ∀ J : Finset (Frequency D.recipe),
      (∀ u ∈ J, u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
        frequencyNorm D.recipe u < 2 * U) →
      ∑ u ∈ J, (if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
          frequencyNorm D.recipe u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
        else 0) ≤
        C * (T + 1) * (N + U ^ 2) * (N * U) ^ ε * detectorDyadicCoefficientMass F b N := by
    intro J hJ
    have hc : ∀ u ∈ J, (if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
          frequencyNorm D.recipe u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
        else 0) =
        detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T := by
      intro u hu
      rw [if_pos (hJ u hu)]
    rw [Finset.sum_congr rfl hc, ← Finset.sum_coe_sort J]
    exact hgen {x // x ∈ J} (fun u => fun I => (FixedData.primMinus D u.1).character I)
      U N T b hU hN hT (hSieve J (fun u hu => (hJ u hu).2)) hsupp
  unfold rowMaximalSum
  by_cases hfin : (Function.support fun u : Frequency D.recipe =>
      if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
          frequencyNorm D.recipe u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
      else 0).Finite
  · have hsub : Function.support (fun u : Frequency D.recipe =>
        if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
            frequencyNorm D.recipe u < 2 * U then
          detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
        else 0) ⊆ ↑hfin.toFinset :=
      fun u hu => Finset.mem_coe.2 ((Set.Finite.mem_toFinset hfin).2 hu)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine hJsum _ (fun u hu => ?_)
    have h1 := (Set.Finite.mem_toFinset hfin).1 hu
    by_contra hn
    exact h1 (if_neg hn)
  · rw [finsum_of_infinite_support hfin]
    exact hK

theorem card_dyad_le_rowMaximalSum (U N T δ : ℝ) (b : Ideal (𝓞 F) → ℂ) (hU : 1 ≤ U)
    (hδ : 0 ≤ δ) (s : Set (Frequency D.recipe))
    (hs : ∀ u ∈ s, u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
      frequencyNorm D.recipe u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (FixedData.primMinus D u).character J) N T) :
    s.Finite ∧ (s.ncard : ℝ) * δ ≤ rowMaximalSum D U N T b := by
  obtain ⟨K, hK, hcount⟩ := RawFrequencyCount.frequency_dyad_count_nonprincipal D.recipe
  obtain ⟨hfin, -⟩ := hcount U hU
  have hsub : s ⊆ {u : Frequency D.recipe | u ≠ principalFrequency D.recipe ∧
      U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U} :=
    fun u hu => ⟨(hs u hu).1, (hs u hu).2.1, (hs u hu).2.2.1⟩
  have hsfin : s.Finite := hfin.subset hsub
  refine ⟨hsfin, ?_⟩
  have hsupp : Function.support (fun u : Frequency D.recipe =>
      if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
          frequencyNorm D.recipe u < 2 * U then
        detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
      else 0) ⊆ ↑hfin.toFinset := by
    intro u hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    exact hu (if_neg h)
  unfold rowMaximalSum
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc (s.ncard : ℝ) * δ = ∑ _u ∈ hsfin.toFinset, δ := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card s hsfin]
    _ ≤ ∑ u ∈ hsfin.toFinset,
        (if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
            frequencyNorm D.recipe u < 2 * U then
          detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
        else 0) := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hu' : u ∈ s := (Set.Finite.mem_toFinset hsfin).1 hu
        obtain ⟨h1, h2, h3, h4⟩ := hs u hu'
        rw [if_pos ⟨h1, h2, h3⟩]
        exact h4
    _ ≤ ∑ u ∈ hfin.toFinset,
        (if u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
            frequencyNorm D.recipe u < 2 * U then
          detectorHeightPrefixMaximum F b (fun I => (FixedData.primMinus D u).character I) N T
        else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => ?_)
        · intro u hu
          rw [Set.Finite.mem_toFinset] at hu ⊢
          exact hsub hu
        · split_ifs
          · exact detectorHeightPrefixMaximum_nonneg' b _ N T
          · exact le_rfl

end

end DedekindZetaZeroFree.Quantitative.RawDetectorMaximal31
