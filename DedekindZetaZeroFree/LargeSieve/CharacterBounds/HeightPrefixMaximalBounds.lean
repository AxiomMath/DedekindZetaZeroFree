module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.IdealOperatorMaximalEstimate
public import DedekindZetaZeroFree.LargeSieve.Exponents.MaximalEstimateLogAbsorption

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

def detectorDyadicPrefix (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N y t : ℝ) : ℂ :=
  ∑ᶠ J : Ideal (𝓞 F),
    if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y then
      b J * ω J * (Ideal.absNorm J : ℂ) ^ (-Complex.I * (t : ℂ))
    else 0

def detectorDyadicSupport (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) : Prop :=
  ∀ J, ¬ (J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N) →
    b J = 0

def detectorDyadicCoefficientMass (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) : ℝ :=
  ∑ᶠ J : Ideal (𝓞 F),
    if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then
      ‖b J‖ ^ 2 else 0

def detectorPrefixMaximum (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ y ∈ Set.Icc N (2 * N),
    v = ‖detectorDyadicPrefix F b ω N y t‖ ^ 2}

def detectorHeightPrefixMaximum (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ t ∈ Set.Icc (-T) T, v = detectorPrefixMaximum F b ω N t}

theorem detectorDyadicCoefficientMass_expression (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) :
    detectorDyadicCoefficientMass F b N = DetectorMaximalExpressions.mass F b N := rfl

theorem detectorHeightPrefixMaximum_expression (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) :
    detectorHeightPrefixMaximum F b ω N T = DetectorMaximalExpressions.heightMaximum F b ω N T := rfl

theorem detectorDyadicCoefficientMass_nonneg (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) : 0 ≤ detectorDyadicCoefficientMass F b N := by
  apply finsum_nonneg
  intro J
  split_ifs <;> positivity

theorem ball_finite (F : Type) [Field F] [NumberField F] (X : ℝ) :
    {J : Ideal (𝓞 F) | J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ X}.Finite := by
  apply (Ideal.finite_setOfPred_absNorm_le ⌈X⌉₊).subset
  intro J hJ
  exact Nat.cast_le.mp (hJ.2.trans (Nat.le_ceil X))
def ball (F : Type) [Field F] [NumberField F] (N : ℝ) : Finset (Ideal (𝓞 F)) :=
  (ball_finite F (2 * N)).toFinset
def active (F : Type) [Field F] [NumberField F] (N y : ℝ) :=
  (ball F N).filter (fun J => N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y)
def poly (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (B : Finset (Ideal (𝓞 F))) (t : ℝ) : ℂ :=
  ∑ J ∈ B, b J * ω J * (Ideal.absNorm J : ℂ) ^ (-Complex.I * (t : ℂ))
private theorem prefix_eq (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N y t : ℝ) (hy : y ≤ 2 * N) :
    detectorDyadicPrefix F b ω N y t = poly F b ω (active F N y) t := by
  unfold detectorDyadicPrefix poly active
  rw [finsum_eq_sum_of_support_subset _ (s := ball F N)]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J hJ
    have hJ' : J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N := by
      simpa [ball] using hJ
    simp [hJ'.1]
  · intro J hJ
    simp only [Function.mem_support, ne_eq] at hJ
    have h : J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y := by
      by_contra hc
      simp [hc] at hJ
    simpa [ball] using And.intro h.1 (h.2.2.trans hy)
private theorem poly_cont (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (B : Finset (Ideal (𝓞 F)))
    (hB : ∀ J ∈ B, J ≠ ⊥) : Continuous (poly F b ω B) := by
  unfold poly
  apply continuous_finset_sum
  intro J hJ
  apply Continuous.mul continuous_const
  apply Continuous.const_cpow
  · fun_prop
  · left
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr (hB J hJ))
def prefixSets (F : Type) [Field F] [NumberField F] (N : ℝ) : Set (Finset (Ideal (𝓞 F))) :=
  active F N '' Set.Icc N (2 * N)
private theorem sets_finite (F : Type) [Field F] [NumberField F] (N : ℝ) :
    (prefixSets F N).Finite := by
  apply (ball F N).powerset.finite_toSet.subset
  rintro B ⟨y, hy, rfl⟩
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
private theorem sets_nonempty (F : Type) [Field F] [NumberField F] (N : ℝ) (hN : 2 ≤ N) :
    (prefixSets F N).Nonempty := by
  exact ⟨active F N N, N, ⟨le_rfl, by linarith⟩, rfl⟩
private theorem values_eq (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N t : ℝ) :
    {v : ℝ | ∃ y ∈ Set.Icc N (2 * N), v = ‖detectorDyadicPrefix F b ω N y t‖ ^ 2} =
      (fun B => ‖poly F b ω B t‖ ^ 2) '' prefixSets F N := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨active F N y, ⟨y, hy, rfl⟩, by rw [prefix_eq F b ω N y t hy.2]⟩
  · rintro ⟨B, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [prefix_eq F b ω N y t hy.2]⟩

theorem detectorPrefixMaximum_attained (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N t : ℝ) (hN : 2 ≤ N) :
    ∃ y ∈ Set.Icc N (2 * N),
      detectorPrefixMaximum F b ω N t = ‖detectorDyadicPrefix F b ω N y t‖ ^ 2 ∧
      ∀ z ∈ Set.Icc N (2 * N),
        ‖detectorDyadicPrefix F b ω N z t‖ ^ 2 ≤ detectorPrefixMaximum F b ω N t := by
  have hv := values_eq F b ω N t
  have hf : {v : ℝ | ∃ y ∈ Set.Icc N (2 * N), v = ‖detectorDyadicPrefix F b ω N y t‖ ^ 2}.Finite := by
    rw [hv]
    exact (sets_finite F N).image _
  have hn : {v : ℝ | ∃ y ∈ Set.Icc N (2 * N), v = ‖detectorDyadicPrefix F b ω N y t‖ ^ 2}.Nonempty := by
    rw [hv]
    exact (sets_nonempty F N hN).image _
  obtain ⟨y, hy, he⟩ := hf.isCompact.sSup_mem hn
  refine ⟨y, hy, he, ?_⟩
  intro z hz
  exact le_csSup hf.bddAbove ⟨z, hz, rfl⟩

private theorem max_cont (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N : ℝ) (hN : 2 ≤ N) :
    Continuous (detectorPrefixMaximum F b ω N) := by
  let S := (sets_finite F N).toFinset
  have hS : S.Nonempty := by
    simpa [S] using sets_nonempty F N hN
  have he : detectorPrefixMaximum F b ω N =
      fun t => S.sup' hS (fun B => ‖poly F b ω B t‖ ^ 2) := by
    funext t
    rw [Finset.sup'_eq_csSup_image]
    simp only [S, Set.Finite.coe_toFinset]
    exact values_eq F b ω N t ▸ rfl
  rw [he]
  apply Continuous.finset_sup'_apply hS
  intro B hB
  apply Continuous.pow
  apply Continuous.norm
  apply poly_cont F b ω B
  intro J hJ
  have hb : B ∈ prefixSets F N := by simpa [S] using hB
  obtain ⟨y, hy, rfl⟩ := hb
  have hj : J ∈ ball F N := (Finset.mem_filter.mp hJ).1
  exact (show J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N by simpa [ball] using hj).1

theorem detectorHeightPrefixMaximum_attained (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) (hN : 2 ≤ N) (hT : 1 ≤ T) :
    ∃ t ∈ Set.Icc (-T) T,
      detectorHeightPrefixMaximum F b ω N T = detectorPrefixMaximum F b ω N t ∧
      ∀ u ∈ Set.Icc (-T) T,
        detectorPrefixMaximum F b ω N u ≤ detectorHeightPrefixMaximum F b ω N T := by
  obtain ⟨t, ht, he, hm⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (f := detectorPrefixMaximum F b ω N) (Set.nonempty_Icc.mpr (by linarith : -T ≤ T))
    (max_cont F b ω N hN).continuousOn
  have hset : {v : ℝ | ∃ t ∈ Set.Icc (-T) T, v = detectorPrefixMaximum F b ω N t} =
      (detectorPrefixMaximum F b ω N) '' Set.Icc (-T) T := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    exact exists_congr (fun t => and_congr_right (fun ht => eq_comm))
  refine ⟨t, ht, ?_, ?_⟩
  · change sSup {v : ℝ | ∃ t ∈ Set.Icc (-T) T, v = detectorPrefixMaximum F b ω N t} = _
    rw [hset]
    exact he
  · intro u hu
    rw [detectorHeightPrefixMaximum, hset, he]
    exact hm u hu

theorem detector_maximal_sieve (F : Type) [Field F] [NumberField F]
    (ε C₀ : ℝ) (hε : 0 < ε) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type*) [Fintype ι] (ω : ι → Ideal (𝓞 F) → ℂ)
        (U N T : ℝ) (b : Ideal (𝓞 F) → ℂ),
        2 ≤ U → 2 ≤ N → 1 ≤ T →
        (∀ (M : ℝ) (c : Ideal (𝓞 F) → ℂ), 2 ≤ M →
          (∀ J, ¬ (J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ M) → c J = 0) →
          (∑ i : ι, ‖∑ᶠ J : Ideal (𝓞 F),
            if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ M then c J * ω i J else 0‖ ^ 2) ≤
            C₀ * (M + U ^ 2) * (M * U) ^ (ε / 2) *
              (∑ᶠ J : Ideal (𝓞 F),
                if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ M then ‖c J‖ ^ 2 else 0)) →
        detectorDyadicSupport F b N →
        (∑ i : ι, detectorHeightPrefixMaximum F b (ω i) N T) ≤
          C * (T + 1) * (N + U ^ 2) * (N * U) ^ ε *
            detectorDyadicCoefficientMass F b N := by
  obtain ⟨A, hA, hmax⟩ := DetectorMaximalIdealAdapter.ideal_operator_maximal
  obtain ⟨D, hD, hcard⟩ := DetectorMaximalIdealAdapter.card_bound F
  obtain ⟨B, hB, habs⟩ := LogAbsorption.log_absorption_linear_two D hD.le hε
  refine ⟨2 * A * C₀ * B, by positivity, ?_⟩
  intro ι _ ω U N T b hU hN hT hSieve _hsupport
  have hop : ∀ c : Ideal (𝓞 F) → ℂ,
      (∀ J, J ∉ DetectorMaximalIdealAdapter.dyad F N → c J = 0) →
      (∑ i : ι, ‖∑ᶠ J : Ideal (𝓞 F),
        if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then c J * ω i J else 0‖ ^ 2) ≤
          C₀ * (2 * N + U ^ 2) * (2 * N * U) ^ (ε / 2) *
          (∑ᶠ J : Ideal (𝓞 F),
            if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then ‖c J‖ ^ 2 else 0) := by
    intro c hc
    apply hSieve (2 * N) c (by linarith)
    intro J hJ
    apply hc J
    intro hd
    have hj := (DetectorMaximalIdealAdapter.mem_dyad F N J).mp hd
    exact hJ ⟨hj.1, hj.2.2⟩
  have hh := hmax F ι ω N T (C₀ * (2 * N + U ^ 2) * (2 * N * U) ^ (ε / 2))
    (Real.log (2 * N)) hN (by linarith) (by positivity)
    (Real.log_nonneg (by linarith)) (DetectorMaximalIdealAdapter.log_bound F N hN) hop b
  simp only [← detectorHeightPrefixMaximum_expression,
    ← detectorDyadicCoefficientMass_expression] at hh
  have ha := habs (DetectorMaximalIdealAdapter.dyad F N).card N U hN hU (hcard N hN)
  have hn : 0 ≤ A * C₀ * (T + 1) * (2 * N + U ^ 2) * detectorDyadicCoefficientMass F b N :=
    mul_nonneg (by positivity) (detectorDyadicCoefficientMass_nonneg F b N)
  have he := mul_le_mul_of_nonneg_left ha hn
  have hstep : (∑ i, detectorHeightPrefixMaximum F b (ω i) N T) ≤
      A * C₀ * B * (T + 1) * (2 * N + U ^ 2) * (N * U) ^ ε *
        detectorDyadicCoefficientMass F b N := by
    apply hh.trans
    convert he using 1 <;> ring
  have hc : 2 * N + U ^ 2 ≤ 2 * (N + U ^ 2) := by nlinarith [sq_nonneg U]
  have hnonneg : 0 ≤ A * C₀ * B * (T + 1) * (N * U) ^ ε *
      detectorDyadicCoefficientMass F b N :=
    mul_nonneg (by positivity) (detectorDyadicCoefficientMass_nonneg F b N)
  exact hstep.trans (by
    convert mul_le_mul_of_nonneg_left hc hnonneg using 1 <;> ring)

end
end DedekindZetaZeroFree
