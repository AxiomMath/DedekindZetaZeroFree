module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.DyadicPrefixMaxima
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorBoundsAndDampedTails
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.FinitePolynomialMaximalEstimate

@[expose] public section

namespace DedekindZetaZeroFree.DetectorMaximalIdealAdapter
noncomputable section
open scoped BigOperators NumberField Classical

def dyad (F : Type) [Field F] [NumberField F] (N : ℝ) : Finset (Ideal (𝓞 F)) :=
  ((Detector.ideals_bounded_norm_finite F (2 * N)).toFinset).filter
    (fun J => N < (Ideal.absNorm J : ℝ))

@[simp] lemma mem_dyad (F : Type) [Field F] [NumberField F] (N : ℝ)
    (J : Ideal (𝓞 F)) : J ∈ dyad F N ↔
    J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N := by
  simp only [dyad, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  tauto

private lemma sorted_equiv {α : Type*} [Fintype α] (f : α → ℝ) :
    ∃ e : Fin (Fintype.card α) ≃ α, Monotone (fun k => f (e k)) := by
  obtain ⟨ord, hf, _⟩ := (monovary_self f).exists_monotone
  letI := ord
  let e := Fintype.orderIsoFinOfCardEq α rfl
  exact ⟨e.toEquiv, hf.comp e.monotone⟩

lemma exists_sortedEnumeration (F : Type) [Field F] [NumberField F] (N : ℝ) :
    ∃ e : Fin (dyad F N).card ≃ dyad F N,
      Monotone (fun k => (Ideal.absNorm (e k).val : ℝ)) := by
  have h := sorted_equiv (fun J : dyad F N => (Ideal.absNorm J.val : ℝ))
  rw [Fintype.card_coe] at h
  exact h

def enumeration (F : Type) [Field F] [NumberField F] (N : ℝ) :
    Fin (dyad F N).card ≃ dyad F N :=
  (exists_sortedEnumeration F N).choose

lemma enumeration_monotone (F : Type) [Field F] [NumberField F] (N : ℝ) :
    Monotone (fun k => (Ideal.absNorm (enumeration F N k).val : ℝ)) :=
  (exists_sortedEnumeration F N).choose_spec

lemma sum_enumeration (F : Type) [Field F] [NumberField F] (N : ℝ)
    {M : Type*} [AddCommMonoid M] (f : Ideal (𝓞 F) → M) :
    (∑ k : Fin (dyad F N).card, f (enumeration F N k).val) =
      ∑ J ∈ dyad F N, f J := by
  exact ((enumeration F N).sum_comp (fun J : dyad F N => f J.val)).trans
    (Finset.sum_coe_sort _ _)

lemma coefficientMass_eq (F : Type) [Field F] [NumberField F]
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ) :
    (∑ᶠ J : Ideal (𝓞 F),
      if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N
        then ‖b J‖ ^ 2 else 0) =
      ∑ k : Fin (dyad F N).card, ‖b (enumeration F N k).val‖ ^ 2 := by
  rw [sum_enumeration F N (fun J => ‖b J‖ ^ 2)]
  rw [finsum_eq_sum_of_support_subset _ (s := dyad F N)]
  · apply Finset.sum_congr rfl
    intro J hJ
    simp [(mem_dyad F N J).mp hJ]
  · intro J hJ
    by_contra h
    simp only [Function.mem_support] at hJ
    simp [(mem_dyad F N J).not.mp h] at hJ

lemma norm_pos (F : Type) [Field F] [NumberField F] (N : ℝ)
    (k : Fin (dyad F N).card) :
    0 < (Ideal.absNorm (enumeration F N k).val : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr ((mem_dyad F N _).mp (enumeration F N k).property).1)

lemma cpow_eq_phase (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-Complex.I * (t : ℂ)) =
      DetectorMaximalFiniteHeight.phase (n : ℝ) t := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.ne_of_gt hn)]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).symm
  rw [hlog]
  unfold DetectorMaximalFiniteHeight.phase
  congr 1
  ring

lemma cutoff_eq_prefix (F : Type) [Field F] [NumberField F] (N : ℝ)
    (b ω : Ideal (𝓞 F) → ℂ) (y t : ℝ) (hy : y ≤ 2 * N) :
    ∃ l : Fin ((dyad F N).card + 1),
      (∑ᶠ J : Ideal (𝓞 F),
        if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y
          then b J * ω J * (Ideal.absNorm J : ℂ) ^ (-Complex.I * (t : ℂ)) else 0) =
      detector_prefixSum (fun k => ω (enumeration F N k).val)
        (fun k => b (enumeration F N k).val *
          DetectorMaximalFiniteHeight.phase (Ideal.absNorm (enumeration F N k).val : ℝ) t) l := by
  let q := fun k => (Ideal.absNorm (enumeration F N k).val : ℝ)
  obtain ⟨l, hl⟩ := detector_normCutoff_eq_prefix (dyad F N).card q
    (enumeration_monotone F N) y
  refine ⟨l, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := dyad F N)]
  · rw [← sum_enumeration F N]
    unfold detector_prefixSum
    apply Finset.sum_congr rfl
    intro k _
    have hk := (mem_dyad F N _).mp (enumeration F N k).property
    have hkl : q k ≤ y ↔ k.val < l.val := by
      have := congr_arg (fun s => k ∈ s) hl
      exact Iff.of_eq (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this)
    have hc : ((enumeration F N k).val ≠ ⊥ ∧
        N < (Ideal.absNorm (enumeration F N k).val : ℝ) ∧
        (Ideal.absNorm (enumeration F N k).val : ℝ) ≤ y) ↔ q k ≤ y :=
      ⟨fun h => h.2.2, fun h => ⟨hk.1, hk.2.1, h⟩⟩
    simp only [hc, hkl]
    by_cases h : k.val < l.val
    · simp only [if_pos h]
      rw [cpow_eq_phase _ (by exact_mod_cast norm_pos F N k)]
      ring
    · simp [h]
  · intro J hJ
    by_contra h
    have hbad : ¬ (J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y) := by
      intro hgood
      exact h ((mem_dyad F N J).mpr ⟨hgood.1, hgood.2.1, hgood.2.2.trans hy⟩)
    simp [Function.mem_support, hbad] at hJ

def extend (F : Type) [Field F] [NumberField F] (N : ℝ)
    (c : Fin (dyad F N).card → ℂ) (J : Ideal (𝓞 F)) : ℂ :=
  if h : J ∈ dyad F N then c ((enumeration F N).symm ⟨J, h⟩) else 0

lemma extend_zero (F : Type) [Field F] [NumberField F] (N : ℝ)
    (c : Fin (dyad F N).card → ℂ) (J : Ideal (𝓞 F)) (hJ : J ∉ dyad F N) :
    extend F N c J = 0 := by simp [extend, hJ]

@[simp] lemma extend_enumeration (F : Type) [Field F] [NumberField F] (N : ℝ)
    (c : Fin (dyad F N).card → ℂ) (k : Fin (dyad F N).card) :
    extend F N c (enumeration F N k).val = c k := by
  simp [extend, (enumeration F N k).property]

lemma ball_sum_eq (F : Type) [Field F] [NumberField F] (N : ℝ)
    {M : Type*} [AddCommMonoid M] (f : Ideal (𝓞 F) → M)
    (hf : ∀ J, J ∉ dyad F N → f J = 0) :
    (∑ᶠ J : Ideal (𝓞 F), if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then f J else 0) =
      ∑ k : Fin (dyad F N).card, f (enumeration F N k).val := by
  rw [sum_enumeration F N f]
  rw [finsum_eq_sum_of_support_subset _ (s := dyad F N)]
  · apply Finset.sum_congr rfl
    intro J hJ
    have h := (mem_dyad F N J).mp hJ
    simp [h.1, h.2.2]
  · intro J hJ
    by_contra h
    simp [Function.mem_support, hf J h] at hJ

lemma operator_transfer (F : Type) [Field F] [NumberField F]
    (ι : Type*) [Fintype ι] (ω : ι → Ideal (𝓞 F) → ℂ) (N K : ℝ)
    (hop : ∀ c : Ideal (𝓞 F) → ℂ, (∀ J, J ∉ dyad F N → c J = 0) →
      (∑ i, ‖∑ᶠ J : Ideal (𝓞 F),
        if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then c J * ω i J else 0‖ ^ 2) ≤
      K * (∑ᶠ J : Ideal (𝓞 F),
        if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then ‖c J‖ ^ 2 else 0)) :
    ∀ c : Fin (dyad F N).card → ℂ,
      (∑ i, ‖∑ k, ω i (enumeration F N k).val * c k‖ ^ 2) ≤ K * ∑ k, ‖c k‖ ^ 2 := by
  intro c
  have h := hop (extend F N c) (extend_zero F N c)
  have he : ∀ i, (∑ᶠ J : Ideal (𝓞 F),
      if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then extend F N c J * ω i J else 0) =
      ∑ k, ω i (enumeration F N k).val * c k := by
    intro i
    rw [ball_sum_eq F N _ (fun J hJ => by rw [extend_zero F N c J hJ, zero_mul])]
    simp [mul_comm]
  have hm : (∑ᶠ J : Ideal (𝓞 F),
      if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then ‖extend F N c J‖ ^ 2 else 0) =
      ∑ k, ‖c k‖ ^ 2 := by
    rw [ball_sum_eq F N _ (fun J hJ => by rw [extend_zero F N c J hJ]; simp)]
    simp
  simpa only [he, hm] using h

lemma prefixMaximum_le (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N t : ℝ) (hN : 2 ≤ N) :
    DetectorMaximalExpressions.prefixMaximum F b ω N t ≤
      detector_prefixMaxSq (fun k => ω (enumeration F N k).val)
        (fun k => b (enumeration F N k).val *
          DetectorMaximalFiniteHeight.phase (Ideal.absNorm (enumeration F N k).val : ℝ) t) := by
  apply csSup_le
  · exact ⟨‖DetectorMaximalExpressions.dyadicPrefix F b ω N N t‖ ^ 2,
      N, ⟨le_rfl, by linarith⟩, rfl⟩
  · rintro v ⟨y, hy, rfl⟩
    obtain ⟨l, hl⟩ := cutoff_eq_prefix F N b ω y t hy.2
    change ‖_‖ ^ 2 ≤ _
    unfold DetectorMaximalExpressions.dyadicPrefix
    rw [hl]
    exact Finset.le_sup' (f := fun l => ‖detector_prefixSum _ _ l‖ ^ 2)
      (Finset.mem_univ l)

lemma heightMaximum_le (F : Type) [Field F] [NumberField F]
    (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) (hN : 2 ≤ N) (hT : 0 ≤ T) :
    DetectorMaximalExpressions.heightMaximum F b ω N T ≤
      sSup ((fun t => detector_prefixMaxSq (fun k => ω (enumeration F N k).val)
        (fun k => b (enumeration F N k).val *
          DetectorMaximalFiniteHeight.phase (Ideal.absNorm (enumeration F N k).val : ℝ) t)) ''
        Set.Icc (-T) T) := by
  let P := fun (l : Fin ((dyad F N).card + 1)) t =>
    detector_prefixSum (fun k => ω (enumeration F N k).val)
      (fun k => b (enumeration F N k).val *
        DetectorMaximalFiniteHeight.phase (Ideal.absNorm (enumeration F N k).val : ℝ) t) l
  have hc : Continuous (DetectorMaximalFiniteHeight.maxSq P) :=
    DetectorMaximalFiniteHeight.maxSq_continuous P (fun l =>
      (DetectorMaximalFiniteHeight.prefix_contDiff _ _ _ l).continuous)
  have hb : BddAbove ((DetectorMaximalFiniteHeight.maxSq P) '' Set.Icc (-T) T) :=
    (isCompact_Icc.image hc).bddAbove
  apply csSup_le
  · exact ⟨DetectorMaximalExpressions.prefixMaximum F b ω N 0,
      0, ⟨by linarith, hT⟩, rfl⟩
  · rintro v ⟨t, ht, rfl⟩
    exact (prefixMaximum_le F b ω N t hN).trans (le_csSup hb ⟨t, ht, rfl⟩)

theorem ideal_operator_maximal :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type) [Field F] [NumberField F]
      (ι : Type*) [Fintype ι] (ω : ι → Ideal (𝓞 F) → ℂ) (N T K L : ℝ),
      2 ≤ N → 0 ≤ T → 0 ≤ K → 0 ≤ L →
      (∀ J ∈ dyad F N, |Real.log (Ideal.absNorm J : ℝ)| ≤ L) →
      (∀ c : Ideal (𝓞 F) → ℂ, (∀ J, J ∉ dyad F N → c J = 0) →
        (∑ i, ‖∑ᶠ J : Ideal (𝓞 F),
          if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then c J * ω i J else 0‖ ^ 2) ≤
        K * (∑ᶠ J : Ideal (𝓞 F),
          if J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then ‖c J‖ ^ 2 else 0)) →
      ∀ b : Ideal (𝓞 F) → ℂ,
        (∑ i, DetectorMaximalExpressions.heightMaximum F b (ω i) N T) ≤
          C * (T + 1) * K * (1 + Real.log ((dyad F N).card + 1)) ^ 2 *
            (1 + L ^ 2) * DetectorMaximalExpressions.mass F b N := by
  obtain ⟨C, hC, h⟩ := DetectorMaximalFiniteHeight.finite_polynomial_maximal_universe
  refine ⟨C, hC, ?_⟩
  intro F _ _ ι _ ω N T K L hN hT hK hL hq hop b
  have hh := h (dyad F N).card ι (fun i k => ω i (enumeration F N k).val)
    (fun k => (Ideal.absNorm (enumeration F N k).val : ℝ)) K L T hK hL hT
    (fun k => hq _ (enumeration F N k).property) (operator_transfer F ι ω N K hop)
    (fun k => b (enumeration F N k).val)
  rw [← coefficientMass_eq F b N] at hh
  exact (Finset.sum_le_sum (fun i _ => heightMaximum_le F b (ω i) N T hN hT)).trans hh

lemma log_bound (F : Type) [Field F] [NumberField F] (N : ℝ) (hN : 2 ≤ N) :
    ∀ J ∈ dyad F N, |Real.log (Ideal.absNorm J : ℝ)| ≤ Real.log (2 * N) := by
  intro J hJ
  have hj := (mem_dyad F N J).mp hJ
  have hn : (1 : ℝ) ≤ Ideal.absNorm J := by linarith [hj.2.1]
  rw [abs_of_nonneg (Real.log_nonneg hn)]
  exact Real.log_le_log (by linarith) hj.2.2

lemma card_bound (F : Type) [Field F] [NumberField F] :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 2 ≤ N → (dyad F N).card ≤ D * N := by
  obtain ⟨D, hD, h⟩ := Detector.ideal_norm_summation_bounds F
  refine ⟨2 * D, by positivity, ?_⟩
  intro N hN
  have hc := (h (2 * N) (by linarith)).1
  have hcard : (dyad F N).card ≤ Detector.idealNormCount F (2 * N) := by
    unfold dyad Detector.idealNormCount
    rw [Set.ncard_eq_toFinset_card _ (Detector.ideals_bounded_norm_finite F (2 * N))]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hcast : ((dyad F N).card : ℝ) ≤ Detector.idealNormCount F (2 * N) :=
    Nat.cast_le.mpr hcard
  nlinarith

end
end DedekindZetaZeroFree.DetectorMaximalIdealAdapter
