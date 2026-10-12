module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

def normBoundedIdeals (F : Type) [Field F] [NumberField F] (X : ℝ) :
    Set (NonzeroIdeal F) :=
  { I | idealNorm I.val ≤ X }

def normDyadicIdeals (F : Type) [Field F] [NumberField F] (C : ℝ) :
    Set (NonzeroIdeal F) :=
  { I | C ≤ idealNorm I.val ∧ idealNorm I.val < 2 * C }

def idealHarmonicSum (A : Set (NonzeroIdeal F)) (X : ℝ) : ℝ :=
  ∑' I : ↥(A ∩ normBoundedIdeals F X), (idealNorm I.val.val)⁻¹

def idealDyadicHarmonicSum (A : Set (NonzeroIdeal F)) (C : ℝ) : ℝ :=
  ∑' I : ↥(A ∩ normDyadicIdeals F C), (idealNorm I.val.val)⁻¹

theorem normBoundedIdeals_finite (F : Type) [Field F] [NumberField F] (X : ℝ) :
    (normBoundedIdeals F X).Finite := by
  refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈X⌉₊).preimage
    Subtype.val_injective.injOn).subset ?_
  intro I hI
  exact_mod_cast (show (Ideal.absNorm I.val : ℝ) ≤ (⌈X⌉₊ : ℝ) from
    hI.trans (Nat.le_ceil X))

theorem normBoundedIdealSubset_finite (A : Set (NonzeroIdeal F)) (X : ℝ) :
    (A ∩ normBoundedIdeals F X).Finite := by
  exact (normBoundedIdeals_finite F X).subset Set.inter_subset_right

theorem normDyadicIdealSubset_finite (A : Set (NonzeroIdeal F)) (C : ℝ) :
    (A ∩ normDyadicIdeals F C).Finite := by
  exact (normBoundedIdeals_finite F (2 * C)).subset (fun I hI => hI.2.2.le)

namespace CountsProof
variable {F : Type} [Field F] [NumberField F]
private theorem linear : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
    ((normBoundedIdeals F X).ncard : ℝ) ≤ K * X := by
  have ht := (NumberField.Ideal.tendsto_norm_le_div_atTop F).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨B, hB⟩ := ht.bddAbove_range
  refine ⟨3 * (max B 1), by positivity, ?_⟩
  intro X hX
  have hfin := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈X⌉₊
  have hc : (normBoundedIdeals F X).ncard ≤
      {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌈X⌉₊}.ncard :=
    Set.ncard_le_ncard_of_injOn Subtype.val (fun I hI => by
      change Ideal.absNorm I.val ≤ ⌈X⌉₊
      exact_mod_cast (show (Ideal.absNorm I.val : ℝ) ≤ (⌈X⌉₊ : ℝ) from hI.trans (Nat.le_ceil X))) Subtype.val_injective.injOn hfin
  have hceil : 0 < (⌈X⌉₊ : ℝ) := lt_of_lt_of_le (by norm_num) (hX.trans (Nat.le_ceil X))
  have hn := hB (Set.mem_range_self ⌈X⌉₊)
  simp only [Function.comp_apply, Nat.card_coe_set_eq] at hn
  have hn' : ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌈X⌉₊}.ncard : ℝ) ≤
      B * (⌈X⌉₊ : ℝ) := by
    apply (div_le_iff₀ hceil).mp
    have he : {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ (⌈X⌉₊ : ℝ)} =
        ↥{I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌈X⌉₊} := by simp only [Nat.cast_le]; rfl
    rw [he, Nat.card_coe_set_eq] at hn
    exact hn
  have hcX : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one (show 0 ≤ X by linarith)
    linarith
  calc _ ≤ ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌈X⌉₊}.ncard : ℝ) := by exact_mod_cast hc
       _ ≤ max B 1 * (⌈X⌉₊ : ℝ) := hn'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hceil.le)
       _ ≤ max B 1 * (2 * X) := mul_le_mul_of_nonneg_left hcX (by positivity)
       _ ≤ 3 * max B 1 * X := by nlinarith [le_max_right B 1]
private theorem norm_pos (I : NonzeroIdeal F) : 0 < Ideal.absNorm I.val :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

private theorem weighted (K : ℝ)
    (hK : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ K * X)
    (u : Finset (NonzeroIdeal F)) (N : ℕ)
    (hN : ∀ I ∈ u, Ideal.absNorm I.val ≤ N)
    (g : ℕ → ℝ) (hg0 : 0 ≤ g) (hg : Antitone g) :
    ∑ I ∈ u, g (Ideal.absNorm I.val - 1) ≤ K * ∑ i ∈ Finset.range N, g i := by
  let f : ℕ → ℝ := fun i => ((u.filter (fun I => Ideal.absNorm I.val - 1 = i)).card : ℝ)
  have hsum (k : ℕ) : ∑ i ∈ Finset.range k, f i =
      ((u.filter (fun I => Ideal.absNorm I.val - 1 < k)).card : ℝ) := by
    simp only [f, ← Finset.sum_boole]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    simp
  have hfc (k : ℕ) (hk : k ≤ N) : ∑ i ∈ Finset.range k, f i ≤
      ∑ i ∈ Finset.range k, K := by
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    by_cases hk0 : k = 0
    · simp [hk0]
    have hsub : (↑(u.filter (fun I => Ideal.absNorm I.val - 1 < k)) : Set (NonzeroIdeal F)) ⊆
        normBoundedIdeals F k := by
      intro I hI
      have hi := (Finset.mem_filter.mp hI).2
      have hp := norm_pos I
      change (Ideal.absNorm I.val : ℝ) ≤ (k : ℝ)
      exact_mod_cast (show Ideal.absNorm I.val ≤ k by omega)
    have hc := Set.ncard_le_ncard hsub (normBoundedIdeals_finite F k)
    have hb := hK k (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0))
    exact (by exact_mod_cast hc : ((u.filter (fun I => Ideal.absNorm I.val - 1 < k)).card : ℝ) ≤
      ((normBoundedIdeals F k).ncard : ℝ)).trans hb
  have he : ∑ I ∈ u, g (Ideal.absNorm I.val - 1) = ∑ i ∈ Finset.range N, f i * g i := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun I : NonzeroIdeal F => Ideal.absNorm I.val - 1)
      (t := Finset.range N) (fun I hI => Finset.mem_range.mpr (by have := hN I hI; have := norm_pos I; omega))]
    apply Finset.sum_congr rfl
    intro i hi
    calc ∑ I ∈ u with Ideal.absNorm I.val - 1 = i, g (Ideal.absNorm I.val - 1)
        = ∑ I ∈ u with Ideal.absNorm I.val - 1 = i, g i := by
            apply Finset.sum_congr rfl
            intro I hI
            rw [(Finset.mem_filter.mp hI).2]
         _ = f i * g i := by simp [f, nsmul_eq_mul]
  rw [he, Finset.mul_sum]
  exact Finset.sum_mul_le_sum_mul_of_sum_range_le hfc hg0 (hg.antitoneOn _)
private theorem summable_norm (s : ℝ) (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal F => Real.rpow (idealNorm I.val) (-s)) := by
  obtain ⟨K, hK0, hK⟩ := linear (F := F)
  let g : ℕ → ℝ := fun i => ((i + 1 : ℕ) : ℝ) ^ (-s)
  have hg0 : 0 ≤ g := fun i => Real.rpow_nonneg (by positivity) _
  have hg : Antitone g := by
    intro i j hij
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.succ_le_succ hij) (by linarith)
  have hgs : Summable g := by
    exact (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).comp_injective (fun i j h => by omega)
  apply summable_of_sum_le (c := K * ∑' i, g i)
    (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro u
  have hw := weighted K hK u (u.sup (fun I => Ideal.absNorm I.val))
    (fun I hI => Finset.le_sup (f := fun J : NonzeroIdeal F => Ideal.absNorm J.val) hI) g hg0 hg
  have he : (fun I : NonzeroIdeal F => g (Ideal.absNorm I.val - 1)) =
      (fun I : NonzeroIdeal F => Real.rpow (idealNorm I.val) (-s)) := by
    funext I
    simp only [g, idealNorm, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (norm_pos I).ne')]
    rfl
  rw [he] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left (hgs.sum_le_tsum (Finset.range _) (fun i _ => hg0 i)) hK0.le)
private theorem harmonic_bound (K : ℝ) (hK0 : 0 < K)
    (hK : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ K * X)
    (A : Set (NonzeroIdeal F)) (X : ℝ) (hX : 1 ≤ X) :
    idealHarmonicSum A X ≤ K * (1 + Real.log X) := by
  let u := (normBoundedIdealSubset_finite A X).toFinset
  have hg : Antitone (fun i : ℕ => ((i + 1 : ℕ) : ℝ)⁻¹) := by
    intro i j hij
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by exact_mod_cast Nat.succ_le_succ hij)
  have hw := weighted K hK u ⌊X⌋₊ (fun I hI => by
    have hb : idealNorm I.val ≤ X := ((Set.Finite.mem_toFinset _).mp hI).2
    exact (Nat.le_floor_iff (by linarith : 0 ≤ X)).mpr hb)
    (fun i : ℕ => ((i + 1 : ℕ) : ℝ)⁻¹) (fun i => by positivity) hg
  have he : ∑ I ∈ u, ((Ideal.absNorm I.val - 1 + 1 : ℕ) : ℝ)⁻¹ = idealHarmonicSum A X := by
    simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (norm_pos _).ne')]
    haveI := (normBoundedIdealSubset_finite A X).fintype
    rw [idealHarmonicSum, tsum_fintype]
    exact (Finset.sum_subtype u (fun I => (Set.Finite.mem_toFinset _)) (fun I => (idealNorm I.val)⁻¹))
  rw [he] at hw
  have hsum : (∑ i ∈ Finset.range ⌊X⌋₊, ((i + 1 : ℕ) : ℝ)⁻¹) = (harmonic ⌊X⌋₊ : ℝ) := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hsum] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log X hX) hK0.le)

private theorem dyadic_bound (K : ℝ) (hK0 : 0 < K)
    (hK : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ K * X)
    (A : Set (NonzeroIdeal F)) (C : ℝ) (hC : 1 ≤ C) :
    idealDyadicHarmonicSum A C ≤ 2 * K := by
  haveI := (normDyadicIdealSubset_finite A C).fintype
  have hc0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hb : ((A ∩ normDyadicIdeals F C).ncard : ℝ) ≤ K * (2 * C) := by
    have hc := Set.ncard_le_ncard (s := A ∩ normDyadicIdeals F C)
      (t := normBoundedIdeals F (2 * C)) (fun I hI => hI.2.2.le)
      (normBoundedIdeals_finite F (2 * C))
    have hc' : ((A ∩ normDyadicIdeals F C).ncard : ℝ) ≤ ((normBoundedIdeals F (2 * C)).ncard : ℝ) := by exact_mod_cast hc
    exact hc'.trans (hK (2 * C) (by linarith))
  calc idealDyadicHarmonicSum A C
      ≤ ∑' I : ↥(A ∩ normDyadicIdeals F C), C⁻¹ := by
        rw [idealDyadicHarmonicSum, tsum_fintype, tsum_fintype]
        exact Finset.sum_le_sum (fun I _ =>
          (inv_le_inv₀ (hc0.trans_le I.property.2.1) hc0).mpr I.property.2.1)
    _ = ((A ∩ normDyadicIdeals F C).ncard : ℝ) * C⁻¹ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    _ ≤ K * (2 * C) * C⁻¹ := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hc0.le)
    _ = 2 * K := by field_simp
private theorem all_bounds :
    ∃ K K' : ℝ, 0 < K ∧ 0 < K' ∧ ∀ A : Set (NonzeroIdeal F),
      (∀ X : ℝ, 1 ≤ X → ((A ∩ normBoundedIdeals F X).ncard : ℝ) ≤ K * X) ∧
      (∀ C : ℝ, 1 ≤ C → idealDyadicHarmonicSum A C ≤ 2 * K) ∧
      (∀ X : ℝ, 1 ≤ X → idealHarmonicSum A X ≤ K' * Real.log (2 * X)) := by
  obtain ⟨K, hK0, hK⟩ := linear (F := F)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, K * (1 + (Real.log 2)⁻¹), hK0, by positivity, ?_⟩
  intro A
  refine ⟨?_, dyadic_bound K hK0 hK A, ?_⟩
  · intro X hX
    have hc := Set.ncard_le_ncard (s := A ∩ normBoundedIdeals F X) Set.inter_subset_right (normBoundedIdeals_finite F X)
    exact (Nat.cast_le.mpr hc).trans (hK X hX)
  · intro X hX
    refine (harmonic_bound K hK0 hK A X hX).trans ?_
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)]
    have hx : 0 ≤ Real.log X := Real.log_nonneg hX
    have hinv := mul_inv_cancel₀ hl.ne'
    nlinarith [mul_nonneg (inv_nonneg.mpr hl.le) hx]
end CountsProof

theorem ideal_counting_harmonic_bounds (F : Type) [Field F] [NumberField F] :
    ∃ K K' : ℝ, 0 < K ∧ 0 < K' ∧
      ∀ A : Set (NonzeroIdeal F),
        (∀ X : ℝ, 1 ≤ X →
          ((A ∩ normBoundedIdeals F X).ncard : ℝ) ≤ K * X) ∧
        (∀ C : ℝ, 1 ≤ C → idealDyadicHarmonicSum A C ≤ 2 * K) ∧
        (∀ X : ℝ, 1 ≤ X → idealHarmonicSum A X ≤ K' * Real.log (2 * X)) := by
  exact CountsProof.all_bounds

theorem ideal_norm_rpow_summable (F : Type) [Field F] [NumberField F]
    (s : ℝ) (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal F => Real.rpow (idealNorm I.val) (-s)) := by
  exact CountsProof.summable_norm s hs

end

end DedekindZetaZeroFree
