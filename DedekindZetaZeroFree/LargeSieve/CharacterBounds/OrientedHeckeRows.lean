module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.GoldmakherLouvel
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

theorem rm_hgl_oriented
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (qS : Ideal (𝓞 F)) (𝓕 : QuadraticHeckeFamily F qS)
    (b : ℝ) (hb : 0 < b) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (X Y : ℝ) (z : Ideal (𝓞 F) →₀ ℂ),
        1 ≤ X → 1 ≤ Y →
        (∀ c ∈ z.support,
          Squarefree c ∧ c ⊔ qS = ⊤ ∧ (Ideal.absNorm c : ℝ) ≤ Y) →
        (∑ᶠ d : Ideal (𝓞 F),
          if Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X then
            ‖∑ c ∈ z.support, z c * (𝓕.χ c) d‖ ^ 2
          else 0) ≤
            L * (X * Y) ^ b * (X + Y) *
              ∑ c ∈ z.support, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := DedekindZetaZeroFree.LargeSieve.goldmakherLouvel F (primitive12_totallyComplex F ζ12 hζ12) qS 𝓕 b hb
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro X Y z hX hY hz
  have hkernel (d : Ideal (𝓞 F)) :
      (∑ᶠ c : Ideal (𝓞 F),
        if Squarefree c ∧ c ⊔ qS = ⊤ ∧ (Ideal.absNorm c : ℝ) ≤ Y then
          z c * (𝓕.χ c) d else 0) = ∑ c ∈ z.support, z c * (𝓕.χ c) d := by
    rw [finsum_eq_sum_of_support_subset _ (s := z.support)]
    · apply Finset.sum_congr rfl
      intro c hc
      simp only [if_pos (hz c hc)]
    · intro c hc
      by_contra hn
      have hzero : z c = 0 := Finsupp.notMem_support_iff.mp hn
      simpa [Function.mem_support, hzero] using hc
  have hmass :
      (∑ᶠ c : Ideal (𝓞 F),
        if Squarefree c ∧ c ⊔ qS = ⊤ ∧ (Ideal.absNorm c : ℝ) ≤ Y then
          ‖z c‖ ^ 2 else 0) = ∑ c ∈ z.support, ‖z c‖ ^ 2 := by
    rw [finsum_eq_sum_of_support_subset _ (s := z.support)]
    · apply Finset.sum_congr rfl
      intro c hc
      simp only [if_pos (hz c hc)]
    · intro c hc
      by_contra hn
      have hzero : z c = 0 := Finsupp.notMem_support_iff.mp hn
      simpa [Function.mem_support, hzero] using hc
  have hbound := hC X Y z hX hY
  simp only [hkernel, hmass] at hbound
  apply hbound.trans
  have hXY : 0 ≤ X + Y := by linarith
  have hnorm : 0 ≤ ∑ c ∈ z.support, ‖z c‖ ^ 2 :=
    Finset.sum_nonneg fun c _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.rpow_nonneg (by positivity) _))
      hXY) hnorm

theorem rm_hgl_oriented_masked
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (qS : Ideal (𝓞 F)) (𝓕 : QuadraticHeckeFamily F qS)
    (b : ℝ) (hb : 0 < b) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (X Y : ℝ) (z : Ideal (𝓞 F) →₀ ℂ)
        (R : Ideal (𝓞 F) → Prop) (ρ : Ideal (𝓞 F) → ℂ),
        1 ≤ X → 1 ≤ Y →
        (∀ c ∈ z.support,
          Squarefree c ∧ c ⊔ qS = ⊤ ∧ (Ideal.absNorm c : ℝ) ≤ Y) →
        (∀ d, ‖ρ d‖ ≤ 1) →
        (∑ᶠ d : Ideal (𝓞 F),
          if Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X ∧ R d then
            ‖ρ d * ∑ c ∈ z.support, z c * (𝓕.χ c) d‖ ^ 2
          else 0) ≤
            L * (X * Y) ^ b * (X + Y) *
              ∑ c ∈ z.support, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨L, hL, hbound⟩ := rm_hgl_oriented F ζ12 hζ12 qS 𝓕 b hb
  refine ⟨L, hL, ?_⟩
  intro X Y z R ρ hX hY hz hρ
  apply le_trans _ (hbound X Y z hX hY hz)
  have hfinite : {d : Ideal (𝓞 F) | (Ideal.absNorm d : ℝ) ≤ X}.Finite := by
    obtain ⟨n, hn⟩ := exists_nat_ge X
    apply (Ideal.finite_setOfPred_absNorm_le n).subset
    intro d hd
    exact_mod_cast (hd.trans hn)
  apply finsum_le_finsum
  · apply hfinite.subset
    intro d hd
    simp only [Function.mem_support] at hd
    by_contra hn
    simp only [Set.mem_setOf_eq] at hn
    simp [hn] at hd
  · apply hfinite.subset
    intro d hd
    simp only [Function.mem_support] at hd
    by_contra hn
    simp only [Set.mem_setOf_eq] at hn
    simp [hn] at hd
  · intro d
    by_cases hd : Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X ∧ R d
    · have hd' : Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X :=
        ⟨hd.1, hd.2.1, hd.2.2.1⟩
      simp only [if_pos hd, if_pos hd', norm_mul]
      have hmul : ‖ρ d‖ * ‖∑ c ∈ z.support, z c * (𝓕.χ c) d‖ ≤
          ‖∑ c ∈ z.support, z c * (𝓕.χ c) d‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hρ d) (norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity) hmul 2
    · simp only [if_neg hd]
      split_ifs <;> positivity

end
end DedekindZetaZeroFree
