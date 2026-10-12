module
public import Mathlib.Algebra.BigOperators.Ring.Nat

public import Mathlib.NumberTheory.NumberField.DedekindZeta

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

def idealAbsoluteWeight (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (I : Ideal (𝓞 F)) : ℝ :=
  if I = ⊥ then 0 else (Ideal.absNorm I : ℝ) ^ (-σ)

def idealAbsoluteSum (F : Type) [Field F] [NumberField F] (σ : ℝ) : ℝ :=
  ∑' I : Ideal (𝓞 F), idealAbsoluteWeight F σ I

theorem idealAbsoluteSum_converges (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (hσ : 1 < σ) :
    Summable (idealAbsoluteWeight F σ) ∧
      (∀ I : Ideal (𝓞 F), 0 ≤ idealAbsoluteWeight F σ I) ∧
      0 < idealAbsoluteSum F σ ∧
      HasSum (idealAbsoluteWeight F σ) (idealAbsoluteSum F σ) := by
  classical
  have hnonneg (I : Ideal (𝓞 F)) : 0 ≤ idealAbsoluteWeight F σ I := by
    unfold idealAbsoluteWeight
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : ℕ → ℝ := fun n => Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  have hlim : Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, a k) / (n : ℝ))
      Filter.atTop (nhds (NumberField.dedekindZeta_residue F)) := by
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp
      tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, a, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [a, Set.coe_eq_subtype]
  have hL : LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
    · exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
        (by simpa using hlim)
    · intro n
      exact Nat.cast_nonneg _
    · exact zero_le_one
    · simpa using hσ
  have hfiber (n : ℕ) :
      (∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
        idealAbsoluteWeight F σ I.val) =
      ‖LSeries.term (fun n => (a n : ℂ)) (σ : ℂ) n‖ := by
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp only [if_pos rfl]
      have hz (I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 0}) :
          idealAbsoluteWeight F σ I.val = 0 := by
        simp [idealAbsoluteWeight, Ideal.absNorm_eq_zero_iff.mp I.property]
      simp [hz]
    · rw [if_neg hn]
      have hweight (I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}) :
          idealAbsoluteWeight F σ I.val = (n : ℝ) ^ (-σ) := by
        have hI : I.val ≠ ⊥ := by
          intro h
          apply hn
          simpa [h] using I.property.symm
        simp [idealAbsoluteWeight, hI, I.property]
      simp_rw [hweight]
      rw [tsum_const, nsmul_eq_mul]
      simp [a, Real.rpow_neg, div_eq_mul_inv]
  have hs : Summable (idealAbsoluteWeight F σ) := by
    apply (summable_partition (f := idealAbsoluteWeight F σ)
      (s := fun n : ℕ => {I | Ideal.absNorm I = n}) hnonneg ?_).mpr
    · refine ⟨?_, ?_⟩
      · intro n
        letI := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).fintype
        exact summable_of_finite_support (Set.toFinite _)
      · exact hL.norm.congr (fun n => (hfiber n).symm)
    · intro I
      exact ⟨Ideal.absNorm I, rfl, fun n hn => hn.symm⟩
  refine ⟨hs, hnonneg, ?_, hs.hasSum⟩
  have htop : idealAbsoluteWeight F σ (⊤ : Ideal (𝓞 F)) = 1 := by
    simp [idealAbsoluteWeight]
  have hle := hs.le_tsum (⊤ : Ideal (𝓞 F)) (fun I _ => hnonneg I)
  rw [htop] at hle
  exact lt_of_lt_of_le zero_lt_one hle

end

end DedekindZetaZeroFree
