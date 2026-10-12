module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormPartition

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.SplitPrefixEnvelope

open scoped Classical

theorem finite_partition_quadratic_bound
    {ι κ A B : Type*} [DecidableEq A] [DecidableEq B]
    (I : Finset ι) (J : Finset κ) (R : Finset A) (S : Finset B)
    (RB : ι → Finset A) (SB : κ → Finset B)
    (hR : I.biUnion RB = R) (hS : J.biUnion SB = S)
    (hRd : Set.PairwiseDisjoint (↑I : Set ι) RB)
    (hSd : Set.PairwiseDisjoint (↑J : Set κ) SB)
    (K : B → A → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hloc : ∀ i ∈ I, ∀ j ∈ J, ∀ lam : B → ℂ,
      ∑ a ∈ RB i, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 ≤
        L * ∑ b ∈ SB j, ‖lam b‖ ^ 2) (lam : B → ℂ) :
    ∑ a ∈ R, ‖∑ b ∈ S, lam b * K b a‖ ^ 2 ≤
      (I.card : ℝ) * (J.card : ℝ) * L * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  classical

  have hcolsum : ∀ a, (∑ b ∈ S, lam b * K b a) = ∑ j ∈ J, ∑ b ∈ SB j, lam b * K b a := by
    intro a
    rw [← hS, Finset.sum_biUnion hSd]

  have hpoint : ∀ a ∈ R, ‖∑ b ∈ S, lam b * K b a‖ ^ 2 ≤
      (J.card : ℝ) * ∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 := by
    intro a _
    rw [hcolsum a]
    calc ‖∑ j ∈ J, ∑ b ∈ SB j, lam b * K b a‖ ^ 2
        ≤ (∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le J _) 2
      _ ≤ (J.card : ℝ) * ∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq

  have hfactor : (∑ i ∈ I, ∑ a ∈ RB i,
        (J.card : ℝ) * ∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2)
      = (J.card : ℝ) * ∑ i ∈ I, ∑ a ∈ RB i,
          ∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]

  have hcollapse : (∑ i ∈ I, ∑ j ∈ J, L * (∑ b ∈ SB j, ‖lam b‖ ^ 2))
      = (I.card : ℝ) * (L * ∑ b ∈ S, ‖lam b‖ ^ 2) := by
    have hY : (∑ j ∈ J, ∑ b ∈ SB j, ‖lam b‖ ^ 2) = ∑ b ∈ S, ‖lam b‖ ^ 2 := by
      rw [← hS]
      exact (Finset.sum_biUnion hSd).symm
    calc ∑ i ∈ I, ∑ j ∈ J, L * (∑ b ∈ SB j, ‖lam b‖ ^ 2)
        = ∑ i ∈ I, L * (∑ j ∈ J, ∑ b ∈ SB j, ‖lam b‖ ^ 2) :=
          Finset.sum_congr rfl fun i _ =>
            (Finset.mul_sum J (fun j => ∑ b ∈ SB j, ‖lam b‖ ^ 2) L).symm
      _ = (I.card : ℝ) * (L * (∑ j ∈ J, ∑ b ∈ SB j, ‖lam b‖ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (I.card : ℝ) * (L * ∑ b ∈ S, ‖lam b‖ ^ 2) := by rw [hY]
  calc ∑ a ∈ R, ‖∑ b ∈ S, lam b * K b a‖ ^ 2
      = ∑ i ∈ I, ∑ a ∈ RB i, ‖∑ b ∈ S, lam b * K b a‖ ^ 2 := by
        rw [← hR, Finset.sum_biUnion hRd]
    _ ≤ ∑ i ∈ I, ∑ a ∈ RB i,
          (J.card : ℝ) * ∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun a ha => ?_
        exact hpoint a (by rw [← hR]; exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩)
    _ = (J.card : ℝ) * ∑ i ∈ I, ∑ a ∈ RB i,
          ∑ j ∈ J, ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 := hfactor
    _ = (J.card : ℝ) * ∑ i ∈ I, ∑ j ∈ J, ∑ a ∈ RB i,
          ‖∑ b ∈ SB j, lam b * K b a‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ (J.card : ℝ) * ∑ i ∈ I, ∑ j ∈ J, L * (∑ b ∈ SB j, ‖lam b‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hloc i hi j hj lam
    _ = (J.card : ℝ) * ((I.card : ℝ) * (L * ∑ b ∈ S, ‖lam b‖ ^ 2)) := by
        rw [hcollapse]
    _ = (I.card : ℝ) * (J.card : ℝ) * L * (∑ b ∈ S, ‖lam b‖ ^ 2) := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve.SplitPrefixEnvelope
