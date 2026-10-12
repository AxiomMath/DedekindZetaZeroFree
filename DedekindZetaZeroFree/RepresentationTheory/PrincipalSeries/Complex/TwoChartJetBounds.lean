module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import DedekindZetaZeroFree.Analysis.Jets.Seminorms
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesTransitionBounds
open Set
open scoped ContDiff

lemma compact_jet_bound (U K : Set ℂ) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ k ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ D := by
  have hb (k : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ D := by
    have hc : ContinuousOn (iteratedFDeriv ℝ k f) K := by
      apply ((hf.continuousOn_iteratedFDerivWithin (by simp) hU.uniqueDiffOn).mono hKU).congr
      intro x hx
      exact (iteratedFDerivWithin_of_isOpen k hU (hKU hx)).symm
    exact hK.exists_bound_of_continuousOn hc
  induction n with
  | zero =>
    obtain ⟨D, hD⟩ := hb 0
    exact ⟨max 1 D, le_max_left _ _, fun k hk x hx => by
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact (hD x hx).trans (le_max_right _ _)⟩
  | succ n ih =>
    obtain ⟨D, hD, hDb⟩ := ih
    obtain ⟨B, hB⟩ := hb (n+1)
    refine ⟨max D B, hD.trans (le_max_left _ _), fun k hk x hx => ?_⟩
    by_cases hn : k ≤ n
    · exact (hDb k hn x hx).trans (le_max_left _ _)
    · have : k = n+1 := by omega
      subst k
      exact (hB x hx).trans (le_max_right _ _)

private lemma weight_smooth (a : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => (Real.rpow ‖z‖ a : ℂ)) ({0}ᶜ : Set ℂ) := by
  intro z hz
  have hz0 : z ≠ 0 := hz
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ‖z‖) z := contDiffAt_norm ℝ hz0
  exact (Complex.ofRealCLM.contDiff.comp_contDiffAt z
    (hn.rpow_const_of_ne (norm_ne_zero_iff.mpr hz0))).contDiffWithinAt

lemma weighted_inversion_jet_bound (a : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hKext : ∀ z ∈ K, 1 ≤ ‖z‖) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) H →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ n
        (fun x => (Real.rpow ‖x‖ a : ℂ) * H x⁻¹) z‖ ≤
        C * ∑ k ∈ Finset.range (n+1), KPCplxPrincipalSeriesJets.jetSup k H := by
  let U : Set ℂ := {0}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hKU : K ⊆ U := by
    intro z hz
    have h := hKext z hz
    change z ≠ 0
    intro he
    rw [he, norm_zero] at h
    linarith
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (Inv.inv : ℂ → ℂ) U := contDiffOn_inv ℝ
  have hw := weight_smooth a
  obtain ⟨D, hD, hDb⟩ := compact_jet_bound U K hU hK hKU _ hi n
  obtain ⟨B, hB, hBb⟩ := compact_jet_bound U K hU hK hKU _ hw n
  let C : ℝ := ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * B * ((n-i).factorial : ℝ) * D ^ (n-i)
  refine ⟨max 1 C, le_max_left _ _, fun H hH z hz => ?_⟩
  let S : ℝ := ∑ k ∈ Finset.range (n+1), KPCplxPrincipalSeriesJets.jetSup k H
  have hS : 0 ≤ S := Finset.sum_nonneg fun k hk =>
    KPCplxPrincipalSeriesJets.jetNonneg k H hH
  have hzi : z⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_inv] using
      inv_le_one_of_one_le₀ (hKext z hz)
  have hc (m : ℕ) (hm : m ≤ n) :
      ‖iteratedFDeriv ℝ m (fun x : ℂ => H x⁻¹) z‖ ≤ (m.factorial : ℝ) * S * D ^ m := by
    have hb (k : ℕ) (hk : k ≤ m) :
        ‖iteratedFDerivWithin ℝ k H univ z⁻¹‖ ≤ S := by
      rw [iteratedFDerivWithin_univ]
      exact (KPCplxPrincipalSeriesJets.jetLe k H hH _ hzi).trans
        (Finset.single_le_sum (fun j hj => KPCplxPrincipalSeriesJets.jetNonneg j H hH)
          (Finset.mem_range.mpr (by omega)))
    have hd (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
        ‖iteratedFDerivWithin ℝ k (Inv.inv : ℂ → ℂ) U z‖ ≤ D ^ k := by
      rw [iteratedFDerivWithin_of_isOpen k hU (hKU hz)]
      exact (hDb k (hkm.trans hm) z hz).trans (le_self_pow₀ hD (by omega))
    have he := norm_iteratedFDerivWithin_comp_le hH.contDiffOn hi (by simp : (m : ℕ∞ω) ≤ (⊤ : ℕ∞))
      uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) (hKU hz) hb hd
    rw [iteratedFDerivWithin_of_isOpen m hU (hKU hz)] at he
    exact he
  have hmul := norm_iteratedFDerivWithin_mul_le hw
    (hH.comp_contDiffOn hi) hU.uniqueDiffOn (hKU hz) (by simp : (n : ℕ∞ω) ≤ (⊤ : ℕ∞))
  simp_rw [iteratedFDerivWithin_of_isOpen _ isOpen_compl_singleton
    (show z ∈ ({0}ᶜ : Set ℂ) from hKU hz)] at hmul
  apply hmul.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ) * B * ((n-i).factorial * S * D ^ (n-i)) := by
      apply Finset.sum_le_sum
      intro i hi'
      have hin : i ≤ n := by simp only [Finset.mem_range] at hi'; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hBb i hin z hz) (by positivity))
        (hc (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = C * S := by
      dsimp [C]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      ring
    _ ≤ max 1 C * S := mul_le_mul_of_nonneg_right (le_max_right _ _) hS

lemma compatible_twoChart_jet_bound (a R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ F H : ℂ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) H →
      (∀ z : ℂ, z ≠ 0 → F z = (Real.rpow ‖z‖ a : ℂ) * H z⁻¹) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖iteratedFDeriv ℝ n F z‖ ≤
        C * ∑ k ∈ Finset.range (n+1),
          (KPCplxPrincipalSeriesJets.jetSup k F + KPCplxPrincipalSeriesJets.jetSup k H) := by
  let K := Metric.closedBall (0 : ℂ) R \ Metric.ball (0 : ℂ) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hKext : ∀ z ∈ K, 1 ≤ ‖z‖ := by
    intro z hz
    exact le_of_not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hz.2)
  obtain ⟨C, hC, hCb⟩ := weighted_inversion_jet_bound a K hK hKext n
  refine ⟨C, hC, fun F H hF hH ht z hz => ?_⟩
  let S := ∑ k ∈ Finset.range (n+1),
    (KPCplxPrincipalSeriesJets.jetSup k F + KPCplxPrincipalSeriesJets.jetSup k H)
  have hnon (k : ℕ) : 0 ≤ KPCplxPrincipalSeriesJets.jetSup k F +
      KPCplxPrincipalSeriesJets.jetSup k H := add_nonneg
    (KPCplxPrincipalSeriesJets.jetNonneg k F hF) (KPCplxPrincipalSeriesJets.jetNonneg k H hH)
  have hS : 0 ≤ S := Finset.sum_nonneg fun k hk => hnon k
  by_cases hi : z ∈ Metric.ball (0 : ℂ) 1
  · have hb : ‖iteratedFDeriv ℝ n F z‖ ≤ S := by
      apply (KPCplxPrincipalSeriesJets.jetLe n F hF z (Metric.ball_subset_closedBall hi)).trans
      exact (le_add_of_nonneg_right (KPCplxPrincipalSeriesJets.jetNonneg n H hH)).trans
        (Finset.single_le_sum (fun k hk => hnon k) (Finset.mem_range.mpr (by omega)))
    exact hb.trans (le_mul_of_one_le_left hS hC)
  · have hzK : z ∈ K := ⟨hz, hi⟩
    have hz0 : z ≠ 0 := by
      intro he
      have hh := hKext z hzK
      rw [he, norm_zero] at hh
      linarith
    have he : F =ᶠ[nhds z] (fun x => (Real.rpow ‖x‖ a : ℂ) * H x⁻¹) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({0}ᶜ : Set ℂ) from hz0)]
        with x hx
      exact ht x hx
    rw [(he.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
    apply (hCb H hH z hzK).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Finset.sum_le_sum
    intro k hk
    exact le_add_of_nonneg_left (KPCplxPrincipalSeriesJets.jetNonneg k F hF)

lemma uniformCauchy_on_enlargedBall (a R : ℝ) (n : ℕ) (F H : ℕ → ℂ → ℂ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hH : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (H i))
    (ht : ∀ i z, z ≠ 0 → F i z = (Real.rpow ‖z‖ a : ℂ) * H i z⁻¹)
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      ∑ k ∈ Finset.range (n+1),
        (KPCplxPrincipalSeriesJets.jetSup k (F i - F j) +
         KPCplxPrincipalSeriesJets.jetSup k (H i - H j)) < ε) :
    UniformCauchySeqOn (fun i => iteratedFDeriv ℝ n (F i)) Filter.atTop
      (Metric.closedBall (0 : ℂ) R) := by
  obtain ⟨C, hC1, hb⟩ := compatible_twoChart_jet_bound a R n
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hCp : 0 < C := by linarith
  obtain ⟨N, hN⟩ := hC (ε / C) (div_pos hε hCp)
  refine ⟨N, fun i hi j hj z hz => ?_⟩
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply
    ((hF i).of_le (by simp)).contDiffAt ((hF j).of_le (by simp)).contDiffAt]
  have ht' : ∀ z : ℂ, z ≠ 0 → (F i - F j) z =
      (Real.rpow ‖z‖ a : ℂ) * (H i - H j) z⁻¹ := by
    intro z hz0
    simp only [Pi.sub_apply, ht i z hz0, ht j z hz0, mul_sub]
  exact (hb _ _ ((hF i).sub (hF j)) ((hH i).sub (hH j)) ht' z hz).trans_lt
    ((mul_lt_mul_of_pos_left (hN i hi j hj) hCp).trans_eq (mul_div_cancel₀ ε hCp.ne'))

end DedekindZetaZeroFree.KPCplxPrincipalSeriesTransitionBounds
