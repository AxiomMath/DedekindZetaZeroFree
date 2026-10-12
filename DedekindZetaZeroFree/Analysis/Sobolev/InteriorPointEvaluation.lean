module

public import DedekindZetaZeroFree.Analysis.Sobolev.LocalEmbeddingAndSmoothRepresentatives

@[expose] public section

noncomputable section
open MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue

open KPContLocalNorm KPContLocalCubeEmbedding

theorem exists_outer_ball_sobolev_point_bound {n : ℕ} (A T : LocalBall n)
    (hAT : closedCarrier A ⊆ T.carrier) :
    ∃ B : LocalBall n, closedCarrier B ⊆ T.carrier ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ f : Space n → ℂ, ContinuousOn f B.carrier →
          ∀ u : IntegerSobolev B n,
            f =ᵐ[volume.restrict B.carrier]
              (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n n) x) →
            ∀ x ∈ closedCarrier A, ‖f x‖ ≤ C * u.sobolevNorm := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall A.center A.radius).exists_cthickening_subset_open
    Metric.isOpen_ball hAT
  rw [cthickening_closedBall hδ.le A.radius_pos.le] at hsub
  let B : LocalBall n := ⟨A.dimension_pos, A.center, δ + A.radius,
    add_pos hδ A.radius_pos⟩
  have hBT : closedCarrier B ⊆ T.carrier := hsub
  have hAB : closedCarrier A ⊆ B.carrier := by
    apply Metric.closedBall_subset_ball
    dsimp [B]
    linarith
  let embeddingAt (k : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ u : IntegerSobolev B k,
      ∃ (f : Space n → ℂ) (j : CompactJets (closedCarrier A) 0),
        ContDiffOn ℝ (0 : ℕ) f B.carrier ∧
        (f =ᵐ[volume.restrict B.carrier]
          (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)) ∧
        (∀ α : MultiIndex n 0, ∀ x : closedCarrier A,
          j α x = coordinateDerivative α f x) ∧
        jetMaxNorm (isCompact_closedBall A.center A.radius) j ≤ C * u.sobolevNorm ∧
        (∀ g : Space n → ℂ, ContDiffOn ℝ (0 : ℕ) g B.carrier →
          (g =ᵐ[volume.restrict B.carrier]
            (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)) →
          Set.EqOn g f B.carrier)
  have hembedding : embeddingAt (0 + n) := ball_sobolev_embedding A B hAB 0
  have hembedding' : embeddingAt n := (Nat.zero_add n) ▸ hembedding
  obtain ⟨C, hC, hbound⟩ := hembedding'
  refine ⟨B, hBT, C, hC, ?_⟩
  intro f hf u hfu x hx
  obtain ⟨g, j, hg, hgu, hj, hjbound, _⟩ := hbound u
  have hfg : Set.EqOn f g B.carrier :=
    Measure.eqOn_open_of_ae_eq (hfu.trans hgu.symm) Metric.isOpen_ball hf hg.continuousOn
  let : CompactSpace (closedCarrier A) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall A.center A.radius)
  let α : MultiIndex n 0 := ⟨fun _ => 0, by simp⟩
  have hzero : coordinateDerivative α g x = g x := by
    have hnil : (List.finRange n).flatMap (fun _ => ([] : List (Fin n))) = [] :=
      List.flatMap_eq_nil_iff.mpr (by simp)
    simp [coordinateDerivative, MultiIndex.directions, α, hnil, coordinateDerivativeList]
  have heval : j α ⟨x, hx⟩ = f x := by
    rw [hj α ⟨x, hx⟩, hzero, hfg (hAB hx)]
  rw [← heval]
  exact ((ContinuousMap.norm_coe_le_norm (j α) ⟨x, hx⟩).trans
    (norm_le_pi_norm j α)).trans hjbound

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue

end
