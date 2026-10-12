module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPActualReflectionData.CanonicalStageCircle
open KPGlobalEisensteinData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem seminorm_sum_bound {V K : Type*} [AddCommGroup V] [Module ℂ V]
    (p : Seminorm ℂ V) (I : Finset K) (u : K → V) : p (∑ k ∈ I, u k) ≤ ∑ k ∈ I, p (u k) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert k I hk ih =>
    simp only [Finset.sum_insert hk]
    exact (map_add_le_add _ _ _).trans (add_le_add le_rfl ih)

 theorem powerSeries_finset_sum {G V J K : Type*} [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (D : J → V →ₗ[ℂ] C(G, ℂ))
    (I : Finset K) (c : K → ℂ) (a : K → ℕ → V) (f : K → ℂ → V)
    (z₀ : ℂ) (ρ : ℝ) (h : ∀ k ∈ I, SmoothPowerSeriesOn D z₀ ρ (a k) (f k)) :
    SmoothPowerSeriesOn D z₀ ρ (fun n => ∑ k ∈ I, c k • a k n)
      (fun z => ∑ k ∈ I, c k • f k z) := by
  intro i r hr hrρ ε hε
  let B : ℝ := 1 + ∑ k ∈ I, ‖c k‖
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < ε / B := div_pos hε hB
  choose N hN using (fun k : {k // k ∈ I} => h k.val k.property i r hr hrρ (ε / B) he)
  refine ⟨I.sup (fun k => if hk : k ∈ I then N ⟨k,hk⟩ else 0), ?_⟩
  intro M hM z hz
  have heq : ((∑ n ∈ Finset.range M, (z-z₀)^n • ∑ k ∈ I, c k • a k n) -
      ∑ k ∈ I, c k • f k z) = ∑ k ∈ I, c k • ((∑ n ∈ Finset.range M, (z-z₀)^n • a k n) - f k z) := by
    simp_rw [Finset.smul_sum, smul_smul, mul_comm ((z-z₀)^_), ← smul_smul]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.smul_sum, smul_sub]
  rw [heq]
  have hsum : smoothSeminorm D i (∑ k ∈ I, c k • ((∑ n ∈ Finset.range M, (z-z₀)^n • a k n) - f k z)) ≤
      ∑ k ∈ I, ‖c k‖ * (ε / B) := by
    calc
      _ ≤ ∑ k ∈ I, smoothSeminorm D i (c k • ((∑ n ∈ Finset.range M, (z-z₀)^n • a k n) - f k z)) :=
        seminorm_sum_bound _ _ _
      _ = ∑ k ∈ I, ‖c k‖ * smoothSeminorm D i ((∑ n ∈ Finset.range M, (z-z₀)^n • a k n) - f k z) := by
        simp only [map_smul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hkM : N ⟨k,hk⟩ ≤ M := by
          have hle := (Finset.le_sup (f := fun k => if hk : k ∈ I then N ⟨k,hk⟩ else 0) hk : (if hk : k ∈ I then N ⟨k,hk⟩ else 0) ≤ I.sup (fun k => if hk : k ∈ I then N ⟨k,hk⟩ else 0))
          simpa only [dite_eq_left hk] using hle.trans hM
        exact (hN ⟨k,hk⟩ M hkM z hz).le
  apply lt_of_le_of_lt hsum
  rw [← Finset.sum_mul]
  have hb : (∑ k ∈ I, ‖c k‖) < B := by dsimp [B]; linarith
  have hmul := mul_lt_mul_of_pos_right hb he
  have hc : B * (ε / B) = ε := by field_simp
  exact hmul.trans_eq hc

end DedekindZetaZeroFree.KPActualReflectionData.CanonicalStageCircle

end
