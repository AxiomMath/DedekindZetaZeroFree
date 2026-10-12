module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace DedekindZetaZeroFree.KPSmoothAutomorphicEvaluation.OrbitTubeComparison

theorem compact_orbit_count_bound {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (dΓ : IsDiscrete (Γ : Set G))
    (C : Set G) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ x : G, ∀ S : Finset Γ,
      (∀ γ ∈ S, (γ : G) * x ∈ C) → S.card ≤ N := by
  classical
  let T := (Γ : Set G) ∩ (C * C⁻¹)
  have hT : T.Finite := ((hC.mul hC.inv).inter_left hΓ).finite
    (dΓ.mono Set.inter_subset_left)
  refine ⟨hT.toFinset.card, ?_⟩
  intro x S hS
  by_cases hne : S.Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    let j : Γ → G := fun γ => (γ : G) * (γ₀ : G)⁻¹
    have hj : Function.Injective j := by
      intro a b h
      apply Subtype.ext
      exact mul_right_cancel h
    have hjT : ∀ γ ∈ S, j γ ∈ hT.toFinset := by
      intro γ hγ
      rw [hT.mem_toFinset]
      refine ⟨Γ.mul_mem γ.property (Γ.inv_mem γ₀.property), ?_⟩
      apply Set.mem_mul.mpr
      refine ⟨(γ : G) * x, hS γ hγ, ((γ₀ : G) * x)⁻¹, ?_, ?_⟩
      · simpa only [Set.mem_inv, inv_inv] using hS γ₀ hγ₀
      · simp [j, mul_assoc]
    exact Finset.card_le_card_of_injOn j hjT (hj.injOn)
  · simp_all

theorem compact_orbit_indicator_bound {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (dΓ : IsDiscrete (Γ : Set G))
    (C : Set G) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ x : G,
      (∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) ≤ N := by
  classical
  obtain ⟨N, hN⟩ := compact_orbit_count_bound Γ hΓ dΓ C hC
  refine ⟨N, ?_⟩
  intro x
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let S' : Finset Γ := S.filter (fun γ => (γ : G) * x ∈ C)
  have hc : S'.card ≤ N := hN x S' (by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2)
  calc
    (∑ γ ∈ S, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) =
        (S'.card : ℝ≥0∞) := by
      simp [S', Set.indicator, Finset.sum_boole]
    _ ≤ N := by exact_mod_cast hc

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

end DedekindZetaZeroFree.KPSmoothAutomorphicEvaluation.OrbitTubeComparison

end
