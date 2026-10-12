module

public import Mathlib.Topology.Algebra.Group.Neighborhood

@[expose] public section

namespace DedekindZetaZeroFree.CubicCoverTranslatedCharts

open Set Topology

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

def topology (s : H →* G) : TopologicalSpace G where
  IsOpen U := ∀ g, IsOpen ((fun h => g * s h) ⁻¹' U)
  isOpen_univ := by intro g; simp
  isOpen_inter := by
    intro U V hU hV g
    simpa only [preimage_inter] using (hU g).inter (hV g)
  isOpen_sUnion := by
    intro S hS g
    rw [preimage_sUnion]
    exact isOpen_biUnion (fun U hU => hS U hU g)

theorem isOpenEmbedding (s : H →* G) (hs : Function.Injective s) (g : G) :
    letI := topology s
    IsOpenEmbedding (fun h => g * s h) := by
  letI := topology s
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_def.mpr (fun U hU => hU g)
  · intro x y hxy
    exact hs (mul_left_cancel hxy)
  · intro U hU
    intro t
    by_cases hex : ∃ k u, u ∈ U ∧ t * s k = g * s u
    · obtain ⟨k₀, u₀, hu₀, he⟩ := hex
      have htr : ∀ k, t * s k = g * s (u₀ * k₀⁻¹ * k) := by
        intro k
        have ht : t = g * s u₀ * (s k₀)⁻¹ := (eq_mul_inv_iff_mul_eq).mpr he
        rw [ht]
        simp only [map_mul, map_inv]
        simp only [mul_assoc]
      have heq : (fun k => t * s k) ⁻¹' ((fun h => g * s h) '' U) =
          (fun k => u₀ * k₀⁻¹ * k) ⁻¹' U := by
        ext k
        simp only [mem_preimage, mem_image, htr]
        constructor
        · rintro ⟨u, hu, heq⟩
          have := hs (mul_left_cancel heq)
          simpa only [← this] using hu
        · intro hk
          exact ⟨_, hk, rfl⟩
      rw [heq]
      exact hU.preimage (continuous_const.mul continuous_id)
    · have heq : (fun k => t * s k) ⁻¹' ((fun h => g * s h) '' U) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro k ⟨u, hu, he⟩
        exact hex ⟨k, u, hu, he.symm⟩
      rw [heq]
      exact isOpen_empty

theorem continuous_left (s : H →* G) (g : G) :
    letI := topology s
    Continuous (fun x => g * x) := by
  letI := topology s
  apply continuous_def.mpr
  intro U hU t
  simpa only [preimage_preimage, Function.comp_def, mul_assoc] using hU (g * t)

def leftHomeomorph (s : H →* G) (g : G) :
    letI := topology s
    G ≃ₜ G :=
  letI := topology s
  { Equiv.mulLeft g with
    continuous_toFun := continuous_left s g
    continuous_invFun := continuous_left s g⁻¹ }

theorem topologicalGroup (s : H →* G) (hs : Function.Injective s)
    (hconj : letI := topology s
      ∀ g : G, Filter.Tendsto (fun x => g * x * g⁻¹) (nhds 1) (nhds 1)) :
    letI := topology s
    IsTopologicalGroup G := by
  letI := topology s
  have ho : IsOpenEmbedding (s : H → G) := by
    simpa only [one_mul] using isOpenEmbedding s hs 1
  have hn : Filter.map s (nhds 1) = nhds 1 := by
    simpa only [map_one] using ho.map_nhds_eq 1
  apply IsTopologicalGroup.of_nhds_one _ _ _ hconj
  · conv_lhs => rw [← hn, Filter.prod_map_map_eq]
    apply Filter.tendsto_map'_iff.mpr
    simpa only [Function.comp_def, Function.uncurry, Prod.map_fst, Prod.map_snd,
      ← map_mul, map_one, nhds_prod_eq, one_mul] using (ho.continuous.tendsto 1).comp
        (by simpa only [one_mul, nhds_prod_eq] using
          (continuous_mul : Continuous (fun p : H × H => p.1 * p.2)).tendsto (1, 1))
  · conv_lhs => rw [← hn]
    apply Filter.tendsto_map'_iff.mpr
    simpa only [Function.comp_def, ← map_inv, map_one] using
      (ho.continuous.tendsto 1).comp (by simpa using
        (continuous_inv : Continuous (fun x : H => x⁻¹)).tendsto 1)
  · intro g
    have hh := ((leftHomeomorph s g).map_nhds_eq 1).symm
    change nhds (g * (1 : G)) = Filter.map (fun x => g * x) (nhds 1) at hh
    simpa only [mul_one] using hh

theorem conjugation_tendsto (s : H →* G) (hs : Function.Injective s) (g : G)
    (J : Subgroup H) (hJ : IsOpen (J : Set H)) (c : J → H) (hc : Continuous c)
    (he : ∀ k : J, g * s k.val * g⁻¹ = s (c k)) :
    letI := topology s
    Filter.Tendsto (fun x => g * x * g⁻¹) (nhds 1) (nhds 1) := by
  letI := topology s
  have ho : IsOpenEmbedding (s : H → G) := by
    simpa only [one_mul] using isOpenEmbedding s hs 1
  have hj := ho.comp hJ.isOpenEmbedding_subtypeVal
  have hc1 : c 1 = 1 := by
    apply hs
    simpa only [OneMemClass.coe_one, map_one, mul_one, mul_inv_cancel] using (he 1).symm
  have ht : Filter.Tendsto (s ∘ c) (nhds 1) (nhds 1) := by
    simpa only [Function.comp_apply, hc1, map_one] using
      (ho.continuous.comp hc).tendsto 1
  have hfun : (fun x => g * x * g⁻¹) ∘ (s ∘ Subtype.val : J → G) = s ∘ c := by
    funext k
    exact he k
  have hh := hj.tendsto_nhds_iff'.mp (hfun ▸ ht)
  simpa only [Function.comp_apply, OneMemClass.coe_one, map_one] using hh

end DedekindZetaZeroFree.CubicCoverTranslatedCharts
