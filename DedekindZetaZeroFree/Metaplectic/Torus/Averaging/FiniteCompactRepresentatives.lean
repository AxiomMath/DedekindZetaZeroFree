module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.InducedJetsAndFinalTopology

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Topology
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.TorusChartTransport
open KPGlobalTorusBorelNormTwistTransport KPGlobalTorusFiniteStagesCofinality
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem compact_lift_of_open_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space Y]
    (p : X → Y) (hp : Continuous p) (ho : IsOpenMap p)
    (hs : Function.Surjective p) (K : Set Y) (hK : IsCompact K) :
    ∃ T : Set X, IsCompact T ∧ p '' T = K := by
  have hn : ∀ x : X, ∃ V : Set X, IsCompact V ∧ V ∈ 𝓝 x :=
    exists_compact_mem_nhds
  choose V hVc hVn using hn
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover
    (fun x : X => p '' interior (V x)) (fun x => ho _ isOpen_interior) (by
      intro y hy
      obtain ⟨x, rfl⟩ := hs y
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_image_of_mem _ (mem_interior_iff_mem_nhds.mpr (hVn x))⟩)
  let T := (⋃ x ∈ S, V x) ∩ p ⁻¹' K
  refine ⟨T, (S.finite_toSet.isCompact_biUnion (fun x _ => hVc x)).inter_right
    (hK.isClosed.preimage hp), ?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    have hh := hS hy
    simp only [Set.mem_iUnion] at hh
    obtain ⟨x, hxS, z, hz, rfl⟩ := hh
    refine ⟨z, ⟨?_, hy⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxS, interior_subset hz⟩⟩

theorem actual_finite_compact_class_representatives (C : ModelData F ζ hζ) :
    ∃ T : Set (finiteTorusForClassLifts F ζ hζ), IsCompact T ∧
      finiteTorusClassProjection F ζ hζ '' T =
        (KPGlobalTorusPeriodizationInverse.M F ζ hζ C : Set (KPGlobalCubicIdelePairing.D F)) := by
  letI := finiteTorusForClassLifts_locallyCompact F ζ hζ
  letI := KPGlobalCubicIdelePairing.hausdorff F
  apply compact_lift_of_open_surjective
    (finiteTorusClassProjection F ζ hζ)
    (finiteTorusClassProjection_continuous F ζ hζ)
    (finiteTorusClassProjection_open_of_surjective F ζ hζ
      (finiteTorusClassProjection_surjective F ζ hζ))
    (finiteTorusClassProjection_surjective F ζ hζ)
    _ (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ C).1

theorem actual_finite_compact_averaging_representatives (C : ModelData F ζ hζ) :
    ∃ T : Set (KPGlobalTorusPeriodizationInverse.B F ζ hζ C), IsCompact T ∧
      (∀ b ∈ T, b.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ) ∧
      KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C '' T = Set.univ := by
  obtain ⟨T, hTc, hTp⟩ := actual_finite_compact_class_representatives F ζ hζ C
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hTc
  have hb : ∀ t : T, t.val.val ∈ KPGlobalTorusPeriodizationInverse.B F ζ hζ C := by
    intro t
    change finiteTorusClassProjection F ζ hζ t.val ∈
      (KPGlobalTorusPeriodizationInverse.M F ζ hζ C : Set _)
    rw [← hTp]
    exact Set.mem_image_of_mem _ t.property
  let f : T → KPGlobalTorusPeriodizationInverse.B F ζ hζ C := fun t => ⟨t.val.val, hb t⟩
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  refine ⟨Set.range f, isCompact_range hfc, ?_, ?_⟩
  · rintro b ⟨t, rfl⟩
    exact t.val.property
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    have hm : m.val ∈ finiteTorusClassProjection F ζ hζ '' T := by
      rw [hTp]
      exact m.property
    obtain ⟨t, ht, he⟩ := hm
    refine ⟨f ⟨t, ht⟩, Set.mem_range_self _, ?_⟩
    unfold KPGlobalTorusPeriodizationInverse.averagingClass
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    exact he

end
end DedekindZetaZeroFree.TorusChartTransport
