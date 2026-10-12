module

public import DedekindZetaZeroFree.Eisenstein.Residues.Exceptional.EntireCoreCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageBounds
open KPLiteralRaw
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalParameterStage renaming literal_entire_coordinate_stage → literal_entire_coordinate_stage

 def compactSup {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ K V} (T U : KPGlobalEisensteinData.CompactTypeStage ρ) :
    KPGlobalEisensteinData.CompactTypeStage ρ where
  space := T.space ⊔ U.space
  finiteDimensional := by
    letI := T.finiteDimensional
    letI := U.finiteDimensional
    infer_instance
  invariant := by
    intro k v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (T.invariant k x hx) (U.invariant k y hy)

 def compactBot {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V) : KPGlobalEisensteinData.CompactTypeStage ρ where
  space := ⊥
  finiteDimensional := inferInstance
  invariant := by
    intro k v hv
    simp only [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]

private theorem core_mem_compact_type {K Gfin V : Type*} [Group K] [Group Gfin]
    [TopologicalSpace Gfin] [AddCommGroup V] [Module ℂ V]
    (ρK : Representation ℂ K V) (ρfin : Representation ℂ Gfin V)
    (smooth : Submodule ℂ V) {v : V}
    (hv : v ∈ KPGlobalEisensteinData.hcHeckeCore ρK ρfin smooth) :
    ∃ T : KPGlobalEisensteinData.CompactTypeStage ρK, v ∈ T.space := by
  unfold KPGlobalEisensteinData.hcHeckeCore at hv
  apply Submodule.iSup_induction
    (motive := fun v => ∃ T : KPGlobalEisensteinData.CompactTypeStage ρK,
      v ∈ T.space) _ hv
  · intro U v hv
    apply Submodule.iSup_induction
      (motive := fun v => ∃ T : KPGlobalEisensteinData.CompactTypeStage ρK,
        v ∈ T.space) _ hv
    · intro T v hv
      exact ⟨T, hv.2⟩
    · exact ⟨compactBot ρK, Submodule.zero_mem _⟩
    · intro x y hx hy
      obtain ⟨T, hT⟩ := hx
      obtain ⟨U, hU⟩ := hy
      exact ⟨compactSup T U, Submodule.add_mem_sup hT hU⟩
  · exact ⟨compactBot ρK, Submodule.zero_mem _⟩
  · intro x y hx hy
    obtain ⟨T, hT⟩ := hx
    obtain ⟨U, hU⟩ := hy
    exact ⟨compactSup T U, Submodule.add_mem_sup hT hU⟩

private theorem finite_image_compact_type {K Gfin V S : Type*}
    [Group K] [Group Gfin] [TopologicalSpace Gfin] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (ρK : Representation ℂ K V) (ρfin : Representation ℂ Gfin V)
    (smooth : Submodule ℂ V)
    (ι : S →ₗ[ℂ] KPGlobalEisensteinData.hcHeckeCore ρK ρfin smooth) :
    ∃ T : KPGlobalEisensteinData.CompactTypeStage ρK,
      ∀ v, (ι v).val ∈ T.space := by
  let e := Module.finBasis ℂ S
  have hfinite (A : Finset (Fin (Module.finrank ℂ S))) :
      ∃ T : KPGlobalEisensteinData.CompactTypeStage ρK,
        ∀ i ∈ A, (ι (e i)).val ∈ T.space := by
    induction A using Finset.induction_on with
    | empty => exact ⟨compactBot ρK, by simp⟩
    | @insert i A hi ih =>
      obtain ⟨T, hT⟩ := core_mem_compact_type ρK ρfin smooth (ι (e i)).property
      obtain ⟨U, hU⟩ := ih
      refine ⟨compactSup T U, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (show T.space ≤ (compactSup T U).space from le_sup_left) hT
      · exact (show U.space ≤ (compactSup T U).space from le_sup_right) (hU j hj)
  obtain ⟨T, hT⟩ := hfinite Finset.univ
  refine ⟨T, ?_⟩
  intro v
  rw [← e.sum_repr v]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  exact T.space.sum_mem fun i hi => T.space.smul_mem _ (hT i hi)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 abbrev D := KPContFlatFullProductIwasawa.iwasawaData F ζ hζ
 abbrev Core := KPMsRationalCompactCrossPairing.Vplus F ζ hζ (D F ζ hζ)
 abbrev compactAction :=
  (KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp (D F ζ hζ).K.subtype

private theorem canonical_stage_bounds {S : Type*}
    [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] Core F ζ hζ)
    (hSmooth : ∀ v, (ι v).val ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)) :
    ∃ (T : KPGlobalEisensteinData.CompactTypeStage (compactAction F ζ hζ))
      (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ),
      (∀ v, (ι v).val ∈ T.space) ∧
      ∀ s v g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        KPContFlatStageJetHolomorphy.L F ζ hζ ι s v (g * j.val) =
          KPContFlatStageJetHolomorphy.L F ζ hζ ι s v g := by
  obtain ⟨T, hT⟩ := finite_image_compact_type (compactAction F ζ hζ)
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp
      (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype)
    (KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)) ι
  obtain ⟨J, hJ⟩ := KPContFlatStageJetHolomorphy.stage_uniform_right_level F ζ hζ ι hSmooth
  exact ⟨T, J, hT, hJ⟩

 theorem literal_bounded_entire_stage (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (ι : (Fin n → ℂ) →ₗ[ℂ] Core F ζ hζ) (p : ℂ → (Fin n → ℂ))
      (T : KPGlobalEisensteinData.CompactTypeStage (compactAction F ζ hζ))
      (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ),
      Function.Injective ι ∧ Differentiable ℂ p ∧
      (∀ v, (ι v).val ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)) ∧
      (∀ v, (ι v).val ∈ T.space) ∧
      (∀ s v g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        KPContFlatStageJetHolomorphy.L F ζ hζ ι s v (g * j.val) =
          KPContFlatStageJetHolomorphy.L F ζ hζ ι s v g) ∧
      ∀ s g, KPContFlatStageJetHolomorphy.L F ζ hζ ι s (p s) g = f.val s g := by
  obtain ⟨n, ι, p, hι, hp, hSmooth, hpin⟩ :=
    literal_entire_coordinate_stage F ζ hζ K hK f
  obtain ⟨T, J, hT, hJ⟩ := canonical_stage_bounds F ζ hζ ι hSmooth
  refine ⟨n, ι, p, T, J, hι, hp, hSmooth, hT, hJ, ?_⟩
  intro s g
  simpa only [KPContFlatStageJetHolomorphy.parameterSection, pow_zero, one_mul]
    using hpin s g

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageBounds

end
