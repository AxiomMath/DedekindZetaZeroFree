module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.CommonSourceStage

 def typeSum {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ K V} (J J' : KPGlobalEisensteinData.CompactTypeStage ρ) :
    KPGlobalEisensteinData.CompactTypeStage ρ where
  space := J.space ⊔ J'.space
  finiteDimensional := by
    letI := J.finiteDimensional
    letI := J'.finiteDimensional
    infer_instance
  invariant := by
    intro k x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (J.invariant k a ha) (J'.invariant k b hb)

theorem finiteLevelTypeStage_common
    {K G V : Type*} [Group K] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V) (σ : Representation ℂ G V) (smooth : Submodule ℂ V)
    (U U' : CompactOpenLevel G) (J J' : KPGlobalEisensteinData.CompactTypeStage ρ) :
    ∃ W : CompactOpenLevel G, ∃ I : KPGlobalEisensteinData.CompactTypeStage ρ,
      KPGlobalEisensteinData.finiteLevelTypeStage ρ σ smooth U J ≤
        KPGlobalEisensteinData.finiteLevelTypeStage ρ σ smooth W I ∧
      KPGlobalEisensteinData.finiteLevelTypeStage ρ σ smooth U' J' ≤
        KPGlobalEisensteinData.finiteLevelTypeStage ρ σ smooth W I := by
  let W : CompactOpenLevel G :=
    ⟨U.toOpenSubgroup ⊓ U'.toOpenSubgroup,
      U.isCompact.inter_right U'.toOpenSubgroup.isClosed⟩
  refine ⟨W, typeSum J J', ?_, ?_⟩
  · intro x hx
    exact ⟨⟨hx.1.1, fun w => hx.1.2 ⟨w.val, w.property.1⟩⟩, (show J.space ≤ J.space ⊔ J'.space from le_sup_left) hx.2⟩
  · intro x hx
    exact ⟨⟨hx.1.1, fun w => hx.1.2 ⟨w.val, w.property.2⟩⟩, (show J'.space ≤ J.space ⊔ J'.space from le_sup_right) hx.2⟩

theorem hcHeckeCore_mem_stage
    {K G V : Type*} [Group K] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    [Nonempty (CompactOpenLevel G)]
    (ρ : Representation ℂ K V) (σ : Representation ℂ G V) (smooth : Submodule ℂ V)
    {x : V} (hx : x ∈ KPGlobalEisensteinData.hcHeckeCore ρ σ smooth) :
    ∃ U J, x ∈ KPGlobalEisensteinData.finiteLevelTypeStage ρ σ smooth U J := by
  letI : Nonempty (KPGlobalEisensteinData.CompactTypeStage ρ) :=
    ⟨⟨⊥, inferInstance, fun k x hx => by have h : x = 0 := hx; subst x; simp⟩⟩
  let stages := fun p : CompactOpenLevel G × KPGlobalEisensteinData.CompactTypeStage ρ =>
    KPGlobalEisensteinData.finiteLevelTypeStage ρ σ smooth p.1 p.2
  have hd : Directed (· ≤ ·) stages := by
    intro p q
    obtain ⟨W, I, hp, hq⟩ := finiteLevelTypeStage_common ρ σ smooth p.1 q.1 p.2 q.2
    exact ⟨(W, I), hp, hq⟩
  have hx' : x ∈ iSup stages := by
    simpa only [stages, iSup_prod, KPGlobalEisensteinData.hcHeckeCore] using hx
  obtain ⟨⟨U, J⟩, h⟩ := (Submodule.mem_iSup_of_directed stages hd).mp hx'
  exact ⟨U, J, h⟩

end DedekindZetaZeroFree.KPGlobalResidualKernel.CommonSourceStage

end
