module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.NegativeSlotCompactBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPAdelicCoverRestrictedProduct
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)

 def compactTailStage (E : Finset (KPFinitePlace F)) : Set (Raw A) :=
  {g | ∀ q, q ∉ E → g (Sum.inr q) ∈ finiteCompact F A.zeta12 A.primitive_zeta12 q}

private theorem compactTailStage_open (E : Finset (KPFinitePlace F)) :
    IsOpen (compactTailStage A E) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 v)
    (A := fun v => (compact F A.zeta12 A.primitive_zeta12 v : Set _))
    (p := fun v => match v with | Sum.inl _ => False | Sum.inr q => q ∉ E)
    (compact_open F A.zeta12 A.primitive_zeta12)
  convert h using 1
  ext g
  constructor
  · intro hg v hv
    cases v with
    | inl w => exact hv.elim
    | inr q => exact hg q hv
  · intro hg q hq
    exact hg (Sum.inr q) hq

theorem exists_uniform_compact_tail (K : Set (Raw A)) (hK : IsCompact K) :
    ∃ E : Finset (KPFinitePlace F),
      ∀ g ∈ K, ∀ q, q ∉ E → g (Sum.inr q) ∈ finiteCompact F A.zeta12 A.primitive_zeta12 q := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (compactTailStage A)
    (compactTailStage_open A) (by
      intro g _
      have hf : {q : KPFinitePlace F | g (Sum.inr q) ∉ finiteCompact F A.zeta12 A.primitive_zeta12 q}.Finite :=
        (Filter.eventually_cofinite.mp g.2).preimage Sum.inr_injective.injOn
      refine Set.mem_iUnion.mpr ⟨hf.toFinset, ?_⟩
      intro q hq
      by_contra h
      exact hq (hf.mem_toFinset.mpr h))
  refine ⟨t.biUnion id, ?_⟩
  intro g hg q hq
  obtain ⟨E, hEt, hgE⟩ := Set.mem_iUnion₂.mp (ht hg)
  exact hgE q (fun h => hq (Finset.mem_biUnion.mpr ⟨E, hEt, h⟩))

theorem exists_compact_reference_stage
    (s : RestrictedTensorSimple.Level (bad A P C)) (K : Set (Raw A)) (hK : IsCompact K) :
    ∃ t : RestrictedTensorSimple.Level (bad A P C), s ≤ t ∧
      ∀ g ∈ K, ∀ v, v ∉ t.val →
        localValue A P C v (g v) (plusReference A P C v) = reference A P C v := by
  obtain ⟨E, hE⟩ := exists_uniform_compact_tail A K hK
  let B := (bad_finite F).toFinset
  let t : RestrictedTensorSimple.Level (bad A P C) :=
    ⟨s.val ∪ E.image Sum.inr ∪ B.image Sum.inr,
      s.property.trans (Finset.subset_union_left.trans Finset.subset_union_left)⟩
  refine ⟨t, Finset.subset_union_left.trans Finset.subset_union_left, ?_⟩
  intro g hg v hv
  have hvs : v ∉ s.val := fun h => hv ((Finset.subset_union_left.trans Finset.subset_union_left) h)
  cases v with
  | inl w =>
    have hb : Sum.inl w ∈ bad A P C := by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad]
    exact False.elim (hvs (s.property hb))
  | inr q =>
    have hqE : q ∉ E := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨q, h, rfl⟩)))
    have hqB : ¬ Bad F q := fun h => hv (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨q, (bad_finite F).mem_toFinset.mpr h, rfl⟩))
    have hqC : q ∉ C.exceptional := by
      intro h
      exact hvs (s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad, h]))
    have hc := hE g hg q hqE
    simp only [finiteCompact, dite_eq_right hqB, MonoidHom.mem_range] at hc
    obtain ⟨k, hk⟩ := hc
    rw [← hk]
    exact plusReference_compact_value A P C q hqC k

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
