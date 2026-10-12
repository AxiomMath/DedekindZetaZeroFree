module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.IdeleUnitValuationPairing

@[expose] public section

open scoped NumberField Classical RestrictedProduct
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
noncomputable section
variable (F : Type) [Field F] [NumberField F]
 instance completionTG (v : KPHilbert.Place F) : IsTopologicalGroup (KPHilbert.Completion F v)ˣ := by
  cases v <;> dsimp [KPHilbert.Completion] <;> infer_instance
 def integralUnits (v : KPHilbert.Place F) : Subgroup (KPHilbert.Completion F v)ˣ :=
  match v with
  | Sum.inl _ => ⊤
  | Sum.inr q => (q.adicCompletionIntegers F).units
private theorem integralUnits_open (v : KPHilbert.Place F) : IsOpen (integralUnits F v : Set (KPHilbert.Completion F v)ˣ) := by
  cases v with
  | inl w => exact isOpen_univ
  | inr q => exact isOpen_finiteLocalUnits F q
private theorem integralUnits_eq_range (q : HeightOneSpectrum (𝓞 F)) :
    integralUnits F (Sum.inr q) = (KPHilbert.integerUnitInclusion F q).range := by
  letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have mem (a : q.adicCompletion F) :
      a ∈ q.adicCompletionIntegers F ↔ a ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer := by
    rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
    exact (Valuation.vle_one_iff (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))).symm
  ext z
  constructor
  · intro hz
    let u : KPHilbert.LocalIntegerUnits F q :=
      ⟨⟨z.val, (mem _).mp hz.1⟩, ⟨z.inv, (mem _).mp hz.2⟩,
      by apply Subtype.ext; exact z.val_inv,
      by apply Subtype.ext; exact z.inv_val⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(mem _).mpr u.val.property, (mem _).mpr u.inv.property⟩
 theorem integralUnits_maps (v : KPHilbert.Place F) :
    Set.MapsTo (localClass F v) (integralUnits F v) (U F v) := by
  cases v with
  | inl w => intro z hz; trivial
  | inr q =>
    intro z hz
    exact ⟨z, (integralUnits_eq_range F q) ▸ hz, rfl⟩
 def integralClass (v : KPHilbert.Place F) : integralUnits F v → U F v :=
  Subtype.map (localClass F v) (integralUnits_maps F v)
private theorem integralClass_open (v : KPHilbert.Place F) : IsOpenMap (integralClass F v) :=
  QuotientGroup.isOpenMap_coe.subtype_map (integralUnits_open F v) (integralUnits_maps F v)
private theorem integralClass_cont (v : KPHilbert.Place F) : Continuous (integralClass F v) :=
  (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
private theorem integralClass_surj (v : KPHilbert.Place F) : Function.Surjective (integralClass F v) := by
  intro z
  cases v with
  | inl w =>
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective _ z.val
    exact ⟨⟨a, Subgroup.mem_top _⟩, Subtype.ext ha⟩
  | inr q =>
    obtain ⟨a, ha, he⟩ := z.property
    exact ⟨⟨a, (integralUnits_eq_range F q).symm ▸ ha⟩, Subtype.ext he⟩
 theorem U_open (v : KPHilbert.Place F) : IsOpen (U F v : Set (LocalD F v)) := by
  cases v with
  | inl w => exact isOpen_univ
  | inr q =>
    have h : (U F (Sum.inr q) : Set (LocalD F (Sum.inr q))) = localClass F (Sum.inr q) '' (integralUnits F (Sum.inr q)) := by
      rw [integralUnits_eq_range F q]
      rfl
    rw [h]
    exact QuotientGroup.isOpenMap_coe _ (integralUnits_open F (Sum.inr q))
 def chart : ((v : KPHilbert.Place F) → integralUnits F v) → Ideles F :=
  fun a => IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F
    (⟨fun w => (a (Sum.inl w)).val.val, fun w => (a (Sum.inl w)).val.inv,
       by funext w; exact (a (Sum.inl w)).val.val_inv,
       by funext w; exact (a (Sum.inl w)).val.inv_val⟩,
     RestrictedProduct.structureMap _ _ Filter.cofinite (fun q => a (Sum.inr q)))
private theorem chart_openEmbedding : Topology.IsOpenEmbedding (chart F) := by
  let h := Homeomorph.sumPiEquivProdPi (InfinitePlace F) (HeightOneSpectrum (𝓞 F)) (fun v => integralUnits F v)
  let h' := (Homeomorph.piCongrRight fun w : InfinitePlace F =>
    Homeomorph.Set.univ (w.Completionˣ)).prodCongr (Homeomorph.refl ((q : HeightOneSpectrum (𝓞 F)) → integralUnits F (Sum.inr q)))
  let h'' := (@ContinuousMulEquiv.piUnits (InfinitePlace F) (fun w => w.Completion) _ _).symm.toHomeomorph.prodCongr (Homeomorph.refl ((q : HeightOneSpectrum (𝓞 F)) → integralUnits F (Sum.inr q)))
  have hop := ((Homeomorph.refl ((w : InfinitePlace F) → w.Completion)ˣ).isOpenEmbedding.prodMap
    (RestrictedProduct.isOpenEmbedding_structureMap (fun q => isOpen_finiteLocalUnits F q)))
  have hh := (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).toHomeomorph.isOpenEmbedding.comp
    (hop.comp (h''.isOpenEmbedding.comp (h'.isOpenEmbedding.comp h.isOpenEmbedding)))
  exact hh
private theorem chart_one : chart F 1 = 1 := by
  apply Units.ext
  apply Prod.ext
  · funext w
    rfl
  · apply RestrictedProduct.ext
    intro q
    rfl
 def st : ((v : KPHilbert.Place F) → U F v) → RestrictedClasses F :=
  RestrictedProduct.structureMap _ _ Filter.cofinite
private theorem chart_comp : restrictedClassMap F ∘ chart F = st F ∘ Pi.map (integralClass F) := by
  funext a
  apply RestrictedProduct.ext
  intro v
  cases v <;> rfl
 instance localD_TG (v : KPHilbert.Place F) : IsTopologicalGroup (LocalD F v) := inferInstance
 instance U_open_fact : Fact (∀ v, IsOpen (U F v : Set (LocalD F v))) := ⟨U_open F⟩
private theorem restrictedClassMap_cont : Continuous (restrictedClassMap F) := by
  apply continuous_of_continuousAt_one
  rw [← chart_one F]
  apply (chart_openEmbedding F).continuousAt_iff.mp
  rw [chart_comp F]
  exact ((RestrictedProduct.isEmbedding_structureMap.continuous).comp
    (continuous_pi fun v => (integralClass_cont F v).comp (continuous_apply v))).continuousAt
private theorem restrictedClassMap_open : IsOpenMap (restrictedClassMap F) := by
  rw [IsTopologicalGroup.isOpenMap_iff_nhds_one]
  have hc : IsOpenMap (Pi.map (integralClass F)) :=
    IsOpenMap.piMap (integralClass_open F) (Filter.Eventually.of_forall (integralClass_surj F))
  have hs : Topology.IsOpenEmbedding (st F) :=
    RestrictedProduct.isOpenEmbedding_structureMap (U_open F)
  have hone : st F (Pi.map (integralClass F) 1) = 1 := by ext v; rfl
  rw [← hone]
  have h := (hs.isOpenMap.comp hc).nhds_le 1
  rw [← chart_comp F, ← Filter.map_map,
    (chart_openEmbedding F).map_nhds_eq, chart_one F] at h
  simpa only [Function.comp_apply, chart_one, map_one, hone] using h

theorem class_comparison_continuous_open :
    Continuous (classComparison F) ∧ IsOpenMap (classComparison F) := by
  constructor
  · apply (QuotientGroup.isQuotientMap_mk (CubicCharacters.cubes (Ideles F))).continuous_iff.mpr
    exact restrictedClassMap_cont F
  · apply IsOpenMap.of_comp QuotientGroup.continuous_mk (QuotientGroup.mk_surjective)
    exact restrictedClassMap_open F
end
end DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
