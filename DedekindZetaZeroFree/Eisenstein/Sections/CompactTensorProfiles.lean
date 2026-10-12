module

public import DedekindZetaZeroFree.Eisenstein.Sections.IwasawaDiscrepancyCuts

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer
open KPLiteralRaw KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

 def quotientHom : RestrictedCover F ζ hζ →* G F ζ hζ :=
  (scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)

 theorem local_arch_mem (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (w : InfinitePlace F)
    (x : PrincipalOfKP.archimedeanLocalCompact F ζ hζ w) :
    quotientHom F ζ hζ (localToRestricted F ζ hζ (Sum.inl w) x.val) ∈ K := by
  have hle : PrincipalOfKP.archimedeanLocalCompact F ζ hζ w ≤
      K.comap ((quotientHom F ζ hζ).comp
        (RestrictedProduct.mulSingleMonoidHom (compact F ζ hζ) (Sum.inl w))) := by
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨k, rfl⟩
    exact hK.2.2 w k
  exact hle x.property

 def finiteProjection : RestrictedCover F ζ hζ →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom
    (KPLocalCover.CubicGL2Raw F ζ hζ) (KPLocalCover.CubicGL2Raw F ζ hζ)
    id Filter.tendsto_id
    (fun v => match v with | Sum.inl _ => 1 | Sum.inr _ => MonoidHom.id _)
    (Filter.Eventually.of_forall (by intro v a ha; cases v <;> simpa using ha))

private theorem finiteProjection_continuous : Continuous (finiteProjection F ζ hζ) := by
  unfold finiteProjection RestrictedProduct.mapAlongMonoidHom
  exact RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id _
    (Filter.Eventually.of_forall (by intro v a ha; cases v <;> simpa using ha))
    (fun v => by cases v <;> first | exact continuous_const | exact continuous_id)

private theorem finiteProjection_infinite (x : RestrictedCover F ζ hζ) (w : InfinitePlace F) :
    finiteProjection F ζ hζ x (Sum.inl w) = 1 := rfl

private theorem finiteProjection_finite (x : RestrictedCover F ζ hζ)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    finiteProjection F ζ hζ x (Sum.inr q) = x (Sum.inr q) := rfl

 theorem finiteProjection_mem (x : RestrictedCover F ζ hζ) :
    quotientHom F ζ hζ (finiteProjection F ζ hζ x) ∈
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  apply Subgroup.mem_map.mpr
  refine ⟨finiteProjection F ζ hζ x, ?_, rfl⟩
  simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]
  intro w
  rfl

 def archProjection (x : RestrictedCover F ζ hζ) : RestrictedCover F ζ hζ :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map
    (fun w => localToRestricted F ζ hζ (Sum.inl w) (x (Sum.inl w)))).prod

 theorem archProjection_infinite (x : RestrictedCover F ζ hζ) (w : InfinitePlace F) :
    archProjection F ζ hζ x (Sum.inl w) = x (Sum.inl w) := by
  change (RestrictedProduct.evalMonoidHom
    (KPLocalCover.CubicGL2Raw F ζ hζ) (Sum.inl w)) _ = _
  rw [archProjection, map_list_prod, List.map_map]
  simp only [Function.comp_def, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.coe_mulSingle_apply]
  rw [List.prod_map_eq_pow_single w _ (by
    intro w' hw' _
    simp [Pi.mulSingle_apply, hw', Ne.symm hw'])]
  rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
  simp

 theorem archProjection_finite (x : RestrictedCover F ζ hζ)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    archProjection F ζ hζ x (Sum.inr q) = 1 := by
  change (RestrictedProduct.evalMonoidHom
    (KPLocalCover.CubicGL2Raw F ζ hζ) (Sum.inr q)) _ = _
  rw [archProjection, map_list_prod, List.map_map]
  simp [Function.comp_def, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_apply]

 theorem tuple_factorization (x : RestrictedCover F ζ hζ) :
    x = archProjection F ζ hζ x * finiteProjection F ζ hζ x := by
  ext v
  cases v with
  | inl w => simp [RestrictedProduct.mul_apply, archProjection_infinite, finiteProjection_infinite]
  | inr q => simp [RestrictedProduct.mul_apply, archProjection_finite, finiteProjection_finite]

private theorem archProjection_mem (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K)
    (x : PrincipalOfKP.fullCompactPreimageMax F ζ hζ) :
    quotientHom F ζ hζ (archProjection F ζ hζ x.val) ∈ K := by
  rw [archProjection, map_list_prod, List.map_map]
  apply Subgroup.list_prod_mem
  intro a ha
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha
  exact local_arch_mem F ζ hζ K hK w ⟨x.val (Sum.inl w), x.property (Sum.inl w)⟩

 def finiteProjectionHom : RestrictedCover F ζ hζ →*
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  ((quotientHom F ζ hζ).comp (finiteProjection F ζ hζ)).codRestrict _
    (finiteProjection_mem F ζ hζ)

private theorem finiteProjectionHom_continuous : Continuous (finiteProjectionHom F ζ hζ) := by
  apply Continuous.subtype_mk
  exact (PrincipalOfKP.continuous_scalarQuotient_comp_amalgamation F ζ hζ).comp
    (finiteProjection_continuous F ζ hζ)

 def finiteCompactSet : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ) :=
  finiteProjectionHom F ζ hζ '' (PrincipalOfKP.fullCompactPreimageMax F ζ hζ : Set _)

private theorem finiteCompactSet_compact : IsCompact (finiteCompactSet F ζ hζ) :=
  (PrincipalOfKP.fullCompactPreimageMax_isCompact F ζ hζ).image
    (finiteProjectionHom_continuous F ζ hζ)

 theorem archProjection_commutes_finite (x : RestrictedCover F ζ hζ)
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (quotientHom F ζ hζ (archProjection F ζ hζ x)) b.val := by
  obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp b.property
  have hc : Commute (archProjection F ζ hζ x) y := by
    show _ * _ = _ * _
    ext v
    cases v with
    | inl w =>
      have hw : y (Sum.inl w) = 1 := (Subgroup.mem_iInf.mp hy) w
      simp [RestrictedProduct.mul_apply, hw]
    | inr q => simp [RestrictedProduct.mul_apply, archProjection_finite]
  change quotientHom F ζ hζ y = b.val at he
  rw [← he]
  exact hc.map (quotientHom F ζ hζ)

private theorem fullCompact_factorization_commuting (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K)
    (k : PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ) :
    ∃ (a : K) (b : KPGlobalTorusFunctionData.finitePart F ζ hζ),
      b ∈ finiteCompactSet F ζ hζ ∧ k.val = a.val * b.val ∧
      ∀ c : KPGlobalTorusFunctionData.finitePart F ζ hζ, Commute a.val c.val := by
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp k.property
  refine ⟨⟨quotientHom F ζ hζ (archProjection F ζ hζ x),
    archProjection_mem F ζ hζ K hK ⟨x, hx⟩⟩,
    finiteProjectionHom F ζ hζ x, ⟨x, hx, rfl⟩, ?_,
    archProjection_commutes_finite F ζ hζ x⟩
  change k.val = quotientHom F ζ hζ (archProjection F ζ hζ x) *
    quotientHom F ζ hζ (finiteProjection F ζ hζ x)
  rw [← map_mul, ← tuple_factorization]
  exact hxe.symm

 theorem kfinite_fullCompact (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) (hk : KFinite F ζ hζ K v) :
    KFinite F ζ hζ (PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ) v := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨S, hS, hvS, hs⟩ := hk
  letI : Module.Finite ℂ S := hS
  obtain ⟨U, hU⟩ := hv.2.2
  let A := K ⊓ Subgroup.centralizer (KPGlobalTorusFunctionData.finitePart F ζ hζ : Set _)
  let W := Submodule.span ℂ (Set.range (fun a : A => rightAction F ζ hζ a.val v))
  have hWS : W ≤ S := by
    apply Submodule.span_le.mpr
    rintro w ⟨a, rfl⟩
    exact hs ⟨a.val, a.property.1⟩ v hvS
  letI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  have hWU : ∀ w ∈ W, ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      w (g * u) = w g := by
    intro w hw
    apply Submodule.span_induction (p := fun w _ => ∀ g u,
      u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U → w (g * u) = w g)
      ?_ ?_ ?_ ?_ hw
    · rintro w ⟨a, rfl⟩ g u hu
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hu
      have hc : b.val * a.val = a.val * b.val := a.property.2 b.val b.property
      change v (g * b.val * a.val) = v (g * a.val)
      rw [mul_assoc, hc, ← mul_assoc]
      exact hU _ _ ⟨b, hb, rfl⟩
    · simp
    · intro x y hx hy ihx ihy g u hu
      simp only [Pi.add_apply, ihx g u hu, ihy g u hu]
    · intro c x hx ih g u hu
      simp only [Pi.smul_apply, ih g u hu]
  let translate : KPGlobalTorusFunctionData.finitePart F ζ hζ →
      (W →ₗ[ℂ] Functions F ζ hζ) := fun b =>
    (rightAction F ζ hζ b.val).comp W.subtype
  have ht : IsLocallyConstant translate := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro b
    have he : ∀ᶠ l : KPGlobalTorusFunctionData.finitePart F ζ hζ in 𝓝 b,
        b⁻¹ * l ∈ U.toOpenSubgroup :=
      (continuous_const.mul continuous_id).continuousAt
        (by simpa using U.toOpenSubgroup.mem_nhds_one)
    filter_upwards [he] with l hl
    apply LinearMap.ext
    intro w
    funext g
    have hu : (b⁻¹ * l).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
      ⟨b⁻¹ * l, hl, rfl⟩
    simpa [translate, rightAction, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using
      hWU w.val w.property (g * b.val) _ hu
  let B := Set.range (fun b : finiteCompactSet F ζ hζ => translate b.val)
  letI : CompactSpace (finiteCompactSet F ζ hζ) :=
    isCompact_iff_compactSpace.mp (finiteCompactSet_compact F ζ hζ)
  letI : Finite B := (ht.comp_continuous continuous_subtype_val).range_finite.to_subtype
  let spaces : B → Submodule ℂ (Functions F ζ hζ) := fun t => t.val.range
  haveI : ∀ t, FiniteDimensional ℂ (spaces t) := fun t => inferInstanceAs
    (FiniteDimensional ℂ t.val.range)
  haveI : FiniteDimensional ℂ ↥(⨆ t : B, spaces t) := inferInstance
  let T := Submodule.span ℂ (Set.range (fun k : PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ =>
    rightAction F ζ hζ k.val v))
  have hT : T ≤ ⨆ t : B, spaces t := by
    apply Submodule.span_le.mpr
    rintro w ⟨k, rfl⟩
    obtain ⟨a, b, hb, he, hc⟩ := fullCompact_factorization_commuting F ζ hζ K hK k
    let a' : A := ⟨a.val, a.property, fun c h => (hc ⟨c,h⟩).eq.symm⟩
    let t : B := ⟨translate b, Set.mem_range_self (⟨b,hb⟩ : finiteCompactSet F ζ hζ)⟩
    apply Submodule.mem_iSup_of_mem t
    apply LinearMap.mem_range.mpr
    refine ⟨⟨rightAction F ζ hζ a'.val v, Submodule.subset_span ⟨a',rfl⟩⟩, ?_⟩
    ext g
    change v (g * b.val * a.val) = v (g * k.val)
    rw [he, mul_assoc, (hc b).eq.symm]
  letI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hT
  refine ⟨T, inferInstance, Submodule.subset_span ⟨1, ?_⟩, ?_⟩
  · ext g; simp [rightAction]
  · intro k w hw
    apply Submodule.span_induction (p := fun w _ => rightAction F ζ hζ k.val w ∈ T)
      ?_ ?_ ?_ ?_ hw
    · rintro w ⟨l,rfl⟩
      exact Submodule.subset_span ⟨k*l, by ext g; simp [rightAction, mul_assoc]⟩
    · exact T.zero_mem
    · intro x y hx hy ihx ihy; exact T.add_mem ihx ihy
    · intro c x hx ih; exact T.smul_mem c ih

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer
open KPLiteralRaw KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

private theorem finite_translate_locallyConstant (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) :
    IsLocallyConstant (fun b : KPGlobalTorusFunctionData.finitePart F ζ hζ =>
      rightAction F ζ hζ b.val v) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨U, hU⟩ := hv.2.2
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro b
  have he : ∀ᶠ l : KPGlobalTorusFunctionData.finitePart F ζ hζ in 𝓝 b,
      b⁻¹ * l ∈ U.toOpenSubgroup :=
    (continuous_const.mul continuous_id).continuousAt
      (by simpa using U.toOpenSubgroup.mem_nhds_one)
  filter_upwards [he] with l hl
  funext g
  have hu : (b⁻¹ * l).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    ⟨b⁻¹ * l, hl, rfl⟩
  simpa [rightAction, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using
    hU (g * b.val) _ hu

 theorem finiteCompact_translate_range (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) :
    (Set.range (fun b : finiteCompactSet F ζ hζ => rightAction F ζ hζ b.val.val v)).Finite := by
  letI : CompactSpace (finiteCompactSet F ζ hζ) :=
    isCompact_iff_compactSpace.mp (finiteCompactSet_compact F ζ hζ)
  exact ((finite_translate_locallyConstant F ζ hζ v hv).comp_continuous
    continuous_subtype_val).range_finite

open KPLiteralChamber

 theorem literal_zero_mem_canonical_core (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    literalSource F ζ hζ K f 0 ∈ KPMsRationalCompactCrossPairing.sourceCore F ζ hζ
      (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ) := by
  obtain ⟨S, hS, hfS, hstable⟩ := kfinite_fullCompact F ζ hζ K hK (f.val 0)
    (f.property.1 0).1 f.property.2.2
  letI : Module.Finite ℂ S := hS
  let e : KPMsRationalCompactCrossPairing.Source F ζ hζ 0 →ₗ[ℂ] Functions F ζ hζ :=
    { toFun := fun v => v.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : Function.Injective e := by intro v w h; exact Subtype.ext h
  let T : KPGlobalEisensteinData.CompactTypeStage
      ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp
          (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K.subtype) :=
    { space := S.comap e
      finiteDimensional := FiniteDimensional.of_injective
        (e.restrict (fun _ hv => hv : ∀ v ∈ S.comap e, e v ∈ S))
        (by
          intro v w h
          apply Subtype.ext
          apply he
          exact congrArg (fun x : S => (x : Functions F ζ hζ)) h)
      invariant := by intro k v hv; exact hstable k (e v) hv }
  obtain ⟨p, hp⟩ := literal_zero_induced_lift F ζ hζ K hK f
  have hs : literalSource F ζ hζ K f 0 ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
    refine ⟨p, ?_⟩
    apply Subtype.ext
    funext g
    rw [KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, hp]
    simp [KPGlobalTorusFunctionData.deltaHalf, literalSource]
  obtain ⟨U, hU⟩ := (f.property.1 0).1.2.2
  apply Submodule.mem_iSup_of_mem U
  apply Submodule.mem_iSup_of_mem T
  refine ⟨⟨hs, ?_⟩, hfS⟩
  intro u
  apply Subtype.ext
  funext g
  exact hU g u.val.val (Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩)

open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cutFlat → cutFlat
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cutCore → cutCore
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming cutCore_formula → cutCore_formula
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.DiscrepancyCuts renaming reweight_expansion_in_literal_core → reweight_expansion_in_literal_core

 def canonicalCutCore (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (a : ℝ) (f : Flat F ζ hζ K) :
    KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ) :=
  ⟨literalSource F ζ hζ K (cutFlat F ζ hζ K hK a f) 0,
    literal_zero_mem_canonical_core F ζ hζ K hK (cutFlat F ζ hζ K hK a f)⟩

 theorem reweight_expansion_in_canonical_core (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ C : Finset ℝ, ∀ (s : ℂ) (g : G F ζ hζ),
      Complex.exp (-s * (KPContFlatFullProductIwasawa.alpha F ζ hζ g : ℂ)) * f.val s g =
        ∑ a ∈ C, Complex.exp (s * (a : ℂ)) * (canonicalCutCore F ζ hζ K hK a f).val.val g := by
  obtain ⟨C,hC⟩ := reweight_expansion_in_literal_core F ζ hζ K hK f
  exact ⟨C,hC⟩

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer

end
end
