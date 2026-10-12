module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.GL2Projection
public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology

@[expose] public section

open scoped NumberField Classical BigOperators Topology
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] localTopology

 theorem localCubicGL2_hausdorff_locallyCompactGroup_CentralExtension (v : KPHilbert.Place F) :
    T2Space (KPLocalCover.CubicGL2Raw F ζ hζ v) ∧
      LocallyCompactSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) ∧
      IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w =>
    have h := KPLocalChartTopology.complex_topological_cover F ζ hζ w
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  | inr q =>
    exact KPLocalChartTopology.finite_topological_group F ζ hζ q
      (depth F ζ hζ q) (depth_admissible F ζ hζ q)

instance local_t2 (v : KPHilbert.Place F) :
    T2Space (KPLocalCover.CubicGL2Raw F ζ hζ v) := (localCubicGL2_hausdorff_locallyCompactGroup_CentralExtension F ζ hζ v).1

instance local_group_instance (v : KPHilbert.Place F) :
    IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := (localCubicGL2_hausdorff_locallyCompactGroup_CentralExtension F ζ hζ v).2.2

 instance local_lc (v : KPHilbert.Place F) :
    LocallyCompactSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) := (localCubicGL2_hausdorff_locallyCompactGroup_CentralExtension F ζ hζ v).2.1

 instance compact_open_fact :
    Fact (∀ v, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
  ⟨compact_open F ζ hζ⟩

theorem centralTupleMap_central :
    (centralTupleMap F ζ hζ).range ≤ Subgroup.center (RestrictedCover F ζ hζ) := by
  rintro x ⟨ε, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply RestrictedProduct.ext
  intro v
  exact (Subgroup.mem_center_iff.mp
    (KPLocalCover.centralInjection_range_le_center F ζ hζ v ⟨ε v, rfl⟩)) (y v)

def M : Subgroup (RestrictedCover F ζ hζ) :=
  (centralProduct F).ker.map (centralTupleMap F ζ hζ)

theorem M_central : M F ζ hζ ≤ Subgroup.center (RestrictedCover F ζ hζ) := by
  rintro x ⟨ε, hε, rfl⟩
  exact centralTupleMap_central F ζ hζ ⟨ε, rfl⟩

instance M_normal : (M F ζ hζ).Normal :=
  Subgroup.normal_of_le_center (M_central F ζ hζ)

theorem M_closed : IsClosed (M F ζ hζ : Set (RestrictedCover F ζ hζ)) := by
  haveI := (restricted_kernel_discrete F ζ hζ).1
  apply isClosed_of_subset_discrete_closed (t := ((restrictedProjection F ζ hζ).ker : Set _))
  · rintro x ⟨ε, hε, rfl⟩
    rw [restrictedProjection_kernel]
    exact ⟨ε, rfl⟩
  · exact isDiscrete_iff_discreteTopology.mpr inferInstance
  · exact (restricted_kernel_discrete F ζ hζ).2

abbrev CubicGL2Adelic := RestrictedCover F ζ hζ ⧸ M F ζ hζ

def amalgamation : RestrictedCover F ζ hζ →* CubicGL2Adelic F ζ hζ :=
  QuotientGroup.mk' (M F ζ hζ)

def localInjection (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v →* CubicGL2Adelic F ζ hζ :=
  (amalgamation F ζ hζ).comp (localToRestricted F ζ hζ v)

def centralSingle (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) : CentralTuples F :=
  RestrictedProduct.mulSingle (fun _ => (⊥ : Subgroup (rootsOfUnity 3 F))) v ε

theorem centralProduct_single (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) :
    centralProduct F (centralSingle F v ε) = ε := by
  change (∏ᶠ w, centralSingle F v ε w) = ε
  rw [finprod_eq_single _ v]
  · exact RestrictedProduct.mulSingle_eq_same _ _ _
  · intro w hw
    exact RestrictedProduct.mulSingle_eq_of_ne _ _ hw

theorem centralTupleMap_single (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) :
    centralTupleMap F ζ hζ (centralSingle F v ε) =
      localToRestricted F ζ hζ v (KPLocalCover.centralInjection F ζ hζ v ε) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    simp [centralTupleMap, centralSingle, localToRestricted, RestrictedProduct.mulSingleMonoidHom]
  · simp [centralTupleMap, centralSingle, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
      RestrictedProduct.mulSingle_eq_of_ne, hw]

theorem localInjection_injective (v : KPHilbert.Place F) :
    Function.Injective (localInjection F ζ hζ v) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨ε, hε, he⟩ := (QuotientGroup.eq_one_iff _).mp hg
  have hsingle : ε = centralSingle F v (ε v) := by
    apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst w
      exact (RestrictedProduct.mulSingle_eq_same
        (fun _ : KPHilbert.Place F => (⊥ : Subgroup (rootsOfUnity 3 F))) v (ε v)).symm
    · have hew := congrArg (fun x : RestrictedCover F ζ hζ => x w) he
      have hroot : ε w = 1 := by
        apply (map_eq_one_iff _ (KPLocalCover.centralInjection_injective F ζ hζ w)).mp
        simpa [centralTupleMap, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
          RestrictedProduct.mulSingle_eq_of_ne, hw] using hew
      simpa [centralSingle, RestrictedProduct.mulSingle_eq_of_ne, hw] using hroot
  have hv : ε v = 1 := by
    have hp : centralProduct F ε = 1 := hε
    rwa [hsingle, centralProduct_single] at hp
  have he' := congrArg (fun x : RestrictedCover F ζ hζ => x v) he
  simpa [centralTupleMap, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
    RestrictedProduct.mulSingle_eq_same, hv] using he'.symm

theorem localInjection_continuous (v : KPHilbert.Place F) :
    Continuous (localInjection F ζ hζ v) := by
  let s : Set (KPHilbert.Place F) := {v}ᶜ
  have hs : Filter.cofinite ≤ Filter.principal s :=
    Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite
  let f : KPLocalCover.CubicGL2Raw F ζ hζ v →
      RestrictedProduct (fun w => KPLocalCover.CubicGL2Raw F ζ hζ w)
        (fun w => (compact F ζ hζ w : Set _)) (Filter.principal s) := fun g =>
    ⟨Pi.mulSingle v g, by
      intro w hw
      have hwv : w ≠ v := hw
      simpa [Pi.mulSingle_eq_of_ne hwv] using (compact F ζ hζ w).one_mem⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_mulSingle v)
  exact QuotientGroup.continuous_mk.comp
    ((RestrictedProduct.continuous_inclusion hs).comp hf)

def distinguishedPlace : KPHilbert.Place F :=
  Sum.inl (Classical.choice (inferInstance : Nonempty (InfinitePlace F)))

def centralInjection : rootsOfUnity 3 F →* CubicGL2Adelic F ζ hζ :=
  (localInjection F ζ hζ (distinguishedPlace F)).comp
    (KPLocalCover.centralInjection F ζ hζ (distinguishedPlace F))

theorem localInjection_central (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) :
    localInjection F ζ hζ v (KPLocalCover.centralInjection F ζ hζ v ε) =
      centralInjection F ζ hζ ε := by
  change amalgamation F ζ hζ (localToRestricted F ζ hζ v
    (KPLocalCover.centralInjection F ζ hζ v ε)) =
    amalgamation F ζ hζ (localToRestricted F ζ hζ (distinguishedPlace F)
    (KPLocalCover.centralInjection F ζ hζ (distinguishedPlace F) ε))
  rw [← centralTupleMap_single, ← centralTupleMap_single]
  apply (div_eq_one.mp ?_)
  rw [← map_div, ← map_div]
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨centralSingle F v ε / centralSingle F (distinguishedPlace F) ε, ?_, rfl⟩
  change centralProduct F (_ / _) = 1
  simp only [map_div, centralProduct_single]
  exact div_self' ε

theorem M_le_ker : M F ζ hζ ≤ (restrictedProjection F ζ hζ).ker := by
  rw [restrictedProjection_kernel]
  rintro x ⟨ε, hε, rfl⟩
  exact ⟨ε, rfl⟩

def projection : CubicGL2Adelic F ζ hζ →* AdelicGL2 F :=
  QuotientGroup.lift (M F ζ hζ) (restrictedProjection F ζ hζ) (M_le_ker F ζ hζ)

@[simp] theorem projection_amalgamation (x : RestrictedCover F ζ hζ) :
    projection F ζ hζ (amalgamation F ζ hζ x) = restrictedProjection F ζ hζ x := rfl

theorem centralInjection_injective : Function.Injective (centralInjection F ζ hζ) := by
  exact (localInjection_injective F ζ hζ (distinguishedPlace F)).comp
    (KPLocalCover.centralInjection_injective F ζ hζ (distinguishedPlace F))

theorem projection_surjective : Function.Surjective (projection F ζ hζ) := by
  intro g
  obtain ⟨x, rfl⟩ := restrictedProjection_surjective F ζ hζ g
  exact ⟨amalgamation F ζ hζ x, rfl⟩

theorem range_centralInjection_eq_ker :
    (centralInjection F ζ hζ).range = (projection F ζ hζ).ker := by
  ext x
  induction x using QuotientGroup.induction_on with | _ g =>
    constructor
    · rintro ⟨ε, he⟩
      rw [← he]
      change restrictedProjection F ζ hζ
        (localToRestricted F ζ hζ (distinguishedPlace F)
          (KPLocalCover.centralInjection F ζ hζ (distinguishedPlace F) ε)) = 1
      rw [← centralTupleMap_single]
      apply (restrictedProjection F ζ hζ).mem_ker.mp
      rw [restrictedProjection_kernel]
      exact ⟨centralSingle F (distinguishedPlace F) ε, rfl⟩
    · intro hg
      have hker : g ∈ (restrictedProjection F ζ hζ).ker := hg
      rw [restrictedProjection_kernel] at hker
      obtain ⟨ε, rfl⟩ := hker
      refine ⟨centralProduct F ε, ?_⟩
      change amalgamation F ζ hζ (localToRestricted F ζ hζ (distinguishedPlace F)
        (KPLocalCover.centralInjection F ζ hζ (distinguishedPlace F) (centralProduct F ε))) = _
      rw [← centralTupleMap_single]
      change amalgamation F ζ hζ (centralTupleMap F ζ hζ
        (centralSingle F (distinguishedPlace F) (centralProduct F ε))) =
        amalgamation F ζ hζ (centralTupleMap F ζ hζ ε)
      apply div_eq_one.mp
      rw [← map_div, ← map_div]
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨centralSingle F (distinguishedPlace F) (centralProduct F ε) / ε, ?_, rfl⟩
      change centralProduct F (_ / _) = 1
      simp only [map_div, centralProduct_single]
      exact div_self' _

theorem centralInjection_central :
    (centralInjection F ζ hζ).range ≤ Subgroup.center (CubicGL2Adelic F ζ hζ) := by
  rintro x ⟨ε, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  induction y using QuotientGroup.induction_on with | _ g =>
    change amalgamation F ζ hζ g * amalgamation F ζ hζ _ =
      amalgamation F ζ hζ _ * amalgamation F ζ hζ g
    rw [← centralTupleMap_single]
    exact congrArg (amalgamation F ζ hζ)
      ((Subgroup.mem_center_iff.mp (centralTupleMap_central F ζ hζ
        ⟨centralSingle F (distinguishedPlace F) ε, rfl⟩)) g)

theorem projection_localInjection (v w : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    matrixEval F w (projection F ζ hζ (localInjection F ζ hζ v g)) =
      (localToRestricted F ζ hζ v g w).g := by
  exact restrictedProjection_eval F ζ hζ (localToRestricted F ζ hζ v g) w

theorem adelic_discrete_kernel :
    DiscreteTopology (projection F ζ hζ).ker ∧
      letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
      ∃ e : rootsOfUnity 3 F ≃ₜ (projection F ζ hζ).ker,
        ∀ ε, (e ε).val = centralInjection F ζ hζ ε := by
  letI : IsClosed (M F ζ hζ : Set (RestrictedCover F ζ hζ)) := M_closed F ζ hζ
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  let f : rootsOfUnity 3 F → (projection F ζ hζ).ker := fun ε =>
    ⟨centralInjection F ζ hζ ε, by
      rw [← range_centralInjection_eq_ker]
      exact ⟨ε, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro ε δ h
      exact centralInjection_injective F ζ hζ (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ (centralInjection F ζ hζ).range := by
        rw [range_centralInjection_eq_ker]
        exact x.property
      obtain ⟨ε, hε⟩ := hx
      exact ⟨ε, Subtype.ext hε⟩
  let e := Equiv.ofBijective f hf
  letI : Finite (projection F ζ hζ).ker := Finite.of_equiv _ e
  letI : DiscreteTopology (projection F ζ hζ).ker := inferInstance
  exact ⟨inferInstance, e.toHomeomorphOfDiscrete, fun _ => rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem local_secondCountable (v : KPHilbert.Place F) :
    SecondCountableTopology (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w =>
    letI : SecondCountableTopology w.Completion := by
      rcases w.isReal_or_isComplex with hv | hv
      · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
      · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology
    letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) := by
      change SecondCountableTopology (Fin 2 → Fin 2 → w.Completion)
      infer_instance
    letI : SecondCountableTopology (KPHilbert.Completion F (Sum.inl w)) := by
      change SecondCountableTopology w.Completion
      infer_instance
    letI : SecondCountableTopology (KPLocalCover.LocalGL2 F (Sum.inl w)) := by
      haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w))) := by
        change SecondCountableTopology (Fin 2 → Fin 2 → KPHilbert.Completion F (Sum.inl w))
        infer_instance
      letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))ᵐᵒᵖ :=
        MulOpposite.opHomeomorph.symm.secondCountableTopology
      exact Units.isEmbedding_embedProduct.secondCountableTopology
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    have hi : Topology.IsEmbedding (KPLocalChartTopology.complexCoordinates F ζ hζ w) :=
      ⟨⟨rfl⟩, (KPLocalChartTopology.complexCoordinates F ζ hζ w).injective⟩
    exact hi.secondCountableTopology
  | inr q =>
    letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
    letI : TopologicalSpace.SeparableSpace (q.adicCompletion F) :=
      ⟨⟨Set.range (algebraMap F (q.adicCompletion F)), Set.countable_range _,
        HeightOneSpectrum.denseRange_algebraMap F q⟩⟩
    letI : SecondCountableTopology (q.adicCompletion F) := inferInstance
    letI : SecondCountableTopology (KPHilbert.Completion F (Sum.inr q)) := by
      change SecondCountableTopology (q.adicCompletion F)
      infer_instance
    letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q))) := by
      change SecondCountableTopology (Fin 2 → Fin 2 → KPHilbert.Completion F (Sum.inr q))
      infer_instance
    letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q)))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    letI : SecondCountableTopology (KPLocalCover.LocalGL2 F (Sum.inr q)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    letI : SecondCountableTopology (KPLocalCube.LocalGL2 F q) := by
      letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalField F q)) := by
        change SecondCountableTopology (Fin 2 → Fin 2 → q.adicCompletion F)
        infer_instance
      letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalField F q))ᵐᵒᵖ :=
        MulOpposite.opHomeomorph.symm.secondCountableTopology
      exact Units.isEmbedding_embedProduct.secondCountableTopology
    let m := depth F ζ hζ q
    have hm := depth_admissible F ζ hζ q
    let U (g : KPLocalCover.LocalGL2 F (Sum.inr q)) : Set (KPLocalCover.LocalGL2 F (Sum.inr q)) :=
      Set.range ((Homeomorph.mulLeft g) ∘ (Subtype.val : KPLocalCube.Gamma F q m → _))
    have hU (g : KPLocalCover.LocalGL2 F (Sum.inr q)) : U g ∈ 𝓝 g := by
      have ho : Topology.IsOpenEmbedding ((Homeomorph.mulLeft g) ∘
          (Subtype.val : KPLocalCube.Gamma F q m → _)) := (Homeomorph.mulLeft g).isOpenEmbedding.comp
        (KPLocalCube.Gamma_compact_open F q m hm.1).2.isOpenEmbedding_subtypeVal
      have heq : (Homeomorph.mulLeft g : _ → _) ∘ (Subtype.val : KPLocalCube.Gamma F q m → _) =
          (fun k : KPLocalCube.Gamma F q m => g * k.val) := rfl
      have hopen : IsOpen (U g) := by
        simpa only [U, Set.image_univ, heq] using ho.isOpen_range
      apply hopen.mem_nhds
      exact ⟨1, mul_one g⟩
    obtain ⟨s, hs, hcover⟩ := LindelofSpace.elim_nhds_subcover U hU
    letI : Countable s := hs.to_subtype
    let V (g : s) : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
      {x | x.g ∈ U g.val}
    have hV (g : s) : IsOpen (V g) := by
      have ho := (Homeomorph.mulLeft g.val).isOpenEmbedding.comp
        (KPLocalCube.Gamma_compact_open F q m hm.1).2.isOpenEmbedding_subtypeVal
      exact ho.isOpen_range.preimage
        (KPLocalChartTopology.finite_projection F ζ hζ q m hm).1.continuous
    letI : ∀ g : s, SecondCountableTopology (V g) := fun g => by
      letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
      letI : SecondCountableTopology (KPLocalCube.Gamma F q m) :=
        Topology.IsEmbedding.subtypeVal.secondCountableTopology
      letI : SecondCountableTopology (rootsOfUnity 3 F) := inferInstance
      obtain ⟨e, _⟩ := KPLocalChartTopology.finite_three_sheet_trivialization F ζ hζ q m hm g.val
      have heq : V g = {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) |
          x.g ∈ (fun k : KPLocalCube.Gamma F q m => g.val * k.val) '' Set.univ} := by
        ext x
        simp only [V, U, Set.mem_setOf_eq, Set.image_univ]
        rfl
      rw [heq]
      exact e.symm.secondCountableTopology
    apply TopologicalSpace.secondCountableTopology_of_countable_cover hV
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.g ∈ ⋃ g ∈ s, U g := by rw [hcover]; trivial
    obtain ⟨g, hg, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hx⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restricted_secondCountable : SecondCountableTopology (RestrictedCover F ζ hζ) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (𝓞 F) := Function.Injective.countable RingOfIntegers.coe_injective
  letI : Countable (Ideal (𝓞 F)) := by
    have h : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (↑s : Set (𝓞 F))) := by
      intro I
      exact IsNoetherian.noetherian I
    exact h.countable
  letI : Countable (HeightOneSpectrum (𝓞 F)) :=
    Function.Injective.countable (fun _ _ h => HeightOneSpectrum.ext h)
  letI : ∀ v : KPHilbert.Place F, SecondCountableTopology
      (KPLocalCover.CubicGL2Raw F ζ hζ v) := local_secondCountable F ζ hζ
  let X := fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v
  let C := fun v : KPHilbert.Place F => (compact F ζ hζ v : Set (X v))
  let f (s : Finset (KPHilbert.Place F)) :=
    RestrictedProduct.inclusion X C (Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite)
  let U (s : Finset (KPHilbert.Place F)) : Set (RestrictedCover F ζ hζ) := Set.range (f s)
  have hf (s : Finset (KPHilbert.Place F)) : Topology.IsOpenEmbedding (f s) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal (compact_open F ζ hζ) _
  letI (s : Finset (KPHilbert.Place F)) :
      SecondCountableTopology (RestrictedProduct X C (Filter.principal (↑s : Set _)ᶜ)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  letI : ∀ s : Finset (KPHilbert.Place F), SecondCountableTopology (U s) :=
    fun s => (hf s).toIsEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) (fun s => (hf s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro a
  have ha : {v | a v ∉ compact F ζ hζ v}.Finite := a.2
  apply Set.mem_iUnion_of_mem ha.toFinset
  refine Set.mem_range.mpr ⟨⟨a.1, ?_⟩, rfl⟩
  intro v hv
  change a v ∈ compact F ζ hζ v
  simpa using hv

theorem adelic_topological_cover :
    T2Space (CubicGL2Adelic F ζ hζ) ∧ LocallyCompactSpace (CubicGL2Adelic F ζ hζ) ∧
      IsTopologicalGroup (CubicGL2Adelic F ζ hζ) ∧
      IsLocalHomeomorph (projection F ζ hζ) := by
  have hcompact : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      IsCompact (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := by
    have hfin : (Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F)).Finite :=
      Set.finite_range _
    filter_upwards [hfin.compl_mem_cofinite] with v hv
    cases v with
    | inl w => exact (hv ⟨w, rfl⟩).elim
    | inr q => exact (finiteCompact_compact_open F ζ hζ q).1
  letI : LocallyCompactSpace (RestrictedCover F ζ hζ) :=
    RestrictedProduct.locallyCompactSpace_of_group
      (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (B := compact F ζ hζ) hcompact
  letI : IsClosed (M F ζ hζ : Set (RestrictedCover F ζ hζ)) := M_closed F ζ hζ
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have hc : Continuous (projection F ζ hζ) :=
    (QuotientGroup.isQuotientMap_mk (M F ζ hζ)).continuous_iff.mpr
      (restrictedProjection_continuous F ζ hζ)
  have ho_raw : IsOpenMap (restrictedProjection F ζ hζ) := by
    letI : SecondCountableTopology (RestrictedCover F ζ hζ) :=
      restricted_secondCountable F ζ hζ
    letI : SigmaCompactSpace (RestrictedCover F ζ hζ) := inferInstance
    letI : LocallyCompactSpace (Adeles F) := KPAdelicTopology.adeles_locallyCompactSpace F
    letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (Adeles F)) := by
      change LocallyCompactSpace (Fin 2 → Fin 2 → Adeles F)
      infer_instance
    letI : LocallyCompactSpace (AdelicGL2 F) := inferInstance
    exact (restrictedProjection F ζ hζ).isOpenMap_of_sigmaCompact
        (restrictedProjection_surjective F ζ hζ) (restrictedProjection_continuous F ζ hζ)
  have ho : IsOpenMap (projection F ζ hζ) :=
    IsOpenMap.of_comp QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective (M F ζ hζ)) ho_raw
  haveI : DiscreteTopology (projection F ζ hζ).ker := (adelic_discrete_kernel F ζ hζ).1
  exact ((ho.isQuotientMap hc (projection_surjective F ζ hζ)).isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isLocalHomeomorph

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
