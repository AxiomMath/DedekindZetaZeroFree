module

public import DedekindZetaZeroFree.Adeles.Lattices.CompactOpenLevelLattices
public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical RestrictedProduct
open NumberField IsDedekindDomain NumberField.InfinitePlace

def finiteLevelFiniteInclusion (F : Type*) [Field F] [NumberField F] :
    FiniteAdeleRing (𝓞 F) F →+ AdeleRing (𝓞 F) F where
  toFun x := (0, x)
  map_zero' := rfl
  map_add' := by
    intro x y
    change (0, x + y) = (0 + 0, x + y)
    simp

def finiteLevelImage {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) :
    AddSubgroup (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) :=
  K.map ((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)).comp
    (finiteLevelFiniteInclusion F))

abbrev finiteLevelAdditiveQuotient {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) :=
  (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ⧸ finiteLevelImage K

private theorem existsOpenDiagonalZero (F : Type*) [Field F] [NumberField F] :
    ∃ U : Set (AdeleRing (𝓞 F) F), IsOpen U ∧ (0 : AdeleRing (𝓞 F) F) ∈ U ∧
      (algebraMap F (AdeleRing (𝓞 F) F)) ⁻¹' U = ({0} : Set F) := by
  classical
  let L := mixedEmbedding.integerLattice F
  obtain ⟨W, hW, hWL⟩ :=
    (isOpen_induced_iff.mp (isOpen_discrete ({0} : Set L)))
  have hW0 : (0 : mixedEmbedding.mixedSpace F) ∈ W := by
    have h : (0 : L) ∈ Subtype.val ⁻¹' W := by
      rw [hWL]
      exact Set.mem_singleton 0
    exact h
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  let U : Set (AdeleRing (𝓞 F) F) :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F ⁻¹' W) ×ˢ
      (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F))
  have hO : IsOpen (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    exact RestrictedProduct.isOpen_forall_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set _))
      (fun v => Valued.isOpen_valuationSubring _)
  refine ⟨U, (hW.preimage hc).prod hO, ?_, ?_⟩
  · constructor
    · change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ W
      simpa only [map_zero] using hW0
    · exact (integralFiniteAdeles F).zero_mem
  · ext x
    constructor
    · intro hx
      have hfinite : ∀ v : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers F),
          v.valuation F x ≤ 1 := by
        intro v
        have hv := hx.2 v
        change (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hv
        simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe] using hv
      obtain ⟨r, hr⟩ :=
        IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x hfinite
      have hL : mixedEmbedding F x ∈ L := by
        exact ⟨r, congrArg (mixedEmbedding F) hr⟩
      have hsmall : mixedEmbedding F x ∈ W := by
        rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
        exact hx.1
      have hz : (⟨mixedEmbedding F x, hL⟩ : L) = 0 := by
        have hm : (⟨mixedEmbedding F x, hL⟩ : L) ∈ Subtype.val ⁻¹' W := hsmall
        rwa [hWL, Set.mem_singleton_iff] at hm
      apply Set.mem_singleton_iff.mpr
      apply NumberField.mixedEmbedding_injective
      simpa using congrArg Subtype.val hz
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp only [Set.mem_preimage, map_zero]
      constructor
      · change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ W
        simpa only [map_zero] using hW0
      · exact (integralFiniteAdeles F).zero_mem

theorem adelePrincipalSubgroup_discrete (F : Type*) [Field F] [NumberField F] :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F) := by
  obtain ⟨U, hU, hU0, hdiag⟩ := existsOpenDiagonalZero F
  apply discreteTopology_of_isOpen_singleton_zero
  have heq : (Subtype.val : AdeleRing.principalSubgroup (𝓞 F) F → AdeleRing (𝓞 F) F) ⁻¹' U = {0} := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := a.property
      have hx0 : x = 0 := by
        have hm : x ∈ (algebraMap F (AdeleRing (𝓞 F) F)) ⁻¹' U := by
          change algebraMap F (AdeleRing (𝓞 F) F) x ∈ U
          rwa [hx]
        rwa [hdiag, Set.mem_singleton_iff] at hm
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      change (a : AdeleRing (𝓞 F) F) = 0
      simpa only [hx0, map_zero] using hx.symm
    · intro ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hU0
  rw [← heq]
  exact hU.preimage continuous_subtype_val

theorem adelePrincipalSubgroup_isClosed (F : Type*) [Field F] [NumberField F] :
    IsClosed (AdeleRing.principalSubgroup (𝓞 F) F : Set (AdeleRing (𝓞 F) F)) := by
  haveI : DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F) :=
    adelePrincipalSubgroup_discrete F
  haveI h1 : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  haveI h2 : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  haveI : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  infer_instance

 def mixedHomeo (F : Type*) [Field F] [NumberField F] :
    InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
    (fun v => v.Completion)).trans
    ((Homeomorph.prodCongr
      (Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))))
private theorem mixedHomeo_apply (F : Type*) [Field F] [NumberField F]
    (x : InfiniteAdeleRing F) : mixedHomeo F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
  rfl

theorem additiveAdeleQuotient_compactHausdorff (F : Type*) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ∧
      T2Space (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hO : IsCompact (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by

    letI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
      fun v => Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
    change IsCompact {a : RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set _)) Filter.cofinite | ∀ v, a.1 v ∈ v.adicCompletionIntegers F}
    have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set _)) (𝓕 := Filter.cofinite)).continuous
    rw [RestrictedProduct.range_structureMap] at h
    convert h using 1 <;> rfl
  have hOpen : IsOpen (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  let b := mixedEmbedding.latticeBasis F
  let e := mixedHomeo F
  let C := e ⁻¹' (b.parallelepiped : Set _)
  have hC : IsCompact C := e.isCompact_preimage.mpr b.parallelepiped.isCompact
  have hcover : (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) ''
      (C ×ˢ (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (AdeleRing.principalSubgroup (𝓞 F) F) q
    obtain ⟨r, k, hr⟩ := finiteAdele_strongApprox F (integralFiniteAdeles F) hOpen hO a.2
    have hrem : a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles F := by
      rw [hr, add_sub_cancel_left]
      exact k.property
    let y := e (a.1 - algebraMap F (InfiniteAdeleRing F) r)
    have hf : (ZSpan.floor b y : mixedEmbedding.mixedSpace F) ∈ mixedEmbedding.integerLattice F :=
      (mixedEmbedding.mem_span_latticeBasis F).mp (ZSpan.floor b y).property
    obtain ⟨s, hs⟩ := hf
    let z : F := r + (s : F)
    refine ⟨a - algebraMap F (AdeleRing (𝓞 F) F) z, ⟨?_, ?_⟩, ?_⟩
    · change e (a.1 - algebraMap F (InfiniteAdeleRing F) z) ∈ (b.parallelepiped : Set _)
      have hs' : mixedEmbedding F (s : F) = (ZSpan.floor b y : mixedEmbedding.mixedSpace F) := hs
      have hmap (x : InfiniteAdeleRing F) (t : F) :
          e (x - algebraMap F (InfiniteAdeleRing F) t) = e x - mixedEmbedding F t := by
        simp only [e, mixedHomeo_apply, map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      have hfrac : e (a.1 - algebraMap F (InfiniteAdeleRing F) z) = ZSpan.fract b y := by
        rw [ZSpan.fract_apply, ← hs']
        change e (a.1 - algebraMap F (InfiniteAdeleRing F) (r + (s : F))) =
          e (a.1 - algebraMap F (InfiniteAdeleRing F) r) - mixedEmbedding F (s : F)
        rw [hmap, hmap, map_add]
        abel
      rw [hfrac]
      exact ZSpan.fundamentalDomain_subset_parallelepiped b (ZSpan.fract_mem_fundamentalDomain b y)
    · change a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) z ∈ integralFiniteAdeles F
      have hsfin : algebraMap F (FiniteAdeleRing (𝓞 F) F) (s : F) ∈ integralFiniteAdeles F := by
        intro v
        exact HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers F) F v s
      dsimp [z]
      rw [map_add, ← sub_sub]
      exact (integralFiniteAdeles F).sub_mem hrem hsfin
    · change QuotientAddGroup.mk (a - algebraMap F (AdeleRing (𝓞 F) F) z) = QuotientAddGroup.mk a
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hz : algebraMap F (AdeleRing (𝓞 F) F) z ∈ AdeleRing.principalSubgroup (𝓞 F) F := ⟨z, rfl⟩
      simpa only [sub_sub_cancel_left] using (AdeleRing.principalSubgroup (𝓞 F) F).neg_mem hz
  have hQ : CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
    apply isCompact_univ_iff.mp
    rw [← hcover]
    exact (hC.prod hO).image QuotientAddGroup.continuous_mk
  haveI : IsClosed (AdeleRing.principalSubgroup (𝓞 F) F : Set (AdeleRing (𝓞 F) F)) :=
    adelePrincipalSubgroup_isClosed F
  exact ⟨hQ, inferInstance⟩

theorem finiteLevelImage_isCompact {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    IsCompact (finiteLevelImage K :
      Set (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F)) := by
  rw [show (finiteLevelImage K : Set _) =
      ((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)).comp
        (finiteLevelFiniteInclusion F)) '' (K : Set (FiniteAdeleRing (𝓞 F) F)) from rfl]
  refine hcompact.image ?_
  exact (QuotientAddGroup.continuous_mk (N := AdeleRing.principalSubgroup (𝓞 F) F)).comp
    (by
      show Continuous (fun x : FiniteAdeleRing (𝓞 F) F => ((0, x) : AdeleRing (𝓞 F) F))
      fun_prop)

private theorem mixedHomeo_symm (F : Type*) [Field F] [NumberField F]
    (x : mixedEmbedding.mixedSpace F) : (mixedHomeo F).symm x =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x := by rfl

set_option backward.isDefEq.respectTransparency false in

theorem finiteLevel_torus_homeomorph {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ∃ e : (NumberField.mixedEmbedding.mixedSpace F ⧸
        (finiteLevelLattice K).toAddSubgroup) ≃ₜ+ finiteLevelAdditiveQuotient K,
      ∀ x : NumberField.mixedEmbedding.mixedSpace F,
        e (QuotientAddGroup.mk x) =
          (QuotientAddGroup.mk' (finiteLevelImage K))
            ((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
              (((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) :
                AdeleRing (𝓞 F) F)) := by
  unfold AdeleRing at *
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let q := QuotientAddGroup.mk' P
  let r := QuotientAddGroup.mk' (finiteLevelImage K)
  let i : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F :=
    { toFun := fun x => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0)
      map_zero' := by
        change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0, 0) = (0, 0)
        exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_zero) rfl
      map_add' := by
        intro x y
        change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x + y), 0) =
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0 + 0)
        exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add x y) (zero_add _).symm }
  let f := r.comp (q.comp i)
  have hf : Continuous f := by
    apply QuotientAddGroup.continuous_mk.comp
    apply QuotientAddGroup.continuous_mk.comp
    have hi : Continuous (fun x : mixedEmbedding.mixedSpace F =>
        (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) : AdeleRing (𝓞 F) F)) := by
      exact ((mixedHomeo F).symm.continuous.congr (fun x => mixedHomeo_symm F x)).prodMk continuous_const
    exact hi
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk'_surjective (finiteLevelImage K) y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective P y'
    obtain ⟨lam, k, hk⟩ := finiteAdele_strongApprox F K hopen hcompact a.2
    refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F
      (a.1 - algebraMap F (InfiniteAdeleRing F) lam), ?_⟩
    change r (q (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 - algebraMap F (InfiniteAdeleRing F) lam)), 0) : AdeleRing (𝓞 F) F)) = r (q a)
    rw [RingEquiv.symm_apply_apply]
    change r (q ((a.1 - algebraMap F (InfiniteAdeleRing F) lam, 0) : AdeleRing (𝓞 F) F)) = r (q a)
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change q _ - q a ∈ finiteLevelImage K
    rw [← map_sub]
    have ha : (show AdeleRing (𝓞 F) F from (a.1 - algebraMap F (InfiniteAdeleRing F) lam, 0)) - a =
        - algebraMap F (AdeleRing (𝓞 F) F) lam + (show AdeleRing (𝓞 F) F from (0, -(k : FiniteAdeleRing (𝓞 F) F))) := by
      apply Prod.ext
      · change a.1 - algebraMap F (InfiniteAdeleRing F) lam - a.1 = -algebraMap F (InfiniteAdeleRing F) lam + 0
        abel
      · change 0 - a.2 = -algebraMap F (FiniteAdeleRing (𝓞 F) F) lam + -(k : FiniteAdeleRing (𝓞 F) F)
        rw [hk]
        abel
    rw [ha, map_add]
    have hlam : q (-algebraMap F (AdeleRing (𝓞 F) F) lam) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (P.neg_mem ⟨lam, rfl⟩)
    rw [hlam, zero_add]
    exact ⟨-(k : FiniteAdeleRing (𝓞 F) F), K.neg_mem k.property, rfl⟩
  have hker : (finiteLevelLattice K).toAddSubgroup = f.ker := by
    ext x
    change x ∈ finiteLevelLattice K ↔ r (q (i x)) = 0
    change x ∈ finiteLevelLattice K ↔ (QuotientAddGroup.mk (q (i x)) : finiteLevelAdditiveQuotient K) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    constructor
    · intro hx
      obtain ⟨lam, hlam, heq⟩ := (mem_finiteLevelLattice_iff K x).mp hx
      refine ⟨-algebraMap F (FiniteAdeleRing (𝓞 F) F) lam, K.neg_mem hlam, ?_⟩
      change q ((0, -algebraMap F (FiniteAdeleRing (𝓞 F) F) lam) : AdeleRing (𝓞 F) F) = q (i x)
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hdiff : (show AdeleRing (𝓞 F) F from (0, -algebraMap F (FiniteAdeleRing (𝓞 F) F) lam)) - i x =
          algebraMap F (AdeleRing (𝓞 F) F) (-lam) := by
        apply Prod.ext
        · change 0 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x = algebraMap F (InfiniteAdeleRing F) (-lam)
          rw [← heq, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
          simp
        · change -algebraMap F (FiniteAdeleRing (𝓞 F) F) lam - 0 = algebraMap F (FiniteAdeleRing (𝓞 F) F) (-lam)
          simp
      rw [hdiff]
      exact ⟨-lam, rfl⟩
    · rintro ⟨k, hk, heq⟩
      change q ((0, k) : AdeleRing (𝓞 F) F) = q (i x) at heq
      obtain ⟨lam, hlam⟩ := QuotientAddGroup.eq_iff_sub_mem.mp heq
      have harch : - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x = algebraMap F (InfiniteAdeleRing F) lam := by
        have h := (congrArg (fun a : AdeleRing (𝓞 F) F => a.1) hlam).symm
        change 0 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x = algebraMap F (InfiniteAdeleRing F) lam at h
        simpa only [zero_sub] using h
      have hfin : algebraMap F (FiniteAdeleRing (𝓞 F) F) lam = k := by
        have h := congrArg (fun a : AdeleRing (𝓞 F) F => a.2) hlam
        change algebraMap F (FiniteAdeleRing (𝓞 F) F) lam = k - 0 at h
        simpa only [sub_zero] using h
      apply (mem_finiteLevelLattice_iff K x).mpr
      refine ⟨-lam, by rw [map_neg, hfin]; exact K.neg_mem hk, ?_⟩
      rw [map_neg, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← harch, map_neg,
        RingEquiv.apply_symm_apply, neg_neg]
  let e := QuotientAddGroup.liftEquiv (finiteLevelLattice K).toAddSubgroup hs hker
  have he : Continuous e :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hf
  letI := finiteLevelLattice_discrete K hcompact hopen
  obtain ⟨hL, _⟩ := finiteLevelLattice_full_rank K hcompact hopen
  letI := hL
  letI : CompactSpace (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup) := by
    apply isCompact_univ_iff.mp
    have hp := IsZLattice.isCompact_range_of_periodic (finiteLevelLattice K)
      (QuotientAddGroup.mk : mixedEmbedding.mixedSpace F → mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup)
      QuotientAddGroup.continuous_mk (by
        intro z w hw
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
    simpa only [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] using hp
  letI := (additiveAdeleQuotient_compactHausdorff F).2
  letI : IsClosed (finiteLevelImage K : Set (AdeleRing (𝓞 F) F ⧸ P)) :=
    (finiteLevelImage_isCompact K hcompact).isClosed
  letI : T2Space (finiteLevelAdditiveQuotient K) := inferInstance
  exact ⟨{ e with continuous_toFun := he
                  continuous_invFun := he.homeoOfEquivCompactToT2.continuous_invFun },
    fun x => QuotientAddGroup.liftEquiv_mk _ hs hker x⟩

private theorem latticeTorus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ L) :
    Nonempty ((E ⧸ L.toAddSubgroup) ≃ₜ+ UnitAddTorus ι) := by
  let c := b.ofZLatticeBasis ℝ
  let f : E →+ UnitAddTorus ι :=
    { toFun := fun x i => (c.equivFun x i : UnitAddCircle)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    exact QuotientAddGroup.continuous_mk.comp
      ((continuous_apply i).comp c.equivFun.toContinuousLinearEquiv.continuous)
  have hs : Function.Surjective f := by
    intro y
    have hy (i : ι) : ∃ r : ℝ, (r : UnitAddCircle) = y i :=
      QuotientAddGroup.mk_surjective (y i)
    choose r hr using hy
    refine ⟨c.equivFun.symm r, ?_⟩
    ext i
    change (c.equivFun (c.equivFun.symm r) i : UnitAddCircle) = y i
    rw [LinearEquiv.apply_symm_apply]
    exact hr i
  have hk : L.toAddSubgroup = f.ker := by
    ext x
    change x ∈ L ↔ f x = 0
    rw [← b.ofZLatticeBasis_span ℝ, c.mem_span_iff_repr_mem ℤ]
    constructor
    · intro hx
      ext i
      obtain ⟨n, hn⟩ := hx i
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨n, by simpa [c, f, Module.Basis.equivFun_apply] using hn⟩
    · intro hx i
      have hi : (c.equivFun x i : UnitAddCircle) = 0 := congrFun hx i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
      exact ⟨n, by simpa [Module.Basis.equivFun_apply] using hn⟩
  let e := QuotientAddGroup.liftEquiv L.toAddSubgroup hs hk
  have he : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk L.toAddSubgroup).continuous_iff.mpr
    exact hf
  have hcomp : CompactSpace (E ⧸ L.toAddSubgroup) := by
    apply isCompact_univ_iff.mp
    have hp := IsZLattice.isCompact_range_of_periodic L
      (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup)
      QuotientAddGroup.continuous_mk (by
        intro z w hw
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
    simpa only [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] using hp
  letI := hcomp
  exact ⟨{ e with continuous_toFun := he
                  continuous_invFun := he.homeoOfEquivCompactToT2.continuous_invFun }⟩

theorem finiteLevel_single_torus {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ConnectedSpace (finiteLevelAdditiveQuotient K) ∧
      CompactSpace (finiteLevelAdditiveQuotient K) ∧
      T2Space (finiteLevelAdditiveQuotient K) ∧
      Nonempty (finiteLevelAdditiveQuotient K ≃ₜ+
        UnitAddTorus (Fin (Module.finrank ℚ F))) := by
  letI := finiteLevelLattice_discrete K hcompact hopen
  obtain ⟨hL, hrank⟩ := finiteLevelLattice_full_rank K hcompact hopen
  letI := hL
  letI := ZLattice.module_finite ℝ (finiteLevelLattice K)
  letI := ZLattice.module_free ℝ (finiteLevelLattice K)
  obtain ⟨t⟩ := latticeTorus (finiteLevelLattice K)
    (Module.finBasisOfFinrankEq ℤ (finiteLevelLattice K) hrank)
  obtain ⟨e, he⟩ := finiteLevel_torus_homeomorph K hcompact hopen
  let g := e.symm.trans t
  letI : ConnectedSpace (finiteLevelAdditiveQuotient K) := g.symm.surjective.connectedSpace g.symm.continuous
  letI : CompactSpace (finiteLevelAdditiveQuotient K) := g.symm.toHomeomorph.compactSpace
  letI : T2Space (finiteLevelAdditiveQuotient K) := g.symm.toHomeomorph.t2Space
  exact ⟨inferInstance, inferInstance, inferInstance, ⟨g⟩⟩

end
end DedekindZetaZeroFree
