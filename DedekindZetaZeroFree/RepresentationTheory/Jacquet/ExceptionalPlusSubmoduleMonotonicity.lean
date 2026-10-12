module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellTestVector
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TorusEquivariantQuotient
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CuspidalSubquotientExclusion

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalJacquetImage
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

section Maps
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def subrepresentationInclusion {ρ : Representation ℂ G V}
    (N : Subrepresentation ρ) : N.toRepresentation.IntertwiningMap ρ where
  toLinearMap := N.toSubmodule.subtype
  isIntertwining' g := by rfl

def jacquetSubmoduleImage (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) :
    Submodule (MonoidAlgebra ℂ G) ρ.asModule →
      Submodule (MonoidAlgebra ℂ H) (jacquetRepresentation A ρ).asModule :=
  fun N => (jacquetMap A (subrepresentationInclusion
    (Subrepresentation.subrepresentationSubmoduleOrderIso.symm N))).range.asSubmodule

end Maps

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable (S : RawFiniteInducingData F ζ hζ q)

 def rawSectionEquiv (P : Polarization S.heisenberg) :
    (IPlus S.borel P).Equiv
      (smoothIndRepresentation S.borel.B (inducingAction S.borel P .plus 0) 1) := by
  let fwd : sectionSpace S.borel P .plus 0 →ₗ[ℂ]
      SmoothInd S.borel.B (inducingAction S.borel P .plus 0) 1 :=
    { toFun := fun f => ⟨⟨f.val, by
        intro b g
        simpa [normalizedSectionRepresentation_apply] using f.property.1 b g⟩, by
        rw [SmoothInd, mem_smoothSubmodule]
        obtain ⟨J, hJ⟩ := f.property.2
        exact ⟨J, fun j hj => Subtype.ext (hJ j hj)⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let rev : SmoothInd S.borel.B (inducingAction S.borel P .plus 0) 1 →ₗ[ℂ]
      sectionSpace S.borel P .plus 0 :=
    { toFun := fun f => ⟨f.val.val, by
        constructor
        · intro b g
          simpa [normalizedSectionRepresentation_apply] using f.val.property b g
        · obtain ⟨J, hJ⟩ := (mem_smoothSubmodule _ _).mp f.property
          exact ⟨J, fun j hj => congrArg Subtype.val (hJ j hj)⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact Representation.Equiv.mk
    { toLinearMap := fwd
      invFun := rev
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
    (by intro g; ext f x; rfl)
private theorem rawAdmissible (P : Polarization S.heisenberg) : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    exact Admissible (IPlus S.borel P) := by
  let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
  have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
  let ht := KPPGLLocalCover.finite_topological_cover F ζ hζ q m hm
  letI := ht.1
  letI : Module.Finite ℂ (InducedModule P) := tau_moduleFinite S.heisenberg P
  have hc : Continuous (KPLocalSmoothRepresentation.projection F ζ hζ q) :=
    (by
      letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
      apply (QuotientGroup.isQuotientMap_mk
        (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))).continuous_iff.mpr
      exact QuotientGroup.continuous_mk : Continuous (KPLocalSmoothRepresentation.ordinaryPGLMap F q)).comp ht.2.2.2.1.continuous
  have ho : IsOpenMap (KPLocalSmoothRepresentation.projection F ζ hζ q) :=
    (by
      letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
      apply IsOpenMap.of_comp
        (QuotientGroup.continuous_mk (N := KPPGLLocalCover.scalarSubgroup F (Sum.inr q)))
        (QuotientGroup.mk'_surjective _)
      exact QuotientGroup.isOpenMap_coe : IsOpenMap (KPLocalSmoothRepresentation.ordinaryPGLMap F q)).comp ht.2.2.2.1.isOpenMap
  have hs : Function.Surjective (KPLocalSmoothRepresentation.projection F ζ hζ q) := by
    intro g
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    obtain ⟨b, hb⟩ := KPPGLLocalCover.projection_surjective F ζ hζ (Sum.inr q)
      (KPPGLLocalCover.baseQuotient F (Sum.inr q) A)
    exact ⟨b, congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q) hb⟩
  have ha := smoothInd_admissible_of_compact_quotient S.borel.B
    (inducingAction S.borel P .plus 0) 1
    (by rw [S.borel_eq]; exact KPRankOneInduction.coveredBorel_closed F q _ hc)
    (by rw [S.borel_eq]; exact KPRankOneInduction.coveredFlag_compact F q _ hc ho hs)
  letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
  letI : AddCommGroup (EqSections S.borel.B (inducingAction S.borel P .plus 0) 1) :=
    (EqSections S.borel.B (inducingAction S.borel P .plus 0) 1).addCommGroup
  letI : AddCommGroup (SmoothInd S.borel.B (inducingAction S.borel P .plus 0) 1) :=
    (SmoothInd S.borel.B (inducingAction S.borel P .plus 0) 1).addCommGroup
  let e := rawSectionEquiv F ζ hζ q S P
  intro J
  let f : fixedSubmodule (IPlus S.borel P) J.toOpenSubgroup.toSubgroup →ₗ[ℂ]
      fixedSubmodule (smoothIndRepresentation S.borel.B (inducingAction S.borel P .plus 0) 1)
        J.toOpenSubgroup.toSubgroup :=
    (e.toLinearMap.comp (fixedSubmodule (IPlus S.borel P) J.toOpenSubgroup.toSubgroup).subtype).codRestrict _
      (fun x => fun g => by
        exact (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g.val x.val).symm.trans
          (congrArg e (x.property g)))
  letI := ha J
  apply Module.Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val hxy)
private theorem rawRoot_eq (P : Polarization S.heisenberg) :
    root S.borel = KPLocalSmoothRepresentation.upperRoot F ζ hζ q := by
  ext x
  exact (S.openCell P).upper_eq x

private theorem rawMap_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (P : Polarization S.heisenberg)
    (σ : Representation ℂ (ActualCover F ζ hζ q) V)
    [Subsingleton (KPLocalSmoothRepresentation.OrdinaryCoinvariants F ζ hζ q σ)]
    (f : σ.IntertwiningMap (IPlus S.borel P)) : f = 0 := by
  let ev : V →ₗ[ℂ] InducedModule P :=
    { toFun := fun v => (f v).val 1
      map_add' := by intros; simp only [map_add]; rfl
      map_smul' := by intros; simp only [map_smul]; rfl }
  have hk : jacquetRelations S.borel σ ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, v⟩, rfl⟩
    change ev (σ (root S.borel x) v - v) = 0
    rw [map_sub]
    change (f (σ (root S.borel x) v)).val 1 - (f v).val 1 = 0
    rw [f.isIntertwining]
    change (f v).val (1 * root S.borel x) - (f v).val 1 = 0
    rw [one_mul]
    have hc := (f v).property.1 (S.borel.upperRoot x) 1
    simp only [mul_one] at hc
    change (f v).val (S.borel.upperRoot x : ActualCover F ζ hζ q) - (f v).val 1 = 0
    rw [hc, upperRoot_trivial, sub_self]
  have hz : Subsingleton (Jacquet S.borel σ) := by
    simpa only [Jacquet, rawRoot_eq F ζ hζ q S P,
      KPLocalSmoothRepresentation.OrdinaryCoinvariants, rootCoinvariants_trivial] using
      (inferInstance : Subsingleton (KPLocalSmoothRepresentation.OrdinaryCoinvariants F ζ hζ q σ))
  let evq := (jacquetRelations S.borel σ).liftQ ev hk
  have he : ∀ v, ev v = 0 := by
    intro v
    have h : (jacquetRelations S.borel σ).mkQ v = 0 := @Subsingleton.elim _ hz _ _
    have hh := congrArg evq h
    change ev v = evq 0 at hh
    simpa using hh
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext g
  have h := he (σ g v)
  change (f (σ g v)).val 1 = 0 at h
  rw [f.isIntertwining] at h
  change (f v).val (1 * g) = 0 at h
  change (f v).val g = 0
  simpa only [one_mul] using h

private theorem rawDetection (P : Polarization S.heisenberg) : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    exact KPLocalPrincipalSeriesCuspidalExclusion.JacquetDetectsSubquotients F ζ hζ q
      (IPlus S.borel P) := by
  letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
  let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
  have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ q m hm).1
  let hs := principalSeries_smooth S.borel P .plus 0
  let ha := rawAdmissible F ζ hζ q S P
  let hb := KPLocalPrincipalSeriesCuspidalExclusion.actual_cover_compact_open_basis F ζ hζ q m hm
  intro A B hA hB hBA hJ
  by_contra hne
  have hJ' : Subsingleton (KPCyclicQuotient.ordinaryJacquet
      (KPCyclicQuotient.subquotientRepresentation (IPlus S.borel P) A B hA hB)
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)) := by
    simpa only [KPLocalSmoothRepresentation.OrdinaryCoinvariants, rootCoinvariants_trivial] using hJ
  obtain ⟨u, hu, M, hM, hQs, hQa, hCs, hCa, hCj, hnS, hiS, hsS, haS, hjS,
      hqS, hsD, hp, hsurj⟩ := KPCyclicQuotient.jacquet_zero_subquotient_cyclic_quotient
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
    (KPLocalSmoothRepresentation.continuousUpperRoot F ζ hζ q m hm).continuous
    (IPlus S.borel P) hs ha A B hA hB hBA (Ne.symm hne) hJ'
  let Q := KPCyclicQuotient.subquotientRepresentation (IPlus S.borel P) A B hA hB
  let C := KPCyclicQuotient.cyclicSubmodule Q u
  let σ := (KPCyclicQuotient.cyclicRepresentation Q u).quotient M hM
  let δ := KPCyclicQuotient.preimageRepresentation (IPlus S.borel P) A B hA hB C
    (KPCyclicQuotient.cyclicSubmodule_stable Q u)
  let qmap := (KPCyclicQuotient.quotientMap (KPCyclicQuotient.cyclicRepresentation Q u) M hM).comp
    (KPCyclicQuotient.preimageMap (IPlus S.borel P) A B hA hB C (KPCyclicQuotient.cyclicSubmodule_stable Q u))
  letI := hnS
  letI := hiS
  have hj : Subsingleton (KPLocalSmoothRepresentation.OrdinaryCoinvariants F ζ hζ q σ) := by
    simpa only [KPLocalSmoothRepresentation.OrdinaryCoinvariants, rootCoinvariants_trivial] using hjS
  have hc : CuspidalProjectiveRetract.CompactSmoothCoefficients σ := by
    intro L hL v
    apply (KPRankOneJacquetZeroCompactCoefficients.coefficient_compact_support
      F ζ hζ q σ m hm hsS _ L hL v).2
    have hn : KPRankOneJacquetZeroCompactCoefficients.upperRoot F ζ hζ q =
        KPLocalSmoothRepresentation.upperRoot F ζ hζ q := by ext t; rfl
    simpa only [KPRankOneJacquetZeroCompactCoefficients.UpperJacquet, hn,
      KPLocalSmoothRepresentation.OrdinaryCoinvariants] using hj
  obtain ⟨s, hsplit⟩ := CuspidalProjectiveRetract.lift_equivariant_surjection
    hb σ hsS haS hc (X := KPCyclicQuotient.preimage A B C) (Y := C ⧸ M)
      δ σ hsD hsS qmap hsurj (Representation.IntertwiningMap.id σ)
  let j : δ.IntertwiningMap (IPlus S.borel P) :=
    { toLinearMap := A.subtype.comp (KPCyclicQuotient.preimage A B C).subtype
      isIntertwining' := fun g => by ext x; rfl }
  letI := hj
  have hz := rawMap_zero F ζ hζ q S P σ (j.comp s)
  have hs0 : ∀ x, s x = 0 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun f : σ.IntertwiningMap (IPlus S.borel P) => f x) hz
  have hzero : ∀ x : C ⧸ M, x = 0 := by
    intro x
    have hx := congrArg (fun f : σ.IntertwiningMap σ => f x) hsplit
    change qmap (s x) = x at hx
    exact hx.symm.trans ((congrArg qmap (hs0 x)).trans qmap.map_zero)
  obtain ⟨x, hx⟩ := exists_ne (0 : C ⧸ M)
  exact hx (hzero x)

section Generic
variable {K G H D V W : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : LocalHeisenbergData H D} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
private theorem oneTwist {K U : Type*} [Field K] [AddCommGroup U] [Module ℂ U]
    (υ : Representation ℂ (Multiplicative K) U) : KPCoinvariants.twistedRepresentation υ 1 = υ := by
  ext g v
  simp [KPCoinvariants.twistedRepresentation]
private theorem rootSmooth {K G V : Type*} [Field K] [TopologicalSpace K]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hs : SmoothRepresentation ρ)
    (n : Multiplicative K →* G) (hn : Continuous n) : KPCoinvariants.IsSmooth (ρ.comp n) := by
  intro v
  have hl : IsLocallyConstant (fun g : G => ρ g v) := by
    obtain ⟨J, hJ⟩ := hs v
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro g
    refine ⟨{h : G | g⁻¹ * h ∈ J}, J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simpa using J.one_mem
    · intro h hh
      have he := hJ (g⁻¹ * h) hh
      have := congrArg (ρ g) he
      simpa [← Module.End.mul_apply, ← map_mul] using this
  exact (hl.isOpen_fiber v).preimage (hn.comp continuous_ofAdd)

private theorem raw_jacquet_inclusion_injective (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ) (N : Subrepresentation ρ) :
    Function.Injective (jacquetMap A (subrepresentationInclusion N)) := by
  let τ := N.toRepresentation
  let σ := ρ.quotient N.toSubmodule (fun g => N.apply_mem_toSubmodule g)
  let n := root A
  have hn : Continuous n := continuous_subtype_val.comp A.upperRoot_continuous
  let i : Representation.IntertwiningMap (τ.comp n) (ρ.comp n) :=
    { toLinearMap := N.toSubmodule.subtype, isIntertwining' _ := rfl }
  let p : Representation.IntertwiningMap (ρ.comp n) (σ.comp n) :=
    { toLinearMap := N.toSubmodule.mkQ, isIntertwining' _ := rfl }
  change Function.Injective (Representation.Coinvariants.map (τ.comp n) (ρ.comp n) i)
  apply KPCoinvariants.TransversalAverages.coinvariants_map_injective_of_annihilating_averages
    (τ.comp n) (ρ.comp n) i Subtype.val_injective
  intro v hv
  have hv' : v ∈ Representation.Coinvariants.ker (KPCoinvariants.twistedRepresentation (ρ.comp n) 1) := by
    simpa only [oneTwist] using hv
  obtain ⟨J, L, R, hJo, hJc, hLo, hLc, hJL, hR, hRne, hψJ, hfix, hkill⟩ :=
    KPCoinvariants.killsRelation (ρ.comp n) (rootSmooth ρ hρ n hn) 1
      (by fun_prop) (IsLocallyConstant.of_constant _ (by intros; rfl)) v hv'
  refine ⟨R, hRne, ?_⟩
  simpa only [KPCoinvariants.psiAverage, MonoidHom.one_apply, Units.val_one, inv_one, one_smul] using hkill

private theorem jacquet_range_eq_map (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) (N : Subrepresentation ρ) :
    (jacquetMap A (subrepresentationInclusion N)).range.toSubmodule =
      N.toSubmodule.map (Representation.Coinvariants.mk (ρ.comp (root A))) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    exact ⟨v.val, v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Representation.Coinvariants.mk _ ⟨v, hv⟩, rfl⟩

private theorem image_mono (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) : Monotone (jacquetSubmoduleImage A ρ) := by
  intro N M hNM
  change (jacquetMap A (subrepresentationInclusion
    (Subrepresentation.subrepresentationSubmoduleOrderIso.symm N))).range.asSubmodule ≤ _
  intro x hx
  change x ∈ (jacquetMap A (subrepresentationInclusion
    (Subrepresentation.subrepresentationSubmoduleOrderIso.symm M))).range.toSubmodule
  change x ∈ (jacquetMap A (subrepresentationInclusion
    (Subrepresentation.subrepresentationSubmoduleOrderIso.symm N))).range.toSubmodule at hx
  rw [jacquet_range_eq_map] at hx ⊢
  apply Submodule.map_mono _ hx
  exact hNM
end Generic

theorem independent_plus_jacquet_strictMono (P : Polarization S.heisenberg) : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    exact StrictMono (jacquetSubmoduleImage S.borel (IPlus S.borel P)) := by
  letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
  let ρ := IPlus S.borel P
  intro M N hMN
  apply lt_of_le_of_ne (image_mono S.borel ρ hMN.le)
  intro heq
  have comparable : ∀ (B A : Subrepresentation ρ), B ≤ A →
      (jacquetMap S.borel (subrepresentationInclusion B)).range.toSubmodule =
        (jacquetMap S.borel (subrepresentationInclusion A)).range.toSubmodule → B = A := by
    intro B A hBA him
    have hi := raw_jacquet_inclusion_injective S.borel ρ (principalSeries_smooth S.borel P .plus 0) A
    let hA : ∀ g, A.toSubmodule ≤ A.toSubmodule.comap (ρ g) := fun g => A.apply_mem_toSubmodule g
    let hB : ∀ g, B.toSubmodule ≤ B.toSubmodule.comap (ρ g) := fun g => B.apply_mem_toSubmodule g
    let Q := KPCyclicQuotient.subquotientRepresentation ρ A.toSubmodule B.toSubmodule hA hB
    let p : A.toRepresentation.IntertwiningMap Q :=
      { toLinearMap := (KPCyclicQuotient.inside A.toSubmodule B.toSubmodule).mkQ
        isIntertwining' _ := rfl }
    have hz : ∀ v : A.toSubmodule, Representation.Coinvariants.mk (Q.comp (root S.borel)) (p v) = 0 := by
      intro v
      have hv : Representation.Coinvariants.mk (ρ.comp (root S.borel)) v.val ∈
          (jacquetMap S.borel (subrepresentationInclusion A)).range.toSubmodule :=
        ⟨Representation.Coinvariants.mk _ v, rfl⟩
      have hvB : Representation.Coinvariants.mk (ρ.comp (root S.borel)) v.val ∈
          (jacquetMap S.borel (subrepresentationInclusion B)).range.toSubmodule := him.symm ▸ hv
      rw [jacquet_range_eq_map] at hvB
      obtain ⟨bval, hbmem, hbq⟩ := hvB
      let b : B.toSubmodule := ⟨bval, hbmem⟩
      let ba : A.toSubmodule := ⟨b.val, hBA b.property⟩
      have he : Representation.Coinvariants.mk (A.toRepresentation.comp (root S.borel)) ba =
          Representation.Coinvariants.mk (A.toRepresentation.comp (root S.borel)) v := by
        apply hi
        exact hbq
      have hp := congrArg (jacquetLinearMap S.borel p) he
      change Representation.Coinvariants.mk (Q.comp (root S.borel)) (p ba) =
        Representation.Coinvariants.mk (Q.comp (root S.borel)) (p v) at hp
      have hb : p ba = 0 := by
        exact (Submodule.Quotient.mk_eq_zero (KPCyclicQuotient.inside A.toSubmodule B.toSubmodule)).mpr b.property
      exact hp.symm.trans ((congrArg (Representation.Coinvariants.mk (Q.comp (root S.borel))) hb).trans (map_zero _))
    have hzero : Subsingleton (Jacquet S.borel Q) := by
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective (Q.comp (root S.borel)) x
      obtain ⟨a, ha⟩ := (KPCyclicQuotient.inside A.toSubmodule B.toSubmodule).mkQ_surjective v
      have he := congrArg (Representation.Coinvariants.mk (Q.comp (root S.borel))) ha
      exact hv.symm.trans (he.symm.trans (hz a))
    have hj : Subsingleton (KPLocalSmoothRepresentation.OrdinaryCoinvariants F ζ hζ q Q) := by
      simpa only [KPLocalSmoothRepresentation.OrdinaryCoinvariants, rootCoinvariants_trivial,
        Jacquet, rawRoot_eq F ζ hζ q S P] using hzero
    apply Subrepresentation.toSubmodule_injective
    exact (rawDetection F ζ hζ q S P A.toSubmodule B.toSubmodule hA hB hBA hj).symm
  let B := Subrepresentation.subrepresentationSubmoduleOrderIso.symm M
  let A := Subrepresentation.subrepresentationSubmoduleOrderIso.symm N
  have hBA : B ≤ A := Subrepresentation.subrepresentationSubmoduleOrderIso.symm.monotone hMN.le
  have him : (jacquetMap S.borel (subrepresentationInclusion B)).range.toSubmodule =
      (jacquetMap S.borel (subrepresentationInclusion A)).range.toSubmodule := by
    apply Submodule.ext
    intro x
    have hx := congrArg (fun U : Submodule (MonoidAlgebra ℂ (actualTorus F ζ hζ q))
      (jacquetRepresentation S.borel ρ).asModule => x ∈ U) heq
    exact Iff.of_eq hx
  have hAB := comparable B A hBA him
  apply hMN.ne
  exact Subrepresentation.subrepresentationSubmoduleOrderIso.symm.injective hAB

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps
