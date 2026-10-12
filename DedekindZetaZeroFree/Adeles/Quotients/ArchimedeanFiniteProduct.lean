module

public import DedekindZetaZeroFree.Adeles.Quotients.PGL.DoubleQuotientTopology
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLComplex.AffineLieDensity
public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting
open NumberField
open scoped Classical
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def insertion (g : ActualQuotient.ArchGroup F) : ActualQuotient.actualCover F ζ hζ :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map fun v =>
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (g v).out)))).prod

 def rawSection (v : InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ →* KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v) where
 toFun g := KPLocalCover.sectionMap F ζ hζ (Sum.inl v) (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom g)
 map_one' := by simp [KPLocalCover.sectionMap]; rfl
 map_mul' := by
  intro g h
  change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
  congr 1
  · simp
  · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]
theorem scalar_killed (v : InfinitePlace F) (u : ℂˣ) :
 KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v) (rawSection F ζ hζ v (Matrix.GeneralLinearGroup.scalar (Fin 2) u))) = 1 := by
 obtain ⟨j, _, _, hj⟩ := KPAdelicCoverRestrictedProduct.local_pgl_injection F ζ hζ (Sum.inl v)
 rw [← hj]
 have h : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl v) (rawSection F ζ hζ v (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom u, ?_⟩
  simp [rawSection, KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift, KPScalarSplitCentral.scalarMatrix, Matrix.GeneralLinearGroup.map_scalar]
 rw [h, map_one]
 def localHom (v : InfinitePlace F) : Matrix.ProjGenLinGroup (Fin 2) ℂ →* ActualQuotient.actualCover F ζ hζ :=
 Matrix.ProjGenLinGroup.lift
  ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
   ((KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)).comp (rawSection F ζ hζ v)))
  (by ext u; exact scalar_killed F ζ hζ v u)
private theorem localHom_out (v : InfinitePlace F) (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
 localHom F ζ hζ v g = KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v) (rawSection F ζ hζ v g.out)) := by
 conv_lhs => rw [← Quotient.out_eq g]
 rfl
private theorem local_commute : Pairwise (fun v w : InfinitePlace F => ∀ g h, Commute (localHom F ζ hζ v g) (localHom F ζ hζ w h)) := by
 intro v w hvw g h
 rw [localHom_out, localHom_out]
 apply Commute.map _ (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
 apply Commute.map _ (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)
 change Commute (KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl v) _) (KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl w) _)
 apply DFunLike.coe_injective
 exact Pi.mulSingle_commute (Sum.inl_injective.ne hvw) _ _

theorem insertion_hom :
    ∃ s : ActualQuotient.ArchGroup F →* ActualQuotient.actualCover F ζ hζ,
      ∀ a, s a = insertion F ζ hζ a := by
  let s := MonoidHom.noncommPiCoprod (localHom F ζ hζ) (local_commute F ζ hζ)
  refine ⟨s, ?_⟩
  intro a
  rw [MonoidHom.noncommPiCoprod_apply]
  have hn := Finset.noncommProd_toFinset (Finset.univ : Finset (InfinitePlace F)).toList
    (fun v => localHom F ζ hζ v (a v))
    (by intro v hv w hw h; exact local_commute F ζ hζ h _ _)
    (Finset.nodup_toList _)
  simpa [insertion, localHom_out, rawSection] using hn

end DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting
open NumberField KPAdelicCoverRestrictedProduct
open scoped Classical NumberField
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem centre_finite : (pglCentralInjection F ζ hζ).range ≤
    ActualQuotient.finiteSubgroup F ζ hζ := by
  obtain ⟨I, hI, hIm⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField F)
  let q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨I, hIm.isPrime, hI⟩
  rintro c ⟨ε, rfl⟩
  refine Subgroup.mem_map.mpr ⟨localToRestricted F ζ hζ (Sum.inr q)
    (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) ε), ?_, ?_⟩
  · intro w
    exact RestrictedProduct.mulSingle_eq_of_ne (compact F ζ hζ) _ (by simp)
  · change scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q)
      (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) ε)) = _
    rw [localInjection_central]
    rfl

private theorem gl_ext {a b : AdelicGL2 F}
    (h : ∀ v, matrixEval F v a = matrixEval F v b) : a = b := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    exact congrArg (fun g : KPLocalCover.LocalGL2 F (Sum.inl w) => g i j) (h (Sum.inl w))
  · apply RestrictedProduct.ext
    intro q
    exact congrArg (fun g : KPLocalCover.LocalGL2 F (Sum.inr q) => g i j) (h (Sum.inr q))

theorem arch_kernel_le_finite :
    (ActualQuotient.archProjection F ζ hζ).ker ≤ ActualQuotient.finiteSubgroup F ζ hζ := by
  intro c hc
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (M F ζ hζ) a
  have hs : ∀ w : InfinitePlace F, ∃ u : w.Completionˣ,
      (x (Sum.inl w)).g = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    intro w
    have hw := congrFun hc w
    change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (adeleEval F (Sum.inl w))) (restrictedProjection F ζ hζ x)) = 1 at hw
    rw [Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply] at hw
    change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
      (matrixEval F (Sum.inl w) (restrictedProjection F ζ hζ x))) = 1 at hw
    rw [restrictedProjection_eval] at hw
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hw
    obtain ⟨u, hu⟩ := hw
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    refine ⟨Units.map e.symm.toRingHom u, ?_⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      Matrix.GeneralLinearGroup.map e.toRingHom (x (Sum.inl w)).g at hu
    have he := congrArg (Matrix.GeneralLinearGroup.map e.symm.toRingHom) hu
    rw [Matrix.GeneralLinearGroup.map_scalar] at he
    have hi : Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (Matrix.GeneralLinearGroup.map e.toRingHom (x (Sum.inl w)).g) = (x (Sum.inl w)).g := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [hi] at he
    exact he.symm
  choose s hs using hs
  let z : Ideles F :=
    ⟨(fun w => (s w).val, 1), (fun w => (s w).inv, 1),
      by
        apply Prod.ext
        · funext w; exact (s w).val_inv
        · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 1 = 1; exact one_mul _,
      by
        apply Prod.ext
        · funext w; exact (s w).inv_val
        · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 1 = 1; exact one_mul _⟩
  have hz (w : InfinitePlace F) : Units.map (adeleEval F (Sum.inl w)) z = s w := by
    apply Units.ext
    rfl
  let y := x * (scalarTuple F ζ hζ z)⁻¹
  have hy (w : InfinitePlace F) : (y (Sum.inl w)).g = 1 := by
    change KPLocalCover.projection F ζ hζ (Sum.inl w) (y (Sum.inl w)) = 1
    change KPLocalCover.projection F ζ hζ (Sum.inl w)
      (x (Sum.inl w) * (scalarCoordinates F ζ hζ z (Sum.inl w))⁻¹) = 1
    rw [map_mul, map_inv]
    change (x (Sum.inl w)).g *
      (KPLocalCover.projection F ζ hζ (Sum.inl w)
        (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w)
          (Units.map (adeleEval F (Sum.inl w)) z)))⁻¹ = 1
    rw [KPScalarSplitCentral.projection_scalarHom, hz, hs]
    exact mul_inv_cancel _
  let t : RestrictedCover F ζ hζ := ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => y (Sum.inr q), by
      filter_upwards [y.property] with v hv
      cases v with
      | inl w => exact (compact F ζ hζ (Sum.inl w)).one_mem
      | inr q => exact hv⟩
  have ht : t ∈ ActualQuotient.finiteTuples F ζ hζ := by intro w; rfl
  have hp : restrictedProjection F ζ hζ y = restrictedProjection F ζ hζ t := by
    apply gl_ext F
    intro v
    rw [restrictedProjection_eval, restrictedProjection_eval]
    cases v with
    | inl w => change (y (Sum.inl w)).g = 1; exact hy w
    | inr q => rfl
  have hk : amalgamation F ζ hζ y * (amalgamation F ζ hζ t)⁻¹ ∈
      (projection F ζ hζ).ker := by
    change projection F ζ hζ (_ * _⁻¹) = 1
    rw [map_mul, map_inv, projection_amalgamation, projection_amalgamation, hp]
    exact mul_inv_cancel _
  rw [← range_centralInjection_eq_ker] at hk
  obtain ⟨ε, hε⟩ := hk
  have hscalar : scalarQuotient F ζ hζ (scalarHom F ζ hζ z) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
  have hxy : scalarQuotient F ζ hζ (amalgamation F ζ hζ y) =
      scalarQuotient F ζ hζ (amalgamation F ζ hζ x) := by
    change scalarQuotient F ζ hζ (amalgamation F ζ hζ (x * (scalarTuple F ζ hζ z)⁻¹)) = _
    rw [map_mul, map_inv, map_mul, map_inv]
    change scalarQuotient F ζ hζ (amalgamation F ζ hζ x) *
      (scalarQuotient F ζ hζ (scalarHom F ζ hζ z))⁻¹ = _
    rw [hscalar, inv_one, mul_one]
  have heq : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) =
      pglCentralInjection F ζ hζ ε * scalarQuotient F ζ hζ (amalgamation F ζ hζ t) := by
    rw [← hxy]
    have he := congrArg (scalarQuotient F ζ hζ) hε
    simp only [map_mul, map_inv] at he
    change pglCentralInjection F ζ hζ ε = _ at he
    exact (eq_mul_inv_iff_mul_eq.mp he).symm
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ x) ∈ _
  rw [heq]
  exact (ActualQuotient.finiteSubgroup F ζ hζ).mul_mem
    (centre_finite F ζ hζ ⟨ε, rfl⟩) (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)

end DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

theorem commuting_split_product
    {A G : Type*} [Group A] [Group G]
    [TopologicalSpace A] [TopologicalSpace G]
    [IsTopologicalGroup A] [IsTopologicalGroup G]
    (p : G →* A) (s : A →* G) (H : Subgroup G)
    (hp : Continuous p) (hs : Continuous s)
    (hsec : ∀ a, p (s a) = a) (hker : p.ker = H)
    (hcomm : ∀ a (h : H), Commute (s a) (h : G)) :
    ∃ e : (A × H) ≃ₜ* G,
      (∀ a h, e (a, h) = s a * h) ∧
      (∀ g, (e.symm g).1 = p g) := by
  have hH : ∀ h : H, p (h : G) = 1 := by
    intro h
    have hm : (h : G) ∈ p.ker := by rw [hker]; exact h.property
    exact hm
  let r : G → H := fun g => ⟨(s (p g))⁻¹ * g, by
    rw [← hker]
    change p ((s (p g))⁻¹ * g) = 1
    simp only [map_mul, map_inv, hsec, inv_mul_cancel]⟩
  let e : (A × H) ≃ₜ* G :=
    { toFun := fun x => s x.1 * x.2
      invFun := fun g => (p g, r g)
      left_inv := by
        intro x
        apply Prod.ext
        · simp only [map_mul, hsec, hH, mul_one]
        · apply Subtype.ext
          change (s (p (s x.1 * (x.2 : G))))⁻¹ * (s x.1 * (x.2 : G)) = x.2
          simp only [map_mul, hsec, hH, mul_one, inv_mul_cancel_left]
      right_inv := by
        intro g
        change s (p g) * ((s (p g))⁻¹ * g) = g
        simp only [mul_inv_cancel_left]
      map_mul' := by
        intro x y
        change s (x.1 * y.1) * ((x.2 : G) * (y.2 : G)) =
          (s x.1 * (x.2 : G)) * (s y.1 * (y.2 : G))
        rw [map_mul]
        exact ((hcomm y.1 x.2).symm.mul_mul_mul_comm (s x.1) (y.2 : G)).symm
      continuous_toFun := (hs.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := hp.prodMk
        (((hs.comp hp).inv.mul continuous_id).subtype_mk _) }
  exact ⟨e, fun _ _ => rfl, fun _ => rfl⟩

end DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem insertion_commutes_finite (a : ActualQuotient.ArchGroup F)
    (h : ActualQuotient.finiteSubgroup F ζ hζ) :
    Commute (insertion F ζ hζ a) (h : ActualQuotient.actualCover F ζ hζ) := by
  classical
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp h.property
  change ∀ w : NumberField.InfinitePlace F, g (Sum.inl w) = 1 at hg
  rw [← hge]
  unfold insertion
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  change Commute
    (((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))
      (KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl v) _))
    (((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)) g)
  apply Commute.map
  change _ * g = g * _
  apply RestrictedProduct.ext
  intro w
  cases w with
  | inl w => simp [hg w]
  | inr q =>
    simp [KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply]

end DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting
open NumberField
open scoped Classical
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem local_insertion_continuous (w : InfinitePlace F) :
    Continuous (fun g : Matrix.ProjGenLinGroup (Fin 2) ℂ =>
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w)
          (KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
            (Matrix.GeneralLinearGroup.map
              (InfinitePlace.Completion.ringEquivComplexOfIsComplex
                (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom g.out)))) := by
  letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI := KPAdelicCoverRestrictedProduct.pglLocalTopology F ζ hζ
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  let s : Matrix.GeneralLinearGroup (Fin 2) ℂ →*
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) := {
    toFun := fun g => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom g)
    map_one' := by
      simp only [map_one]
      rfl
    map_mul' := by
      intro g h
      change KPLocalCover.CubicGL2Raw.mk _ 1 =
        KPLocalCover.CubicGL2Raw.mk _
          (1 * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _)
      rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
      simp only [one_mul, map_mul, KPLocalCover.sectionMap_g] }
  have hs : Continuous s := by
    apply continuous_induced_rng.mpr
    change Continuous (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ =>
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom g, (1 : rootsOfUnity 3 F)))
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.continuous.generalLinearGroup_map.prodMk
        continuous_const
  obtain ⟨j, _, hj, hformula⟩ :=
    KPAdelicCoverRestrictedProduct.local_pgl_injection F ζ hζ (Sum.inl w)
  let t := j.comp ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)).comp s)
  have ht : Continuous t := hj.comp (QuotientGroup.continuous_mk.comp hs)
  have hk : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) ≤ t.ker := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u, rfl⟩ := hg
    have hscalar : s (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
        KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w)
          (Units.map e.symm.toRingHom u) := by
      simp [s, Matrix.GeneralLinearGroup.map_scalar,
        KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
        KPScalarSplitCentral.scalarMatrix]
    change j (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
      (s (Matrix.GeneralLinearGroup.scalar (Fin 2) u))) = 1
    rw [hscalar]
    have hz : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
        (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w)
          (Units.map e.symm.toRingHom u)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
    rw [hz, map_one]
  let l := QuotientGroup.lift (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)) t hk
  have hl : Continuous l :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ht
  change Continuous (fun g : Matrix.ProjGenLinGroup (Fin 2) ℂ => l g) at hl
  apply hl.congr
  intro g
  calc
    l g = l (Matrix.ProjGenLinGroup.mk g.out) :=
      congrArg l (Quotient.out_eq g).symm
    _ = _ := hformula _

theorem splitting_maps_continuous :
    Continuous (insertion F ζ hζ) ∧
      Continuous (ActualQuotient.archProjection F ζ hζ) := by
  constructor
  · letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
    apply continuous_list_prod
    intro w hw
    exact (local_insertion_continuous F ζ hζ w).comp (continuous_apply w)
  · have hp : Continuous (KPAdelicCoverRestrictedProduct.projection F ζ hζ) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (KPAdelicCoverRestrictedProduct.restrictedProjection_continuous F ζ hζ)
    have hpg : Continuous (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp hp)
    have ha : Continuous (ActualQuotient.glArchProjection F ζ hζ) := by
      apply continuous_pi
      intro w
      apply QuotientGroup.continuous_mk.comp
      apply Continuous.generalLinearGroup_map
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).continuous.comp
          ((continuous_apply w).comp continuous_fst)
    have hdesc : Continuous (QuotientGroup.lift
        (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
        (ActualQuotient.glArchProjection F ζ hζ)
        (by
          intro g hg
          obtain ⟨u, rfl⟩ := hg
          ext w
          change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
            (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
          rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar])) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ha
    exact hdesc.comp hpg

end DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem projective_t2 : T2Space (Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  have he : (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      Set (Matrix.GeneralLinearGroup (Fin 2) ℂ)) =
      ⋂ g : Matrix.GeneralLinearGroup (Fin 2) ℂ, {h | g * h = h * g} := by
    ext h
    simp [Subgroup.mem_center_iff]
  haveI : IsClosed (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      Set (Matrix.GeneralLinearGroup (Fin 2) ℂ)) := by
    rw [he]
    exact isClosed_iInter (fun g => isClosed_eq (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const))
  exact inferInstanceAs (T2Space (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

private theorem finite_le_kernel : ActualQuotient.finiteSubgroup F ζ hζ ≤
    (ActualQuotient.archProjection F ζ hζ).ker := by
  rintro c ⟨x, hx, rfl⟩
  change ActualQuotient.archProjection F ζ hζ
    (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) = 1
  ext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (restrictedProjection F ζ hζ x)) = 1
  rw [Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (matrixEval F (Sum.inl w) (restrictedProjection F ζ hζ x))) = 1
  rw [restrictedProjection_eval, hx w]
  simp

theorem finite_factor_locallyCompact :
    LocallyCompactSpace (ActualQuotient.finiteSubgroup F ζ hζ) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := projective_t2
  have hker : (ActualQuotient.archProjection F ζ hζ).ker =
      ActualQuotient.finiteSubgroup F ζ hζ :=
    le_antisymm (arch_kernel_le_finite F ζ hζ) (finite_le_kernel F ζ hζ)
  apply IsClosed.locallyCompactSpace
  rw [← hker]
  exact isClosed_singleton.preimage (splitting_maps_continuous F ζ hζ).2

end DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AdelicSlicesRaw
open MeasureTheory Topology NumberField
open scoped Classical Pointwise NumberField ENNReal Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ActualCover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ

abbrev rationalSplit := KPRationalAdelicSplitting.rationalPGLHom F ζ hζ

abbrev rationalSubgroup : Subgroup (ActualCover F ζ hζ) :=
  (rationalSplit F ζ hζ).range

abbrev X := _root_.Quotient (QuotientGroup.rightRel (rationalSubgroup F ζ hζ))

instance : MeasurableSpace (ActualCover F ζ hζ) := borel _

instance : MeasurableSpace (X F ζ hζ) := borel _

instance : BorelSpace (ActualCover F ζ hζ) := ⟨rfl⟩

instance : BorelSpace (X F ζ hζ) := ⟨rfl⟩

def finiteTuples : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) where
  carrier := {g | ∀ w : NumberField.InfinitePlace F, g (Sum.inl w) = 1}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh w; simp [hg w, hh w]
  inv_mem' := by intro g hg w; simp [hg w]

def finiteSubgroup : Subgroup (ActualCover F ζ hζ) :=
  (finiteTuples F ζ hζ).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

abbrev FiniteLevel := CompactOpenLevel (finiteSubgroup F ζ hζ)

def levelSubgroup (U : FiniteLevel F ζ hζ) : Subgroup (ActualCover F ζ hζ) :=
  U.toOpenSubgroup.toSubgroup.map (finiteSubgroup F ζ hζ).subtype

abbrev centreMap := KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ

def rightSubgroup (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    Subgroup (ActualCover F ζ hζ) :=
  if geometric then levelSubgroup F ζ hζ U ⊔ (centreMap F ζ hζ).range
  else levelSubgroup F ζ hζ U

abbrev LevelSpace (U : FiniteLevel F ζ hζ) (geometric : Bool) :=
  DoubleCoset.Quotient (rationalSubgroup F ζ hζ : Set (ActualCover F ζ hζ))
    (rightSubgroup F ζ hζ U geometric : Set (ActualCover F ζ hζ))

instance (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    TopologicalSpace (LevelSpace F ζ hζ U geometric) :=
  inferInstanceAs (TopologicalSpace (_root_.Quotient _))

instance (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    MeasurableSpace (LevelSpace F ζ hζ U geometric) := borel _

abbrev ArchGroup := NumberField.InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

instance : TopologicalSpace (ArchGroup F) := Pi.topologicalSpace

instance : MeasurableSpace (ArchGroup F) := borel _

def glArchProjection : KPAdelicCoverRestrictedProduct.AdelicGL2 F →* ArchGroup F where
  toFun g w := Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))) g)
  map_one' := by ext w; simp
  map_mul' := by intro g h; ext w; simp

theorem scalars_le_arch_kernel : KPAdelicCoverRestrictedProduct.scalarSubgroup F ≤
    (glArchProjection F ζ hζ).ker := by
  rintro g ⟨u, rfl⟩
  change glArchProjection F ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1
  ext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
  rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar]

def archProjection : ActualCover F ζ hζ →* ArchGroup F :=
  (QuotientGroup.lift (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (glArchProjection F ζ hζ) (scalars_le_arch_kernel F ζ hζ)).comp
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

def archimedeanInsertion (g : ArchGroup F) : ActualCover F ζ hζ :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map fun v =>
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (g v).out)))).prod

open KPAdelicCoverRestrictedProduct
theorem archProjection_restricted_eval (x : RestrictedCover F ζ hζ) (w : InfinitePlace F) :
  archProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) w =
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom (x (Sum.inl w)).g) := by
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (projection F ζ hζ (amalgamation F ζ hζ x))) = _
  rw [projection_amalgamation]
  rw [Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
  rw [show Matrix.GeneralLinearGroup.map (adeleEval F (Sum.inl w))
    (restrictedProjection F ζ hζ x) = (x (Sum.inl w)).g from
      restrictedProjection_eval F ζ hζ x (Sum.inl w)]
private theorem splitting_local_arch (v w : InfinitePlace F) (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v)) :
 archProjection F ζ hζ (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v) g)) w =
 Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
 (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
 ((localToRestricted F ζ hζ (Sum.inl v) g (Sum.inl w)).g)) := by
 change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _ _) = _
 rw [Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
 congr 2
private theorem splitting_local_arch_same (v : InfinitePlace F) (a : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
 archProjection F ζ hζ (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v)
 (KPLocalCover.sectionMap F ζ hζ (Sum.inl v) (Matrix.GeneralLinearGroup.map
 (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom a.out)))) v = a := by
 rw [splitting_local_arch]
 change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
   ((RestrictedProduct.mulSingle (compact F ζ hζ) (Sum.inl v) _ (Sum.inl v)).g)) = a
 rw [RestrictedProduct.mulSingle_eq_same, KPLocalCover.sectionMap_g]
 have he : Matrix.GeneralLinearGroup.map
     (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ v)).toRingHom
     (Matrix.GeneralLinearGroup.map
       (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom a.out) = a.out := by
   apply Matrix.GeneralLinearGroup.ext
   intro i j
   simp [Matrix.GeneralLinearGroup.map_apply]
 rw [he]
 exact Quotient.out_eq a
private theorem splitting_local_arch_ne (v w : InfinitePlace F) (hne : v ≠ w)
 (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v)) :
 archProjection F ζ hζ (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v) g)) w = 1 := by
 rw [splitting_local_arch]
 change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
   ((RestrictedProduct.mulSingle (compact F ζ hζ) (Sum.inl v) g (Sum.inl w)).g)) = 1
 have h : (RestrictedProduct.mulSingle (compact F ζ hζ) (Sum.inl v) g (Sum.inl w)) = 1 :=
   RestrictedProduct.mulSingle_eq_of_ne' (compact F ζ hζ) g (by simpa using hne)
 rw [h]
 simp

theorem archProjection_archimedeanInsertion (a : ArchGroup F) : archProjection F ζ hζ (archimedeanInsertion F ζ hζ a) = a := by
 ext w
 let f : InfinitePlace F → ActualCover F ζ hζ := fun v =>
   scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v)
     (KPLocalCover.sectionMap F ζ hζ (Sum.inl v) (Matrix.GeneralLinearGroup.map
       (InfinitePlace.Completion.ringEquivComplexOfIsComplex
         (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (a v).out)))
 let p : ActualCover F ζ hζ →* Matrix.ProjGenLinGroup (Fin 2) ℂ :=
   (Pi.evalMonoidHom _ w).comp (archProjection F ζ hζ)
 change p ((Finset.univ.toList.map f).prod) = a w
 rw [map_list_prod]
 simp only [List.map_map, Function.comp_def]
 rw [List.prod_map_eq_pow_single w (fun v => p (f v)) (by
   intro v hv _
   exact splitting_local_arch_ne F ζ hζ v w hv _)]
 have hc : (Finset.univ : Finset (InfinitePlace F)).toList.count w = 1 := by
   exact List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)
 rw [hc, pow_one]
 exact splitting_local_arch_same F ζ hζ w (a w)

theorem centreMap_range_le_finiteSubgroup : (centreMap F ζ hζ).range ≤ finiteSubgroup F ζ hζ := by
 obtain ⟨I, hI, hIm⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField F)
 let q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨I, hIm.isPrime, hI⟩
 rintro c ⟨ε, rfl⟩
 refine Subgroup.mem_map.mpr ⟨localToRestricted F ζ hζ (Sum.inr q)
   (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) ε), ?_, ?_⟩
 · intro w
   exact RestrictedProduct.mulSingle_eq_of_ne (compact F ζ hζ) _ (by simp)
 · change scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q)
     (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) ε)) = _
   rw [localInjection_central]
   rfl

theorem finiteSubgroup_le_archProjection_ker : finiteSubgroup F ζ hζ ≤ (archProjection F ζ hζ).ker := by
 rintro c ⟨x, hx, rfl⟩
 change archProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) = 1
 ext w
 change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
   (restrictedProjection F ζ hζ x)) = 1
 rw [Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
 change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
   (matrixEval F (Sum.inl w) (restrictedProjection F ζ hζ x))) = 1
 rw [restrictedProjection_eval, hx w]
 simp

theorem actualArchFiniteSplitting :
    ∃ e : (ArchGroup F × finiteSubgroup F ζ hζ) ≃ₜ* ActualCover F ζ hζ,
      (∀ a h, e (a, h) = archimedeanInsertion F ζ hζ a * h) ∧
      (∀ g, (e.symm g).1 = archProjection F ζ hζ g) ∧
      (∀ a, archProjection F ζ hζ (archimedeanInsertion F ζ hζ a) = a) ∧
      (archProjection F ζ hζ).ker = finiteSubgroup F ζ hζ ∧
      (centreMap F ζ hζ).range ≤ finiteSubgroup F ζ hζ ∧
      LocallyCompactSpace (finiteSubgroup F ζ hζ) := by
  letI : IsTopologicalGroup (ActualCover F ζ hζ) :=
    (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
  obtain ⟨s, hs⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  have hsraw : ∀ a, s a = archimedeanInsertion F ζ hζ a := hs
  have hker : (archProjection F ζ hζ).ker = finiteSubgroup F ζ hζ := by
    apply le_antisymm
    · exact RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
    · exact finiteSubgroup_le_archProjection_ker F ζ hζ
  obtain ⟨hinsertion, hprojection⟩ :=
    RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ
  have hscont : Continuous s := by
    have heq : (s : ArchGroup F → ActualCover F ζ hζ) =
        RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ := funext hs
    rw [heq]
    exact hinsertion
  have hsec : ∀ a, archProjection F ζ hζ (s a) = a := by
    intro a
    rw [hsraw]
    exact archProjection_archimedeanInsertion F ζ hζ a
  have hcomm : ∀ a (h : finiteSubgroup F ζ hζ), Commute (s a) (h : ActualCover F ζ hζ) := by
    intro a h
    rw [hsraw]
    exact RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a h
  obtain ⟨e, he, hep⟩ := RepresentationTheory.ArchFiniteSplitting.commuting_split_product
    (archProjection F ζ hζ) s (finiteSubgroup F ζ hζ)
    hprojection hscont hsec hker hcomm
  refine ⟨e, ?_, hep, archProjection_archimedeanInsertion F ζ hζ,
    hker, centreMap_range_le_finiteSubgroup F ζ hζ, ?_⟩
  · intro a h
    rw [he, hsraw]
  · exact RepresentationTheory.ArchFiniteSplitting.finite_factor_locallyCompact F ζ hζ

end DedekindZetaZeroFree.PGLComplex.AdelicSlicesRaw

end

end
