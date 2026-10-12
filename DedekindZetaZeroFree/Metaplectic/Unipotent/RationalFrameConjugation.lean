module

public import DedekindZetaZeroFree.Geometry.PGL.Horospheres.RationalRootAction
public import DedekindZetaZeroFree.Adeles.Approximation.UpperRoots.FiniteRootReduction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archProjection_compare (g : KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) g
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _ (projection F ζ hζ g)) =
    Matrix.ProjGenLinGroup.map _ (Matrix.ProjGenLinGroup.mk (matrixEval F (Sum.inl w) (projection F ζ hζ g)))
  rw [Matrix.ProjGenLinGroup.map_mk, Matrix.GeneralLinearGroup.map_comp]
  rfl

theorem insertion_commutes_cover (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  have hc : c.val ∈ (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
    rw [MonoidHom.mem_ker]
    funext w
    rw [archProjection_compare]
    have he := c.property
    rw [MonoidHom.mem_ker] at he
    rw [he]
    exact map_one _
  have hm := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.2.2.2.1
  rw [hm] at hc
  exact RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a ⟨c.val, hc⟩

def complexParameter (a : NumberField.InfiniteAdeleRing F) : NumberField.InfinitePlace F → ℂ :=
  fun w => NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w) (a w)

private theorem map_upper {K L : Type} [Field K] [Field L] (f : K →+* L) (t : K) :
    Matrix.GeneralLinearGroup.map f (KubotaRankTwo.n K t) = KubotaRankTwo.n L (f t) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, KubotaRankTwo.coe_n]

theorem root_arch_insertion (a : NumberField.InfiniteAdeleRing F) :
    KPGlobalTorusFunctionData.N F ζ hζ (a,0) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRoot (complexParameter F ζ hζ a)) := by
  unfold archRoot
  rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  simp only [map_upper]
  have he : ∀ w, (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (complexParameter F ζ hζ a w) = a w := by
    intro w
    exact RingEquiv.symm_apply_apply _ _
  simp only [complexParameter, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  let l := (Finset.univ : Finset (NumberField.InfinitePlace F)).toList
  let f := fun w => localToRestricted F ζ hζ (Sum.inl w)
    (KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (a w))
  have ht : KPGlobalTorusFunctionData.rootTuple F ζ hζ (a,0) = (l.map f).prod := by
    apply Subtype.ext
    funext v
    let p : RestrictedCover F ζ hζ →* KPLocalCover.CubicGL2Raw F ζ hζ v :=
      RestrictedProduct.evalMonoidHom (KPLocalCover.CubicGL2Raw F ζ hζ)
        (B := compact F ζ hζ) v
    change _ = p ((l.map f).prod)
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def]
    cases v with
    | inl w =>
      rw [List.prod_map_eq_pow_single w (fun v => p (f v)) (by
        intro v hv _
        simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
          RestrictedProduct.coe_mulSingle_apply, hv])]
      have hc : l.count w = 1 := List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp [l])
      rw [hc, pow_one]
      simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
        KPGlobalTorusFunctionData.rootTuple, adeleEval, RingHom.fst]
      rfl
    | inr q =>
      have hf : ∀ w, p (f w) = 1 := by
        intro w
        simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
          RestrictedProduct.coe_mulSingle_apply]
      simp [hf, KPGlobalTorusFunctionData.rootTuple, adeleEval, RingHom.snd, KPStandardLocalRootLifts.N_zero]
      change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) 0 = 1
      exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inr q)
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ (KPGlobalTorusFunctionData.rootTuple F ζ hζ (a,0))) = _
  rw [ht, map_list_prod, map_list_prod]
  simp only [List.map_map]
  rfl

private theorem projective_equiv_injective {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) : Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) e.toRingHom) := by
  intro x y h
  have h' := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) h
  simp only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp] at h'
  simpa using h'

theorem complex_kernel_mem {g : KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ}
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g = 1) :
    g ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [MonoidHom.mem_ker]
  funext w
  apply projective_equiv_injective
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w))
  rw [← archProjection_compare, hg]
  exact (map_one _).symm

theorem rationalLift_archProjection (σ : KPCuspArithmetic.PGL2 F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (KPMsClearedTruncationL2.rationalLift F ζ hζ σ) = archRational σ := by
  have hs : σ = Matrix.ProjGenLinGroup.mk σ.out := (Quotient.out_eq σ).symm
  rw [hs, KPMsClearedTruncationL2.rationalLift_mk]
  funext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (projection F ζ hζ (rationalSection F ζ hζ σ.out))) = _
  rw [projection_rationalSection]
  have hmap : (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
      ((adeleEval F (Sum.inl w)).comp (algebraMap F (Adeles F))) = w.embedding := by
    ext x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap F w.Completion x) = w.embedding x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      ((WithAbs.equiv w.1).symm x : w.Completion) = _
    simp
  change Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ σ.out)) = _
  simp only [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
  rw [RingHom.comp_assoc, hmap]
  unfold archRational
  simp only [MonoidHom.comp_apply]
  rw [← Matrix.ProjGenLinGroup.map_mk, ← Matrix.ProjGenLinGroup.map_mk]
  exact congrArg (Matrix.ProjGenLinGroup.map w.embedding)
    (Quotient.out_eq (Matrix.ProjGenLinGroup.mk σ.out)).symm

theorem rationalLift_split (σ : KPCuspArithmetic.PGL2 F) :
    ∃ s : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      KPMsClearedTruncationL2.rationalLift F ζ hζ σ =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val := by
  let r := KPMsClearedTruncationL2.rationalLift F ζ hζ σ
  let i := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ)
  have hm : i⁻¹ * r ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
    apply complex_kernel_mem
    rw [map_mul, map_inv]
    change (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (archRational σ)))⁻¹ *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ r = 1
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, rationalLift_archProjection,
      inv_mul_cancel]
  exact ⟨⟨i⁻¹ * r, hm⟩, by change r = i * (i⁻¹ * r); group⟩

private theorem conjugation_split {G : Type} [Group G] (i s z n : G)
    (hsz : Commute s z) (his : Commute i s) (hin : Commute i n) :
    (i * s) * (z * n) * (i * s)⁻¹ =
      (i * z * i⁻¹) * (s * n * s⁻¹) := by
  rw [mul_inv_rev, hsz.mul_mul_mul_comm]
  have hsi : Commute (s * n) i⁻¹ := (his.symm.mul_left hin.symm).inv_right
  calc
    i * z * (s * n) * (s⁻¹ * i⁻¹) =
        (i * z) * (s * n) * (i⁻¹ * s⁻¹) := by rw [his.symm.inv_left.inv_right.eq]
    _ = (i * z) * i⁻¹ * ((s * n) * s⁻¹) := by
      exact (hsi.mul_mul_mul_comm (i * z) s⁻¹).trans (by group)
    _ = _ := by group

theorem conjugated_root_split (σ : KPCuspArithmetic.PGL2 F)
    (s : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hs : KPMsClearedTruncationL2.rationalLift F ζ hζ σ =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val)
    (a : NumberField.InfiniteAdeleRing F)
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    KPMsClearedTruncationL2.rationalLift F ζ hζ σ *
      KPGlobalTorusFunctionData.N F ζ hζ (a,z) *
      (KPMsClearedTruncationL2.rationalLift F ζ hζ σ)⁻¹ =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (archRational σ * archRoot (complexParameter F ζ hζ a) * (archRational σ)⁻¹) *
      (s * finiteRoot F ζ hζ z * s⁻¹).val := by
  have he : (a,z) = (a, (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) + (0,z) := by
    apply Prod.ext <;> simp
  rw [he, KPGlobalTorusFunctionData.N_add, root_arch_insertion, hs]
  change (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val) *
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRoot (complexParameter F ζ hζ a)) *
      (finiteRoot F ζ hζ z).val) *
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) * s.val)⁻¹ =
    _ * (s.val * (finiteRoot F ζ hζ z).val * s.val⁻¹)
  rw [conjugation_split _ _ _ _
    (insertion_commutes_cover F ζ hζ _ s).symm
    (insertion_commutes_cover F ζ hζ _ s)
    (insertion_commutes_cover F ζ hζ _ (finiteRoot F ζ hζ z))]
  congr 1
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  change _ = RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
  rw [← hih, map_mul, map_mul, map_inv]
  simp only [hih]
  rfl

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end
