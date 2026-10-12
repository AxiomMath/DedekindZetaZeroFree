module

public import DedekindZetaZeroFree.Metaplectic.Unipotent.RationalFrameConjugation

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPContinuation.RationalArchFiniteSplitting
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem infinite_section_mul (w : NumberField.InfinitePlace F)
    (A B : KPLocalCover.LocalGL2 F (Sum.inl w)) :
    KPLocalCover.sectionMap F ζ hζ (Sum.inl w) (A * B) =
      KPLocalCover.sectionMap F ζ hζ (Sum.inl w) A *
        KPLocalCover.sectionMap F ζ hζ (Sum.inl w) B := by
  have hσ : KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) A B = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      KPHilbert.B3, KPHilbert.B6_infinite]
  change KPLocalCover.CubicGL2Raw.mk (A * B) 1 =
    KPLocalCover.CubicGL2Raw.mk (A * B) (1 * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) A B)
  rw [one_mul, one_mul, hσ]

private theorem local_section_congr (w : NumberField.InfinitePlace F)
    (A B : KPLocalCover.LocalGL2 F (Sum.inl w))
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) A)) =
    scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) B)) := by
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  rw [← hz, infinite_section_mul]
  rw [map_mul, map_mul]
  have hs : scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) (Matrix.GeneralLinearGroup.scalar (Fin 2) z))) = 1 := by
    rw [← ActualFiniteFactor.localInsertion_coverQuotient]
    have hq : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨z, rfl⟩
    rw [hq, map_one]
  rw [hs, mul_one]
private theorem rational_tuple_split (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalTuple F ζ hζ A =
      ((Finset.univ : Finset (NumberField.InfinitePlace F)).toList.map
        (fun w => localToRestricted F ζ hζ (Sum.inl w)
          (rationalCoordinates F ζ hζ A (Sum.inl w)))).prod *
      KPCuspGenuineMonodromy.finiteRationalTuple F ζ hζ A := by
  apply Subtype.ext
  funext v
  let l := (Finset.univ : Finset (NumberField.InfinitePlace F)).toList
  let f := fun w => localToRestricted F ζ hζ (Sum.inl w)
    (rationalCoordinates F ζ hζ A (Sum.inl w))
  let p : RestrictedCover F ζ hζ →* KPLocalCover.CubicGL2Raw F ζ hζ v :=
    RestrictedProduct.evalMonoidHom (KPLocalCover.CubicGL2Raw F ζ hζ)
      (B := compact F ζ hζ) v
  change rationalCoordinates F ζ hζ A v =
    p ((l.map f).prod) * (KPCuspGenuineMonodromy.finiteRationalTuple F ζ hζ A) v
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
    simp [p, f, localToRestricted, KPCuspGenuineMonodromy.finiteRationalTuple]
  | inr q =>
    have hf : ∀ w, p (f w) = 1 := by
      intro w
      simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
        RestrictedProduct.coe_mulSingle_apply]
    simp [hf, KPCuspGenuineMonodromy.finiteRationalTuple]

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability in
private theorem arch_local_rational (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (w : NumberField.InfinitePlace F) :
    scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl w)
      (rationalCoordinates F ζ hζ A (Sum.inl w))) =
    scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
          (archRational (Matrix.ProjGenLinGroup.mk A) w).out))) := by
  apply local_section_congr
  let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  have hp := congrFun (rationalLift_archProjection F ζ hζ (Matrix.ProjGenLinGroup.mk A)) w
  rw [KPMsClearedTruncationL2.rationalLift_mk] at hp
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map e.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F (Sum.inl w))) A)) =
    archRational (Matrix.ProjGenLinGroup.mk A) w at hp
  have h := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) hp
  rw [Matrix.ProjGenLinGroup.map_mk] at h
  have he : Matrix.GeneralLinearGroup.map e.symm.toRingHom
      (Matrix.GeneralLinearGroup.map e.toRingHom
        (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F (Sum.inl w))) A)) =
      Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F (Sum.inl w))) A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  rw [he] at h
  calc
    _ = Matrix.ProjGenLinGroup.map e.symm.toRingHom
        (archRational (Matrix.ProjGenLinGroup.mk A) w) := h
    _ = _ := by
      rw [← Matrix.ProjGenLinGroup.map_mk]
      exact congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom)
        (Quotient.out_eq (archRational (Matrix.ProjGenLinGroup.mk A) w)).symm
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability in
private theorem rationalTuple_product (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (rationalTuple F ζ hζ A)) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (archRational (Matrix.ProjGenLinGroup.mk A)) *
      scalarQuotient F ζ hζ
        (amalgamation F ζ hζ (KPCuspGenuineMonodromy.finiteRationalTuple F ζ hζ A)) := by
  rw [rational_tuple_split, map_mul, map_mul, map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro w hw
  exact arch_local_rational F ζ hζ A w

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability in

theorem rationalLift_product (σ : KPCuspArithmetic.PGL2 F) :
    KPMsClearedTruncationL2.rationalLift F ζ hζ σ =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) *
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ :
        KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := by
  induction σ using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
    rw [KPMsClearedTruncationL2.rationalLift_mk,
      KPCuspGenuineMonodromy.finiteRationalLift_formula]
    exact rationalTuple_product F ζ hζ A

theorem rationalSubgroup_eq_lift_range :
    (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :
      Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) =
      Set.range (KPMsClearedTruncationL2.rationalLift F ζ hζ) := by
  ext g
  constructor
  · intro hg
    obtain ⟨q, hq⟩ := hg
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨Matrix.ProjGenLinGroup.mk A,
      (KPMsClearedTruncationL2.rationalLift_mk F ζ hζ A).trans hq⟩
  · rintro ⟨σ, rfl⟩
    induction σ using Matrix.ProjGenLinGroup.induction_on with
    | mk A =>
      refine ⟨KPRationalAdelicSplitting.rationalPGLQuotient F A, ?_⟩
      rw [KPRationalAdelicSplitting.rationalPGLHom_mk,
        KPMsClearedTruncationL2.rationalLift_mk]
      rfl
end DedekindZetaZeroFree.KPContinuation.RationalArchFiniteSplitting

end
