module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.EquivariantAffineUnitCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPCuspMonodromy
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ

def archProjection : Cover F ζ hζ →*
    (∀ w : NumberField.InfinitePlace F, Matrix.ProjGenLinGroup (Fin 2) w.Completion) :=
  QuotientGroup.lift (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ)
    ((MonoidHom.pi (fun w => Matrix.ProjGenLinGroup.mk.comp
      (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)))).comp
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ)) (by
      intro c hc
      obtain ⟨z, rfl⟩ := hc
      change (fun w => Matrix.ProjGenLinGroup.mk
        (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
          (KPAdelicCoverRestrictedProduct.projection F ζ hζ
            (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ z)))) = 1
      rw [KPAdelicCoverRestrictedProduct.projection_scalarHom]
      funext w
      simp [KPAdelicCoverRestrictedProduct.matrixEval,
        Matrix.GeneralLinearGroup.map_scalar])

def finiteProjection : Cover F ζ hζ →* KPFiniteComponents.FinitePGL2 F :=
  QuotientGroup.lift (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ)
    ((Matrix.ProjGenLinGroup.mk.comp
      (Matrix.GeneralLinearGroup.map (RingHom.snd _ _))).comp
        (KPAdelicCoverRestrictedProduct.projection F ζ hζ)) (by
      intro c hc
      obtain ⟨z, rfl⟩ := hc
      change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
          (KPAdelicCoverRestrictedProduct.projection F ζ hζ
            (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ z))) = 1
      rw [KPAdelicCoverRestrictedProduct.projection_scalarHom]
      erw [Matrix.GeneralLinearGroup.map_scalar]
      exact Matrix.ProjGenLinGroup.mk_scalar _)

abbrev FiniteCover := (archProjection F ζ hζ).ker

def finiteBase : FiniteCover F ζ hζ →* KPFiniteComponents.FinitePGL2 F :=
  (finiteProjection F ζ hζ).comp (FiniteCover F ζ hζ).subtype

 def pairGL {R S : Type*} [CommRing R] [CommRing S]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (B : Matrix.GeneralLinearGroup (Fin 2) S) :
    Matrix.GeneralLinearGroup (Fin 2) (R × S) where
  val i j := (A i j, B i j)
  inv i j := (A⁻¹ i j, B⁻¹ i j)
  val_inv := by
    apply Matrix.ext
    intro i j
    erw [Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
    apply Prod.ext
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, apply_ite] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M i j) A.val_inv
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, apply_ite] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M i j) B.val_inv
  inv_val := by
    apply Matrix.ext
    intro i j
    erw [Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
    apply Prod.ext
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, apply_ite] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M i j) A.inv_val
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, apply_ite] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M i j) B.inv_val

 def finiteMatrix (A : Matrix.GeneralLinearGroup (Fin 2) (KPFiniteComponents.FiniteAdeles F)) :
    KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
  pairGL (1 : Matrix.GeneralLinearGroup (Fin 2) (NumberField.InfiniteAdeleRing F)) A

private theorem finiteMatrix_continuous : Continuous (finiteMatrix F) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    exact continuous_const.prodMk (by fun_prop)
  · apply continuous_matrix
    intro i j
    exact continuous_const.prodMk (by fun_prop)

theorem projected_finite_level_compact_open
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    IsCompact ((U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)) :
      Set (KPFiniteComponents.FinitePGL2 F)) ∧
    IsOpen ((U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)) :
      Set (KPFiniteComponents.FinitePGL2 F)) := by
  have hc : Continuous (finiteProjection F ζ hζ) := by
    apply (QuotientGroup.isQuotientMap_mk
      (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp
      ((continuous_snd.generalLinearGroup_map).comp
        (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.2.continuous)
  refine ⟨U.isCompact.image (hc.comp continuous_subtype_val), ?_⟩
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp U.toOpenSubgroup.isOpen
  have h1V : (1 : Cover F ζ hζ) ∈ V := by
    have hh : (1 : FiniteCover F ζ hζ) ∈ (U.toOpenSubgroup : Set _) := U.toOpenSubgroup.one_mem
    rw [← hVU] at hh
    exact hh
  let W : Set (KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ ⁻¹' V
  have hW : IsOpen W := hV.preimage QuotientGroup.continuous_mk
  have h1W : (1 : KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ) ∈ W := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ 1 ∈ V
    simpa using h1V
  obtain ⟨e, he, heq⟩ :=
    (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.2 1
  have he1 : e 1 = 1 := by rw [← heq]; exact map_one _
  have hm1 : finiteMatrix F 1 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hN : {A : Matrix.GeneralLinearGroup (Fin 2) (KPFiniteComponents.FiniteAdeles F) |
      finiteMatrix F A ∈ e.target ∧ e.symm (finiteMatrix F A) ∈ W} ∈ nhds 1 := by
    have ht := e.open_target.mem_nhds (e.map_source he)
    have hw := (e.continuousAt_symm (e.map_source he)).preimage_mem_nhds
      (hW.mem_nhds (by simpa [e.left_inv he] using h1W))
    have hh : e.target ∩ (e.symm ⁻¹' W) ∈ nhds (finiteMatrix F 1) := by
      simpa only [hm1, he1] using Filter.inter_mem ht hw
    exact (finiteMatrix_continuous F).continuousAt.preimage_mem_nhds hh
  let H := U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)
  haveI : IsTopologicalGroup
      (Matrix.GeneralLinearGroup (Fin 2) (KPFiniteComponents.FiniteAdeles F)) := by
    unfold Matrix.GeneralLinearGroup
    infer_instance
  haveI : IsTopologicalGroup (KPFiniteComponents.FinitePGL2 F) :=
    KPFiniteAdelicLatticeStabilizers.projective_topological_group F
  apply H.isOpen_of_mem_nhds (g := 1)
  have hn := (QuotientGroup.isOpenMap_coe (N := Subgroup.center
    (Matrix.GeneralLinearGroup (Fin 2) (KPFiniteComponents.FiniteAdeles F)))).image_mem_nhds hN
  change Matrix.ProjGenLinGroup.mk '' _ ∈ nhds (Matrix.ProjGenLinGroup.mk 1) at hn
  rw [map_one] at hn
  apply Filter.mem_of_superset hn
  rintro _ ⟨A, hA, rfl⟩
  let c := e.symm (finiteMatrix F A)
  have hp : KPAdelicCoverRestrictedProduct.projection F ζ hζ c = finiteMatrix F A := by
    rw [heq]
    exact e.right_inv hA.1
  let t := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ c
  have ht : t ∈ FiniteCover F ζ hζ := by
    change archProjection F ζ hζ t = 1
    change (fun w => Matrix.ProjGenLinGroup.mk
      (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
        (KPAdelicCoverRestrictedProduct.projection F ζ hζ c))) = 1
    rw [hp]
    funext w
    have ha : KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w) (finiteMatrix F A) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    simp [ha]
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · change (⟨t, ht⟩ : FiniteCover F ζ hζ) ∈ (U.toOpenSubgroup : Set _)
    rw [← hVU]
    exact hA.2
  · change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
        (KPAdelicCoverRestrictedProduct.projection F ζ hζ c)) = _
    rw [hp]
    rfl

end DedekindZetaZeroFree.KPCuspMonodromy

end
