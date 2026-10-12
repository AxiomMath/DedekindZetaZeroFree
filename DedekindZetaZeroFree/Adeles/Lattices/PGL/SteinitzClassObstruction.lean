module

public import DedekindZetaZeroFree.Adeles.Lattices.RankTwo.LocalIntegralOrbits
public import DedekindZetaZeroFree.Adeles.Lattices.RankTwo.RationalIntersectionRealization

@[expose] public section

section

open scoped Pointwise

namespace DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

private theorem intersection_mem (F : Type*) [Field F] [NumberField F]
    (g : AdelicGL F) (x : F × F) :
    x ∈ (intersectionLattice F g).val ↔ diagonalVector F x ∈ g • integralVectors F :=
  (Classical.choose_spec ((bounded_crt_lattice_and_projective_compact F).2 g)).1 x

theorem intersectionLattice_mul_integral (F : Type*) [Field F] [NumberField F]
    (g : AdelicGL F) (k : integralGL F) :
    intersectionLattice F (g * k) = intersectionLattice F g := by
  apply Subtype.ext
  apply Submodule.ext
  intro x
  rw [intersection_mem, intersection_mem, mul_smul]
  have hk : (k : AdelicGL F) • integralVectors F = integralVectors F :=
    MulAction.mem_stabilizer_iff.mp k.property
  rw [hk]

 noncomputable def rationalVectorAction (F : Type*) [Field F] (h : RationalGL F) :
    (F × F) ≃ₗ[F] (F × F) :=
  (LinearEquiv.finTwoArrow F F).symm.trans
    ((Matrix.GeneralLinearGroup.toLin h).toLinearEquiv.trans
      (LinearEquiv.finTwoArrow F F))

private theorem diagonalVector_action (F : Type*) [Field F] [NumberField F]
    (h : RationalGL F) (x : F × F) :
    diagonalVector F (rationalVectorAction F h x) = diagonalGL F h • diagonalVector F x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalVector, rationalVectorAction, diagonalGL,
      Matrix.GeneralLinearGroup.smul_def, Matrix.GeneralLinearGroup.toLin_apply,
      Matrix.mul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, LinearEquiv.finTwoArrow, finTwoArrowEquiv]

private theorem intersectionLattice_diagonal_map (F : Type*) [Field F] [NumberField F]
    (h : RationalGL F) (g : AdelicGL F) :
    Submodule.map ((rationalVectorAction F h).toLinearMap.restrictScalars
      (NumberField.RingOfIntegers F)) (intersectionLattice F g).val =
        (intersectionLattice F (diagonalGL F h * g)).val := by
  let e := rationalVectorAction F h
  apply Submodule.ext
  intro x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [intersection_mem, mul_smul]
    change diagonalVector F (rationalVectorAction F h y) ∈ _
    rw [diagonalVector_action]
    exact Set.smul_mem_smul_set (intersection_mem F g y |>.mp hy)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [intersection_mem]
    have he : diagonalVector F x = diagonalGL F h • diagonalVector F (e.symm x) := by
      simpa only [← show e = rationalVectorAction F h from rfl, e.apply_symm_apply] using
        diagonalVector_action F h (e.symm x)
    rw [intersection_mem, mul_smul, he] at hx
    exact (Set.smul_mem_smul_set_iff).mp hx

theorem intersectionLattice_diagonal_equivalent (F : Type*) [Field F] [NumberField F]
    (h : RationalGL F) (g : AdelicGL F) :
    latticeEquivalent (NumberField.RingOfIntegers F) F
      (intersectionLattice F g).val (intersectionLattice F (diagonalGL F h * g)).val :=
  ⟨rationalVectorAction F h, intersectionLattice_diagonal_map F h g⟩

theorem intersectionLattice_doubleCoset_rel (F : Type*) [Field F] [NumberField F]
    {g g' : AdelicGL F}
    (hrel : DoubleCoset.setoid ((diagonalGL F).range : Set (AdelicGL F))
      (integralGL F : Set (AdelicGL F)) g g') :
    latticeSetoid (NumberField.RingOfIntegers F) F
      (intersectionLattice F g) (intersectionLattice F g') := by
  obtain ⟨h, ⟨a, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.mp hrel
  rw [show intersectionLattice F (diagonalGL F a * g * k) =
      intersectionLattice F (diagonalGL F a * g) from
    intersectionLattice_mul_integral F _ ⟨k, hk⟩]
  exact intersectionLattice_diagonal_equivalent F a g

noncomputable def glLatticeMap (F : Type*) [Field F] [NumberField F] :
    DoubleCoset.Quotient ((diagonalGL F).range : Set (AdelicGL F))
      (integralGL F : Set (AdelicGL F)) →
      Quotient (latticeSetoid (NumberField.RingOfIntegers F) F) :=
  Quotient.map (intersectionLattice F) (fun {_ _} h => intersectionLattice_doubleCoset_rel F h)

@[simp] theorem glLatticeMap_mk (F : Type*) [Field F] [NumberField F] (g : AdelicGL F) :
    glLatticeMap F (DoubleCoset.mk (diagonalGL F).range (integralGL F) g) =
      Quotient.mk (latticeSetoid (NumberField.RingOfIntegers F) F) (intersectionLattice F g) := rfl

private theorem rationalVectorAction_surjective (F : Type*) [Field F] :
    Function.Surjective (rationalVectorAction F) := by
  intro e
  let t := LinearEquiv.finTwoArrow F F
  let l := t.trans (e.trans t.symm)
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv l), ?_⟩
  apply LinearEquiv.ext
  intro x
  simp [rationalVectorAction, l, t]

theorem glLatticeMap_injective_of_local_detection (F : Type*) [Field F] [NumberField F]
    (hlocal : ∀ g g' : AdelicGL F,
      (∀ v, localTranslatedLattice F g v = localTranslatedLattice F g' v) →
        ∃ k : integralGL F, g' = g * k) :
    Function.Injective (glLatticeMap F) := by
  intro q q' heq
  obtain ⟨g, rfl⟩ := Quotient.exists_rep q
  obtain ⟨g', rfl⟩ := Quotient.exists_rep q'
  obtain ⟨e, he⟩ := Quotient.eq.mp heq
  obtain ⟨a, rfl⟩ := rationalVectorAction_surjective F e
  have hm : intersectionLattice F (diagonalGL F a * g) = intersectionLattice F g' := by
    apply Subtype.ext
    exact (intersectionLattice_diagonal_map F a g).symm.trans he
  have hl : ∀ v, localTranslatedLattice F (diagonalGL F a * g) v =
      localTranslatedLattice F g' v := by
    intro v
    have h₁ := (Classical.choose_spec
      ((bounded_crt_lattice_and_projective_compact F).2 (diagonalGL F a * g))).2 v
    have h₂ := (Classical.choose_spec
      ((bounded_crt_lattice_and_projective_compact F).2 g')).2 v
    change closure (localVector F v '' ((intersectionLattice F (diagonalGL F a * g)).val :
      Set (F × F))) = _ at h₁
    change closure (localVector F v '' ((intersectionLattice F g').val : Set (F × F))) = _ at h₂
    rw [hm] at h₁
    exact h₁.symm.trans h₂
  obtain ⟨k, hk⟩ := hlocal _ _ hl
  exact DoubleCoset.eq.mpr ⟨diagonalGL F a, ⟨a, rfl⟩, k, k.property, hk⟩

theorem glLatticeMap_surjective_of_trivializations (F : Type*) [Field F] [NumberField F]
    (htriv : ∀ M : FullLattice (NumberField.RingOfIntegers F) F,
      ∃ g : AdelicGL F, ∀ x : F × F,
        x ∈ M.val ↔ diagonalVector F x ∈ g • integralVectors F) :
    Function.Surjective (glLatticeMap F) := by
  intro q
  obtain ⟨M, rfl⟩ := Quotient.exists_rep q
  obtain ⟨g, hg⟩ := htriv M
  refine ⟨DoubleCoset.mk (diagonalGL F).range (integralGL F) g, ?_⟩
  rw [glLatticeMap_mk]
  have hm : intersectionLattice F g = M := by
    apply Subtype.ext
    apply Submodule.ext
    intro x
    exact (intersection_mem F g x).trans (hg x).symm
  rw [hm]

theorem gl_lattice_equivalence_of_local_inputs (F : Type*) [Field F] [NumberField F]
    (hlocal : ∀ g g' : AdelicGL F,
      (∀ v, localTranslatedLattice F g v = localTranslatedLattice F g' v) →
        ∃ k : integralGL F, g' = g * k)
    (htriv : ∀ M : FullLattice (NumberField.RingOfIntegers F) F,
      ∃ g : AdelicGL F, ∀ x : F × F,
        x ∈ M.val ↔ diagonalVector F x ∈ g • integralVectors F) :
    ∃ e : DoubleCoset.Quotient ((diagonalGL F).range : Set (AdelicGL F))
        (integralGL F : Set (AdelicGL F)) ≃
        Quotient (latticeSetoid (NumberField.RingOfIntegers F) F),
      ∀ g : AdelicGL F,
        e (DoubleCoset.mk (diagonalGL F).range (integralGL F) g) =
          Quotient.mk (latticeSetoid (NumberField.RingOfIntegers F) F)
            (intersectionLattice F g) := by
  refine ⟨Equiv.ofBijective (glLatticeMap F)
    ⟨glLatticeMap_injective_of_local_detection F hlocal,
      glLatticeMap_surjective_of_trivializations F htriv⟩, ?_⟩
  intro g
  rfl

theorem gl_lattice_equivalence (F : Type*) [Field F] [NumberField F] :
    ∃ e : DoubleCoset.Quotient
        ((diagonalGL F).range : Set (AdelicGL F))
        (integralGL F : Set (AdelicGL F)) ≃
        Quotient (latticeSetoid (NumberField.RingOfIntegers F) F),
      ∀ g : AdelicGL F,
        e (DoubleCoset.mk (diagonalGL F).range (integralGL F) g) =
          Quotient.mk (latticeSetoid (NumberField.RingOfIntegers F) F)
            (intersectionLattice F g) := by
  exact gl_lattice_equivalence_of_local_inputs F
    (local_lattice_right_orbit F) (full_lattice_adelic_realization F)

end DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

end

section

open scoped Pointwise

namespace DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

theorem projective_class_finiteness (F : Type*) [Field F] [NumberField F] :
    Finite (DoubleCoset.Quotient
      ((diagonalPG F).range : Set (AdelicPG F))
      (integralPG F : Set (AdelicPG F))) := by
  classical
  obtain ⟨e, _⟩ := gl_lattice_equivalence F
  letI := kp_cusp_numberField_lattice_quotient_finite F
  letI : Finite (DoubleCoset.Quotient
      ((diagonalGL F).range : Set (AdelicGL F))
      (integralGL F : Set (AdelicGL F))) := Finite.of_injective e e.injective
  let q : DoubleCoset.Quotient
      ((diagonalGL F).range : Set (AdelicGL F))
      (integralGL F : Set (AdelicGL F)) →
      DoubleCoset.Quotient ((diagonalPG F).range : Set (AdelicPG F))
        (integralPG F : Set (AdelicPG F)) :=
    Quotient.lift (fun g => DoubleCoset.mk (diagonalPG F).range (integralPG F)
      (Matrix.ProjGenLinGroup.mk g)) (by
        intro a b hab
        obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.rel_iff.mp hab
        apply DoubleCoset.eq.mpr
        refine ⟨Matrix.ProjGenLinGroup.mk h, ?_,
          Matrix.ProjGenLinGroup.mk k, ?_, ?_⟩
        · obtain ⟨r, rfl⟩ := hh
          exact ⟨Matrix.ProjGenLinGroup.mk r, rfl⟩
        · exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
        · simpa only [map_mul] using congrArg Matrix.ProjGenLinGroup.mk he)
  apply Finite.of_surjective q
  intro z
  obtain ⟨g, rfl⟩ := Quotient.exists_rep z
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  exact ⟨DoubleCoset.mk (diagonalGL F).range (integralGL F) a, rfl⟩

theorem projective_topological_group (F : Type*) [Field F] [NumberField F] :
    letI := projectiveTopology F; IsTopologicalGroup (AdelicPG F) := by
  letI := projectiveTopology F
  letI : IsTopologicalGroup (AdelicGL F) := by
    unfold AdelicGL Matrix.GeneralLinearGroup
    infer_instance
  change IsTopologicalGroup (AdelicGL F ⧸ Subgroup.center (AdelicGL F))
  infer_instance

theorem finite_doubleCoset_refine_open
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H K U : Subgroup G) (hK : IsCompact (K : Set G))
    (hU : IsOpen (U : Set G))
    (hfinite : Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))) :
    Finite (DoubleCoset.Quotient (H : Set G) (U : Set G)) := by
  classical
  letI := hfinite
  let S : Set G := ⋃ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
    (fun k => q.out * k) '' (K : Set G)
  have hS : IsCompact S := isCompact_iUnion fun q =>
    hK.image (continuous_const_mul q.out)
  let O : G → Set G := fun a => (fun u => a * u) '' (U : Set G)
  have hopen : ∀ a, IsOpen (O a) := fun a => isOpenMap_mul_left a _ hU
  have hcover : S ⊆ ⋃ a, O a := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, 1, U.one_mem, mul_one x⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover O hopen hcover
  apply Finite.of_surjective (fun a : t => DoubleCoset.mk H U a.val)
  intro z
  obtain ⟨g, rfl⟩ := Quotient.exists_rep z
  let q := DoubleCoset.mk H K g
  obtain ⟨h, hh, k, hk, hg⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' q)
  have hx : q.out * k ∈ S := Set.mem_iUnion.mpr ⟨q, k, hk, rfl⟩
  obtain ⟨a, ha, u, hu, he⟩ := Set.mem_iUnion₂.mp (ht hx)
  refine ⟨⟨a, ha⟩, DoubleCoset.eq.mpr ⟨h, hh, u, hu, ?_⟩⟩
  calc
    g = h * q.out * k := hg
    _ = h * (q.out * k) := mul_assoc _ _ _
    _ = h * (a * u) := congrArg (h * ·) he.symm
    _ = h * a * u := (mul_assoc _ _ _).symm

theorem finite_doubleCoset_at_open_level
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H K U : Subgroup G) (hKcompact : IsCompact (K : Set G))
    (hKopen : IsOpen (K : Set G)) (hUopen : IsOpen (U : Set G))
    (hfinite : Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))) :
    Finite (DoubleCoset.Quotient (H : Set G) (U : Set G)) := by
  have hV := finite_doubleCoset_refine_open H K (K ⊓ U) hKcompact
    (hKopen.inter hUopen) hfinite
  let q : DoubleCoset.Quotient (H : Set G) ((K ⊓ U : Subgroup G) : Set G) →
      DoubleCoset.Quotient (H : Set G) (U : Set G) :=
    Quotient.lift (DoubleCoset.mk H U) (by
      intro a b hab
      obtain ⟨h, hh, v, hv, he⟩ := DoubleCoset.rel_iff.mp hab
      exact DoubleCoset.eq.mpr ⟨h, hh, v, hv.2, he⟩)
  letI := hV
  apply Finite.of_surjective q
  intro z
  obtain ⟨g, rfl⟩ := Quotient.exists_rep z
  exact ⟨DoubleCoset.mk H (K ⊓ U) g, rfl⟩

end DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

end

section

open scoped Pointwise

namespace DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

def idealVectors (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Set (Matrix (Fin 2) (Fin 1) F) :=
  {x | (∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = x 0 0) ∧ x 1 0 ∈ I}

noncomputable def idealProjectiveAut (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Subgroup (RationalPG F) :=
  (MulAction.stabilizer (RationalGL F) (idealVectors F I)).map Matrix.ProjGenLinGroup.mk

noncomputable def levelStabilizer (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (AdelicPG F)) (g : AdelicPG F) : Subgroup (RationalPG F) :=
  (U.map (MulAut.conj g).toMonoidHom).comap (diagonalPG F)

theorem open_finite_relative_index_compact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) :
    U.IsFiniteRelIndex K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen := K.subgroupOf_isOpen U hU
  letI := (U.subgroupOf K).quotient_finite_of_isOpen hopen
  exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
    (Subgroup.finiteIndex_of_finite_quotient)

theorem compact_open_commensurable
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hUcompact : IsCompact (U : Set G))
    (hUopen : IsOpen (U : Set G)) (hKcompact : IsCompact (K : Set G))
    (hKopen : IsOpen (K : Set G)) : U.Commensurable K :=
  ⟨open_finite_relative_index_compact K U hKcompact hUopen,
    open_finite_relative_index_compact U K hUcompact hKopen⟩

theorem level_stabilizers_commensurable_standard
    (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (AdelicPG F))
    (hUcompact : letI := projectiveTopology F; IsCompact (U : Set (AdelicPG F)))
    (hUopen : letI := projectiveTopology F; IsOpen (U : Set (AdelicPG F)))
    (g : AdelicPG F) :
    (levelStabilizer F U g).Commensurable (levelStabilizer F (integralPG F) g) ∧
    (levelStabilizer F (U ⊓ integralPG F) g).Commensurable
      (levelStabilizer F (integralPG F) g) := by
  letI := projectiveTopology F
  letI := projective_topological_group F
  obtain ⟨hKcompact, hKopen⟩ := integralPG_compact_open F
  have hUK := compact_open_commensurable U (integralPG F)
    hUcompact hUopen hKcompact hKopen
  constructor
  · exact (hUK.map (MulAut.conj g).toMonoidHom).comap (diagonalPG F)
  · exact ((hUK.inf_left (.refl (integralPG F))).map
      (MulAut.conj g).toMonoidHom).comap (diagonalPG F)

theorem standard_stabilizers_commensurable_identity
    (F : Type*) [Field F] [NumberField F] (g : AdelicPG F) :
    (levelStabilizer F (integralPG F) g).Commensurable
      (levelStabilizer F (integralPG F) 1) := by
  letI := projectiveTopology F
  letI := projective_topological_group F
  obtain ⟨hc, ho⟩ := integralPG_compact_open F
  have hc' : IsCompact
      ((integralPG F).map (MulAut.conj g).toMonoidHom : Set (AdelicPG F)) := by
    rw [Subgroup.coe_map]
    exact hc.image ((continuous_const_mul g).mul_const g⁻¹)
  have ho' : IsOpen
      ((integralPG F).map (MulAut.conj g).toMonoidHom : Set (AdelicPG F)) := by
    rw [Subgroup.coe_map]
    change IsOpen ((fun x => g * x * g⁻¹) '' (integralPG F : Set (AdelicPG F)))
    rw [show (fun x => g * x * g⁻¹) =
      (fun x => x * g⁻¹) ∘ (fun x => g * x) from rfl, Set.image_comp]
    exact isOpenMap_mul_right g⁻¹ _ (isOpenMap_mul_left g _ ho)
  have h := compact_open_commensurable
    ((integralPG F).map (MulAut.conj g).toMonoidHom) (integralPG F) hc' ho' hc ho
  have h1 : (MulAut.conj (1 : AdelicPG F)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  simpa only [levelStabilizer, h1, Subgroup.map_id] using h.comap (diagonalPG F)

theorem standard_stabilizer_class_obstruction_of_identity
    (F : Type*) [Field F] [NumberField F]
    (h : (levelStabilizer F (integralPG F) 1).Commensurable
      (idealProjectiveAut F 1)) (g : AdelicPG F) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
      (a : RationalPG F), I ≠ 0 ∧
      (levelStabilizer F (integralPG F) g).Commensurable
        ((idealProjectiveAut F I).map (MulAut.conj a).toMonoidHom) := by
  refine ⟨1, 1, one_ne_zero, ?_⟩
  have h1 : (MulAut.conj (1 : RationalPG F)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [h1, Subgroup.map_id]
  exact (standard_stabilizers_commensurable_identity F g).trans h

theorem idealVectors_one_mem (F : Type*) [Field F] [NumberField F]
    (x : Matrix (Fin 2) (Fin 1) F) :
    x ∈ idealVectors F 1 ↔ ∀ i j, ∃ a : NumberField.RingOfIntegers F,
      algebraMap _ F a = x i j := by
  simp only [idealVectors, Set.mem_setOf_eq, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨h0, h1⟩ i j
    fin_cases i <;> fin_cases j
    · exact h0
    · exact h1
  · intro h
    exact ⟨h 0 0, h 1 0⟩

theorem rational_stabilizer_entries (F : Type*) [Field F] [NumberField F]
    (A : RationalGL F)
    (hA : A ∈ MulAction.stabilizer (RationalGL F) (idealVectors F 1)) :
    ∀ i j, ∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = A.val i j := by
  intro i j
  have he : Matrix.single j (0 : Fin 1) (1 : F) ∈ idealVectors F 1 := by
    rw [idealVectors_one_mem]
    intro k l
    simp only [Matrix.single, Matrix.of_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  have hh : A • Matrix.single j (0 : Fin 1) (1 : F) ∈ idealVectors F 1 := by
    rw [← MulAction.mem_stabilizer_iff.mp hA]
    exact Set.smul_mem_smul_set he
  have h := (idealVectors_one_mem F _).mp hh i 0
  fin_cases j <;> simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply,
    Matrix.single, Matrix.of_apply] using h

theorem diagonalGL_integral_of_rational_stabilizer (F : Type*) [Field F] [NumberField F]
    (A : RationalGL F)
    (hA : A ∈ MulAction.stabilizer (RationalGL F) (idealVectors F 1)) :
    diagonalGL F A ∈ integralGL F := by
  have entries (B : RationalGL F)
      (hB : B ∈ MulAction.stabilizer (RationalGL F) (idealVectors F 1)) :
      ∀ i j v, (diagonalGL F B).val i j v ∈ v.adicCompletionIntegers F := by
    intro i j v
    obtain ⟨a, ha⟩ := rational_stabilizer_entries F B hB i j
    change (algebraMap F (Adeles F) (B.val i j)) v ∈ v.adicCompletionIntegers F
    rw [← ha, IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
    exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem _ F v a
  have act (B : AdelicGL F)
      (hB : ∀ i j v, B.val i j v ∈ v.adicCompletionIntegers F)
      (x : Matrix (Fin 2) (Fin 1) (Adeles F)) (hx : x ∈ integralVectors F) :
      B • x ∈ integralVectors F := by
    intro i j v
    change ((B.val * x) i j) v ∈ v.adicCompletionIntegers F
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (B.val i 0 v * x 0 j v + B.val i 1 v * x 1 j v) ∈ v.adicCompletionIntegers F
    exact (v.adicCompletionIntegers F).toSubring.add_mem
      ((v.adicCompletionIntegers F).toSubring.mul_mem (hB i 0 v) (hx 0 j v))
      ((v.adicCompletionIntegers F).toSubring.mul_mem (hB i 1 v) (hx 1 j v))
  have hi := entries A⁻¹ ((MulAction.stabilizer (RationalGL F) (idealVectors F 1)).inv_mem hA)
  rw [map_inv] at hi
  apply MulAction.mem_stabilizer_iff.mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact act _ (entries A hA) x hx
  · intro x hx
    exact ⟨(diagonalGL F A)⁻¹ • x, act _ hi x hx, by simp⟩

theorem idealProjectiveAut_le_identity (F : Type*) [Field F] [NumberField F] :
    idealProjectiveAut F 1 ≤ levelStabilizer F (integralPG F) 1 := by
  rintro q hq
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hq
  have h1 : (MulAut.conj (1 : AdelicPG F)).toMonoidHom = MonoidHom.id _ := by
    ext x; simp
  simp only [levelStabilizer, h1, Subgroup.map_id, Subgroup.mem_comap]
  change Matrix.ProjGenLinGroup.mk (diagonalGL F A) ∈ integralPG F
  exact Subgroup.mem_map.mpr ⟨_, diagonalGL_integral_of_rational_stabilizer F A hA, rfl⟩

theorem rational_integral_detection (F : Type*) [Field F] [NumberField F]
    (x : F) :
    (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      (algebraMap F (Adeles F) x) v ∈ v.adicCompletionIntegers F) ↔
      ∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = x := by
  constructor
  · intro h
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := h v
    rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  · rintro ⟨a, rfl⟩ v
    rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
    exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem _ F v a

theorem rational_action_integral (F : Type*) [Field F] [NumberField F]
    (A : RationalGL F)
    (hA : ∀ i j, ∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = A.val i j)
    (x : Matrix (Fin 2) (Fin 1) F) (hx : x ∈ idealVectors F 1) :
    A • x ∈ idealVectors F 1 := by
  rw [idealVectors_one_mem] at hx ⊢
  intro i j
  obtain ⟨a0, ha0⟩ := hA i 0
  obtain ⟨a1, ha1⟩ := hA i 1
  obtain ⟨x0, hx0⟩ := hx 0 j
  obtain ⟨x1, hx1⟩ := hx 1 j
  refine ⟨a0 * x0 + a1 * x1, ?_⟩
  simp only [map_add, map_mul, ha0, ha1, hx0, hx1,
    Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply, Fin.sum_univ_two]

theorem rational_stabilizer_of_integralGL (F : Type*) [Field F] [NumberField F]
    (A : RationalGL F)
    (hA : diagonalGL F A ∈ integralGL F) :
    A ∈ MulAction.stabilizer (RationalGL F) (idealVectors F 1) := by
  have entries (B : RationalGL F) (hB : diagonalGL F B ∈ integralGL F) :
      ∀ i j, ∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = B.val i j := by
    intro i j
    apply (rational_integral_detection F (B.val i j)).mp
    intro v
    have he : Matrix.single j (0 : Fin 1) (1 : Adeles F) ∈ integralVectors F := by
      intro k l w
      simp only [Matrix.single, Matrix.of_apply]
      split_ifs <;> first | exact (w.adicCompletionIntegers F).one_mem | exact (w.adicCompletionIntegers F).zero_mem
    have hh : diagonalGL F B • Matrix.single j (0 : Fin 1) (1 : Adeles F) ∈ integralVectors F := by
      rw [← MulAction.mem_stabilizer_iff.mp hB]
      exact Set.smul_mem_smul_set he
    have h := hh i 0 v
    fin_cases j <;> simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply,
      Matrix.single, Matrix.of_apply, diagonalGL, Matrix.GeneralLinearGroup.map] using h
  have hi : diagonalGL F A⁻¹ ∈ integralGL F := by
    rw [map_inv]
    exact (integralGL F).inv_mem hA
  apply MulAction.mem_stabilizer_iff.mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact rational_action_integral F A (entries A hA) x hx
  · intro x hx
    exact ⟨A⁻¹ • x, rational_action_integral F A⁻¹ (entries A⁻¹ hi) x hx, by simp⟩

theorem standard_stabilizer_class_obstruction_of_finite_index
    (F : Type*) [Field F] [NumberField F]
    (h : (idealProjectiveAut F 1).IsFiniteRelIndex (levelStabilizer F (integralPG F) 1))
    (g : AdelicPG F) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
      (a : RationalPG F), I ≠ 0 ∧
      (levelStabilizer F (integralPG F) g).Commensurable
        ((idealProjectiveAut F I).map (MulAut.conj a).toMonoidHom) := by
  apply standard_stabilizer_class_obstruction_of_identity F ?_ g
  refine ⟨?_, h⟩
  exact Subgroup.isFiniteRelIndex_of_le_left (idealProjectiveAut F 1)
    (idealProjectiveAut_le_identity F)

theorem projective_standard_mem_iff_scalar (F : Type*) [Field F] [NumberField F]
    (A : RationalGL F) :
    Matrix.ProjGenLinGroup.mk A ∈ levelStabilizer F (integralPG F) 1 ↔
      ∃ u : (Adeles F)ˣ,
        Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagonalGL F A ∈ integralGL F := by
  have h1 : (MulAut.conj (1 : AdelicPG F)).toMonoidHom = MonoidHom.id _ := by
    ext x; simp
  simp only [levelStabilizer, h1, Subgroup.map_id, Subgroup.mem_comap,
    diagonalPG, Matrix.ProjGenLinGroup.map_mk, integralPG, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, he⟩
    have hc : B⁻¹ * diagonalGL F A ∈ Subgroup.center (AdelicGL F) :=
      QuotientGroup.eq.mp he
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨u⁻¹, ?_⟩
    have hEq : Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * diagonalGL F A = B := by
      apply (mul_right_cancel_iff).mp
      show Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * diagonalGL F A *
          Matrix.GeneralLinearGroup.scalar (Fin 2) u = B * Matrix.GeneralLinearGroup.scalar (Fin 2) u
      rw [mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute u (diagonalGL F A),
        ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, hu]
      group
    rwa [hEq]
  · rintro ⟨u, hu⟩
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagonalGL F A, hu, ?_⟩
    apply QuotientGroup.eq.mpr
    have hEq : (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagonalGL F A)⁻¹ *
        diagonalGL F A = Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ := by
      have hc := Matrix.GeneralLinearGroup.scalar_commute u⁻¹ (diagonalGL F A)
      simp only [map_inv] at hc
      rw [mul_inv_rev, mul_assoc, hc, ← mul_assoc]
      simp
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagonalGL F A)⁻¹ *
      diagonalGL F A ∈ Subgroup.center (AdelicGL F)
    rw [hEq, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u⁻¹, rfl⟩

theorem scalar_mem_integralGL_iff (F : Type*) [Field F] [NumberField F]
    (u : (Adeles F)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ integralGL F ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        (u.val v ∈ v.adicCompletionIntegers F ∧ u.inv v ∈ v.adicCompletionIntegers F) := by
  have act (w : (Adeles F)ˣ)
      (hw : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        w.val v ∈ v.adicCompletionIntegers F)
      (x : Matrix (Fin 2) (Fin 1) (Adeles F)) (hx : x ∈ integralVectors F) :
      Matrix.GeneralLinearGroup.scalar (Fin 2) w • x ∈ integralVectors F := by
    intro i j v
    have he : (Matrix.GeneralLinearGroup.scalar (Fin 2) w • x) i j = w.val * x i j := by
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.smul_def, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal, Matrix.mul_apply]
    rw [he]
    exact (v.adicCompletionIntegers F).toSubring.mul_mem (hw v) (hx i j v)
  have detect (w : (Adeles F)ˣ)
      (hw : Matrix.GeneralLinearGroup.scalar (Fin 2) w ∈ integralGL F) :
      ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        w.val v ∈ v.adicCompletionIntegers F := by
    intro v
    have he : Matrix.single (0 : Fin 2) (0 : Fin 1) (1 : Adeles F) ∈ integralVectors F := by
      intro k l w
      simp only [Matrix.single, Matrix.of_apply]
      split_ifs <;> first | exact (w.adicCompletionIntegers F).one_mem | exact (w.adicCompletionIntegers F).zero_mem
    have hh : Matrix.GeneralLinearGroup.scalar (Fin 2) w •
        Matrix.single (0 : Fin 2) (0 : Fin 1) (1 : Adeles F) ∈ integralVectors F := by
      rw [← MulAction.mem_stabilizer_iff.mp hw]
      exact Set.smul_mem_smul_set he
    have h := hh 0 0 v
    simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.single, Matrix.of_apply] using h
  constructor
  · intro hu v
    refine ⟨detect u hu v, ?_⟩
    have hi : Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ ∈ integralGL F := by
      rw [map_inv]
      exact (integralGL F).inv_mem hu
    exact detect u⁻¹ hi v
  · intro h
    apply MulAction.mem_stabilizer_iff.mpr
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact act u (fun v => (h v).1) x hx
    · intro x hx
      refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ • x,
        act u⁻¹ (fun v => (h v).2) x hx, ?_⟩
      simp only [map_inv, smul_inv_smul]

namespace StabilizerClassRaw

variable (F : Type*) [Field F] [NumberField F]

noncomputable def scalarFinite : IdeleGroup F →* AdelicGL F :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2)).comp
    ((IdeleGroup.finiteEquivFiniteAdeleUnits (K := F)).toMonoidHom.comp (MonoidHom.snd _ _))

theorem scalarFinite_integral (a : IdeleGroup F)
    (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := F)) :
    scalarFinite F a ∈ integralGL F := by
  change Matrix.GeneralLinearGroup.scalar (Fin 2) _ ∈ integralGL F
  rw [scalar_mem_integralGL_iff]
  intro v
  have h := ha v
  change a.2 v ∈ (v.adicCompletionIntegers F).units at h
  exact h

noncomputable def pairedIntegralHom : RationalGL F × IdeleGroup F →* AdelicGL F where
  toFun p := scalarFinite F p.2 * diagonalGL F p.1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, a⟩ ⟨B, b⟩
    change scalarFinite F (a * b) * diagonalGL F (A * B) =
      (scalarFinite F a * diagonalGL F A) * (scalarFinite F b * diagonalGL F B)
    simp only [map_mul]
    have hc : scalarFinite F b * diagonalGL F A = diagonalGL F A * scalarFinite F b :=
      Matrix.GeneralLinearGroup.scalar_commute _ _
    calc
      _ = scalarFinite F a * (scalarFinite F b * diagonalGL F A) * diagonalGL F B := by group
      _ = scalarFinite F a * (diagonalGL F A * scalarFinite F b) * diagonalGL F B := by rw [hc]
      _ = _ := by group

noncomputable def pairedIntegral : Subgroup (RationalGL F × IdeleGroup F) :=
  (integralGL F).comap (pairedIntegralHom F)

noncomputable def pairedProjective : pairedIntegral F →* RationalPG F :=
  Matrix.ProjGenLinGroup.mk.comp ((MonoidHom.fst _ _).comp (pairedIntegral F).subtype)

noncomputable def pairedClass : pairedIntegral F →* ClassGroup (NumberField.RingOfIntegers F) :=
  (IdeleGroup.idealClass (K := F)).comp ((MonoidHom.snd _ _).comp (pairedIntegral F).subtype)

theorem scalarFinite_principal (x : Fˣ) :
    scalarFinite F (IdeleGroup.principalIdele F x) =
      diagonalGL F (Matrix.GeneralLinearGroup.scalar (Fin 2) x) := by
  change Matrix.GeneralLinearGroup.scalar (Fin 2) _ =
    Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F)) (Matrix.GeneralLinearGroup.scalar (Fin 2) x)
  rw [Matrix.GeneralLinearGroup.map_scalar]
  congr 1

theorem pairedProjective_range : (pairedProjective F).range =
    levelStabilizer F (integralPG F) 1 := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    apply (projective_standard_mem_iff_scalar F p.val.1).mpr
    exact ⟨IdeleGroup.finiteEquivFiniteAdeleUnits p.val.2.2, p.property⟩
  · intro hq
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q
    obtain ⟨u, hu⟩ := (projective_standard_mem_iff_scalar F A).mp hq
    exact ⟨⟨(A, (1, (IdeleGroup.finiteEquivFiniteAdeleUnits (K := F)).symm u)),
      by simpa [pairedIntegral, pairedIntegralHom, scalarFinite] using hu⟩, rfl⟩

theorem pairedClass_ker_image_le : (pairedClass F).ker.map (pairedProjective F) ≤
    idealProjectiveAut F 1 := by
  rintro q ⟨p, hp, rfl⟩
  have ha : p.val.2 ∈ IdeleGroup.ordinaryIdealClassSubgroup (K := F) := by
    rw [IdeleGroup.ordinaryIdealClassSubgroup_eq_ker]
    exact hp
  rw [IdeleGroup.ordinaryIdealClassSubgroup, Subgroup.mem_sup] at ha
  obtain ⟨u, hu, s, hs, he⟩ := ha
  obtain ⟨x, hx⟩ := hs
  have hint : diagonalGL F (Matrix.GeneralLinearGroup.scalar (Fin 2) x * p.val.1) ∈ integralGL F := by
    have hpp := p.property
    change scalarFinite F p.val.2 * diagonalGL F p.val.1 ∈ integralGL F at hpp
    rw [← he, ← hx, map_mul, scalarFinite_principal, mul_assoc] at hpp
    have h := (integralGL F).mul_mem ((integralGL F).inv_mem (scalarFinite_integral F u hu)) hpp
    simpa only [inv_mul_cancel_left, map_mul] using h
  apply Subgroup.mem_map.mpr
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) x * p.val.1,
    rational_stabilizer_of_integralGL F _ hint, ?_⟩
  apply QuotientGroup.eq.mpr
  have hc := Matrix.GeneralLinearGroup.scalar_commute x⁻¹ p.val.1
  simp only [map_inv] at hc
  change (Matrix.GeneralLinearGroup.scalar (Fin 2) x * p.val.1)⁻¹ * p.val.1 ∈
    Subgroup.center (RationalGL F)
  rw [mul_inv_rev, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨x⁻¹, map_inv _ _⟩

theorem standard_stabilizer_identity_finite_index :
    (idealProjectiveAut F 1).IsFiniteRelIndex (levelStabilizer F (integralPG F) 1) := by
  letI : Finite (ClassGroup (NumberField.RingOfIntegers F)) := inferInstance
  letI : (pairedClass F).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have hc : ((pairedClass F).ker).Commensurable ⊤ := Subgroup.Commensurable.top_right_iff.mpr inferInstance
  have hm := (hc.map (pairedProjective F)).1
  rw [Subgroup.map_top, pairedProjective_range] at hm
  letI := hm
  exact Subgroup.isFiniteRelIndex_of_le_left _ (pairedClass_ker_image_le F)

end StabilizerClassRaw

theorem standard_stabilizer_class_obstruction
    (F : Type*) [Field F] [NumberField F] (g : AdelicPG F) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
      (a : RationalPG F), I ≠ 0 ∧
      (levelStabilizer F (integralPG F) g).Commensurable
        ((idealProjectiveAut F I).map (MulAut.conj a).toMonoidHom) := by
  exact standard_stabilizer_class_obstruction_of_finite_index F
    (StabilizerClassRaw.standard_stabilizer_identity_finite_index F) g

end DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

end
