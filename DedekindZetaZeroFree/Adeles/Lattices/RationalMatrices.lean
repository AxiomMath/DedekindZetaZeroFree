module

public import DedekindZetaZeroFree.Adeles.Lattices.PrincipalAdeleDiscreteness
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotientTopology.Arithmetic
open Topology
open scoped NumberField Classical

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev RawCover := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ
abbrev rawRationalSubgroup : Subgroup (RawCover F ζ hζ) :=
  (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).range

abbrev RawArchGroup := NumberField.InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

def rawGLArchProjection : KPAdelicCoverRestrictedProduct.AdelicGL2 F →* RawArchGroup F where
  toFun g w := Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))) g)
  map_one' := by ext w; simp
  map_mul' := by intro g h; ext w; simp

 theorem rawScalars_le_arch_kernel :
    KPAdelicCoverRestrictedProduct.scalarSubgroup F ≤ (rawGLArchProjection F ζ hζ).ker := by
  rintro g ⟨u, rfl⟩
  ext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
  rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar]

def rawArchProjection : RawCover F ζ hζ →* RawArchGroup F :=
  (QuotientGroup.lift (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (rawGLArchProjection F ζ hζ) (rawScalars_le_arch_kernel F ζ hζ)).comp
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

 def adjHom {R : Type*} [CommRing R] :
    Matrix.GeneralLinearGroup (Fin 2) R →* Equiv.Perm (Matrix (Fin 2) (Fin 2) R) :=
  (MulAction.toPermHom (ConjAct (Matrix.GeneralLinearGroup (Fin 2) R)) _).comp
    ConjAct.toConjAct.toMonoidHom

private theorem adjHom_apply {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin 2) R) (m : Matrix (Fin 2) (Fin 2) R) :
    adjHom g m = g.val * m * g.inv := rfl

 theorem adjHom_scalar {R : Type*} [CommRing R] (u : Rˣ) :
    adjHom (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  apply Equiv.ext
  intro m
  change (Matrix.scalar (Fin 2) u.val * m) *
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u).inv = m
  rw [Matrix.scalar_comm _ (fun _ => Commute.all _ _), mul_assoc]
  simpa using congrArg (fun n : Matrix (Fin 2) (Fin 2) R => m * n)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u).val_inv

 def adelicAdj : KPAdelicCoverRestrictedProduct.AdelicPGL2 F →*
    Equiv.Perm (Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) :=
  QuotientGroup.lift _ adjHom (by
    rintro g ⟨u, rfl⟩
    exact adjHom_scalar u)

private theorem scalar_of_adj_singles {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (hg : ∀ i j, adjHom g (Matrix.single i j 1) = Matrix.single i j 1) :
    g ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar,
    Matrix.mem_range_scalar_iff_commute_single']
  intro i j
  have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) R => m * g.val) (hg i j)
  rw [adjHom_apply, mul_assoc, g.inv_val, mul_one] at h
  exact h.symm

private theorem adelicAdj_continuous (i j k l : Fin 2) :
    Continuous (fun x : KPAdelicCoverRestrictedProduct.AdelicPGL2 F =>
      adelicAdj F x (Matrix.single i j 1) k l) := by
  apply (QuotientGroup.isQuotientMap_mk
    (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).continuous_iff.mpr
  change Continuous (fun g : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
    (g.val * Matrix.single i j 1 * g.inv :
      Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) k l)
  exact (continuous_apply l).comp ((continuous_apply k).comp
    ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv))

private theorem map_scalar_detect {R S : Type*} [Field R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (hg : Matrix.GeneralLinearGroup.map f g ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    g ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  obtain ⟨u, hu⟩ := hg
  have he (i j : Fin 2) : f (g i j) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u) i j :=
    congrArg (fun m : Matrix.GeneralLinearGroup (Fin 2) S => m i j) hu.symm
  have h00 : f (g 0 0) = (u : S) := by simpa using he 0 0
  have hn : g 0 0 ≠ 0 := by
    intro h
    exact u.ne_zero (by simpa [h] using h00.symm)
  refine ⟨Units.mk0 (g 0 0) hn, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply f.injective
  by_cases hij : i = j
  · subst j
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
      Matrix.diagonal, h00] using (he i i).symm
  · simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
      Matrix.diagonal, hij] using (he i j).symm

private theorem rational_adj_formula (g : KubotaRankTwo.GL2 F) (i j k l : Fin 2) :
    adelicAdj F (KPRationalAdelicSplitting.rationalPGLBase F
      (KPRationalAdelicSplitting.rationalPGLQuotient F g)) (Matrix.single i j 1) k l =
    algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)
      (adjHom g (Matrix.single i j 1) k l) := by
  change (adjHom (Matrix.GeneralLinearGroup.map
    (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)) g)) _ k l = _
  change ((g.val.map (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F))) *
    Matrix.single i j 1 * g.inv.map (algebraMap F
      (KPAdelicCoverRestrictedProduct.Adeles F)) :
      Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) k l = _
  rw [← map_one (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)),
    ← Matrix.map_single, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

private theorem rational_arch_injective :
    Function.Injective ((rawArchProjection F ζ hζ).comp
      (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ)) := by
  apply (((rawArchProjection F ζ hζ).comp
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ)).ker_eq_bot_iff).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply (QuotientGroup.eq_one_iff _).mpr
    have w : NumberField.InfinitePlace F := Classical.choice inferInstance
    have hw := congrArg (fun a : RawArchGroup F => a w) hx
    have hf : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
        (((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
          (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))).comp
          (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F))) g) = 1 := by
      change Matrix.ProjGenLinGroup.mk _ = 1 at hw
      change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
        (KPAdelicCoverRestrictedProduct.projection F ζ hζ
          (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ g))) = 1 at hw
      rw [KPAdelicCoverRestrictedProduct.projection_rationalSection] at hw
      simpa [KPAdelicCoverRestrictedProduct.rationalBase,
        Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply] using hw
    apply map_scalar_detect (S := ℂ) _ g
    rwa [Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at hf

private theorem rational_discrete :
    DiscreteTopology (rawRationalSubgroup F ζ hζ) := by
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hc := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous
  obtain ⟨U, hU, hU0, hdiag⟩ := KPAdelicDiagonal.exists_open_diag_preimage_zero F
  let f := fun (i j k l : Fin 2) (γ : rawRationalSubgroup F ζ hζ) =>
    adelicAdj F (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ γ)
      (Matrix.single i j 1) k l - (Matrix.single i j 1 :
        Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) k l
  have hcont (i j k l : Fin 2) : Continuous (f i j k l) :=
    ((adelicAdj_continuous F i j k l).comp
      (hc.comp continuous_subtype_val)).sub continuous_const
  let V : Set (rawRationalSubgroup F ζ hζ) :=
    ⋂ i, ⋂ j, ⋂ k, ⋂ l, (f i j k l) ⁻¹' U
  have hV : IsOpen V := isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k =>
      isOpen_iInter_of_finite fun l => hU.preimage (hcont i j k l)
  have he : V = {1} := by
    ext γ
    simp only [V, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγ
      obtain ⟨x, hx⟩ := γ.property
      have hxV (i j k l : Fin 2) :
          adelicAdj F (KPRationalAdelicSplitting.rationalPGLBase F x)
            (Matrix.single i j 1) k l - (Matrix.single i j 1 :
              Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) k l ∈ U := by
        have hh := hγ i j k l
        dsimp [f] at hh
        rw [← hx] at hh
        have hh' := congrArg (fun t => t x)
          (KPRationalAdelicSplitting.rationalPGL_splitting F ζ hζ).2
        simp only [MonoidHom.comp_apply] at hh'
        rw [hh'] at hh
        exact hh
      have hx1 : x = 1 := by
        induction x using QuotientGroup.induction_on with
        | H g =>
          apply (QuotientGroup.eq_one_iff _).mpr
          apply scalar_of_adj_singles g
          intro i j
          ext k l
          have hh := hxV i j k l
          change adelicAdj F (KPRationalAdelicSplitting.rationalPGLBase F
            (KPRationalAdelicSplitting.rationalPGLQuotient F g))
            (Matrix.single i j 1) k l - _ ∈ U at hh
          rw [rational_adj_formula] at hh
          have hs : (Matrix.single i j 1 :
              Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) k l =
              algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)
                ((Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) F) k l) := by
            have hm := Matrix.map_single i j (1 : F)
              (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F))
            simpa using congrArg (fun m => m k l) hm.symm
          rw [hs, ← map_sub] at hh
          have hz : adjHom g (Matrix.single i j 1) k l -
              (Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) F) k l = 0 := by
            have hm : adjHom g (Matrix.single i j 1) k l -
                (Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) F) k l ∈
                (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F)) ⁻¹' U := hh
            rw [hdiag] at hm
            exact hm
          exact sub_eq_zero.mp hz
      apply Subtype.ext
      simpa [hx1] using hx.symm
    · rintro rfl i j k l
      simpa [f] using hU0
  apply discreteTopology_of_isOpen_singleton_one
  rwa [he] at hV

theorem rawRational_arithmetic_certificate :
    IsClosed (rawRationalSubgroup F ζ hζ : Set (RawCover F ζ hζ)) ∧
      IsDiscrete (rawRationalSubgroup F ζ hζ : Set (RawCover F ζ hζ)) ∧
      Function.Injective ((rawArchProjection F ζ hζ).comp
        (rawRationalSubgroup F ζ hζ).subtype) := by
  letI := rational_discrete F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨Subgroup.isClosed_of_discreteTopology,
    isDiscrete_iff_discreteTopology.mpr inferInstance, ?_⟩
  intro x y hxy
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  apply Subtype.ext
  have hab : a = b := rational_arch_injective F ζ hζ (by
    change rawArchProjection F ζ hζ
      (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ a) =
      rawArchProjection F ζ hζ
        (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ b)
    rw [ha, hb]
    exact hxy)
  rw [← ha, ← hb, hab]

end DedekindZetaZeroFree.ActualQuotientTopology.Arithmetic

end
