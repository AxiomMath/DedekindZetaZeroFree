module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.ParabolicExtensionCharts
public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CompactBoxes
public import DedekindZetaZeroFree.Metaplectic.Kubota.FiniteAdelicLevelProjection
public import DedekindZetaZeroFree.Metaplectic.Torus.LocalDiagonalRatioCoordinates

@[expose] public section

noncomputable section

open scoped Classical NumberField

namespace DedekindZetaZeroFree

namespace KPCuspGenuineMonodromy

variable (F : Type) [Field F] [NumberField F]

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ

abbrev SymmetricSpace := KPArch.Space (KPCuspLogShape.dimension F)

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

def central : rootsOfUnity 3 F →* FiniteCover F ζ hζ :=
  (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).codRestrict
    (FiniteCover F ζ hζ) (by
      intro ε
      rw [MonoidHom.mem_ker]
      have hmem : KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ ε ∈
          (KPAdelicCoverRestrictedProduct.projection F ζ hζ).ker := by
        rw [← KPAdelicCoverRestrictedProduct.range_centralInjection_eq_ker F ζ hζ]
        exact ⟨ε, rfl⟩
      have hproj := MonoidHom.mem_ker.mp hmem
      rw [KPAdelicCoverRestrictedProduct.pglCentralInjection,
        KPAdelicCoverRestrictedProduct.scalarQuotient, archProjection]
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.lift_mk']
      simp [hproj])

def finiteRationalTuple (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
  ⟨(fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => KPAdelicCoverRestrictedProduct.rationalCoordinates F ζ hζ A
        (Sum.inr q)), by
      filter_upwards [KPAdelicCoverRestrictedProduct.rationalCoordinates_restricted F ζ hζ A]
        with v hv
      cases v with
      | inl w => exact (KPAdelicCoverRestrictedProduct.compact F ζ hζ (Sum.inl w)).one_mem
      | inr q => exact hv⟩

def finiteErase : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ →*
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ where
  toFun x := ⟨fun v => match v with
      | Sum.inl _ => 1
      | Sum.inr q => x (Sum.inr q), by
    filter_upwards [x.property] with v hv
    cases v with
    | inl w => exact (KPAdelicCoverRestrictedProduct.compact F ζ hζ (Sum.inl w)).one_mem
    | inr q => exact hv⟩
  map_one' := by ext v; cases v <;> rfl
  map_mul' x y := by
    apply Subtype.ext
    funext v
    cases v with
    | inl w => exact (one_mul _).symm
    | inr q => rfl

theorem infinite_section_mul (w : NumberField.InfinitePlace F)
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

def finiteRationalGLHom : Matrix.GeneralLinearGroup (Fin 2) F →* Cover F ζ hζ where
  toFun A := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (finiteRationalTuple F ζ hζ A))
  map_one' := by
    have ht : finiteRationalTuple F ζ hζ 1 = 1 := by
      ext v
      cases v with
      | inl w => rfl
      | inr q =>
        simp [finiteRationalTuple, KPAdelicCoverRestrictedProduct.rationalCoordinates,
          KPLocalCover.sectionMap]
        rfl
    rw [ht]
    simp
  map_mul' A B := by
    let T := KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ
    let δ := T A * T B * (T (A * B))⁻¹
    have hδ : KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ δ = 1 := by
      dsimp [δ, T]
      rw [map_mul, map_mul, map_inv]
      change KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ A *
        KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ B *
          (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (A * B))⁻¹ = 1
      rw [KPAdelicCoverRestrictedProduct.rationalSection_mul]
      exact mul_inv_cancel _
    have he : finiteErase F ζ hζ δ = δ := by
      ext v
      cases v with
      | inr q => rfl
      | inl w =>
        change 1 = (T A (Sum.inl w) * T B (Sum.inl w)) * (T (A * B) (Sum.inl w))⁻¹
        have ht : T (A * B) (Sum.inl w) = T A (Sum.inl w) * T B (Sum.inl w) := by
          dsimp [T, KPAdelicCoverRestrictedProduct.rationalTuple,
            KPAdelicCoverRestrictedProduct.rationalCoordinates]
          rw [map_mul, infinite_section_mul]
        rw [ht, mul_inv_cancel]
    have hf : KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
        (finiteRationalTuple F ζ hζ A) *
          KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (finiteRationalTuple F ζ hζ B) =
            KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (finiteRationalTuple F ζ hζ (A * B)) := by
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul, ← map_mul]
      have hmap : finiteErase F ζ hζ δ =
          finiteRationalTuple F ζ hζ A * finiteRationalTuple F ζ hζ B *
            (finiteRationalTuple F ζ hζ (A * B))⁻¹ := by
        dsimp [δ, T]
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [← hmap, he, hδ]
    rw [← map_mul, hf]

def finiteRationalLift : KPCuspArithmetic.PGL2 F →* FiniteCover F ζ hζ :=
  (QuotientGroup.lift (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F))
    (finiteRationalGLHom F ζ hζ) (by
      intro A hA
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
      obtain ⟨z, rfl⟩ := hA
      let zf : KPAdelicCoverRestrictedProduct.Ideles F := MulEquiv.prodUnits.symm
        (1, Units.map (algebraMap F (KPFiniteComponents.FiniteAdeles F)) z)
      have ht : finiteRationalTuple F ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
          KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ zf := by
        apply Subtype.ext
        funext v
        cases v with
        | inl w =>
          change 1 = KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w)
            (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)).toMonoidHom zf)
          have he : Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)).toMonoidHom zf = 1 := by
            apply Units.ext
            rfl
          rw [he, map_one]
        | inr q =>
          change KPLocalCover.sectionMap F ζ hζ (Sum.inr q) _ =
            KPLocalCover.sectionMap F ζ hζ (Sum.inr q) _
          congr 1
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.scalar,
              Matrix.scalar, KPScalarSplitCentral.scalarMatrix, Matrix.diagonal,
              KPAdelicCoverRestrictedProduct.adeleEval, zf] <;> rfl
      change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
          (finiteRationalTuple F ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))) = 1
      rw [ht]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨zf, rfl⟩)).codRestrict (FiniteCover F ζ hζ) (by
      intro γ
      induction γ using Matrix.ProjGenLinGroup.induction_on with
      | mk A =>
        change archProjection F ζ hζ
          (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
            (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
              (finiteRationalTuple F ζ hζ A))) = 1
        change (fun w => Matrix.ProjGenLinGroup.mk
          (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
            (KPAdelicCoverRestrictedProduct.projection F ζ hζ
              (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
                (finiteRationalTuple F ζ hζ A))))) = 1
        rw [KPAdelicCoverRestrictedProduct.projection_amalgamation]
        funext w
        rw [KPAdelicCoverRestrictedProduct.restrictedProjection_eval]
        change Matrix.ProjGenLinGroup.mk (KPLocalCover.projection F ζ hζ (Sum.inl w) 1) = 1
        simp)

end KPCuspGenuineMonodromy

end DedekindZetaZeroFree

end

section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree
namespace KPCuspGenuineMonodromy

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem finiteProjection_continuous : Continuous (finiteProjection F ζ hζ) := by
  apply (QuotientGroup.isQuotientMap_mk (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp ((continuous_snd.generalLinearGroup_map).comp
    (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.2.continuous)
theorem finiteBase_continuous : Continuous (finiteBase F ζ hζ) :=
  (finiteProjection_continuous F ζ hζ).comp continuous_subtype_val
theorem finiteBase_level_compact (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    IsCompact (U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ) : Set (KPFiniteComponents.FinitePGL2 F)) := by
  exact U.isCompact.image (finiteBase_continuous F ζ hζ)

theorem finiteRationalLift_formula (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    (finiteRationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk A) : Cover F ζ hζ) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (finiteRationalTuple F ζ hζ A)) := by
  rfl

theorem projection_formulas (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (c : KPCubicCoverConstruction.AdelicGL2Cover F ζ hζ)
    (hc : KPAdelicCoverRestrictedProduct.projection F ζ hζ c = A) :
    finiteProjection F ζ hζ (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ c) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (RingHom.snd _ _) A) ∧
    ∀ w : NumberField.InfinitePlace F,
      archProjection F ζ hζ (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ c) w =
        Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map
            (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)) A) := by
  subst A
  exact ⟨rfl, fun _ => rfl⟩

private theorem adelicMatrix_ext
    (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hf : Matrix.GeneralLinearGroup.map (RingHom.snd _ _) A =
      Matrix.GeneralLinearGroup.map (RingHom.snd _ _) B)
    (hinf : ∀ w : NumberField.InfinitePlace F,
      KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w) A =
        KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w) B) : A = B := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inl w) => M i j) (hinf w)
  · exact congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) (KPFiniteComponents.FiniteAdeles F) =>
      M i j) hf

private def pairGL {R S : Type*} [CommRing R] [CommRing S]
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

private def finiteMatrix (A : Matrix.GeneralLinearGroup (Fin 2) (KPFiniteComponents.FiniteAdeles F)) :
    KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
  pairGL (1 : Matrix.GeneralLinearGroup (Fin 2) (NumberField.InfiniteAdeleRing F)) A

private theorem finiteBase_surjective : Function.Surjective (finiteBase F ζ hζ) := by
  intro a
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  obtain ⟨c, hc⟩ := KPAdelicCoverRestrictedProduct.projection_surjective F ζ hζ (finiteMatrix F A)
  let t := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ c
  have ht : t ∈ FiniteCover F ζ hζ := by
    change archProjection F ζ hζ t = 1
    funext w
    rw [(projection_formulas F ζ hζ _ c hc).2 w]
    have hA : Matrix.GeneralLinearGroup.map
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)) (finiteMatrix F A) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hA, map_one]
    rfl
  refine ⟨⟨t, ht⟩, ?_⟩
  change finiteProjection F ζ hζ t = _
  rw [(projection_formulas F ζ hζ _ c hc).1]
  congr 1

private theorem finiteBase_diagonal : (finiteBase F ζ hζ).comp (finiteRationalLift F ζ hζ) =
    KPFiniteComponents.diagonal F := by
  ext γ
  induction γ using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
    change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
        (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
          (finiteRationalTuple F ζ hζ A))) =
            Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
              (algebraMap F (KPFiniteComponents.FiniteAdeles F)) A)
    congr 1

private theorem joint_projection_kernel (c : Cover F ζ hζ)
    (hf : finiteProjection F ζ hζ c = 1) (hi : archProjection F ζ hζ c = 1) :
    c ∈ (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) c
  let A := KPAdelicCoverRestrictedProduct.projection F ζ hζ d
  have hAf : Matrix.GeneralLinearGroup.map (RingHom.snd _ _) A ∈ Subgroup.center _ := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    exact hf
  have hAi : ∀ w : NumberField.InfinitePlace F,
      KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w) A ∈ Subgroup.center _ := by
    intro w
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    exact congrFun hi w
  have hA : A ∈ Subgroup.center _ := by
    apply Subgroup.mem_center_iff.mpr
    intro B
    apply adelicMatrix_ext F
    · rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hAf _
    · intro w
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp (hAi w) _
  rw [KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel]
  change QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  simpa only [KPAdelicCoverRestrictedProduct.scalarSubgroup,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] using hA

private theorem finiteBase_kernel : (central F ζ hζ).range = (finiteBase F ζ hζ).ker := by
  ext c
  constructor
  · rintro ⟨ε, rfl⟩
    change finiteProjection F ζ hζ
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ ε)) = 1
    have hc : KPAdelicCoverRestrictedProduct.projection F ζ hζ
        (KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ ε) = 1 := by
      exact (KPAdelicCoverRestrictedProduct.range_centralInjection_eq_ker F ζ hζ ▸
        ⟨ε, rfl⟩ : KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ ε ∈
          (KPAdelicCoverRestrictedProduct.projection F ζ hζ).ker)
    change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map
        (RingHom.snd (NumberField.InfiniteAdeleRing F) (KPFiniteComponents.FiniteAdeles F))
          (KPAdelicCoverRestrictedProduct.projection F ζ hζ
            (KPAdelicCoverRestrictedProduct.centralInjection F ζ hζ ε))) = 1
    rw [hc]
    erw [map_one]
    exact map_one _
  · intro hc
    obtain ⟨ε, he⟩ := joint_projection_kernel F ζ hζ c hc c.property
    refine ⟨ε, ?_⟩
    apply Subtype.ext
    exact he

theorem finite_cover_exact :
    Function.Injective (central F ζ hζ) ∧
    (central F ζ hζ).range = (finiteBase F ζ hζ).ker ∧
    Function.Surjective (finiteBase F ζ hζ) ∧
    (finiteBase F ζ hζ).comp (finiteRationalLift F ζ hζ) =
      KPFiniteComponents.diagonal F ∧
    ∀ ε : rootsOfUnity 3 F,
      (central F ζ hζ ε : Cover F ζ hζ) =
        KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε  := by
  refine ⟨?_, ?_, ?_, finiteBase_diagonal F ζ hζ, fun _ => rfl⟩
  · intro ε δ h
    apply KPAdelicCoverRestrictedProduct.pglCentralInjection_injective F ζ hζ
    exact congrArg (fun x : FiniteCover F ζ hζ => (x : Cover F ζ hζ)) h
  · exact finiteBase_kernel F ζ hζ
  · exact finiteBase_surjective F ζ hζ

def chi : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

def scalarFiber (U : CompactOpenLevel (FiniteCover F ζ hζ)) : Submodule ℂ ℂ where
  carrier := {a | ∀ ε : rootsOfUnity 3 F,
    central F ζ hζ ε ∈ U.toOpenSubgroup → (chi F ζ hζ ε : ℂ) * a = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb ε hε
    rw [mul_add, ha ε hε, hb ε hε]
  smul_mem' := by
    intro c a ha ε hε
    show (chi F ζ hζ ε : ℂ) * (c * a) = c * a
    rw [← mul_assoc, mul_comm (chi F ζ hζ ε : ℂ) c, mul_assoc, ha ε hε]

private theorem scalarFiber_rank (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    scalarFiber F ζ hζ U = ⊥ ∨ scalarFiber F ζ hζ U = ⊤ := by
  by_cases h : ∀ ε : rootsOfUnity 3 F,
      central F ζ hζ ε ∈ U.toOpenSubgroup → chi F ζ hζ ε = 1
  · right
    apply top_unique
    intro a _
    change ∀ ε : rootsOfUnity 3 F,
      central F ζ hζ ε ∈ U.toOpenSubgroup → (chi F ζ hζ ε : ℂ) * a = a
    intro ε hε
    rw [h ε hε]
    simp
  · left
    push Not at h
    obtain ⟨ε, hε, hχ⟩ := h
    apply bot_unique
    intro a ha
    change a = 0
    have he : (chi F ζ hζ ε : ℂ) * a = a := ha ε hε
    have hn : (chi F ζ hζ ε : ℂ) ≠ 1 := by
      intro hc
      exact hχ (Units.ext hc)
    have hz : ((chi F ζ hζ ε : ℂ) - 1) * a = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

private theorem scalarFiber_rank_zero (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (h : ∃ ε : rootsOfUnity 3 F,
      central F ζ hζ ε ∈ U.toOpenSubgroup ∧ chi F ζ hζ ε ≠ 1) :
    scalarFiber F ζ hζ U = ⊥ := by
  obtain ⟨ε, hε, hχ⟩ := h
  apply bot_unique
  intro a ha
  change a = 0
  have he : (chi F ζ hζ ε : ℂ) * a = a := ha ε hε
  have hn : (chi F ζ hζ ε : ℂ) ≠ 1 := by
    intro hc
    exact hχ (Units.ext hc)
  have hz : ((chi F ζ hζ ε : ℂ) - 1) * a = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

abbrev Component (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) :=
  KPFiniteComponents.arithmeticStabilizer F
    (U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)) (finiteBase F ζ hζ g)

private theorem central_comm (ε : rootsOfUnity 3 F) (c : FiniteCover F ζ hζ) :
    central F ζ hζ ε * c = c * central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

theorem finiteComparison_exists (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (γ : Component F ζ hζ U g) :
    ∃ (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ ε * g * u := by
  have hγ := γ.property
  change KPFiniteComponents.diagonal F γ ∈
    (U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)).map
      (MulAut.conj (finiteBase F ζ hζ g)).toMonoidHom at hγ
  obtain ⟨b, hb, he⟩ := hγ
  obtain ⟨u, hu, rfl⟩ := hb
  have hp : finiteBase F ζ hζ (finiteRationalLift F ζ hζ γ) =
      finiteBase F ζ hζ (g * u * g⁻¹) := by
    rw [← MonoidHom.comp_apply, (finite_cover_exact F ζ hζ).2.2.2.1]
    simpa [MulAut.conj_apply] using he.symm
  have hk : finiteRationalLift F ζ hζ γ * (g * u * g⁻¹)⁻¹ ∈
      (central F ζ hζ).range := by
    rw [(finite_cover_exact F ζ hζ).2.1]
    change finiteBase F ζ hζ _ = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  obtain ⟨ε, hε⟩ := hk
  refine ⟨ε, ⟨u, hu⟩, ?_⟩
  have heq := (mul_inv_eq_iff_eq_mul).mp hε.symm
  simpa [mul_assoc] using congrArg (fun c : FiniteCover F ζ hζ => c * g) heq

private def Comparison (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (γ : Component F ζ hζ U g) (ε : rootsOfUnity 3 F) : Prop :=
  ∃ u : U.toOpenSubgroup,
    finiteRationalLift F ζ hζ γ * g = central F ζ hζ ε * g * u

private theorem comparison_mul (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (γ δ : Component F ζ hζ U g) (ε η : rootsOfUnity 3 F)
    (hγ : Comparison F ζ hζ U g γ ε) (hδ : Comparison F ζ hζ U g δ η) :
    Comparison F ζ hζ U g (γ * δ) (ε * η) := by
  obtain ⟨u, hu⟩ := hγ
  obtain ⟨v, hv⟩ := hδ
  refine ⟨u * v, ?_⟩
  change finiteRationalLift F ζ hζ (γ * δ) * g =
    central F ζ hζ (ε * η) * g * ((u : FiniteCover F ζ hζ) * v)
  calc
    finiteRationalLift F ζ hζ (γ * δ) * g =
      finiteRationalLift F ζ hζ γ * (central F ζ hζ η * g * v) := by rw [map_mul, mul_assoc, hv]
    _ = central F ζ hζ η * (finiteRationalLift F ζ hζ γ * g) * v := by
      rw [← mul_assoc, ← mul_assoc, ← central_comm F ζ hζ η]
      group
    _ = central F ζ hζ η * (central F ζ hζ ε * g * u) * v := by rw [hu]
    _ = _ := by
      simp only [map_mul, ← mul_assoc]
      rw [central_comm F ζ hζ η (central F ζ hζ ε)]

private theorem comparison_unique (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ)
    (hU : U.toOpenSubgroup.toSubgroup.comap (central F ζ hζ) = ⊥)
    (γ : Component F ζ hζ U g) (ε η : rootsOfUnity 3 F)
    (hε : Comparison F ζ hζ U g γ ε) (hη : Comparison F ζ hζ U g γ η) : ε = η := by
  obtain ⟨u, hu⟩ := hε
  obtain ⟨v, hv⟩ := hη
  have he : central F ζ hζ (η⁻¹ * ε) = (v : FiniteCover F ζ hζ) * u⁻¹ := by
    have hc := hu.symm.trans hv
    rw [central_comm F ζ hζ ε g, central_comm F ζ hζ η g] at hc
    have hc' : central F ζ hζ ε * u = central F ζ hζ η * v := by
      apply mul_left_cancel (a := g)
      simpa [mul_assoc] using hc
    have heq := congrArg (fun x : FiniteCover F ζ hζ =>
      (central F ζ hζ η)⁻¹ * x * (u : FiniteCover F ζ hζ)⁻¹) hc'
    simpa [map_mul, map_inv, mul_assoc] using heq
  have hm : η⁻¹ * ε ∈ U.toOpenSubgroup.toSubgroup.comap (central F ζ hζ) := by
    change central F ζ hζ (η⁻¹ * ε) ∈ U.toOpenSubgroup
    rw [he]
    exact U.toOpenSubgroup.mul_mem v.property (U.toOpenSubgroup.inv_mem u.property)
  rw [hU, Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm).symm

theorem descentCharacter_exists (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) :
    ∃ ρ : Component F ζ hζ U g →* rootsOfUnity 3 F,
      ∀ γ : Component F ζ hζ U g,
        ∃ u : U.toOpenSubgroup,
          finiteRationalLift F ζ hζ γ * g = central F ζ hζ (ρ γ)⁻¹ * g * u := by
  have hcard : Nat.card (rootsOfUnity 3 F) = 3 :=
    (hζ.pow (by decide) (by decide : 12 = 4 * 3)).card_rootsOfUnity
  letI : Fact (Nat.Prime (Nat.card (rootsOfUnity 3 F))) := ⟨by rw [hcard]; exact Nat.prime_three⟩
  rcases (U.toOpenSubgroup.toSubgroup.comap (central F ζ hζ)).eq_bot_or_eq_top_of_prime_card with hU | hU
  · let c (γ : Component F ζ hζ U g) : rootsOfUnity 3 F :=
      (finiteComparison_exists F ζ hζ U g γ).choose
    have hc : ∀ γ, Comparison F ζ hζ U g γ (c γ) := fun γ =>
      (finiteComparison_exists F ζ hζ U g γ).choose_spec
    let r : Component F ζ hζ U g →* rootsOfUnity 3 F := {
      toFun := c
      map_one' := comparison_unique F ζ hζ U g hU 1 (c 1) 1 (hc 1)
        ⟨1, by simp⟩
      map_mul' := fun γ δ => comparison_unique F ζ hζ U g hU (γ * δ)
        (c (γ * δ)) (c γ * c δ) (hc (γ * δ))
          (comparison_mul F ζ hζ U g γ δ (c γ) (c δ) (hc γ) (hc δ)) }
    refine ⟨(invMonoidHom : rootsOfUnity 3 F →* rootsOfUnity 3 F).comp r, ?_⟩
    intro γ
    change Comparison F ζ hζ U g γ (c γ)
    exact hc γ
  · refine ⟨1, ?_⟩
    intro γ
    obtain ⟨ε, u, hu⟩ := finiteComparison_exists F ζ hζ U g γ
    have hε : central F ζ hζ ε ∈ U.toOpenSubgroup := by
      change ε ∈ U.toOpenSubgroup.toSubgroup.comap (central F ζ hζ)
      rw [hU]
      trivial
    refine ⟨⟨central F ζ hζ ε * u, U.toOpenSubgroup.mul_mem hε u.property⟩, ?_⟩
    simpa [central_comm F ζ hζ ε g, mul_assoc] using hu

def sections (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F) :
    Submodule ℂ (SymmetricSpace F → ℂ) where
  carrier := {f | (∀ x, f x ∈ scalarFiber F ζ hζ U) ∧
    ∀ (γ : Component F ζ hζ U g) x,
      f ((γ : KPCuspArithmetic.PGL2 F) • x) = (chi F ζ hζ (ρ γ) : ℂ) * f x}
  zero_mem' := ⟨fun x => (scalarFiber F ζ hζ U).zero_mem, by intro γ x; simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun x => (scalarFiber F ζ hζ U).add_mem (hf1 x) (hg1 x), ?_⟩
    intro γ x
    simp only [Pi.add_apply]
    rw [hf2 γ x, hg2 γ x, mul_add]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun x => (scalarFiber F ζ hζ U).smul_mem c (hf1 x), ?_⟩
    intro γ x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf2 γ x]
    ring

def flatLineRelation (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F) :
    Setoid (SymmetricSpace F × scalarFiber F ζ hζ U) where
  r p p' := ∃ γ : Component F ζ hζ U g,
    p'.1 = (γ : KPCuspArithmetic.PGL2 F) • p.1 ∧
    (p'.2 : ℂ) = (chi F ζ hζ (ρ γ) : ℂ) * (p.2 : ℂ)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨1, by simp, by simp⟩
    · rintro p p' ⟨γ, h1, h2⟩
      refine ⟨γ⁻¹, ?_, ?_⟩
      · rw [h1, ← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
      · have hz : (chi F ζ hζ (ρ (γ⁻¹)) : ℂˣ) * (chi F ζ hζ (ρ γ) : ℂˣ) = 1 := by
          rw [map_inv, map_inv, inv_mul_cancel]
        have hz' : (chi F ζ hζ (ρ (γ⁻¹)) : ℂ) * (chi F ζ hζ (ρ γ) : ℂ) = 1 := by
          rw [← Units.val_mul, hz, Units.val_one]
        rw [h2, ← mul_assoc, hz', one_mul]
    · rintro p p' p'' ⟨γ, h1, h2⟩ ⟨δ, h3, h4⟩
      refine ⟨δ * γ, ?_, ?_⟩
      · rw [h3, h1, ← mul_smul, Subgroup.coe_mul]
      · rw [h4, h2, ← mul_assoc, ← Units.val_mul, ← map_mul, ← map_mul]

abbrev OrbifoldLine (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F) :=
  Quotient (flatLineRelation F ζ hζ U g ρ)

def chartMultiplier (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (b : SymmetricSpace F → rootsOfUnity 3 F)
    (γ : Component F ζ hζ U g) (x : SymmetricSpace F) : rootsOfUnity 3 F :=
  b ((γ : KPCuspArithmetic.PGL2 F) • x) * ρ γ * (b x)⁻¹

private theorem chi_norm (ε : rootsOfUnity 3 F) : ‖(chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun x => (chi F ζ hζ x : ℂ)) hp

theorem unitary_chart_cocycle (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (b : SymmetricSpace F → rootsOfUnity 3 F) (hb : IsLocallyConstant b) :
    (∀ ε : rootsOfUnity 3 F, ‖(chi F ζ hζ ε : ℂ)‖ = 1) ∧
    (∀ γ : Component F ζ hζ U g,
      IsLocallyConstant (chartMultiplier F ζ hζ U g ρ b γ)) ∧
    (∀ (γ δ : Component F ζ hζ U g) x,
      chartMultiplier F ζ hζ U g ρ b (γ * δ) x =
        chartMultiplier F ζ hζ U g ρ b γ ((δ : KPCuspArithmetic.PGL2 F) • x) *
          chartMultiplier F ζ hζ U g ρ b δ x) ∧
    (∀ (γ : Component F ζ hζ U g) x,
      ‖(chi F ζ hζ (chartMultiplier F ζ hζ U g ρ b γ x) : ℂ)‖ = 1) := by
  refine ⟨chi_norm F ζ hζ, ?_, ?_, ?_⟩
  · intro γ
    exact ((hb.comp_continuous (KPCuspSiegel.continuous_action F γ)).mul
      (IsLocallyConstant.const (ρ γ))).mul (hb.comp Inv.inv)
  · intro γ δ x
    simp only [chartMultiplier, Subgroup.coe_mul, mul_smul, map_mul]
    group
  · intro γ x
    exact chi_norm F ζ hζ _

def finiteOrbit (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) : Set (FiniteCover F ζ hζ) :=
  {c | ∃ (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
    c = central F ζ hζ ε * g * u}

def automorphicScalars (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) :
    Submodule ℂ (SymmetricSpace F × FiniteCover F ζ hζ → ℂ) where
  carrier := {H |
    (∀ x c, c ∉ finiteOrbit F ζ hζ U g → H (x,c) = 0) ∧
    (∀ x c (ε : rootsOfUnity 3 F),
      H (x, central F ζ hζ ε * c) = (chi F ζ hζ ε : ℂ) * H (x,c)) ∧
    (∀ x c (u : U.toOpenSubgroup), H (x,c * u) = H (x,c)) ∧
    (∀ (γ : Component F ζ hζ U g) x c,
      H ((γ : KPCuspArithmetic.PGL2 F) • x,
        finiteRationalLift F ζ hζ γ * c) = H (x,c))}
  zero_mem' := ⟨by intro x c _; simp, by intro x c ε; simp,
    by intro x c u; simp, by intro γ x c; simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x c hc; simp only [Pi.add_apply]; rw [hf1 x c hc, hg1 x c hc, add_zero]
    · intro x c ε; simp only [Pi.add_apply]; rw [hf2 x c ε, hg2 x c ε, mul_add]
    · intro x c u; simp only [Pi.add_apply]; rw [hf3 x c u, hg3 x c u]
    · intro γ x c; simp only [Pi.add_apply]; rw [hf4 γ x c, hg4 γ x c]
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3, hf4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x c hc; simp only [Pi.smul_apply]; rw [hf1 x c hc, smul_zero]
    · intro x c ε; simp only [Pi.smul_apply, smul_eq_mul]; rw [hf2 x c ε]; ring
    · intro x c u; simp only [Pi.smul_apply]; rw [hf3 x c u]
    · intro γ x c; simp only [Pi.smul_apply]; rw [hf4 γ x c]

def restriction (U : CompactOpenLevel (FiniteCover F ζ hζ)) (g : FiniteCover F ζ hζ)
    (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (hρ : ∀ γ : Component F ζ hζ U g, ∃ u : U.toOpenSubgroup,
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ (ρ γ)⁻¹ * g * u) :
    automorphicScalars F ζ hζ U g →ₗ[ℂ] sections F ζ hζ U g ρ where
  toFun H := ⟨fun x => H.val (x, g), by
    refine ⟨?_, ?_⟩
    · intro x ε hε
      have hr := H.property.2.2.1 x g (⟨central F ζ hζ ε, hε⟩ : U.toOpenSubgroup)
      have hg := H.property.2.1 x g ε
      rw [central_comm F ζ hζ ε g] at hg
      exact hg.symm.trans hr
    · intro γ x
      obtain ⟨u, hu⟩ := hρ γ
      have ha := H.property.2.2.2 γ x g
      rw [hu, H.property.2.2.1, H.property.2.1] at ha
      have hi : (chi F ζ hζ ((ρ γ)⁻¹) : ℂ) * (chi F ζ hζ (ρ γ) : ℂ) = 1 := by
        simp [map_inv]
      have he := congrArg (fun a : ℂ => (chi F ζ hζ (ρ γ) : ℂ) * a) ha
      simpa [map_inv, mul_assoc] using he⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restriction_injective (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (hρ : ∀ γ : Component F ζ hζ U g, ∃ u : U.toOpenSubgroup,
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ (ρ γ)⁻¹ * g * u) :
    Function.Injective (restriction F ζ hζ U g ρ hρ) := by
  intro H J he
  apply Subtype.ext
  funext p
  rcases p with ⟨x, c⟩
  by_cases hc : c ∈ finiteOrbit F ζ hζ U g
  · obtain ⟨ε, u, rfl⟩ := hc
    rw [H.property.2.2.1, J.property.2.2.1, H.property.2.1, J.property.2.1]
    have hx := congrArg (fun f : sections F ζ hζ U g ρ => f.val x) he
    exact congrArg ((chi F ζ hζ ε : ℂ) * ·) hx
  · rw [H.property.1 x c hc, J.property.1 x c hc]

private theorem orbit_scalar_independent (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (ε η : rootsOfUnity 3 F) (u v : U.toOpenSubgroup)
    (he : central F ζ hζ ε * g * u = central F ζ hζ η * g * v)
    (a : scalarFiber F ζ hζ U) : (chi F ζ hζ ε : ℂ) * a = (chi F ζ hζ η : ℂ) * a := by
  rw [central_comm F ζ hζ ε g, central_comm F ζ hζ η g] at he
  have hc : central F ζ hζ ε * u = central F ζ hζ η * v := by
    apply mul_left_cancel (a := g)
    simpa [mul_assoc] using he
  have hh : central F ζ hζ (η⁻¹ * ε) = (v : FiniteCover F ζ hζ) * u⁻¹ := by
    have heq := congrArg (fun x : FiniteCover F ζ hζ =>
      (central F ζ hζ η)⁻¹ * x * (u : FiniteCover F ζ hζ)⁻¹) hc
    simpa [map_mul, map_inv, mul_assoc] using heq
  have hm : central F ζ hζ (η⁻¹ * ε) ∈ U.toOpenSubgroup := by
    rw [hh]
    exact U.toOpenSubgroup.mul_mem v.property (U.toOpenSubgroup.inv_mem u.property)
  have ha := a.property (η⁻¹ * ε) hm
  have heq := congrArg (fun z : ℂ => (chi F ζ hζ η : ℂ) * z) ha
  simpa [map_mul, map_inv, mul_assoc] using heq

def extensionValue (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (f : SymmetricSpace F → scalarFiber F ζ hζ U)
    (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) : ℂ :=
  if hc : c ∈ finiteOrbit F ζ hζ U g then
    (chi F ζ hζ hc.choose : ℂ) * f x else 0

private theorem extensionValue_formula (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (f : SymmetricSpace F → scalarFiber F ζ hζ U)
    (x : SymmetricSpace F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) :
    extensionValue F ζ hζ U g f x (central F ζ hζ ε * g * u) =
      (chi F ζ hζ ε : ℂ) * f x := by
  have hc : central F ζ hζ ε * g * u ∈ finiteOrbit F ζ hζ U g := ⟨ε, u, rfl⟩
  rw [extensionValue, dif_pos hc]
  exact orbit_scalar_independent F ζ hζ U g hc.choose ε hc.choose_spec.choose u
    hc.choose_spec.choose_spec.symm (f x)

private theorem finiteOrbit_central_iff (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g c : FiniteCover F ζ hζ) (ε : rootsOfUnity 3 F) :
    central F ζ hζ ε * c ∈ finiteOrbit F ζ hζ U g ↔ c ∈ finiteOrbit F ζ hζ U g := by
  constructor
  · rintro ⟨η, u, hu⟩
    refine ⟨ε⁻¹ * η, u, ?_⟩
    have he := congrArg (fun z => (central F ζ hζ ε)⁻¹ * z) hu
    simpa [map_mul, map_inv, mul_assoc] using he
  · rintro ⟨η, u, rfl⟩
    exact ⟨ε * η, u, by simp [map_mul, mul_assoc]⟩

private theorem finiteOrbit_right_iff (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g c : FiniteCover F ζ hζ) (u : U.toOpenSubgroup) :
    c * u ∈ finiteOrbit F ζ hζ U g ↔ c ∈ finiteOrbit F ζ hζ U g := by
  constructor
  · rintro ⟨ε, v, hv⟩
    refine ⟨ε, v * u⁻¹, ?_⟩
    have he := congrArg (fun z => z * (u : FiniteCover F ζ hζ)⁻¹) hv
    simpa [mul_assoc] using he
  · rintro ⟨ε, v, rfl⟩
    exact ⟨ε, v * u, by simp [mul_assoc]⟩

private theorem finiteOrbit_rational_iff (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g c : FiniteCover F ζ hζ) (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (hρ : ∀ γ : Component F ζ hζ U g, ∃ u : U.toOpenSubgroup,
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ (ρ γ)⁻¹ * g * u)
    (γ : Component F ζ hζ U g) :
    finiteRationalLift F ζ hζ γ * c ∈ finiteOrbit F ζ hζ U g ↔
      c ∈ finiteOrbit F ζ hζ U g := by
  have hp : ∀ (δ : Component F ζ hζ U g) (d : FiniteCover F ζ hζ),
      d ∈ finiteOrbit F ζ hζ U g → finiteRationalLift F ζ hζ δ * d ∈ finiteOrbit F ζ hζ U g := by
    intro δ d hd
    obtain ⟨ε, u, rfl⟩ := hd
    obtain ⟨v, hv⟩ := hρ δ
    refine ⟨ε * (ρ δ)⁻¹, v * u, ?_⟩
    calc
      finiteRationalLift F ζ hζ δ * (central F ζ hζ ε * g * u) =
        central F ζ hζ ε * (finiteRationalLift F ζ hζ δ * g) * u := by
          simp only [← mul_assoc]
          rw [← central_comm F ζ hζ ε]
      _ = _ := by rw [hv]; simp [map_mul, mul_assoc]
  constructor
  · intro hc
    have he := hp γ⁻¹ _ hc
    simpa [map_inv, mul_assoc] using he
  · exact hp γ c

def extension (U : CompactOpenLevel (FiniteCover F ζ hζ)) (g : FiniteCover F ζ hζ)
    (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (hρ : ∀ γ : Component F ζ hζ U g, ∃ u : U.toOpenSubgroup,
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ (ρ γ)⁻¹ * g * u) :
    sections F ζ hζ U g ρ →ₗ[ℂ] automorphicScalars F ζ hζ U g where
  toFun f := ⟨fun p => extensionValue F ζ hζ U g (fun x => ⟨f.val x, f.property.1 x⟩) p.1 p.2, by
    let fv : SymmetricSpace F → scalarFiber F ζ hζ U := fun x => ⟨f.val x, f.property.1 x⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x c hc
      exact dif_neg hc
    · intro x c ε
      by_cases hc : c ∈ finiteOrbit F ζ hζ U g
      · obtain ⟨η, u, rfl⟩ := hc
        have he : central F ζ hζ ε * (central F ζ hζ η * g * u) =
            central F ζ hζ (ε * η) * g * u := by simp [map_mul, mul_assoc]
        change extensionValue F ζ hζ U g fv x _ = _ * extensionValue F ζ hζ U g fv x _
        rw [he]
        dsimp only [Prod.fst, Prod.snd]
        rw [extensionValue_formula, extensionValue_formula]
        simp [map_mul, mul_assoc]
      · have hn := (finiteOrbit_central_iff F ζ hζ U g c ε).not.mpr hc
        simp only [extensionValue, dif_neg hc, dif_neg hn, mul_zero]
    · intro x c u
      by_cases hc : c ∈ finiteOrbit F ζ hζ U g
      · obtain ⟨ε, v, rfl⟩ := hc
        change extensionValue F ζ hζ U g fv x _ = extensionValue F ζ hζ U g fv x _
        have he : (central F ζ hζ ε * g * v) * u = central F ζ hζ ε * g * (v * u) := by
          simp [mul_assoc]
        rw [he]
        dsimp only [Prod.fst, Prod.snd]
        erw [extensionValue_formula F ζ hζ U g fv x ε (v * u)]
        rw [extensionValue_formula]
      · have hn := (finiteOrbit_right_iff F ζ hζ U g c u).not.mpr hc
        simp only [extensionValue, dif_neg hc, dif_neg hn]
    · intro γ x c
      by_cases hc : c ∈ finiteOrbit F ζ hζ U g
      · obtain ⟨ε, u, rfl⟩ := hc
        obtain ⟨v, hv⟩ := hρ γ
        have he : finiteRationalLift F ζ hζ γ * (central F ζ hζ ε * g * u) =
            central F ζ hζ (ε * (ρ γ)⁻¹) * g * (v * u) := by
          calc
            _ = central F ζ hζ ε * (finiteRationalLift F ζ hζ γ * g) * u := by
              simp only [← mul_assoc]; rw [← central_comm F ζ hζ ε]
            _ = _ := by rw [hv]; simp [map_mul, mul_assoc]
        change extensionValue F ζ hζ U g fv _ _ = extensionValue F ζ hζ U g fv x _
        rw [he]
        dsimp only [Prod.fst, Prod.snd]
        erw [extensionValue_formula F ζ hζ U g fv _ (ε * (ρ γ)⁻¹) (v * u)]
        rw [extensionValue_formula]
        change _ * f.val _ = _ * f.val x
        rw [f.property.2 γ x]
        simp [map_mul, map_inv, mul_assoc]
      · have hn := (finiteOrbit_rational_iff F ζ hζ U g c ρ hρ γ).not.mpr hc
        simp only [extensionValue, dif_neg hc, dif_neg hn]⟩
  map_add' f h := by
    apply Subtype.ext
    funext p
    change extensionValue F ζ hζ U g (fun x => ⟨f.val x + h.val x, _⟩) p.1 p.2 =
      extensionValue F ζ hζ U g (fun x => ⟨f.val x, _⟩) p.1 p.2 +
        extensionValue F ζ hζ U g (fun x => ⟨h.val x, _⟩) p.1 p.2
    by_cases hc : p.2 ∈ finiteOrbit F ζ hζ U g
    · simp only [extensionValue, dif_pos hc, mul_add]
    · simp only [extensionValue, dif_neg hc, add_zero]
  map_smul' a f := by
    apply Subtype.ext
    funext p
    change extensionValue F ζ hζ U g (fun x => ⟨a * f.val x, _⟩) p.1 p.2 =
      a * extensionValue F ζ hζ U g (fun x => ⟨f.val x, _⟩) p.1 p.2
    by_cases hc : p.2 ∈ finiteOrbit F ζ hζ U g
    · simp only [extensionValue, dif_pos hc]
      ring
    · simp only [extensionValue, dif_neg hc, mul_zero]

def sectionEquiv (U : CompactOpenLevel (FiniteCover F ζ hζ)) (g : FiniteCover F ζ hζ)
    (ρ : Component F ζ hζ U g →* rootsOfUnity 3 F)
    (hρ : ∀ γ : Component F ζ hζ U g, ∃ u : U.toOpenSubgroup,
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ (ρ γ)⁻¹ * g * u) :
    automorphicScalars F ζ hζ U g ≃ₗ[ℂ] sections F ζ hζ U g ρ :=
  LinearEquiv.ofLinear (restriction F ζ hζ U g ρ hρ) (extension F ζ hζ U g ρ hρ)
    (by
      ext f x
      change extensionValue F ζ hζ U g (fun y => ⟨f.val y, f.property.1 y⟩) x g = f.val x
      have he : g = central F ζ hζ 1 * g * (1 : U.toOpenSubgroup) := by simp
      simpa using extensionValue_formula F ζ hζ U g
        (fun y => ⟨f.val y, f.property.1 y⟩) x 1 (1 : U.toOpenSubgroup))
    (by
      apply LinearMap.ext
      intro H
      apply restriction_injective F ζ hζ U g ρ hρ
      apply Subtype.ext
      funext x
      change extensionValue F ζ hζ U g
        (fun y => ⟨H.val (y,g), _⟩) x g = H.val (x,g)
      have he : g = central F ζ hζ 1 * g * (1 : U.toOpenSubgroup) := by simp
      simpa using extensionValue_formula F ζ hζ U g
        (fun y => ⟨H.val (y,g), _⟩) x 1 (1 : U.toOpenSubgroup))

structure LineOutput (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) where
  rho : Component F ζ hζ U g →* rootsOfUnity 3 F
  finite_comparison : ∀ γ : Component F ζ hζ U g,
    ∃ u : U.toOpenSubgroup,
      finiteRationalLift F ζ hζ γ * g = central F ζ hζ (rho γ)⁻¹ * g * u
  unitary : ∀ ε : rootsOfUnity 3 F, ‖(chi F ζ hζ ε : ℂ)‖ = 1
  locally_constant : ∀ γ : Component F ζ hζ U g,
    IsLocallyConstant (fun _ : SymmetricSpace F => rho γ)
  hermitian : ∀ (γ : Component F ζ hζ U g) (a : scalarFiber F ζ hζ U),
    ‖(chi F ζ hζ (rho γ) : ℂ) * (a : ℂ)‖ = ‖(a : ℂ)‖
  rank : scalarFiber F ζ hζ U = ⊥ ∨ scalarFiber F ζ hζ U = ⊤
  rank_zero : (∃ ε : rootsOfUnity 3 F,
    central F ζ hζ ε ∈ U.toOpenSubgroup ∧ chi F ζ hζ ε ≠ 1) →
    scalarFiber F ζ hζ U = ⊥
  realization : automorphicScalars F ζ hζ U g ≃ₗ[ℂ] sections F ζ hζ U g rho
  realization_formula : ∀ (H : automorphicScalars F ζ hζ U g) x,
    (realization H).val x = H.val (x,g)

theorem lineOutput_exists (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) : Nonempty (LineOutput F ζ hζ U g) := by
  obtain ⟨ρ, hρ⟩ := descentCharacter_exists F ζ hζ U g
  exact ⟨{
    rho := ρ
    finite_comparison := hρ
    unitary := chi_norm F ζ hζ
    locally_constant := fun γ => IsLocallyConstant.const (ρ γ)
    hermitian := fun γ a => by rw [norm_mul, chi_norm F ζ hζ, one_mul]
    rank := scalarFiber_rank F ζ hζ U
    rank_zero := scalarFiber_rank_zero F ζ hζ U
    realization := sectionEquiv F ζ hζ U g ρ hρ
    realization_formula := fun _ _ => rfl }⟩

def cuspInclusion (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) :
    KPCuspArithmetic.conjugatedStabilizer F Γ q σ →* Γ :=
  (((MulAut.conj σ).toMonoidHom).comp
    (KPCuspArithmetic.conjugatedStabilizer F Γ q σ).subtype).codRestrict Γ (by
      intro s
      obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp s.property
      have hconj : (MulAut.conj σ) (s : KPCuspArithmetic.PGL2 F) = k := by
        rw [← hk_eq]
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      change (MulAut.conj σ) (s : KPCuspArithmetic.PGL2 F) ∈ Γ
      rw [hconj]
      exact hk.1)

theorem cuspInclusion_formula (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (s : KPCuspArithmetic.conjugatedStabilizer F Γ q σ) :
    (cuspInclusion F Γ q σ s : KPCuspArithmetic.PGL2 F) = σ * s * σ⁻¹ := by
  simp only [cuspInclusion, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply]

section Cusp
variable {F ζ hζ}
variable (S : Subgroup (KPCuspArithmetic.PGL2 F))
variable (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)

def kernelLattice : AddSubgroup F where
  carrier := {x | x ∈ D.L ∧ ∀ hx : x ∈ D.L,
    ρ (D.inclusion (Multiplicative.ofAdd (⟨x,hx⟩ : D.L))) = 1}
  zero_mem' := by
    refine ⟨D.L.zero_mem, ?_⟩
    intro hx
    have h : (⟨(0 : F), hx⟩ : D.L) = 0 := Subtype.ext rfl
    rw [h]
    simp
  add_mem' := by
    rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
    refine ⟨D.L.add_mem hxL hyL, ?_⟩
    intro h
    have hxy : (⟨x + y, h⟩ : D.L) =
        (⟨x, hxL⟩ : D.L) + (⟨y, hyL⟩ : D.L) := Subtype.ext rfl
    rw [hxy, ofAdd_add, map_mul, map_mul, hx hxL, hy hyL, one_mul]
  neg_mem' := by
    rintro x ⟨hxL, hx⟩
    refine ⟨D.L.neg_mem hxL, ?_⟩
    intro h
    have hxy : (⟨-x, h⟩ : D.L) = -(⟨x, hxL⟩ : D.L) := Subtype.ext rfl
    rw [hxy, ofAdd_neg, map_inv, map_inv, hx hxL, inv_one]

private def translationCharacter : D.L →+ Additive (rootsOfUnity 3 F) where
  toFun x := Additive.ofMul (ρ (D.inclusion (Multiplicative.ofAdd x)))
  map_zero' := by
    change ρ (D.inclusion 1) = 1
    simp
  map_add' x y := by
    change ρ (D.inclusion (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) =
      ρ (D.inclusion (Multiplicative.ofAdd x)) * ρ (D.inclusion (Multiplicative.ofAdd y))
    simp

private theorem kernelLattice_subgroupOf :
    (kernelLattice S D ρ).addSubgroupOf D.L = (translationCharacter S D ρ).ker := by
  ext x
  change (x.val ∈ D.L ∧ ∀ hx : x.val ∈ D.L,
    ρ (D.inclusion (Multiplicative.ofAdd (⟨x.val, hx⟩ : D.L))) = 1) ↔
      ρ (D.inclusion (Multiplicative.ofAdd x)) = 1
  exact ⟨fun h => h.2 x.property, fun h => ⟨x.property, fun _ => h⟩⟩

private theorem kernelLattice_index : ((kernelLattice S D ρ).addSubgroupOf D.L).index ≤ 3 := by
  rw [kernelLattice_subgroupOf, AddSubgroup.index_ker]
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
    (card_rootsOfUnity F 3)

private theorem kernelLattice_finite_deck :
    Finite (D.L ⧸ (kernelLattice S D ρ).addSubgroupOf D.L) := by
  rw [kernelLattice_subgroupOf]
  exact Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange
    (translationCharacter S D ρ)).symm.toEquiv

abbrev KernelTorus := KPCuspCharts.Torus F (kernelLattice S D ρ)

def torusSections (V : Submodule ℂ ℂ) : Submodule ℂ (KernelTorus S D ρ → ℂ) where
  carrier := {f | (∀ z, f z ∈ V) ∧ ∀ (x : D.L) (y : KPCuspCharts.Horizontal F),
    f (QuotientAddGroup.mk (y + KPCuspCharts.embedding F x)) =
      (chi F ζ hζ (ρ (D.inclusion (Multiplicative.ofAdd x))) : ℂ) *
        f (QuotientAddGroup.mk y)}
  zero_mem' := ⟨fun z => V.zero_mem, by intro x y; simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun z => V.add_mem (hf1 z) (hg1 z), ?_⟩
    intro x y
    simp only [Pi.add_apply]
    rw [hf2 x y, hg2 x y, mul_add]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun z => V.smul_mem c (hf1 z), ?_⟩
    intro x y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf2 x y]
    ring

def horizontalSections (V : Submodule ℂ ℂ) :
    Submodule ℂ (KPCuspCharts.Horizontal F → ℂ) where
  carrier := {f | (∀ y, f y ∈ V) ∧ ∀ (x : D.L) y,
    f (y + KPCuspCharts.embedding F x) =
      (chi F ζ hζ (ρ (D.inclusion (Multiplicative.ofAdd x))) : ℂ) * f y}
  zero_mem' := ⟨fun y => V.zero_mem, by intro x y; simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun y => V.add_mem (hf1 y) (hg1 y), ?_⟩
    intro x y
    simp only [Pi.add_apply]
    rw [hf2 x y, hg2 x y, mul_add]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun y => V.smul_mem c (hf1 y), ?_⟩
    intro x y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf2 x y]
    ring

theorem kernelLattice_stable (s : S) (x : kernelLattice S D ρ) :
    ((D.ratio s : Fˣ) : F) * x ∈ kernelLattice S D ρ := by
  obtain ⟨τ, hτ1, hτmul, hτformula⟩ := KPCuspLogShape.upper_translation_cocycle
    F S D.upper D.E D.ratio D.ratioFormula
  have hτi (y : D.L) : τ (D.inclusion (Multiplicative.ofAdd y)) = y := by
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
      (D.inclusion (Multiplicative.ofAdd y) : KPCuspArithmetic.PGL2 F)
    obtain ⟨hzero, hdiag, ht⟩ := D.unipotentFormula y A hA
    have hd : A 1 1 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hzero, hz])
    rw [hτformula _ _ hA, ht, hdiag, mul_div_cancel_right₀ _ hd]
  let xi : D.L := ⟨x.val, x.property.1⟩
  have hri : D.ratio (D.inclusion (Multiplicative.ofAdd xi)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← D.exact]
    exact ⟨Multiplicative.ofAdd xi, rfl⟩
  have hker : s * D.inclusion (Multiplicative.ofAdd xi) * s⁻¹ ∈ D.inclusion.range := by
    rw [D.exact, MonoidHom.mem_ker, map_mul, map_mul, hri, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨y, hy⟩ := hker
  have hinv : ((D.ratio s : Fˣ) : F) * τ s⁻¹ + τ s = 0 := by
    rw [← hτmul, mul_inv_cancel, hτ1]
  have hconj : τ (s * D.inclusion (Multiplicative.ofAdd xi) * s⁻¹) =
      ((D.ratio s : Fˣ) : F) * x.val := by
    rw [hτmul, map_mul, hri, mul_one, hτmul, hτi]
    change ((D.ratio s : Fˣ) : F) * τ s⁻¹ +
      (((D.ratio s : Fˣ) : F) * x.val + τ s) = ((D.ratio s : Fˣ) : F) * x.val
    linear_combination hinv
  have hxy : (y.toAdd : F) = ((D.ratio s : Fˣ) : F) * x.val := by
    rw [← hτi y.toAdd]
    change τ (D.inclusion y) = _
    rw [hy, hconj]
  have hr : ρ (D.inclusion y) = 1 := by
    rw [hy, map_mul, map_mul, x.property.2 x.property.1, mul_one, map_inv, mul_inv_cancel]
  change ((D.ratio s : Fˣ) : F) * x.val ∈ kernelLattice S D ρ
  rw [← hxy]
  refine ⟨y.toAdd.property, ?_⟩
  intro h
  exact hr

private theorem horizontal_kernel_invariant (V : Submodule ℂ ℂ)
    (f : horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V)
    (x : kernelLattice S D ρ) (y : KPCuspCharts.Horizontal F) :
    f.val (y + KPCuspCharts.embedding F x) = f.val y := by
  have he := f.property.2 (⟨x.val, x.property.1⟩ : D.L) y
  rw [x.property.2 x.property.1] at he
  simpa using he

def descendHorizontal (V : Submodule ℂ ℂ)
    (f : horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V) : KernelTorus S D ρ → ℂ :=
  Quotient.lift f.val (by
    intro a b hab
    obtain ⟨x, hx, he⟩ := (QuotientAddGroup.leftRel_apply.mp hab)
    have hb : b = a + KPCuspCharts.embedding F x := by
      rw [he]
      abel
    rw [hb]
    exact (horizontal_kernel_invariant S D ρ V f ⟨x,hx⟩ a).symm)

def torusSectionEquiv (V : Submodule ℂ ℂ) :
    torusSections (ζ := ζ) (hζ := hζ) S D ρ V ≃ₗ[ℂ]
      horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V where
  toFun f := ⟨fun y => f.val (QuotientAddGroup.mk y),
    ⟨fun y => f.property.1 _, f.property.2⟩⟩
  invFun f := ⟨descendHorizontal S D ρ V f, by
    refine ⟨?_, ?_⟩
    · intro z
      induction z using QuotientAddGroup.induction_on with
      | H y => exact f.property.1 y
    · intro x y
      exact f.property.2 x y⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    induction z using QuotientAddGroup.induction_on with
    | H y => rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := rfl

structure CuspOutput (V : Submodule ℂ ℂ) where
  kernel_le : kernelLattice S D ρ ≤ D.L
  index : ((kernelLattice S D ρ).addSubgroupOf D.L).index ≤ 3
  finite_deck : Finite (D.L ⧸ (kernelLattice S D ρ).addSubgroupOf D.L)
  deck_card : Nat.card (D.L ⧸ (kernelLattice S D ρ).addSubgroupOf D.L) ≤ 3
  compact : CompactSpace (KernelTorus S D ρ)
  stable : ∀ (s : S) (x : kernelLattice S D ρ),
    ((D.ratio s : Fˣ) : F) * x ∈ kernelLattice S D ρ
  monodromy : S →* (KernelTorus S D ρ ≃ₜ KernelTorus S D ρ)
  monodromy_formula : ∀ (s : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
      (y : KPCuspCharts.Horizontal F),
    Matrix.ProjGenLinGroup.mk A = (s : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
    monodromy s (QuotientAddGroup.mk y) =
      QuotientAddGroup.mk (fun i => KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i *
        y i + KPCuspCharts.embedding F (A 0 1 / A 1 1) i)
  preserves_sections : ∀ (s : S) (f : torusSections (ζ := ζ) (hζ := hζ) S D ρ V),
    (fun z => f.val (monodromy s z)) ∈ torusSections (ζ := ζ) (hζ := hζ) S D ρ V
  realization : torusSections (ζ := ζ) (hζ := hζ) S D ρ V ≃ₗ[ℂ]
    horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V
  realization_formula : ∀ (f : torusSections (ζ := ζ) (hζ := hζ) S D ρ V) y,
    (realization f).val y = f.val (QuotientAddGroup.mk y)

private theorem triple_kernel (x : D.L) : (3 : ℤ) • (x : F) ∈ kernelLattice S D ρ := by
  refine ⟨D.L.zsmul_mem x.property 3, ?_⟩
  intro hx
  have he : (⟨(3 : ℤ) • (x : F), hx⟩ : D.L) = (3 : ℤ) • x := rfl
  rw [he]
  change ρ (D.inclusion ((Multiplicative.ofAdd x) ^ (3 : ℤ))) = 1
  rw [map_zpow, map_zpow]
  change ρ (D.inclusion (Multiplicative.ofAdd x)) ^ (3 : ℕ) = 1
  apply Subtype.ext
  exact (ρ (D.inclusion (Multiplicative.ofAdd x))).property
private theorem kernel_horiz_full (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ hd : DiscreteTopology (KPCuspCharts.translationLattice F (kernelLattice S D ρ)).toIntSubmodule,
    letI := hd; IsZLattice ℝ (KPCuspCharts.translationLattice F (kernelLattice S D ρ)).toIntSubmodule := by
  obtain ⟨hd, hf⟩ := G.lattice
  letI := hd
  letI := hf
  have hle : KPCuspCharts.translationLattice F (kernelLattice S D ρ) ≤
      KPCuspCharts.translationLattice F D.L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx.1, rfl⟩
  letI : DiscreteTopology (KPCuspCharts.translationLattice F (kernelLattice S D ρ)).toIntSubmodule := DiscreteTopology.of_subset hd hle
  refine ⟨inferInstance, ⟨?_⟩⟩
  apply top_le_iff.mp
  rw [← IsZLattice.span_top (K := ℝ) (L := (KPCuspCharts.translationLattice F D.L).toIntSubmodule)]
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hm : (3 : ℤ) • KPCuspCharts.embedding F x ∈
      KPCuspCharts.translationLattice F (kernelLattice S D ρ) := by
    refine ⟨(3 : ℤ) • x, triple_kernel S D ρ ⟨x,hx⟩, ?_⟩
    exact map_zsmul _ _ _
  have hs := Submodule.subset_span (R := ℝ) hm
  have hh := Submodule.smul_mem (Submodule.span ℝ (KPCuspCharts.translationLattice F (kernelLattice S D ρ) : Set (KPCuspCharts.Horizontal F))) (1/3 : ℝ) hs
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul] at hh
  norm_num at hh
  exact hh
private theorem conjugate_translation (s : S) (x : D.L) :
    ∃ (y : D.L), (y : F) = ((D.ratio s : Fˣ) : F) * x ∧
      D.inclusion (Multiplicative.ofAdd y) = s * D.inclusion (Multiplicative.ofAdd x) * s⁻¹ := by
  obtain ⟨τ, hτ1, hτmul, hτformula⟩ := KPCuspLogShape.upper_translation_cocycle F S D.upper D.E D.ratio D.ratioFormula
  have hτi (x : D.L) : τ (D.inclusion (Multiplicative.ofAdd x)) = x := by
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (D.inclusion (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F)
    obtain ⟨hzero, hdiag, ht⟩ := D.unipotentFormula x A hA
    have hd : A 1 1 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hzero, hz])
    rw [hτformula _ _ hA, ht, hdiag, mul_div_cancel_right₀ _ hd]
  have hri : D.ratio (D.inclusion (Multiplicative.ofAdd x)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← D.exact]
    exact ⟨_, rfl⟩
  have hk : s * D.inclusion (Multiplicative.ofAdd x) * s⁻¹ ∈ D.ratio.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, hri, mul_one, map_inv, mul_inv_cancel]
  rw [← D.exact] at hk
  obtain ⟨y, hy⟩ := hk
  refine ⟨y.toAdd, ?_, hy⟩
  have hτinv : ((D.ratio s : Fˣ) : F) * τ s⁻¹ + τ s = 0 := by
    rw [← hτmul, mul_inv_cancel, hτ1]
  rw [← hτi y.toAdd]
  change τ (D.inclusion y) = _
  rw [hy, hτmul, map_mul, hri, mul_one, hτmul, hτi]
  change ((D.ratio s : Fˣ) : F) * τ s⁻¹ +
    (((D.ratio s : Fˣ) : F) * (x : F) + τ s) = ((D.ratio s : Fˣ) : F) * (x : F)
  linear_combination hτinv
private theorem kernel_stable (s : S) (x : kernelLattice S D ρ) :
    ((D.ratio s : Fˣ) : F) * x ∈ kernelLattice S D ρ := by
  obtain ⟨y, hy, hc⟩ := conjugate_translation S D s ⟨x, x.property.1⟩
  refine ⟨hy ▸ y.property, ?_⟩
  intro hx
  have he : (⟨((D.ratio s : Fˣ) : F) * x, hx⟩ : D.L) = y := Subtype.ext hy.symm
  rw [he, hc, map_mul, map_mul, x.property.2 x.property.1, mul_one, map_inv, mul_inv_cancel]
private def placeRing : F →+* KPCuspCharts.Horizontal F where
  toFun := KPCuspCharts.embedding F
  map_zero' := (KPCuspCharts.embedding F).map_zero
  map_add' := (KPCuspCharts.embedding F).map_add
  map_one' := by ext i; simp [KPCuspCharts.embedding]
  map_mul' := by intro x y; ext i; simp [KPCuspCharts.embedding]
private def scalarMap (s : S) : KernelTorus S D ρ →+ KernelTorus S D ρ :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (placeRing ((D.ratio s : Fˣ) : F))) (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨((D.ratio s : Fˣ) : F) * a, kernel_stable S D ρ s ⟨a, ha⟩, (placeRing).map_mul _ _⟩)
private theorem scalarMap_mk (s : S) (x : KPCuspCharts.Horizontal F) :
    scalarMap S D ρ s (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (placeRing ((D.ratio s : Fˣ) : F) * x) := rfl
private theorem scalarMap_one : scalarMap S D ρ 1 = AddMonoidHom.id _ := by
  ext x
  simp [scalarMap_mk]
private theorem scalarMap_mul (s t : S) : scalarMap S D ρ (s * t) =
    (scalarMap S D ρ s).comp (scalarMap S D ρ t) := by
  ext x
  simp [scalarMap_mk, mul_assoc]
private theorem scalarMap_continuous (s : S) : Continuous (scalarMap S D ρ s) := by
  rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
  exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)
private theorem kernel_monodromy :
    ∃ α : S →* (KernelTorus S D ρ ≃ₜ KernelTorus S D ρ),
      ∀ (s : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (x : KPCuspCharts.Horizontal F),
        Matrix.ProjGenLinGroup.mk A = (s : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
        α s (QuotientAddGroup.mk x) = QuotientAddGroup.mk
          (fun i => KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * x i +
            KPCuspCharts.embedding F (A 0 1 / A 1 1) i) := by
  obtain ⟨τ, hτ1, hτmul, hτformula⟩ :=
    KPCuspLogShape.upper_translation_cocycle F S D.upper D.E D.ratio D.ratioFormula
  let b : S → KernelTorus S D ρ → KernelTorus S D ρ := fun s x =>
    scalarMap S D ρ s x + QuotientAddGroup.mk (placeRing (τ s))
  have hb1 (x : KernelTorus S D ρ) : b 1 x = x := by
    simp only [b, hτ1, map_zero, QuotientAddGroup.mk_zero, add_zero]
    exact DFunLike.congr_fun (scalarMap_one S D ρ) x
  have hbmul (s t : S) (x : KernelTorus S D ρ) : b (s * t) x = b s (b t x) := by
    simp only [b, hτmul, map_add, QuotientAddGroup.mk_add, map_mul]
    rw [scalarMap_mul]
    change scalarMap S D ρ s (scalarMap S D ρ t x) +
      (QuotientAddGroup.mk (placeRing ((D.ratio s : Fˣ) : F) * placeRing (τ t)) +
        QuotientAddGroup.mk (placeRing (τ s))) = _
    rw [scalarMap_mk]
    abel
  have hbcont (s : S) : Continuous (b s) := (scalarMap_continuous S D ρ s).add continuous_const
  let e : S → (KernelTorus S D ρ ≃ₜ KernelTorus S D ρ) := fun s => {
    toFun := b s
    invFun := b s⁻¹
    left_inv := fun x => by rw [← hbmul, inv_mul_cancel, hb1]
    right_inv := fun x => by rw [← hbmul, mul_inv_cancel, hb1]
    continuous_toFun := hbcont s
    continuous_invFun := hbcont s⁻¹ }
  let α : S →* (KernelTorus S D ρ ≃ₜ KernelTorus S D ρ) := {
    toFun := e
    map_one' := by apply Homeomorph.ext; exact hb1
    map_mul' := fun s t => by apply Homeomorph.ext; exact hbmul s t }
  refine ⟨α, ?_⟩
  intro s A x hA hc
  change b s (QuotientAddGroup.mk x) = _
  simp only [b, scalarMap_mk, ← QuotientAddGroup.mk_add, hτformula s A hA]
  rfl
private def pullback (V : Submodule ℂ ℂ) : torusSections (ζ := ζ) (hζ := hζ) S D ρ V →ₗ[ℂ] horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V where
  toFun f := ⟨fun y => f.val (QuotientAddGroup.mk y),
    ⟨fun y => f.property.1 _, fun x y => f.property.2 x y⟩⟩
  map_add' f g := rfl
  map_smul' c f := rfl
private theorem pullback_injective (V : Submodule ℂ ℂ) : Function.Injective (pullback (ζ := ζ) (hζ := hζ) S D ρ V) := by
  intro f g h
  apply Subtype.ext
  funext z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact congrFun (congrArg Subtype.val h) y
private theorem horizontal_invariant (V : Submodule ℂ ℂ)
    (f : horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V)
    (a b : KPCuspCharts.Horizontal F) (hab : (QuotientAddGroup.mk a : KernelTorus S D ρ) = QuotientAddGroup.mk b) : f.val a = f.val b := by
  have hx : -a + b ∈ KPCuspCharts.translationLattice F (kernelLattice S D ρ) := by
    simpa [sub_eq_add_neg, add_comm] using (QuotientAddGroup.eq_iff_sub_mem).mp hab.symm
  obtain ⟨x, hx, he⟩ := hx
  have hb : b = a + KPCuspCharts.embedding F x := by rw [he]; abel
  rw [hb, f.property.2 ⟨x, hx.1⟩ a, hx.2 hx.1, map_one, Units.val_one, one_mul]
private theorem pullback_surjective (V : Submodule ℂ ℂ) : Function.Surjective (pullback (ζ := ζ) (hζ := hζ) S D ρ V) := by
  intro f
  let H : KernelTorus S D ρ → ℂ := Quotient.lift f.val (fun a b h =>
    horizontal_invariant (ζ := ζ) (hζ := hζ) S D ρ V f a b (Quotient.sound h))
  have hH : H ∈ torusSections (ζ := ζ) (hζ := hζ) S D ρ V := by
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact f.property.1 y
    · intro x y
      exact f.property.2 x y
  exact ⟨⟨H, hH⟩, rfl⟩
private theorem monodromy_preserves (V : Submodule ℂ ℂ)
    (α : S →* (KernelTorus S D ρ ≃ₜ KernelTorus S D ρ))
    (hα : ∀ (s : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (y : KPCuspCharts.Horizontal F),
      Matrix.ProjGenLinGroup.mk A = (s : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      α s (QuotientAddGroup.mk y) = QuotientAddGroup.mk (fun i =>
        KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * y i + KPCuspCharts.embedding F (A 0 1 / A 1 1) i))
    (s : S) (f : torusSections (ζ := ζ) (hζ := hζ) S D ρ V) :
    (fun z => f.val (α s z)) ∈ torusSections (ζ := ζ) (hζ := hζ) S D ρ V := by
  refine ⟨fun z => f.property.1 _, ?_⟩
  intro x y
  obtain ⟨A, hA, hzero⟩ := D.upper s s.property
  dsimp only
  rw [hα s A _ hA hzero, hα s A _ hA hzero]
  obtain ⟨v, hv, hc⟩ := conjugate_translation S D s x
  have ht : (fun i => KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i *
      (y + KPCuspCharts.embedding F x) i + KPCuspCharts.embedding F (A 0 1 / A 1 1) i) =
      (fun i => KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * y i +
        KPCuspCharts.embedding F (A 0 1 / A 1 1) i) + KPCuspCharts.embedding F v := by
    funext i
    change KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * (y i + KPCuspCharts.embedding F x i) +
      KPCuspCharts.embedding F (A 0 1 / A 1 1) i =
      KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * y i +
      KPCuspCharts.embedding F (A 0 1 / A 1 1) i + KPCuspCharts.embedding F v i
    rw [hv]
    have hm (a b : F) : KPCuspCharts.embedding F (a * b) i = KPCuspCharts.embedding F a i * KPCuspCharts.embedding F b i := map_mul (KPCusp.complexPlace F i).embedding a b
    rw [hm]
    ring
  rw [ht, f.property.2 v]
  have hr : ρ (D.inclusion (Multiplicative.ofAdd v)) = ρ (D.inclusion (Multiplicative.ofAdd x)) := by
    rw [hc, map_mul, map_mul, map_inv, mul_comm (ρ s), mul_assoc, mul_inv_cancel, mul_one]
  rw [hr]
theorem cuspOutput_exists (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (G : KPCuspCharts.ChartOutput F hF S D) (V : Submodule ℂ ℂ) :
    Nonempty (CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) := by
  obtain ⟨α, hα⟩ := kernel_monodromy S D ρ
  obtain ⟨hd, hl⟩ := kernel_horiz_full S D ρ hF G
  let e := LinearEquiv.ofBijective (pullback (ζ := ζ) (hζ := hζ) S D ρ V)
    ⟨pullback_injective S D ρ V, pullback_surjective S D ρ V⟩
  have hi : ((kernelLattice S D ρ).addSubgroupOf D.L).index ≤ 3 := kernelLattice_index S D ρ
  refine ⟨{
    kernel_le := fun x hx => hx.1
    index := hi
    finite_deck := kernelLattice_finite_deck S D ρ
    deck_card := hi
    compact := KPCuspChart.compact_torus_of_lattice F _ hd hl
    stable := kernel_stable S D ρ
    monodromy := α
    monodromy_formula := hα
    preserves_sections := monodromy_preserves S D ρ V α hα
    realization := e
    realization_formula := fun f y => rfl }⟩

end Cusp
end KPCuspGenuineMonodromy

theorem kp_cusp_genuine_hermitian_monodromy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (g : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    ∃ O : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g,
      ∀ (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
        (hσ : σ • KPCuspArithmetic.infinity F = q),
      let S := KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) q σ
      let ρ := O.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) q σ)
      ∃ (D : KPCuspCharts.ParabolicData F S)
        (_G : KPCuspCharts.ChartOutput F hF S D),
        Nonempty (KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ
          (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)) := by
  obtain ⟨O⟩ := KPCuspGenuineMonodromy.lineOutput_exists F ζ hζ U g
  refine ⟨O, ?_⟩
  intro q σ hσ
  obtain ⟨hc, ho⟩ := KPCuspMonodromy.projected_finite_level_compact_open F ζ hζ U
  obtain ⟨D, ⟨G⟩⟩ := KPCuspMonodromy.finite_adelic_cusp_charts F hF
    (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)) hc ho
    (KPCuspGenuineMonodromy.finiteBase F ζ hζ g) q σ hσ
  refine ⟨D, G, ?_⟩
  exact KPCuspGenuineMonodromy.cuspOutput_exists _ D _ hF G
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)

end DedekindZetaZeroFree

end
end
