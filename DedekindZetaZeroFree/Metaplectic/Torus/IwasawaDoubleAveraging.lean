module

public import DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import DedekindZetaZeroFree.Eisenstein.Induction.BorelModulusAndIwasawaContinuity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ProjectiveWeights.CompactAveraging

@[expose] public section

set_option synthInstance.maxHeartbeats 100000
open scoped Classical BigOperators Matrix.Norms.Elementwise ComplexConjugate
open MeasureTheory Complex

noncomputable section
open scoped NumberField Classical Matrix
open NumberField
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def sectionTuple (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl w => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (r w))
    | Sum.inr _ => 1,
    Filter.Eventually.of_forall (by
      intro v; cases v <;> simp [KPAdelicCoverRestrictedProduct.compact])⟩

private theorem tuple_prod (a : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (ha : ∀ q, a (Sum.inr q) = 1) :
    a = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      (fun w => KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl w)
        (a (Sum.inl w)))).prod := by
  apply RestrictedProduct.ext
  intro v
  change a v = (RestrictedProduct.evalMonoidHom _ v) _
  rw [map_list_prod, List.map_map]
  cases v with
  | inl w =>
    simp only [Function.comp_def, KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply]
    simp only [RestrictedProduct.evalMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply]
    have he : (fun x : InfinitePlace F => Pi.mulSingle (Sum.inl x) (a (Sum.inl x)) (Sum.inl w)) =
        fun x => if x = w then a (Sum.inl w) else 1 := by
      funext x
      by_cases h : x = w
      · subst x; simp
      · simp [Pi.mulSingle_apply, Sum.inl_injective.ne h, h]
    rw [he]
    rw [List.prod_map_eq_pow_single w _ (by intro x hx _; simp [hx])]
    rw [List.nodup_iff_count_le_one.mp (Finset.nodup_toList _) w |>.antisymm
      (Nat.succ_le_of_lt (List.count_pos_iff.mpr (by simp)))]
    simp
  | inr q =>
    simp [ha, KPAdelicCoverRestrictedProduct.localToRestricted, Function.comp_def,
      RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_apply]

private theorem sectionTuple_insertion
    (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (sectionTuple F ζ hζ r)) =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (r w)) := by
  rw [tuple_prod F ζ hζ (sectionTuple F ζ hζ r) (by intro q; rfl)]
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro w hw
  obtain ⟨j, hj, hjf⟩ := KPAdelicCoverRestrictedProduct.local_pgl_injection F ζ hζ (Sum.inl w)
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) (Matrix.GeneralLinearGroup.map e.symm.toRingHom (r w)))) =
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) (Matrix.GeneralLinearGroup.map e.symm.toRingHom (Matrix.ProjGenLinGroup.mk (r w)).out)))
  rw [← hjf.2, ← hjf.2]
  apply congrArg j
  let f : Matrix.GeneralLinearGroup (Fin 2) ℂ →* KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inl w) :=
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)).comp
      { toFun := fun g => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
          (Matrix.GeneralLinearGroup.map e.symm.toRingHom g)
        map_one' := by simp [KPLocalCover.sectionMap]; rfl
        map_mul' := by
          intro g h
          change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
          congr 1
          · simp
          · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one] }
  have hf : f.comp (Matrix.GeneralLinearGroup.scalar (Fin 2)) = 1 := by
    ext u
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.map e.symm.toRingHom u, ?_⟩
    simp [f, KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, Matrix.GeneralLinearGroup.map_scalar]
  have he := Matrix.ProjGenLinGroup.lift_mk hf (r w)
  have he' := Matrix.ProjGenLinGroup.lift_mk hf (Matrix.ProjGenLinGroup.mk (r w)).out
  rw [show Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk (r w)).out = Matrix.ProjGenLinGroup.mk (r w) from Quotient.out_eq _] at he'
  exact he.symm.trans he'

private lemma gl_map_d {K L : Type*} [Field K] [Field L] (φ : K →+* L) (u v : Kˣ) :
    Matrix.GeneralLinearGroup.map φ (KubotaRankTwo.d K u v) =
      KubotaRankTwo.d L (Units.map φ u) (Units.map φ v) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.map_apply, Units.coe_map]

private lemma gl_map_n {K L : Type*} [Field K] [Field L] (φ : K →+* L) (t : K) :
    Matrix.GeneralLinearGroup.map φ (KubotaRankTwo.n K t) = KubotaRankTwo.n L (φ t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.map_apply]

private lemma archDiagonalTuple_eq_sectionTuple (u : InfinitePlace F → ℂˣ) :
    KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (u w : ℂ)) =
      sectionTuple F ζ hζ (fun w => KubotaRankTwo.d ℂ (u w) 1) := by
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl w =>
    change KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w))
          (if h : ((u w : ℂˣ) : ℂ) = 0 then 1
            else Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ w)).symm ((u w : ℂˣ) : ℂ)) _) 1)
      = KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
            (KubotaRankTwo.d ℂ (u w) 1))
    simp only [Units.ne_zero, ↓reduceDIte, gl_map_d]
    congr 1
    apply Units.ext
    simp [Units.coe_map]
  | inr q => rfl

private theorem archDiagonalLift_eq_insertion (u : InfinitePlace F → ℂˣ) :
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (u w : ℂ)) =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (u w) 1)) := by
  unfold KPGlobalTorusFunctionData.archDiagonalLift
  rw [archDiagonalTuple_eq_sectionTuple F ζ hζ u, sectionTuple_insertion]

 def adeleOfArch (c : InfinitePlace F → ℂ) : KPGlobalTorusFunctionData.Adeles F :=
  ((fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (c w)), 0)

private theorem rootTuple_eq_sectionTuple (c : InfinitePlace F → ℂ) :
    KPGlobalTorusFunctionData.rootTuple F ζ hζ (adeleOfArch F ζ hζ c) =
      sectionTuple F ζ hζ (fun w => KubotaRankTwo.n ℂ (c w)) := by
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl w =>
    change KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (KubotaRankTwo.n (KPHilbert.Completion F (Sum.inl w))
          ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm (c w)))
      = KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
            (KubotaRankTwo.n ℂ (c w)))
    rw [gl_map_n]
    rfl
  | inr q =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) 0 = 1
    simp

private theorem N_eq_insertion (c : InfinitePlace F → ℂ) :
    KPGlobalTorusFunctionData.N F ζ hζ (adeleOfArch F ζ hζ c) =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ (c w))) := by
  unfold KPGlobalTorusFunctionData.N
  rw [rootTuple_eq_sectionTuple F ζ hζ c, sectionTuple_insertion]

 def archDen (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2
 def archS (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (archDen A)

 lemma archDen_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) : 0 < archDen A := by
  unfold archDen
  have h : A 1 0 ≠ 0 ∨ A 1 1 ≠ 0 := by
    by_contra hc; push Not at hc
    exact hA (by rw [Matrix.det_fin_two]; simp [hc.1, hc.2])
  rcases h with h | h
  · nlinarith [norm_pos_iff.mpr h, sq_nonneg ‖A 1 1‖, sq_nonneg ‖A 1 0‖]
  · nlinarith [norm_pos_iff.mpr h, sq_nonneg ‖A 1 1‖, sq_nonneg ‖A 1 0‖]

private lemma archS_sq (A : Matrix (Fin 2) (Fin 2) ℂ) : archS A ^ 2 = archDen A :=
  Real.sq_sqrt (by unfold archDen; positivity)

private lemma archS_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) : 0 < archS A :=
  Real.sqrt_pos.mpr (archDen_pos A hA)

 def archK (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star (A 1 1) / ((archS A : ℝ) : ℂ), -star (A 1 0) / ((archS A : ℝ) : ℂ);
     A 1 0 / ((archS A : ℝ) : ℂ), A 1 1 / ((archS A : ℝ) : ℂ)]
 def archY (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) : ℂˣ :=
  Units.mk0 (A.det / ((archDen A : ℝ) : ℂ))
    (div_ne_zero hA (by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (archDen_pos A hA)))
 def archX (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (A 0 0 * star (A 1 0) + A 0 1 * star (A 1 1)) / A.det

private lemma archK_mul_star (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    archK A * star (archK A) = 1 := by
  have hspos : 0 < archS A := archS_pos A hA
  have hs : ((archS A : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hspos
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [archK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      star_div₀, star_inv₀, star_star, Complex.conj_ofReal, Complex.mul_conj',
      Complex.conj_mul', ← Complex.ofReal_add, ← Complex.ofReal_pow,
      archS_sq, archDen, Complex.ofReal_inj]
  · rw [abs_of_pos hspos]; field_simp; rw [archS_sq]; unfold archDen; ring
  · ring
  · ring
  · rw [abs_of_pos hspos]; field_simp; rw [archS_sq]; unfold archDen; ring

private lemma archK_det (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (archK A).det = 1 := by
  have hspos : 0 < archS A := archS_pos A hA
  have hs : ((archS A : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hspos
  rw [Matrix.det_fin_two]
  simp only [archK, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  rw [Complex.star_def]
  rw [Complex.conj_mul', Complex.conj_mul']
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  rw [sub_neg_eq_add, ← Complex.ofReal_add, Complex.ofReal_inj, archS_sq]
  unfold archDen
  ring

private lemma archK_mem (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    archK A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨Matrix.mem_unitaryGroup_iff.mpr (archK_mul_star A hA), archK_det A hA⟩

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
open scoped Matrix

private lemma archY_norm (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    ‖(archY A hA : ℂ)‖ = ‖A.det‖ / archDen A := by
  rw [archY, Units.val_mk0, norm_div, Complex.norm_of_nonneg (le_of_lt (archDen_pos A hA))]

private lemma archY_archX_left (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (archY A hA : ℂ) * (star (A 1 1) + archX A * A 1 0) = A 0 0 := by
  have hden : ((archDen A : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (archDen_pos A hA)
  rw [archY, archX, Units.val_mk0]
  field_simp
  rw [Matrix.det_fin_two, Complex.star_def]
  ring_nf
  rw [mul_assoc, Complex.mul_conj', mul_assoc, Complex.mul_conj']
  rw [← mul_add, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
  rw [show ‖A 1 1‖ ^ 2 + ‖A 1 0‖ ^ 2 = archDen A by unfold archDen; ring]

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
open scoped Matrix

private lemma archY_archX_right (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (archY A hA : ℂ) * (-star (A 1 0) + archX A * A 1 1) = A 0 1 := by
  have hden : ((archDen A : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (archDen_pos A hA)
  rw [archY, archX, Units.val_mk0]
  field_simp
  rw [Matrix.det_fin_two, Complex.star_def]
  ring_nf
  rw [mul_comm (A 1 1) (A 0 1), mul_assoc, mul_assoc, Complex.mul_conj',
    Complex.mul_conj']
  rw [← mul_add, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
  rw [show ‖A 1 1‖ ^ 2 + ‖A 1 0‖ ^ 2 = archDen A by unfold archDen; ring]

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
open scoped Matrix

private lemma arch_matrix_identity (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (KubotaRankTwo.d ℂ (archY A hA) 1 : Matrix (Fin 2) (Fin 2) ℂ) *
      (KubotaRankTwo.n ℂ (archX A) : Matrix (Fin 2) (Fin 2) ℂ) * archK A =
      Matrix.scalar (Fin 2) (((archS A : ℝ) : ℂ)⁻¹) * A := by
  have hspos : 0 < archS A := archS_pos A hA
  have hs : ((archS A : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hspos
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [archK, KubotaRankTwo.d, KubotaRankTwo.n, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  · rw [← archY_archX_left A hA]; field_simp; rw [Complex.star_def]
  · rw [← archY_archX_right A hA]; field_simp; rw [Complex.star_def]
  · field_simp
  · field_simp

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
open scoped Matrix
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archimedean_factorization
    (a : PGLComplex.AdelicSlicesRaw.ArchGroup F) :
    ∃ (y : InfinitePlace F → ℂˣ)
      (x : KPGlobalTorusFunctionData.Adeles F)
      (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2),
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a =
        (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
          KPGlobalTorusFunctionData.N F ζ hζ x) *
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk
            (KPCplxCharacterHaar.complexSU2Embedding (u w))) ∧
      ∀ w : InfinitePlace F, ‖(y w : ℂ)‖ =
        ‖((a w).out : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖(a w).out 1 0‖ ^ 2 + ‖(a w).out 1 1‖ ^ 2) := by
  classical
  let Aw : InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ :=
    fun w => ((a w).out : Matrix (Fin 2) (Fin 2) ℂ)
  have hAw : ∀ w, (Aw w).det ≠ 0 :=
    fun w => Matrix.GeneralLinearGroup.det_ne_zero (a w).out
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  have hhom (g h : PGLComplex.AdelicSlicesRaw.ArchGroup F) :
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (g * h) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ g *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ h := by
    change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ =
      RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ * RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
    rw [← hih, ← hih, ← hih]
    exact map_mul ih g h
  refine ⟨fun w => archY (Aw w) (hAw w),
    adeleOfArch F ζ hζ (fun w => archX (Aw w)),
    fun w => ⟨archK (Aw w), archK_mem (Aw w) (hAw w)⟩, ?_, ?_⟩
  · have key : (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
          (fun w => (archY (Aw w) (hAw w) : ℂ)) *
        KPGlobalTorusFunctionData.N F ζ hζ (adeleOfArch F ζ hζ (fun w => archX (Aw w)))) *
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk
            (KPCplxCharacterHaar.complexSU2Embedding
              (⟨archK (Aw w), archK_mem (Aw w) (hAw w)⟩))) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a := by
      rw [archDiagonalLift_eq_insertion F ζ hζ (fun w => archY (Aw w) (hAw w)),
        N_eq_insertion F ζ hζ (fun w => archX (Aw w))]
      rw [← hhom, ← hhom]
      congr 1
      funext w
      simp only [Pi.mul_apply]
      rw [← map_mul, ← map_mul]
      have hGL : (KubotaRankTwo.d ℂ (archY (Aw w) (hAw w)) 1 *
            KubotaRankTwo.n ℂ (archX (Aw w)) *
            KPCplxCharacterHaar.complexSU2Embedding
              (⟨archK (Aw w), archK_mem (Aw w) (hAw w)⟩)) =
          Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.mk0 (((archS (Aw w) : ℝ) : ℂ)⁻¹) (by
              simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
              exact ne_of_gt (archS_pos (Aw w) (hAw w)))) * (a w).out := by
        apply Units.ext
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
        exact arch_matrix_identity (Aw w) (hAw w)
      rw [hGL, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
      exact Quotient.out_eq (a w)
    exact key.symm
  · intro w
    rw [archY_norm]
    rfl

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
open scoped NumberField Classical Matrix
open NumberField
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 def diagonalUnit (x : ℂ) : ℂˣ := if h : x = 0 then 1 else Units.mk0 x h

def leftMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPStandardLocalRootLifts.lowerN ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KubotaRankTwo.n ℂ (x 2)

 def complexSectionHom (w : InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ →* KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) where
  toFun r := KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
    (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom r)
  map_one' := by simp [KPLocalCover.sectionMap]; rfl
  map_mul' := by
    intro r s
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · simp
    · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]

private theorem mapped_diagonalUnit (w : InfinitePlace F) (x : ℂ) :
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (diagonalUnit x) =
      (if h : x = 0 then (1 : (w.Completion)ˣ) else Units.mk0
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm x)
        (by
          intro hx
          apply h
          simpa using congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)) hx)) := by
  by_cases hx : x = 0
  · simp [diagonalUnit, hx]
  · simp only [diagonalUnit, hx, ↓reduceDIte]
    apply Units.ext; rfl

private theorem sectionTuple_left (x : KPGlobalTorusBorelNormTwistTransport.GroupArch F) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
          (sectionTuple F ζ hζ (fun w => leftMatrix (x w)))) =
      KPGlobalTorusBorelNormTwistTransport.groupArchChart F ζ hζ x := by
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change complexSectionHom F ζ hζ w (leftMatrix (x w)) = _
    simp only [leftMatrix, map_mul]
    congr 1
    · congr 1
      · simp [complexSectionHom, KPStandardLocalRootLifts.LowerN, KPLocalCover.sectionMap]
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, KPStandardLocalRootLifts.lowerN]
      · simp [complexSectionHom, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
        rw [← mapped_diagonalUnit F ζ hζ w (x w 1)]
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]
    · simp [complexSectionHom, KPStandardLocalRootLifts.N, KPLocalCover.sectionMap]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]

theorem groupArchChart_eq_archimedeanInsertion
    (x : KPGlobalTorusBorelNormTwistTransport.GroupArch F) :
    KPGlobalTorusBorelNormTwistTransport.groupArchChart F ζ hζ x =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (x w))) := by
  rw [← sectionTuple_left F ζ hζ, sectionTuple_insertion]

theorem leftMatrix_val (x : Fin 3 → ℂ) (hx : x 1 ≠ 0) :
    (leftMatrix x).val = !![x 1, x 1*x 2; x 0*x 1, 1+x 0*x 1*x 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMatrix, diagonalUnit, hx,
    KPStandardLocalRootLifts.lowerN, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.ArchRowFactorization
noncomputable section
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.NormContinuity
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct

theorem fullCusp_isClosed_ordinaryBorel :
    IsClosed (KPGlobalTorusFunctionData.ordinaryBorel F : Set (AdelicPGL2 F)) := by
  letI : IsTopologicalGroup (AdelicGL2 F) := inferInstance
  rw [← (QuotientGroup.isQuotientMap_mk (scalarSubgroup F)).isClosed_preimage]
  have he : (QuotientGroup.mk (s := scalarSubgroup F)) ⁻¹'
      (KPGlobalTorusFunctionData.ordinaryBorel F : Set (AdelicPGL2 F)) =
      {A : AdelicGL2 F | A 1 0 = 0} := by
    ext A
    constructor
    · rintro ⟨B,hB,h10⟩
      have hm := QuotientGroup.eq.mp hB
      obtain ⟨z,hz⟩ := hm
      have he : A = B * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
        change Matrix.GeneralLinearGroup.scalar (Fin 2) z = B⁻¹ * A at hz
        rw [hz]
        group
      rw [he]
      simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.scalar, h10]
    · intro h
      exact ⟨A,rfl,h⟩
  rw [he]
  exact isClosed_eq (by fun_prop) continuous_const
theorem fullCusp_isClosed_borel :
    IsClosed (KPGlobalTorusFunctionData.borel F ζ hζ : Set (KPGlobalTorusFunctionData.G F ζ hζ)) := by
  exact (fullCusp_isClosed_ordinaryBorel F).preimage
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

theorem fullCusp_iwasawaNorm_continuous_of_borel
    (D : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ)
    (hcont : ContinuousOn (fun g =>
      (((KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))
      (KPGlobalTorusFunctionData.borel F ζ hζ : Set _)) :
    Continuous (fun g =>
      (((KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))) := by
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let raw : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ :=
    { K := D.K, compact := D.compact, decomposition := D.decomposition, overlap := D.overlap }
  apply DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.continuous_of_closed_compact_factor (fullCusp_isClosed_borel F ζ hζ) D.compact
  · intro g
    obtain ⟨t,x,k,hg⟩ := D.decomposition g
    refine ⟨t.val * KPGlobalTorusFunctionData.N F ζ hζ x, ?_, k.val, k.property, hg⟩
    have ht : t.val ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
      obtain ⟨A,hA,h10,h01⟩ := t.property
      exact ⟨A,hA,h10⟩
    apply Subgroup.mul_mem _ ht
    refine ⟨KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalTorusFunctionData.rootTuple F ζ hζ x), rfl, ?_⟩
    apply Prod.ext
    · funext w
      simp [KPAdelicCoverRestrictedProduct.restrictedProjection,
        KPAdelicCoverRestrictedProduct.matrixValue, KPAdelicCoverRestrictedProduct.matrixEntry,
        KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N]
      rfl
    · apply RestrictedProduct.ext
      intro q
      simp [KPAdelicCoverRestrictedProduct.restrictedProjection,
        KPAdelicCoverRestrictedProduct.matrixValue, KPAdelicCoverRestrictedProduct.matrixEntry,
        KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N]
      rfl
  · intro b hb k hk
    obtain ⟨t,x,hb⟩ := KPGlobalTorusBorelNormTwistTransport.actual_borel_factorization F ζ hζ ⟨b,hb⟩
    change b = t.val * KPGlobalTorusFunctionData.N F ζ hζ x at hb
    rw [hb]
    have hk' := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_formula F ζ hζ raw t x ⟨k,hk⟩
    have h1 := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_formula F ζ hζ raw t x 1
    simp only [OneMemClass.coe_one, mul_one] at h1
    change KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x * k) = _ at hk'
    change KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) = _ at h1
    rw [hk',h1]
  · exact hcont

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.NormContinuity

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.NormContinuity
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct
open KPGlobalTorusBorelNormTwistTransport

private theorem upperRatio_det (A : AdelicGL2 F) (h : A 1 0 = 0) :
    iwasawaUpperRatio F A h = (iwasawaUpperUnits F A h).1.unit ^ 2 * (Matrix.GeneralLinearGroup.det A)⁻¹ ∧
    (iwasawaUpperRatio F A h)⁻¹ = (iwasawaUpperUnits F A h).2.unit ^ 2 * (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  have hd : Matrix.GeneralLinearGroup.det A =
      (iwasawaUpperUnits F A h).1.unit * (iwasawaUpperUnits F A h).2.unit := by
    apply Units.ext
    change (A : Matrix (Fin 2) (Fin 2) (Adeles F)).det = _
    simp [Matrix.det_fin_two, h, IsUnit.unit_spec]
  rw [hd]
  unfold iwasawaUpperRatio
  constructor <;> simp [pow_two, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

private theorem upperRatio_continuous :
    Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} => iwasawaUpperRatio F A.val A.property) := by
  apply Units.continuous_iff.mpr
  have hc (i j : Fin 2) : Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} => A.val i j) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hd : Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} =>
      ((Matrix.GeneralLinearGroup.det A.val)⁻¹ : (Adeles F)ˣ).val) := by
    exact Units.continuous_coe_inv.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  constructor
  · have he : (fun A : {A : AdelicGL2 F | A 1 0 = 0} =>
        (iwasawaUpperRatio F A.val A.property).val) =
        fun A => (A.val 0 0)^2 * ((Matrix.GeneralLinearGroup.det A.val)⁻¹ : (Adeles F)ˣ).val := by
      funext A
      rw [(upperRatio_det F A.val A.property).1]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    change Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} => (iwasawaUpperRatio F A.val A.property).val)
    rw [he]
    exact (hc 0 0).pow 2 |>.mul hd
  · have he : (fun A : {A : AdelicGL2 F | A 1 0 = 0} =>
        ((iwasawaUpperRatio F A.val A.property)⁻¹).val) =
        fun A => (A.val 1 1)^2 * ((Matrix.GeneralLinearGroup.det A.val)⁻¹ : (Adeles F)ˣ).val := by
      funext A
      rw [(upperRatio_det F A.val A.property).2]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [he]
    exact (hc 1 1).pow 2 |>.mul hd

 def ordinaryUpperRatio (b : KPGlobalTorusFunctionData.ordinaryBorel F) : (Adeles F)ˣ :=
  iwasawaUpperRatio F (Classical.choose b.property) (Classical.choose_spec b.property).2

private theorem ordinaryUpperRatio_formula (b : KPGlobalTorusFunctionData.ordinaryBorel F)
    (A : AdelicGL2 F) (hA : QuotientGroup.mk' (scalarSubgroup F) A = b.val) (h : A 1 0 = 0) :
    ordinaryUpperRatio F b = iwasawaUpperRatio F A h := by
  apply iwasawaUpperRatio_scalar
  exact (Classical.choose_spec b.property).1.trans hA.symm

private theorem upper_preimage_zero (A : AdelicGL2 F)
    (h : QuotientGroup.mk' (scalarSubgroup F) A ∈ KPGlobalTorusFunctionData.ordinaryBorel F) :
    A 1 0 = 0 := by
  obtain ⟨B,hB,h10⟩ := h
  have hm := QuotientGroup.eq.mp hB
  obtain ⟨z,hz⟩ := hm
  have he : A = B * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = B⁻¹ * A at hz
    rw [hz]; group
  rw [he]
  simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, h10]

private theorem ordinaryUpperRatio_continuous : Continuous (ordinaryUpperRatio F) := by
  let q : AdelicGL2 F → AdelicPGL2 F := QuotientGroup.mk' (scalarSubgroup F)
  let S : Set (AdelicPGL2 F) := KPGlobalTorusFunctionData.ordinaryBorel F
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk (N := scalarSubgroup F)
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u : (q ⁻¹' S) → {A : AdelicGL2 F | A 1 0 = 0} :=
    fun A => ⟨A.val, upper_preimage_zero F A.val A.property⟩
  have he : (ordinaryUpperRatio F) ∘ S.restrictPreimage q =
      (fun A : {A : AdelicGL2 F | A 1 0 = 0} => iwasawaUpperRatio F A.val A.property) ∘ u := by
    funext A
    exact ordinaryUpperRatio_formula F _ _ rfl (u A).property
  rw [he]
  exact (upperRatio_continuous F).comp (continuous_subtype_val.subtype_mk _)

private theorem fullCusp_ideleAbs_continuous : Continuous (KPGlobalTorusFunctionData.ideleAbs F) := by
  have hfinite : Continuous (FiniteIdeleGroup.absoluteNorm (K := F)) := by
    apply continuous_of_continuousAt_one
    apply (continuousAt_const (y := (1 : ℝ≥0ˣ))).congr_of_eventuallyEq
    have ho : IsOpen (FiniteIdeleGroup.integralSubgroup (K := F) : Set (FiniteIdeleGroup F)) := by
      simpa only [Finset.coe_empty, FiniteIdeleGroup.supportedAt_empty] using
        (FiniteIdeleGroup.isOpen_supportedAt (K := F) ∅)
    filter_upwards [ho.mem_nhds (Subgroup.one_mem _)] with a ha
    exact IdeleGroup.finite_absoluteNorm_eq_one_of_integral a ha
  have hidele : Continuous (IdeleGroup.absoluteNorm (K := F)) :=
    (hfinite.comp continuous_snd).mul
      ((InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst).inv)
  exact (hidele.comp (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm.continuous).inv

theorem fullCusp_iwasawaNorm_continuousOn_borel
    (D : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ) :
    ContinuousOn (fun g =>
      (((KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))
      (KPGlobalTorusFunctionData.borel F ζ hζ : Set _) := by
  apply continuousOn_iff_continuous_restrict.mpr
  let proj : KPGlobalTorusFunctionData.borel F ζ hζ → KPGlobalTorusFunctionData.ordinaryBorel F :=
    fun b => ⟨pglProjection F ζ hζ b.val, b.property⟩
  have hp : Continuous proj :=
    ((adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
      continuous_subtype_val).subtype_mk _
  have he : (KPGlobalTorusFunctionData.borel F ζ hζ : Set _).domRestrict (fun g =>
      (((KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))) =
      fun b => (((KPGlobalTorusFunctionData.ideleAbs F (ordinaryUpperRatio F (proj b)) : ℝ≥0) : ℝ)) := by
    funext b
    obtain ⟨t,x,hb⟩ := actual_borel_factorization F ζ hζ b
    obtain ⟨B,hB,h10⟩ := b.property
    have hr := iwasawaUpperRatio_torus_root F ζ hζ t x B h10 (hB.trans (congrArg (pglProjection F ζ hζ) hb))
    have hf := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_formula F ζ hζ D t x 1
    simp only [OneMemClass.coe_one, mul_one] at hf
    change (((KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D b.val : ℝ≥0) : ℝ)) = _
    rw [hb, hf, ordinaryUpperRatio_formula F (proj b) B hB h10, hr]
    rfl
  rw [he]
  exact NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((fullCusp_ideleAbs_continuous F).comp ((ordinaryUpperRatio_continuous F).comp hp)))

theorem fullCusp_iwasawaNorm_continuous
    (D : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ) :
    Continuous (fun g =>
      (((KPGlobalTorusBorelNormTwistTransport.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))) :=
  fullCusp_iwasawaNorm_continuous_of_borel F ζ hζ D
    (fullCusp_iwasawaNorm_continuousOn_borel F ζ hζ D)

end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.NormContinuity
open scoped NumberField Classical NNReal BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusBorelNormTwistTransport
abbrev ArchCompact := InfinitePlace F → KPCplxCharacterHaar.ComplexSU2
 local instance su_compact : CompactSpace KPCplxCharacterHaar.ComplexSU2 := by
  apply isCompact_iff_compactSpace.mp
  exact (show IsCompact (KPCplxCharacterHaar.ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) from by
    convert KPCplxCharacterHaar.complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
 local instance su_group : IsTopologicalGroup KPCplxCharacterHaar.ComplexSU2 where
  continuous_mul := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
  continuous_inv := (continuous_star.comp continuous_subtype_val).subtype_mk _
 local instance archCompactMeas : MeasurableSpace (ArchCompact F) := borel _
 local instance archCompactBorel : BorelSpace (ArchCompact F) := ⟨rfl⟩
 local instance coverGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

def compactInsert (k : ArchCompact F) : G F ζ hζ :=
  PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (k w)))

lemma compactInsert_continuous : Continuous (compactInsert F ζ hζ) := by
  apply (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).1.comp
  apply continuous_pi
  intro w
  apply QuotientGroup.continuous_mk.comp
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val.comp (continuous_apply w)
  · rw [show (fun k : ArchCompact F => (KPCplxCharacterHaar.complexSU2Embedding (k w))⁻¹.val) =
      (fun k => (k w)⁻¹.val) by funext k; rw [← map_inv]; rfl]
    exact continuous_subtype_val.comp ((continuous_apply w).inv)

lemma compactInsert_mul (k l : ArchCompact F) :
    compactInsert F ζ hζ (k * l) = compactInsert F ζ hζ k * compactInsert F ζ hζ l := by
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  unfold compactInsert
  change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ =
    RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ * RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
  rw [← hih, ← hih, ← hih, ← map_mul]
  congr 1
  funext w
  simp only [Pi.mul_apply, map_mul]

def firstAverage (D : IwasawaData F ζ hζ) (g : G F ζ hζ) : ℝ :=
  ∫ k : ArchCompact F,
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) ∂Measure.haar

lemma firstAverage_compactInsert (D : IwasawaData F ζ hζ) (g : G F ζ hζ)
    (k : ArchCompact F) :
    firstAverage F ζ hζ D (g * compactInsert F ζ hζ k) = firstAverage F ζ hζ D g := by
  unfold firstAverage
  have he : (fun l : ArchCompact F =>
    (((iwasawaNorm F ζ hζ D ((g * compactInsert F ζ hζ k) * compactInsert F ζ hζ l) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)) =
    (fun l : ArchCompact F =>
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ (k * l)) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)) := by
    funext l
    rw [compactInsert_mul, mul_assoc]
  rw [he]
  exact integral_mul_left_eq_self (μ := (Measure.haar : Measure (ArchCompact F))) (fun l : ArchCompact F => (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ l) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)) k

lemma firstAverage_borel (D : IwasawaData F ζ hζ) (t : E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    firstAverage F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) *
        firstAverage F ζ hζ D g := by
  unfold firstAverage
  have he : ∀ k : ArchCompact F,
    (((iwasawaNorm F ζ hζ D (((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) =
    (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) *
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2) := by
    intro k
    rw [mul_assoc, iwasawaNorm_borel_mul, Units.val_mul, NNReal.coe_mul]
    simp only [Real.rpow_eq_pow]
    apply Real.mul_rpow
    all_goals positivity
  simp_rw [he]
  rw [integral_const_mul]

lemma firstAverage_pos (D : IwasawaData F ζ hζ) (g : G F ζ hζ)
    (hcont : Continuous (fun g => (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))) :
    0 < firstAverage F ζ hζ D g := by
  let v (k : ArchCompact F) : ℝ :=
    (((iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k) : ℝ≥0) : ℝ)).rpow (-(1:ℝ)/2)
  have hp (k : ArchCompact F) : 0 < v k := by
    dsimp only [v]
    simp only [Real.rpow_eq_pow]
    apply Real.rpow_pos_of_pos
    exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero _)
  have hc : Continuous v := by
    dsimp only [v]
    simp only [Real.rpow_eq_pow]
    apply Continuous.rpow_const
    · exact hcont.comp (continuous_const.mul (compactInsert_continuous F ζ hζ))
    · intro k
      left
      exact_mod_cast (Units.ne_zero (iwasawaNorm F ζ hζ D (g * compactInsert F ζ hζ k)))
  apply (integral_pos_iff_support_of_nonneg
    (μ := (Measure.haar : Measure (ArchCompact F))) (fun k => (hp k).le)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have he : Function.support v = Set.univ := by
    ext k
    simp [Function.mem_support, ne_of_gt (hp k)]
  rw [he]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

lemma firstAverage_continuous (D : IwasawaData F ζ hζ)
    (hcont : Continuous (fun g => (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))) :
    Continuous (firstAverage F ζ hζ D) := by
  letI : SecondCountableTopology (G F ζ hζ) := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : LocallyCompactSpace (G F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  unfold firstAverage
  simp only [Real.rpow_eq_pow]
  have hc : Continuous (fun p : G F ζ hζ × ArchCompact F =>
      (((iwasawaNorm F ζ hζ D (p.1 * compactInsert F ζ hζ p.2) : ℝ≥0) : ℝ)) ^ (-(1:ℝ)/2)) := by
    apply Continuous.rpow_const
    · exact hcont.comp (continuous_fst.mul ((compactInsert_continuous F ζ hζ).comp continuous_snd))
    · intro p
      left
      exact_mod_cast (Units.ne_zero (iwasawaNorm F ζ hζ D (p.1 * compactInsert F ζ hζ p.2)))
  simpa using continuous_parametric_integral_of_continuous
    (μ := (Measure.haar : Measure (ArchCompact F))) hc isCompact_univ

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage
open scoped NumberField Classical NNReal BigOperators ComplexConjugate
open NumberField MeasureTheory
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusBorelNormTwistTransport
open ArchRowFactorization ProjectiveAverage
 local instance coverGroup' : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

def finiteComponent (g : G F ζ hζ) : G F ζ hζ :=
  (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g))⁻¹ * g

lemma finiteComponent_raw (g : G F ζ hζ) :
    finiteComponent F ζ hζ g ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
  apply RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (finiteComponent F ζ hζ g) = 1
  unfold finiteComponent
  rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  simp

lemma finiteComponent_continuous : Continuous (finiteComponent F ζ hζ) := by
  unfold finiteComponent
  have hc := RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ
  exact ((hc.1.comp hc.2).inv).mul continuous_id

lemma firstAverage_factorization (D : IwasawaData F ζ hζ) (g : G F ζ hζ) :
    firstAverage F ζ hζ D g =
      (∏ w : InfinitePlace F, projectiveRowWeight (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w)) *
        firstAverage F ζ hζ D (finiteComponent F ζ hζ g) := by
  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  obtain ⟨y, x, u, hfac, hy⟩ := archimedean_factorization F ζ hζ a
  let k := compactInsert F ζ hζ u
  have hc : Commute k (finiteComponent F ζ hζ g) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _
      ⟨_, finiteComponent_raw F ζ hζ g⟩
  have hg : g = ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
      KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) * k := by
    calc g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * finiteComponent F ζ hζ g := by
              dsimp [a, finiteComponent]; group
         _ = _ := by rw [hfac]; dsimp [k, compactInsert] at hc ⊢; rw [mul_assoc, hc.eq, ← mul_assoc]
  conv_lhs => rw [hg, firstAverage_compactInsert]
  have hb := firstAverage_borel F ζ hζ D
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (y w : ℂ))) x (finiteComponent F ζ hζ g)
  change firstAverage F ζ hζ D ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
    KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) = _ at hb
  rw [hb]
  congr 1
  rw [AnalyticInputs.delta_chart_formula F ζ hζ _ (fun w => (y w).ne_zero)]
  simp only [Real.rpow_eq_pow]
  rw [← Real.finsetProd_rpow _ _ (fun w _ => sq_nonneg ‖(y w : ℂ)‖)]
  apply Finset.prod_congr rfl
  intro w _
  have hn : (‖(y w : ℂ)‖ ^ 2 : ℝ) ^ (-(1:ℝ)/2) = ‖(y w : ℂ)‖⁻¹ := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hn, hy w]
  have he : projectiveRowWeight (a w) =
      (‖(a w).out 1 0‖ ^ 2 + ‖(a w).out 1 1‖ ^ 2) / ‖((a w).out.val).det‖ := by
    have hh := projectiveRowWeight_mk (a w).out
    rw [show Matrix.ProjGenLinGroup.mk (a w).out = a w from Quotient.out_eq _] at hh
    exact hh
  rw [he, inv_div]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage
open scoped NumberField Classical NNReal BigOperators ComplexConjugate
open NumberField MeasureTheory
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusBorelNormTwistTransport
open ArchRowFactorization ProjectiveAverage
 local instance coverGroup'' : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

lemma finiteComponent_groupChart (g : G F ζ hζ) (z : GroupArch F) :
    finiteComponent F ζ hζ (groupArchChart F ζ hζ z * g) = finiteComponent F ζ hζ g := by
  obtain ⟨ih, hih⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  have hmult (u v : PGLComplex.AdelicSlicesRaw.ArchGroup F) :
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (u * v) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ u *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ v := by
    change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ =
      RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _ * RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ _
    rw [← hih, ← hih, ← hih]
    exact map_mul ih u v
  have hχ := groupArchChart_eq_archimedeanInsertion F ζ hζ z
  have hp : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (groupArchChart F ζ hζ z) =
      (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))) := by
    rw [hχ, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  unfold finiteComponent
  rw [map_mul, hp, hχ, hmult]
  group

 local instance compactD (D : IwasawaData F ζ hζ) : CompactSpace D.K :=
  isCompact_iff_compactSpace.mp D.compact
 local instance measurableD (D : IwasawaData F ζ hζ) : MeasurableSpace D.K := borel _
 local instance borelD (D : IwasawaData F ζ hζ) : BorelSpace D.K := ⟨rfl⟩

lemma secondAverage_smooth (D : IwasawaData F ζ hζ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ∫ k : D.K, firstAverage F ζ hζ D ((groupArchChart F ζ hζ z * g) * k.val) ∂Measure.haar)
      (groupArchDomain F) := by
  have hn := NormContinuity.fullCusp_iwasawaNorm_continuous F ζ hζ D
  let B (k : D.K) (w : InfinitePlace F) :=
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (g * k.val) w
  let h (k : D.K) := firstAverage F ζ hζ D (finiteComponent F ζ hζ (g * k.val))
  let A (z : GroupArch F) (w : InfinitePlace F) := leftMatrix (z w)
  have hB (w : InfinitePlace F) : Continuous (fun k : D.K => B k w) :=
    (continuous_apply w).comp
      ((RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).2.comp
        (continuous_const.mul continuous_subtype_val))
  have hh : Continuous h :=
    (firstAverage_continuous F ζ hζ D hn).comp
      ((finiteComponent_continuous F ζ hζ).comp (continuous_const.mul continuous_subtype_val))
  have hA (w : InfinitePlace F) (p q : Fin 2) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : GroupArch F => A z w p q) (groupArchDomain F) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : GroupArch F =>
      (!![z w 1, z w 1 * z w 2; z w 0 * z w 1, 1 + z w 0 * z w 1 * z w 2]) p q) := by
      fin_cases p <;> fin_cases q <;> simp <;> fun_prop
    apply hs.contDiffOn.congr
    intro z hz
    dsimp [A]
    rw [leftMatrix_val _ (hz w)]
    rfl
  have hs := projective_compact_average_smooth (Measure.haar : Measure D.K) B h hB hh
    (groupArchDomain F) A hA
  apply hs.congr
  intro z hz
  apply integral_congr_ae
  filter_upwards [] with k
  rw [firstAverage_factorization, mul_assoc, finiteComponent_groupChart]
  rw [mul_comm (h k)]
  apply congrArg (fun r : ℝ => r * h k)
  apply Finset.prod_congr rfl
  intro w _
  rw [groupArchChart_eq_archimedeanInsertion, map_mul,
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  rfl

open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport renaming iwasawa_compactAverage_normalization → iwasawa_compactAverage_normalization
open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport renaming iwasawaNorm_pos → iwasawaNorm_pos

lemma genuine_weight_smooth (D : IwasawaData F ζ hζ) (s : ℂ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => iwasawaWeight F ζ hζ D s (groupArchChart F ζ hζ z * g))
      (groupArchDomain F) := by
  have hn := NormContinuity.fullCusp_iwasawaNorm_continuous F ζ hζ D
  have ha := iwasawa_compactAverage_normalization F ζ hζ D (-(1:ℝ)/2)
    (firstAverage F ζ hζ D) (firstAverage_continuous F ζ hζ D hn)
    (firstAverage_pos F ζ hζ D · hn) (firstAverage_borel F ζ hζ D)
  have hl := GramCoefficients.normalized_average_log_smooth (groupArchDomain F)
    (fun z => (((iwasawaNorm F ζ hζ D (groupArchChart F ζ hζ z * g) : ℝ≥0) : ℝ)))
    (fun z => ∫ k : D.K, firstAverage F ζ hζ D ((groupArchChart F ζ hζ z * g) * k.val) ∂Measure.haar)
    (∫ k : D.K, firstAverage F ζ hζ D k.val ∂Measure.haar)
    ha.1 (fun z _ => iwasawaNorm_pos F ζ hζ D _) (secondAverage_smooth F ζ hζ D g)
    (fun z _ => ha.2 _)
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hl)).cexp

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage

end
end
end
