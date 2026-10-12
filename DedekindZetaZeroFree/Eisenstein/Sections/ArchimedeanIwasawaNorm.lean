module

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix
open NumberField
namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
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
  exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2 r |>.symm

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

 theorem archDiagonalLift_eq_insertion (u : InfinitePlace F → ℂˣ) :
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

 theorem N_eq_insertion (c : InfinitePlace F → ℂ) :
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

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
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

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
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

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
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

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

namespace DedekindZetaZeroFree.KPContFlatArchProjectionNorm
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
  have hhom : ∀ g h : PGLComplex.AdelicSlicesRaw.ArchGroup F,
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (g * h) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ g *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ h :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
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

end DedekindZetaZeroFree.KPContFlatArchProjectionNorm

end
