module

public import DedekindZetaZeroFree.Eisenstein.Sections.ArchimedeanIwasawaNorm
public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteNormTranslationRange

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField

namespace DedekindZetaZeroFree.KPContFlatLogNormSmooth

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteComponent (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPGlobalTorusFunctionData.G F ζ hζ :=
  (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g))⁻¹ * g

private theorem finiteSubgroup_le_finitePart :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ ≤
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨y, ?_, hyx⟩
  rw [Subgroup.mem_iInf]
  intro w
  rw [MonoidHom.mem_ker, RestrictedProduct.evalMonoidHom_apply]
  exact hy w

theorem finiteComponent_mem (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    finiteComponent F ζ hζ g ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  apply finiteSubgroup_le_finitePart
  have hker : finiteComponent F ζ hζ g ∈ (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
    rw [MonoidHom.mem_ker]
    unfold finiteComponent
    rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    simp
  exact RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ hker

end DedekindZetaZeroFree.KPContFlatLogNormSmooth

end

section

noncomputable section
open scoped NumberField Classical BigOperators Matrix NNReal
open NumberField

namespace DedekindZetaZeroFree.KPContFlatLogNormSmooth

def complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.log ((‖A.det‖ / (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)) ^ 2)

private def ratio (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖A.det‖ / (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)

private lemma complexMatrixLogNorm_eq_ratio (A : Matrix (Fin 2) (Fin 2) ℂ) :
    complexMatrixLogNorm A = Real.log ((ratio A) ^ 2) := rfl

private lemma bottomRow_ne_zero_of_det_ne_zero (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.det ≠ 0) :
    A 1 0 ≠ 0 ∨ A 1 1 ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h0, h1⟩ := hc
  exact h (by rw [Matrix.det_fin_two]; simp [h0, h1])

private lemma ratio_denom_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.det ≠ 0) :
    0 < ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
  rcases bottomRow_ne_zero_of_det_ne_zero A h with h0 | h1
  · have : 0 < ‖A 1 0‖ := norm_pos_iff.mpr h0
    nlinarith [sq_nonneg ‖A 1 1‖, sq_nonneg ‖A 1 0‖]
  · have : 0 < ‖A 1 1‖ := norm_pos_iff.mpr h1
    nlinarith [sq_nonneg ‖A 1 1‖, sq_nonneg ‖A 1 0‖]

private lemma ratio_pos (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.det ≠ 0) : 0 < ratio A :=
  div_pos (norm_pos_iff.mpr h) (ratio_denom_pos A h)

theorem complexMatrixLogNorm_argument_pos
    (A : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    0 < (‖(A : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)) ^ 2 := by
  have h : (A : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  exact pow_pos (ratio_pos _ h) 2

private lemma ratio_scalar_mul (c : ℂ) (hc : c ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ratio (Matrix.scalar (Fin 2) c * A) = ratio A := by
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hent : ∀ i j, (Matrix.scalar (Fin 2) c * A) i j = c * A i j := by
    intro i j
    rw [Matrix.scalar_apply, Matrix.diagonal_mul]
  have hdet : (Matrix.scalar (Fin 2) c * A).det = c ^ 2 * A.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hent 0 0, hent 0 1, hent 1 0, hent 1 1]
    ring
  have hnum : ‖(Matrix.scalar (Fin 2) c * A).det‖ = ‖c‖ ^ 2 * ‖A.det‖ := by
    rw [hdet, norm_mul, norm_pow]
  have hden : ‖(Matrix.scalar (Fin 2) c * A) 1 0‖ ^ 2
      + ‖(Matrix.scalar (Fin 2) c * A) 1 1‖ ^ 2
      = ‖c‖ ^ 2 * (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
    rw [hent 1 0, hent 1 1, norm_mul, norm_mul]; ring
  unfold ratio
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hc2

private lemma ratio_mul_scalar (c : ℂ) (hc : c ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ratio (A * Matrix.scalar (Fin 2) c) = ratio A := by
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hent : ∀ i j, (A * Matrix.scalar (Fin 2) c) i j = A i j * c := by
    intro i j
    rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  have hdet : (A * Matrix.scalar (Fin 2) c).det = A.det * c ^ 2 := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hent 0 0, hent 0 1, hent 1 0, hent 1 1]
    ring
  have hnum : ‖(A * Matrix.scalar (Fin 2) c).det‖ = ‖A.det‖ * ‖c‖ ^ 2 := by
    rw [hdet, norm_mul, norm_pow]
  have hden : ‖(A * Matrix.scalar (Fin 2) c) 1 0‖ ^ 2
      + ‖(A * Matrix.scalar (Fin 2) c) 1 1‖ ^ 2
      = (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) * ‖c‖ ^ 2 := by
    rw [hent 1 0, hent 1 1, norm_mul, norm_mul]; ring
  unfold ratio
  rw [hnum, hden, mul_comm (‖A.det‖) (‖c‖ ^ 2),
    mul_comm (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) (‖c‖ ^ 2)]
  exact mul_div_mul_left _ _ hc2

theorem complexMatrixLogNorm_scalar
    (A : Matrix.GeneralLinearGroup (Fin 2) ℂ) (c : ℂˣ) :
    complexMatrixLogNorm
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * A :
        Matrix.GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * A :
        Matrix.GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.scalar (Fin 2) (c : ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
  rw [hcoe, complexMatrixLogNorm_eq_ratio, complexMatrixLogNorm_eq_ratio,
    ratio_scalar_mul _ (Units.ne_zero c) _]

theorem complexMatrixLogNorm_eq_of_mk_eq
    (A B : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) =
      complexMatrixLogNorm (B : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hcoe : (B : Matrix (Fin 2) (Fin 2) ℂ)
      = (A : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.scalar (Fin 2) (u : ℂ) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
  rw [hcoe, complexMatrixLogNorm_eq_ratio, complexMatrixLogNorm_eq_ratio,
    ratio_mul_scalar _ (Units.ne_zero u) _]

def complexProjectiveLogNorm (a : Matrix.ProjGenLinGroup (Fin 2) ℂ) : ℝ :=
  complexMatrixLogNorm (a.out : Matrix (Fin 2) (Fin 2) ℂ)

theorem complexProjectiveLogNorm_mk
    (A : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    complexProjectiveLogNorm (Matrix.ProjGenLinGroup.mk A) =
      complexMatrixLogNorm (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold complexProjectiveLogNorm
  exact complexMatrixLogNorm_eq_of_mk_eq _ _ (Quotient.out_eq _)

theorem complexMatrixLogNorm_contDiffOn :
    ContDiffOn ℝ ⊤ complexMatrixLogNorm
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by
  have hdet : ContDiff ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) := by
    have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det)
        = fun A => A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
      funext A; rw [Matrix.det_fin_two]
    rw [h]; fun_prop
  have hnum : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => ‖A.det‖)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} :=
    ContDiffOn.norm ℂ hdet.contDiffOn (fun A hA => hA)
  have hd0 : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by fun_prop
  have hd1 : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by fun_prop
  have hden : ContDiffOn ℝ ⊤
      (fun A : Matrix (Fin 2) (Fin 2) ℂ => ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} :=
    (ContDiffOn.norm_sq ℂ hd0).add (ContDiffOn.norm_sq ℂ hd1)
  have hden_ne : ∀ A ∈ {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0},
      ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 ≠ 0 :=
    fun A hA => ne_of_gt (ratio_denom_pos A hA)
  have hratio : ContDiffOn ℝ ⊤ (ratio)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := by
    unfold ratio
    exact hnum.div hden hden_ne
  have hsq : ContDiffOn ℝ ⊤ (fun A => (ratio A) ^ 2)
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} := hratio.pow 2
  have hpos : ∀ A ∈ {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0}, (ratio A) ^ 2 ≠ 0 :=
    fun A hA => pow_ne_zero 2 (ne_of_gt (ratio_pos A hA))
  have hlog := hsq.log hpos
  refine hlog.congr (fun A _ => ?_)
  exact complexMatrixLogNorm_eq_ratio A

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private def diagonalUnit (x : ℂ) : ℂˣ := if h : x = 0 then 1 else Units.mk0 x h

private def leftMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPStandardLocalRootLifts.lowerN ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KubotaRankTwo.n ℂ (x 2)

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

 theorem sectionTuple_insertion
    (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (sectionTuple F ζ hζ r)) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (r w)) := by
  rw [tuple_prod F ζ hζ (sectionTuple F ζ hζ r) (by intro q; rfl)]
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2 r |>.symm

private def complexSectionHom (w : InfinitePlace F) :
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

private theorem sectionTuple_left (x : KPGlobalTorusBorelTwistCompatibility.GroupArch F) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
          (sectionTuple F ζ hζ (fun w => leftMatrix (x w)))) =
      KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x := by
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

private theorem groupArchChart_eq_archimedeanInsertion
    (x : KPGlobalTorusBorelTwistCompatibility.GroupArch F) :
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ x =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (x w))) := by
  rw [← sectionTuple_left F ζ hζ, sectionTuple_insertion]

private theorem leftMatrix_val (x : Fin 3 → ℂ) (hx : x 1 ≠ 0) :
    (leftMatrix x).val = !![x 1, x 1*x 2; x 0*x 1, 1+x 0*x 1*x 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMatrix, diagonalUnit, hx,
    KPStandardLocalRootLifts.lowerN, Matrix.mul_apply, Fin.sum_univ_two]
  ring

def finiteLogNorm (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℝ :=
  KPContFlatFullProductIwasawa.alpha F ζ hζ (finiteComponent F ζ hζ g)

 lemma compact_insertion (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
  PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w))) ∈ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K := by
  rw [show PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ from rfl,
   (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  apply list_prod_mem
  intro k hk
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ w (u w)
private lemma finite_component_raw (g : KPGlobalTorusFunctionData.G F ζ hζ) :
  finiteComponent F ζ hζ g ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
  apply RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (finiteComponent F ζ hζ g) = 1
  unfold finiteComponent
  rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  simp

theorem alpha_eq_arch_sum_add_finite
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPContFlatFullProductIwasawa.alpha F ζ hζ g =
      (∑ w : InfinitePlace F, complexProjectiveLogNorm
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w)) +
      finiteLogNorm F ζ hζ g := by
  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  obtain ⟨y, x, u, hfac, hy⟩ := KPContFlatArchProjectionNorm.archimedean_factorization F ζ hζ a
  let k := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w)))
  have hk : k ∈ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K := compact_insertion F ζ hζ u
  have hc : Commute k (finiteComponent F ζ hζ g) :=
   RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _ ⟨_, finite_component_raw F ζ hζ g⟩
  have hg : g = ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) * KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) * k := by
   calc g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * finiteComponent F ζ hζ g := by
         dsimp [a, finiteComponent]; group
        _ = _ := by rw [hfac]; dsimp [k] at hc ⊢; rw [mul_assoc, hc.eq, ← mul_assoc]
  have hn := KPContFlatFullProductIwasawa.alpha_borel_mul F ζ hζ (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (y w : ℂ))) x (finiteComponent F ζ hζ g)
  change KPContFlatFullProductIwasawa.alpha F ζ hζ ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) * KPGlobalTorusFunctionData.N F ζ hζ x) * finiteComponent F ζ hζ g) = _ at hn
  rw [show KPContFlatFullProductIwasawa.alpha F ζ hζ g = _ from (congrArg (KPContFlatFullProductIwasawa.alpha F ζ hζ) hg).trans (KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ _ ⟨k, hk⟩), hn]
  congr 1
  have hdelta := KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ (fun w => (y w : ℂ)) (fun w => (y w).ne_zero)
  rw [hdelta]
  rw [Real.log_prod (fun w _ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (y w).ne_zero))]
  apply Finset.sum_congr rfl
  intro w _
  unfold complexProjectiveLogNorm complexMatrixLogNorm
  rw [hy w]

theorem finiteComponent_groupArchChart_mul
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
    (hz : z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
    finiteComponent F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      finiteComponent F ζ hζ g := by
  have hmult : ∀ (u v : PGLComplex.AdelicSlicesRaw.ArchGroup F),
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (u * v) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ u *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ v :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  have hχ : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))) :=
    groupArchChart_eq_archimedeanInsertion F ζ hζ z
  have hprojχ : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z) =
      fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w)) := by
    rw [hχ, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  unfold finiteComponent
  rw [map_mul (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ), hprojχ, hχ,
    hmult (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w)))
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g)]
  group

theorem alpha_groupArchChart_mul_matrix_formula
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (S : Set (KPGlobalTorusBorelTwistCompatibility.GroupArch F))
    (hS : S ⊆ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)
    (A : InfinitePlace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F →
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hA : ∀ z ∈ S, ∀ w : InfinitePlace F,
      Matrix.ProjGenLinGroup.mk (A w z) =
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) w) :
    ∀ z ∈ S,
      KPContFlatFullProductIwasawa.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      (∑ w : InfinitePlace F,
        Real.log ((‖(A w z : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖A w z 1 0‖ ^ 2 + ‖A w z 1 1‖ ^ 2)) ^ 2)) +
        finiteLogNorm F ζ hζ g := by
  intro z hz
  rw [alpha_eq_arch_sum_add_finite F ζ hζ]
  have h1 : (∑ w : InfinitePlace F, complexProjectiveLogNorm
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) w)) =
      ∑ w : InfinitePlace F,
        Real.log ((‖(A w z : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖A w z 1 0‖ ^ 2 + ‖A w z 1 1‖ ^ 2)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro w _
    rw [← hA z hz w]
    exact complexProjectiveLogNorm_mk (A w z)
  have h2 : finiteLogNorm F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      finiteLogNorm F ζ hζ g := by
    unfold finiteLogNorm
    rw [finiteComponent_groupArchChart_mul F ζ hζ g z (hS hz)]
  rw [h1, h2]

theorem alpha_continuous :
    Continuous (KPContFlatFullProductIwasawa.alpha F ζ hζ) := by
  have h := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous
    F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ)
  exact h.log (fun g => NNReal.coe_ne_zero.mpr (Units.ne_zero _))

set_option maxHeartbeats 800000 in

theorem alpha_groupArchChart_mul_contDiffOn
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ ⊤
      (fun z => KPContFlatFullProductIwasawa.alpha F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  let R : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun w => (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w).out
  let A : InfinitePlace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F →
      Matrix.GeneralLinearGroup (Fin 2) ℂ := fun w z => leftMatrix (z w) * R w
  let B : InfinitePlace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F →
      Matrix (Fin 2) (Fin 2) ℂ := fun w z =>
    !![z w 1, z w 1 * z w 2; z w 0 * z w 1, 1 + z w 0 * z w 1 * z w 2] *
      (R w : Matrix (Fin 2) (Fin 2) ℂ)
  have hBA : ∀ w z, z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F →
      B w z = (A w z : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro w z hz
    dsimp [B, A]
    rw [leftMatrix_val _ (hz w)]
  have hA : ∀ z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F,
      ∀ w : InfinitePlace F, Matrix.ProjGenLinGroup.mk (A w z) =
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) w := by
    intro z hz w
    have hχ : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (leftMatrix (z w))) :=
      groupArchChart_eq_archimedeanInsertion F ζ hζ z
    rw [hχ, map_mul (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ),
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    dsimp [A, R]
    rw [map_mul]
    congr 1
    exact Quotient.out_eq _
  have hB : ∀ w, ContDiff ℝ ⊤ (B w) := by
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> fun_prop
  have hlocal : ∀ w, ContDiffOn ℝ ⊤ (fun z => complexMatrixLogNorm (B w z))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    intro w
    apply complexMatrixLogNorm_contDiffOn.comp (hB w).contDiffOn
    intro z hz
    rw [Set.mem_setOf_eq, hBA w z hz]
    exact Matrix.GeneralLinearGroup.det_ne_zero (A w z)
  have hsum : ContDiffOn ℝ ⊤ (fun z =>
      (∑ w : InfinitePlace F, complexMatrixLogNorm (B w z)) + finiteLogNorm F ζ hζ g)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
    (ContDiffOn.sum (fun w _ => hlocal w)).add contDiffOn_const
  apply hsum.congr
  intro z hz
  have h := alpha_groupArchChart_mul_matrix_formula F ζ hζ g
    (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) (fun _ h => h) A hA z hz
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [hBA w z hz]
  rfl

end DedekindZetaZeroFree.KPContFlatLogNormSmooth

end
end
