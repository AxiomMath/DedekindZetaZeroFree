module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.PrincipalExteriorCharacter
public import DedekindZetaZeroFree.Adeles.Characters.PrincipalFiniteTrace

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.PrincipalData

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

private lemma norm_mulChar_unit {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (u : Rˣ) : ‖χ u‖ = 1 := by
  change ‖((MulChar.equivToUnitHom χ) u : ℂ)‖ = 1
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

private lemma norm_mulChar {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (x : R) : ‖χ x‖ ^ 2 = if IsUnit x then 1 else 0 := by
  split_ifs with hx
  · rw [← hx.unit_spec, norm_mulChar_unit]; norm_num
  · rw [χ.map_nonunit hx]; norm_num

private lemma gauss_parseval {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ∑ a : R, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 =
      (Fintype.card R : ℝ) * ∑ x : R, ‖χ x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]

  have hnormC (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  simp only [Complex.ofReal_pow]
  simp_rw [← Complex.ofReal_pow, hnormC, gaussSum, star_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  have hterm (a y : R) :
      χ x * ψ.mulShift a x * star (χ y * ψ.mulShift a y) =
        (χ x * star (χ y)) * ψ (a * (x - y)) := by
    rw [star_mul, AddChar.mulShift_apply, AddChar.mulShift_apply,
      ← starRingEnd_apply, ← AddChar.map_neg_eq_conj]
    rw [show a * (x - y) = a * x + -(a * y) by ring, ψ.map_add_eq_mul]
    ring
  simp_rw [hterm, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
  simp only [sub_eq_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

theorem norm_gauss_le_sqrt_card {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ≤ Real.sqrt (Fintype.card R) := by
  classical
  have hshift (u : Rˣ) : ‖gaussSum χ (ψ.mulShift u)‖ = ‖gaussSum χ ψ‖ := by
    have h := congrArg norm (gaussSum_mulShift χ ψ u)
    simpa only [norm_mul, norm_mulChar_unit, one_mul] using h
  have hsub : (∑ u : Rˣ, ‖gaussSum χ (ψ.mulShift u)‖ ^ 2) ≤
      ∑ a : R, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun a : R => ‖gaussSum χ (ψ.mulShift a)‖ ^ 2)
      (g := fun u : Rˣ => (u : R)) (by intro a _ b _ h; exact Units.ext h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (by intros; positivity)
  have hmask : (∑ x : R, ‖χ x‖ ^ 2) = (Fintype.card Rˣ : ℝ) := by
    simp_rw [norm_mulChar]
    have h := MulChar.sum_one_eq_card_units (R := R) (R' := ℝ)
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with hx
    · exact (MulChar.one_apply hx).symm
    · exact (MulChar.map_nonunit _ hx).symm
  simp_rw [hshift] at hsub
  rw [gauss_parseval χ ψ hψ, hmask] at hsub
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsub
  have hu : (0 : ℝ) < Fintype.card Rˣ := by exact_mod_cast Fintype.card_pos
  have hs : ‖gaussSum χ ψ‖ ^ 2 ≤ (Fintype.card R : ℝ) := by
    nlinarith
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hs

theorem norm_idealGauss_le_one (A : SArithmeticData F) (ι : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior)
    (a : A.R) (ha : A.Generates I a) (j : ℤ) :
    ‖A.idealGauss ι hS I a ha j‖ ≤ 1 := by
  letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
  let ψ : AddChar (A.R ⧸ A.extendIdeal I) ℂ :=
    Circle.coeHom.compAddChar (A.residueTraceCharacter hS I a ha)
  have hprim : (A.residueTraceCharacter hS I a ha).IsPrimitive := by
    intro x hx heq
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxI : x ∉ A.extendIdeal I := by
      intro hm
      exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
    obtain ⟨y, hy⟩ := ResidueTraceFactorProductFormula.principalResidue_separation
      ResidueTrace.baseEmbedding
      (fun v => (ResidueTrace.baseEmbedding_spec v).1)
      (fun v => (ResidueTrace.baseEmbedding_spec v).2) A hS I a ha x hxI
    have h := congrArg (fun χ : AddChar (A.R ⧸ A.extendIdeal I) Circle =>
      χ (Ideal.Quotient.mk (A.extendIdeal I) y)) heq
    rw [AddChar.mulShift_apply, ← map_mul, A.residueTraceCharacter_apply] at h
    exact hy h
  have hψ : ψ.IsPrimitive :=
    hprim.compMulHom_of_isPrimitive Subtype.val_injective
  have hg := norm_gauss_le_sqrt_card (A.sexticResiduePowerChar ι I j) ψ hψ
  have hcard : (Fintype.card (A.R ⧸ A.extendIdeal I) : ℝ) = A.exteriorNorm I := by
    rw [← Nat.card_eq_fintype_card, A.exteriorResidue_card I]
    rfl
  rw [hcard] at hg
  have hn : 0 < A.exteriorNorm I := by
    rw [← hcard]
    exact_mod_cast Fintype.card_pos
  have hs : 0 < Real.sqrt (A.exteriorNorm I) := Real.sqrt_pos.mpr hn
  change ‖(Real.sqrt (A.exteriorNorm I) : ℂ)⁻¹ *
    gaussSum (A.sexticResiduePowerChar ι I j) ψ‖ ≤ 1
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  exact (inv_mul_le_iff₀ hs).mpr (by simpa using hg)

private lemma additiveCharacter_eq_fieldTrace (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS) (x : F) :
    P.coefficients.additiveCharacter x = (A.fieldTraceCharacter x : ℂ) := by
  rw [P.sameTrace]
  have harch (y : NumberField.InfiniteAdeleRing F) :
      ProbeAdditive.archPhase F y = ∏ w, (archTraceCharacter w (y w) : ℂ) := by
    simp only [archTraceCharacter_of_isComplex _ (A.complex_place _), Circle.coe_exp,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    rw [ProbeAdditive.archPhase, ← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  simp only [ProbeAdditive.phase, harch, finiteTrace_eq_localTraceCharacter A ι η hS P]
  change _ = (A.eS (sLocalDiagonal F A.Sf x) : ℂ)
  change _ = Circle.coeHom ((∏ w, archTraceCharacter w ((sLocalDiagonal F A.Sf x).1 w)) *
    ∏ v : ↥A.Sf, ResidueTrace.localTraceCharacter v.val ((sLocalDiagonal F A.Sf x).2 v))
  rw [map_mul, map_prod, map_prod]
  rfl

theorem gammaTwo_eq_idealGauss (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (c : ExteriorSquarefreeIdeal A.cS) :
    P.coefficients.gammaTwo c =
      A.idealGauss ι hS c.val (P.coefficients.generator c.val)
        (P.coefficients.generates c.val) 2 := by
  let a := P.coefficients.generator c.val
  have ha : A.Generates c.val a := P.coefficients.generates c.val
  letI := P.coefficients.finiteResidue a ha.1
  letI : Finite (A.R ⧸ A.extendIdeal c.val) := A.exteriorResidue_finite c.val
  letI : Fintype (A.R ⧸ A.extendIdeal c.val) := Fintype.ofFinite _
  let e := Ideal.quotientEquivAlgOfEq A.R ha.2
  rw [P.gammaTwo_recipe]
  unfold ThetaReflectionData.gammaTwoRecipe SArithmeticData.idealGauss
  congr 1
  unfold FiniteTransform.gaussSum FiniteTransform.gaussSumWithLifts
  apply Fintype.sum_equiv e.toEquiv
  intro x
  congr 1
  · rw [MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
      character_eq_sexticResiduePowerChar A ι η hS P c.val a ha x]
    simp only [SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent]
    norm_num
    rw [MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
  · simp only [OneMemClass.coe_one, one_mul]
    rw [additiveCharacter_eq_fieldTrace A ι η hS P]
    have hx := (FiniteTransform.canonicalLifts A.R.toSubring a).property x
    have he : e x = Ideal.Quotient.mk (A.extendIdeal c.val)
        ((FiniteTransform.canonicalLifts A.R.toSubring a).val x) := by
      calc
        e x = e (FiniteTransform.residueMap A.R.toSubring a
            ((FiniteTransform.canonicalLifts A.R.toSubring a).val x)) := congrArg e hx.symm
        _ = _ := Ideal.quotientEquivAlgOfEq_mk A.R ha.2 _
    change (A.fieldTraceCharacter
        (((FiniteTransform.canonicalLifts A.R.toSubring a).val x : F) / (a : F)) : ℂ) =
      (A.residueTraceCharacter hS c.val a ha (e x) : ℂ)
    rw [he, A.residueTraceCharacter_apply]

theorem norm_gammaTwo_le_one (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (c : ExteriorSquarefreeIdeal A.cS) :
    ‖P.coefficients.gammaTwo c‖ ≤ 1 := by
  rw [gammaTwo_eq_idealGauss A ι η hS P c]
  exact norm_idealGauss_le_one A ι hS c.val
    (P.coefficients.generator c.val) (P.coefficients.generates c.val) 2

end
end DedekindZetaZeroFree.NormalizedProbe.PrincipalData
