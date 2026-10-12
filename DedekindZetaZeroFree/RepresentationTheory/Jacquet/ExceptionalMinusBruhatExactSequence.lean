module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalPlusBruhatExactSequence

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalJacquetImage
open KPJacquetExceptionalFactorSeparation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open KPLocalSmoothRepresentation
open PlusLengthSteps
open scoped NNReal

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable (S : RawFiniteInducingData F ζ hζ q)

private theorem minus_smooth (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) (P : Polarization S.heisenberg) :
    let ρ := weylConjugate P S.borel.weyl
    letI := finiteCoverTopology F ζ hζ q m
    SmoothRepresentation ρ := by
  have ht := KPPGLLocalCover.finiteTopology_independent F ζ hζ q m
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q) hm
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)
  change @SmoothRepresentation _ _ _
    (@instTopologicalSpaceSubtype _ _ (KPPGLLocalCover.finiteTopology F ζ hζ q m)) _ _ _
  rw [ht]
  exact (weyl_conjugate_properties S.heisenberg P S.borel.weyl
    S.borel.weylCenter S.borel.weylCenter_coe).2.1

private theorem minus_scalar_weight (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) (h : Torus F ζ hζ q) :
    (Real.sqrt (KPJacquetOpenCell.d F ζ hζ q m hm h) : ℂ) =
      inducingScalar S.borel 0 (S.borel.torus h) := by
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one]
  rw [← raw_modulus_binding F ζ hζ q m hm S]
  change _ = (((KPRankOneInduction.halfModulus (deltaB F ζ hζ q)
    (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ q m hm h) : ℝ≥0) : ℝ) : ℂ)
  rw [KPRankOneInduction.halfModulus_eq]
  rfl

private theorem minus_weyl_twice (h : Torus F ζ hζ q) :
    S.borel.weyl (KPJacquetOpenCell.alpha F ζ hζ q h) = h := by
  rw [← raw_alpha_binding F ζ hζ q S]
  apply Subtype.ext
  change _ * (_ * h.val * _) * _ = h.val
  have hw : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ =
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q))
  simp only [hw, ← mul_assoc]
  rw [show KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) = 1 by simpa [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q)]
  simp only [one_mul]
  rw [mul_assoc, show KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) = 1 by simpa [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q), mul_one]

theorem independent_minus_jacquet_short_exact (P : Polarization S.heisenberg) : by
    letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
    exact ∃ (i : (factorPlus S.borel P).IntertwiningMap
        (jacquetRepresentation S.borel (IMinus S.borel P)))
      (p : (jacquetRepresentation S.borel (IMinus S.borel P)).IntertwiningMap
        (factorMinus S.borel P)),
      Function.Injective i ∧ Function.Surjective p ∧ Function.Exact i p := by
  letI : FiniteDimensional ℂ (InducedModule P) := tau_moduleFinite S.heisenberg P
  let eb := (Module.finBasis ℂ (InducedModule P)).equivFun
  letI : NormedAddCommGroup (InducedModule P) :=
    NormedAddCommGroup.induced _ _ eb eb.injective
  letI : NormedSpace ℂ (InducedModule P) := NormedSpace.induced ℂ _ _ eb
  let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
  have hm : KPLocalChartTopology.MatrixChartDepth F q m :=
    KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
  have hs := minus_smooth F ζ hζ q S m hm P
  let μ : Measure (LocalField F q) := Measure.addHaar
  obtain ⟨e⟩ := raw_principal_series_equiv_core F ζ hζ q m hm S P .minus
  let E := raw_jacquet_equiv F ζ hζ q S
    (V := sectionSpace S.borel P .minus 0)
    (W := KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ q m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ q) (weylConjugate P S.borel.weyl))
    (ρ := IMinus S.borel P)
    (σ := KPLocalInductionJacquetReciprocity.inducedAction F ζ hζ q m hm (weylConjugate P S.borel.weyl)) e
  let O : (KPJacquetOrdinaryCell.openWeight F ζ hζ q m hm (weylConjugate P S.borel.weyl)).Equiv
      (factorPlus S.borel P) := by
    refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_
    intro h
    apply LinearMap.ext
    intro v
    change (Real.sqrt (KPJacquetOpenCell.d F ζ hζ q m hm h) : ℂ) •
      tau P (S.borel.weyl (KPJacquetOpenCell.alpha F ζ hζ q h)) v =
      inducingScalar S.borel 0 (S.borel.torus h) • tau P (S.borel.retract (S.borel.torus h)) v
    rw [minus_scalar_weight F ζ hζ q S m hm, minus_weyl_twice F ζ hζ q S,
      S.borel.retract_torus]
  let C : (KPJacquetOrdinaryCell.closedWeight F ζ hζ q m hm (weylConjugate P S.borel.weyl)).Equiv
      (factorMinus S.borel P) := by
    refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_
    intro h
    apply LinearMap.ext
    intro v
    change (Real.sqrt (KPJacquetOpenCell.d F ζ hζ q m hm h) : ℂ) •
      tau P (S.borel.weyl h) v = inducingScalar S.borel 0 (S.borel.torus h) •
        tau P (S.borel.weyl (S.borel.retract (S.borel.torus h))) v
    rw [minus_scalar_weight F ζ hζ q S m hm, S.borel.retract_torus]
  let i₀ : (KPJacquetOrdinaryCell.openWeight F ζ hζ q m hm (weylConjugate P S.borel.weyl)).IntertwiningMap
      (KPJacquetOrdinaryCell.torusAction F ζ hζ q m hm (weylConjugate P S.borel.weyl)) :=
    { toLinearMap := KPJacquetOrdinaryCell.openInjection F ζ hζ q m hm (weylConjugate P S.borel.weyl) hs μ
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        exact (KPJacquetOrdinaryCell.ordinary_cell_short_exact F ζ hζ q m hm (weylConjugate P S.borel.weyl) hs μ).2.2.2.1 h v }
  let p₀ : (KPJacquetOrdinaryCell.torusAction F ζ hζ q m hm (weylConjugate P S.borel.weyl)).IntertwiningMap
      (KPJacquetOrdinaryCell.closedWeight F ζ hζ q m hm (weylConjugate P S.borel.weyl)) :=
    { toLinearMap := KPJacquetOrdinaryCell.closedProjection F ζ hζ q m hm (weylConjugate P S.borel.weyl)
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        exact (KPJacquetOrdinaryCell.ordinary_cell_short_exact F ζ hζ q m hm (weylConjugate P S.borel.weyl) hs μ).2.2.2.2 h v }
  let i := E.symm.toIntertwiningMap.comp (i₀.comp O.symm.toIntertwiningMap)
  let p := C.toIntertwiningMap.comp (p₀.comp E.toIntertwiningMap)
  obtain ⟨hi, hex, hp, _, _⟩ :=
    KPJacquetOrdinaryCell.ordinary_cell_short_exact F ζ hζ q m hm (weylConjugate P S.borel.weyl) hs μ
  refine ⟨i, p, ?_, ?_, ?_⟩
  · exact E.symm.injective.comp (hi.comp O.symm.injective)
  · exact C.surjective.comp (hp.comp E.surjective)
  · intro x
    change C (p₀ (E x)) = 0 ↔ ∃ v, E.symm (i₀ (O.symm v)) = x
    constructor
    · intro hx
      have hx₀ : p₀ (E x) = 0 := C.injective (by simpa using hx)
      have hmem : E x ∈ LinearMap.range i₀.toLinearMap := by
        rw [hex]
        exact hx₀
      obtain ⟨v, hv⟩ := hmem
      refine ⟨O v, ?_⟩
      rw [O.symm_apply_apply]
      exact (congrArg E.symm hv).trans (E.symm_apply_apply x)
    · rintro ⟨v, rfl⟩
      have hmem : i₀ (O.symm v) ∈ LinearMap.ker p₀.toLinearMap := by
        rw [← hex]
        exact ⟨O.symm v, rfl⟩
      change p₀ (i₀ (O.symm v)) = 0 at hmem
      simp only [E.apply_symm_apply, hmem, map_zero]

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps
