module

public import DedekindZetaZeroFree.Theta.Periods.ComplexRotationOddness

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.IdeleInsertion
open NumberField MeasureTheory
open scoped Classical
open MomentSources ThetaProfileHaarSheets ThetaSheetExactUnfolding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

 instance sheetContinuousConstSMul (A : SArithmeticData F) (l : PositiveAxis) :
    ContinuousConstSMul A.Gamma1 (Sheet A l) where
  continuous_const_smul γ := (continuous_const.mul continuous_subtype_val).subtype_mk _

 instance sheetInvariant (A : SArithmeticData F) (w : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    SMulInvariantMeasure A.Gamma1 (Sheet A l) (sheetHaar A w μG l) := by
  have he (γ : A.Gamma1) (z : A.G1) :
      sheetTranslation A w l (γ • z) = γ • sheetTranslation A w l z := by
    apply Subtype.ext
    change normSection A w l * (γ.val.val * z.val) =
      γ.val.val * (normSection A w l * z.val)
    ac_rfl
  exact smulInvariantMeasure_map (kernelHaar A w μG) (sheetTranslation A w l)
    he (sheetTranslation A w l).measurable

lemma norm_insertion_one (w : InfinitePlace F) (z : w.Completionˣ)
    (hz : ‖(z : w.Completion)‖ = 1) : R.A.norm (infiniteInsertion R.A w z) = 1 := by
  unfold SArithmeticData.norm infiniteInsertion
  have hi : ∀ u : InfinitePlace F,
      ‖((Function.update (fun u : InfinitePlace F => (1 : u.Completionˣ)) w z u :
        u.Completionˣ) : u.Completion)‖ = 1 := by
    intro u
    by_cases hu : u = w
    · subst u; simpa using hz
    · simp [Function.update_of_ne hu]
  simp only [hi, one_pow, Finset.prod_const_one, Pi.one_apply, Units.val_one, norm_one,
    one_mul]

theorem quotient_integral_zero_of_odd (A : SArithmeticData F) (w : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (t : A.G1) (f : SheetQuotient A l → ℂ)
    (hf : Integrable f (sheetQuotientHaar A w μG l))
    (hodd : ∀ y y' : Sheet A l, y'.val = t.val * y.val →
      f (sheetProjection A l y') = -f (sheetProjection A l y)) :
    (∫ q, f q ∂sheetQuotientHaar A w μG l) = 0 := by
  let T := sheetTranslation A w l
  let e : Sheet A l ≃ₜ Sheet A l := T.symm.trans ((Homeomorph.mulLeft t).trans T)
  have he (y : Sheet A l) : (e y).val = t.val * y.val := by
    change normSection A w l * (t.val * ((normSection A w l)⁻¹ * y.val)) = _
    calc
      _ = t.val * (normSection A w l * ((normSection A w l)⁻¹ * y.val)) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel_left]
  let μ := sheetHaar A w μG l
  have hT : MeasurePreserving T (kernelHaar A w μG) μ := ⟨T.measurable, rfl⟩
  have hep : MeasurePreserving e μ μ :=
    hT.comp ((measurePreserving_mul_left (kernelHaar A w μG) t).comp
      (hT.symm T.toMeasurableEquiv))
  obtain ⟨Ω, _, _, _, hΩ⟩ := exists_sheetFundamentalDomain A w μG l
  have hΩ' : IsFundamentalDomain A.Gamma1 (e '' Ω) μ := by
    apply hΩ.image_of_equiv e.toEquiv (hep.symm e.toMeasurableEquiv).quasiMeasurePreserving
      (Equiv.refl A.Gamma1)
    intro γ y
    apply Subtype.ext
    change (e (γ • y)).val = (γ • e y).val
    rw [he]
    change t.val * (γ.val.val * y.val) = γ.val.val * (e y).val
    rw [he]
    ac_rfl
  let g := fun y : Sheet A l => f (sheetProjection A l y)
  have hg : ∀ γ : A.Gamma1, ∀ y, g (γ • y) = g y := by
    intro γ y
    apply congrArg f
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨γ, rfl⟩
  have hneg (y : Sheet A l) : g (e y) = -g y := hodd y (e y) (he y)
  have hmap : (∫ q, f q ∂sheetQuotientHaar A w μG l) = ∫ y in Ω, g y ∂μ := by
    rw [sheetQuotientHaar_eq A w μG l Ω hΩ]
    apply integral_map measurable_quotient_mk''.aemeasurable
    simpa only [sheetQuotientHaar_eq A w μG l Ω hΩ, sheetProjection] using hf.aestronglyMeasurable
  have hz : (∫ y in Ω, g y ∂μ) = -(∫ y in Ω, g y ∂μ) := by
    calc
      _ = ∫ y in e '' Ω, g y ∂μ := hΩ.setIntegral_eq hΩ' hg
      _ = ∫ y in Ω, g (e y) ∂μ := hep.setIntegral_image_emb e.measurableEmbedding g Ω
      _ = _ := by simp only [hneg, integral_neg]
  rw [hmap]
  have htwo : (2 : ℂ) * (∫ y in Ω, g y ∂μ) = 0 := by linear_combination hz
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

lemma quotientUpper_projection {N : TraceHaarTransport R} {Q : AdmissibleFlatSources R}
    {T : Realization R Q} {P : Packet R Q} (D : DigitsDescent R N Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (l : PositiveAxis) (y : Sheet R.A l) :
    quotientUpper R Q T P v m b l (sheetProjection R.A l y) =
      weightedUpper R Q T P v m b y.val := by
  unfold quotientUpper
  have h := Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection R.A l y)).val at hv
  rw [← hv]
  exact D.weighted_upper_descent v m b ⟨γ.val.val, γ.property⟩ _

theorem bothUpperZero {N : TraceHaarTransport R} {Q : AdmissibleFlatSources R}
    {T : Realization R Q} {P : Packet R Q} (C : ResidualConstantTerm R Q T)
    (D : DigitsDescent R N Q T P) : BothUpperZero R N Q T P := by
  letI := N.groupHaar_isHaar
  intro v m b l
  let t : R.A.G1 := ⟨infiniteInsertion R.A P.v₀ (-1), norm_insertion_one R P.v₀ (-1) (by simp)⟩
  apply quotient_integral_zero_of_odd R.A P.v₀ N.groupHaar l t
    (quotientUpper R Q T P v m b l) (D.upper_integrable v m b l)
  intro y y' hy'
  rw [quotientUpper_projection R D, quotientUpper_projection R D, hy']
  exact weightedUpper_neg_one R P C v m b P.v₀ y.val

end DedekindZetaZeroFree.IdeleInsertion

end
