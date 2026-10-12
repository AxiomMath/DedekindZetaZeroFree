module

public import DedekindZetaZeroFree.Metaplectic.Torus.ScalarSections.FiberCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct KPGlobalResidualConstruction
open KPGlobalTorusPeriodizationInverse hiding productModel
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

private theorem pure_rawCoreFiber_torus (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (u g : Raw A)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix A w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    rawCoreFiber A P C (u*g) (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) s (PiTensorProduct.tprod ℂ x)) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) •
      rightAction F ζ hζ (productModel F ζ hζ P) e
        (rawCoreFiber A P C g (RestrictedTensorSimple.stageInclusion (Plus A P C)
          (plusReference A P C) (bad A P C) s (PiTensorProduct.tprod ℂ x))) := by
  obtain ⟨v, hv⟩ := exists_reference_stage A P C g
  obtain ⟨w, hw⟩ := exists_reference_stage A P C (u*g)
  let z : RestrictedTensorSimple.Level (bad A P C) := ⟨s.val ∪ v.val ∪ w.val,
    (s.property.trans Finset.subset_union_left).trans Finset.subset_union_left⟩
  have hsz : s ≤ z := Finset.subset_union_left.trans Finset.subset_union_left
  let y : ∀ j : z.val, Plus A P C j.val := fun j => pureSections A P C s x j.val
  have hi : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) z
      (PiTensorProduct.tprod ℂ y) = RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ x) := by
    have hins := RestrictedTensorSimple.insert_pure (Plus A P C) (plusReference A P C) s.val z.val hsz x
    have hins' := congrArg (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) z) hins
    convert hins'.symm.trans Module.DirectLimit.of_f using 1
    · congr 2
      funext j
      change (if h : j.val ∈ s.val then x ⟨j.val, h⟩ else plusReference A P C j.val) = _
      split_ifs <;> rfl
    · rfl
  rw [← hi]
  apply rawCoreFiber_pure_torus A P C z y u g t a d b e
  · intro p hp
    exact hv p (fun h => hp (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  · intro p hp
    exact hw p (fun h => hp (Finset.mem_union_right _ h))
  · exact ht
  · exact hp
  · exact he

theorem rawCoreFiber_torus
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
    (u g : Raw A) (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix A w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    rawCoreFiber A P C (u*g) x = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) •
      rightAction F ζ hζ (productModel F ζ hζ P) e (rawCoreFiber A P C g x) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    change rawCoreFiber A P C (u*g) (RestrictedTensorSimple.stageInclusion _ _ _ s x) = _
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul]
      rw [pure_rawCoreFiber_torus A P C s x u g t a d b e ht hp he]
      exact smul_comm _ _ _
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

private theorem rational_contraction_torus (r : KPGlobalCenterRationalCharacter.R F ζ hζ)
    (f : ProductUnitary F ζ hζ P) :
    rationalEvaluation A
      (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
        ((KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
          ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ)) •
          rightAction F ζ hζ (productModel F ζ hζ P) r.val f)) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      rationalEvaluation A
        (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P f) := by
  rw [map_smul, map_smul]
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ)) *
      ((untwistRational F ζ hζ).symm (unitaryPeriodization F ζ hζ P
        (rightAction F ζ hζ (productModel F ζ hζ P) r.val f))).val.val 1 =
    KPGlobalExceptionalParameter.realLogPower
      (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      ((untwistRational F ζ hζ).symm (unitaryPeriodization F ζ hζ P f)).val.val 1
  rw [unitaryPeriodization_intertwines, retwistRational_formula, rightAction_formula,
    one_mul, retwistRational_formula]
  have hc := (unitaryPeriodization F ζ hζ P f).val.property r 1
  change _ = (rationalUnitCharacter F ζ hζ r : ℂ) * _ at hc
  rw [mul_one] at hc
  have hpos := KPGlobalCenterRationalCharacter.nu_positive F ζ hζ r.val
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hchar : (rationalUnitCharacter F ζ hζ r : ℂ) =
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) /
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ) := by
    change ((rationalUnitValue F ζ hζ r : ℂˣ) : ℂ) = _
    simp [rationalUnitValue, Units.val_div_eq_div_val, KPGlobalCenterRationalCharacter.positiveComplex]
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) := by
    unfold KPGlobalTorusFunctionData.deltaHalf KPGlobalExceptionalParameter.realLogPower
    have hδ : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hδ, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hc, hchar, hd]
  simp only [map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one, smul_eq_mul,
    Submodule.coe_smul_of_tower, Pi.smul_apply]
  field_simp

theorem quotientCoreEvaluator_rational_torus
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
    (r : KPGlobalCenterRationalCharacter.R F ζ hζ) (g : G F ζ hζ) :
    quotientCoreEvaluator A P C x (r.val.val*g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2 : ℂ) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * quotientCoreEvaluator A P C x g := by
  obtain ⟨u,t,a,d,ht,hp,he⟩ := EisensteinReferenceSections.TorusNorms.raw_lifts F ζ hζ r.val
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreValue A P C x (r.val.val * scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) = _
      rw [← he, ← map_mul, ← map_mul, quotientCoreValue_raw]
      change rawCoreValue A P C (u*g) x = _ * _ * rawCoreValue A P C g x
      rw [rawCoreValue_fiber, rawCoreValue_fiber,
        rawCoreFiber_torus A P C x u g t a d (fun _ => 0) r.val ht hp he]
      exact rational_contraction_torus A P r _

theorem quotientCoreEvaluator_induced
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    KPLiteralRaw.Induced F ζ hζ 0 (quotientCoreEvaluator A P C x) := by
  refine ⟨quotientCoreEvaluator_smooth A P C x, ?_⟩
  intro r y g
  rw [mul_assoc, quotientCoreEvaluator_rational_torus, quotientCoreEvaluator_upper]
  simp
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
