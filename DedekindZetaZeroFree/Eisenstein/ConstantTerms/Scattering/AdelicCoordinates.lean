module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.ChamberHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Continuation.Scattering.SpectralSlices
public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.LocalCompactsAndScalarSlots

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPAdelicCoverRestrictedProduct
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localAdele → eval_localAdele
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem finiteScatteringRaw_unsigned (q : KPFinitePlace F) (y : q.adicCompletion F) :
    finiteScatteringRaw A q (-y) * KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) =
      KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) y := by
  have hn := KPCorrectedBruhatLifts.upper_diagonal F ζ hζ (Sum.inr q) (-y) (-1)
  simp only [Units.val_neg, Units.val_one, div_neg, div_one, neg_neg] at hn
  have hw : (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q))⁻¹ =
      KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using KPStandardLocalRootLifts.W_sq F ζ hζ (Sum.inr q)
  unfold finiteScatteringRaw KPRankOneOpenCellKernel.signedWeylRaw
  rw [mul_inv_rev, hw, mul_assoc, hn]
  group

def scatteringComplement (q : KPFinitePlace F) (u : KPAdeles F) (g : Raw A) : Raw A :=
  localToRestricted F ζ hζ (Sum.inr q)
    (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
      (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q))⁻¹) *
    KPRationalAdelicSplitting.WTuple F ζ hζ * KPGlobalTorusFunctionData.rootTuple F ζ hζ u * g

theorem scattering_raw_split (q : KPFinitePlace F) (u : KPAdeles F)
    (hu : adeleEval F (Sum.inr q) u = 0) (y : q.adicCompletion F) (g : Raw A) :
    KPRationalAdelicSplitting.WTuple F ζ hζ *
      KPGlobalTorusFunctionData.rootTuple F ζ hζ
        (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) * g =
    localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw A q (-y)) *
      scatteringComplement A q u g := by
  apply RestrictedProduct.ext
  intro v
  by_cases hv : v = Sum.inr q
  · subst v
    simp only [RestrictedProduct.mul_apply, scatteringComplement,
      localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_same]
    change KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) *
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q)
        (adeleEval F (Sum.inr q) (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y)) *
      g (Sum.inr q) = _
    rw [map_add, hu, eval_localAdele, Pi.single_eq_same, zero_add]
    change _ = finiteScatteringRaw A q (-y) *
      ((KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
        (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q))⁻¹) *
        KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (adeleEval F (Sum.inr q) u) * g (Sum.inr q))
    rw [hu, KPStandardLocalRootLifts.N_zero, mul_one]
    calc
      _ = (finiteScatteringRaw A q (-y) * KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1)) *
          g (Sum.inr q) := by rw [finiteScatteringRaw_unsigned]
      _ = _ := by group
  · simp only [RestrictedProduct.mul_apply, scatteringComplement,
      localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne hv, one_mul]
    change KPStandardLocalRootLifts.W F ζ hζ v *
      KPStandardLocalRootLifts.N F ζ hζ v
        (adeleEval F v (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y)) * g v =
      KPStandardLocalRootLifts.W F ζ hζ v *
        KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v u) * g v
    rw [map_add, eval_localAdele, Pi.single_eq_of_ne hv, add_zero]

section Spectral
open KPGlobalTorusFiniteStages MomentSources
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem coreFlatInsertion_original_slice
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C))
    (q : KPFinitePlace F) (u : KPAdeles F) (hu : adeleEval F (Sum.inr q) u = 0)
    (y : q.adicCompletion F) (g : Raw R.A) (z : ℂ) :
    (coreFlatInsertion R P C x).val z
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) *
        scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
    (coreFlatInsertion R P C x).val z
      (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (finiteScatteringRaw R.A q (-y))) *
      scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (scatteringComplement R.A q u g))) := by
  change (coreFlatInsertion R P C x).val z
    (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12)) *
      scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (KPGlobalTorusFunctionData.rootTuple F R.A.zeta12 R.A.primitive_zeta12 _)) *
      scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) = _
  change _ = (coreFlatInsertion R P C x).val z
    (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) _)) *
      scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 _))
  simp only [← map_mul]
  rw [scattering_raw_split R.A q u hu y g]

attribute [local irreducible] coreFlatInsertion
set_option backward.isDefEq.respectTransparency true

theorem coreFlatInsertion_original_slice_integrable
    (N : TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (u : KPAdeles F) (hu : adeleEval F (Sum.inr q) u = 0)
    (g : Raw R.A) (z : ℂ)
    (hz : KPRankOneShellContinuation.convergenceHalfPlane .plus z) :
    MeasureTheory.Integrable (fun y : q.adicCompletion F =>
      (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ t
        (PiTensorProduct.tprod ℂ x))).val z
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
          KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
            (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) *
          scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
            (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g))) (N.finiteHaar q) := by
  open MeasureTheory in
    let b := scatteringComplement R.A q u g
    obtain ⟨d, hd⟩ := exists_reference_stage R.A P C b
    let T : RestrictedTensorSimple.Level (bad R.A P C) :=
      ⟨t.val ∪ d.val, t.property.trans Finset.subset_union_left⟩
    have htT : t ≤ T := Finset.subset_union_left
    let X : ∀ j : T.val, Plus R.A P C j.val :=
      fun j => if hj : j.val ∈ t.val then x ⟨j.val,hj⟩ else plusReference R.A P C j.val
    have hT : ∀ v, v ∉ T.val → localValue R.A P C v (b v)
        (plusReference R.A P C v) = reference R.A P C v :=
      fun v hv => hd v (fun h => hv (Finset.mem_union_right _ h))
    have he : RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) t (PiTensorProduct.tprod ℂ x) =
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) T (PiTensorProduct.tprod ℂ X) := by
      have hX : RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C)
          (bad R.A P C) t T htT (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ X := by
        unfold RestrictedTensorSimple.transition
        apply (RestrictedTensorSimple.insert_pure (Plus R.A P C) (plusReference R.A P C) t.val T.val htT x).trans
        congr 1
        funext j
        dsimp only [X]
        split_ifs <;> rfl
      exact (Module.DirectLimit.of_f (hij := htT)).symm.trans
        (congrArg (RestrictedTensorSimple.stageInclusion _ _ _ T) hX)
    let μ := Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
    have hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1 :=
      Measure.addHaarMeasure_self
    have hi := coreFlatInsertion_scattering_stage_integral R P C T X b q (htT hq) hT μ hμ z hz
    have htr := traceHaar_eq_smul_unit R N P C q μ hμ
    have htrace : Integrable (fun y => (coreFlatInsertion R P C
        (RestrictedTensorSimple.stageInclusion _ _ _ T (PiTensorProduct.tprod ℂ X))).val z
        (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (finiteScatteringRaw R.A q y)) *
          scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
            (amalgamation F R.A.zeta12 R.A.primitive_zeta12 b))) (N.finiteHaar q) := by
      rw [htr]
      exact hi.1.smul_measure ENNReal.ofReal_ne_top
    letI : (N.finiteHaar q).IsAddHaarMeasure := N.finiteHaar_add q
    have hneg := (Measure.measurePreserving_neg (N.finiteHaar q)).integrable_comp_of_integrable htrace
    simpa only [Function.comp_def, b, ← he, ← coreFlatInsertion_original_slice R P C _ q u hu] using hneg

theorem coreFlatInsertion_original_stage_integral
    (N : TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (u : KPAdeles F) (hu : adeleEval F (Sum.inr q) u = 0)
    (g : Raw R.A)
    (hg : ∀ v, v ∉ t.val → localValue R.A P C v
      (scatteringComplement R.A q u g v) (plusReference R.A P C v) = reference R.A P C v)
    (μ : MeasureTheory.Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (z : ℂ) (hz : KPRankOneShellContinuation.convergenceHalfPlane .plus z) :
    let b := scatteringComplement R.A q u g
    let f := integralSpectralSection R P C q (x ⟨Sum.inr q,hq⟩) z
    let out := KPRankOneShellContinuation.transportToSections (q.adicCompletion F)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus z
      (KPRankOneShellRepair.actualCanonicalContinued F q R.A.zeta12 R.A.primitive_zeta12
        (C.canonical q) (C.polarization q) μ hμ .plus z) f
    (∫ y : q.adicCompletion F, (coreFlatInsertion R P C
      (RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x))).val z
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) *
        scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) ∂N.finiteHaar q) =
      (PoissonS.integerVolume F q : ℂ) *
        (Complex.exp (z * (awayHeight R P C q b : ℂ)) *
          rationalSlotContraction R.A P C t q hq
            (fun j => localValue R.A P C j.val (b j.val) (x j))
            (out.val (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
              (Sum.inr q) (b (Sum.inr q))))) := by
  open MeasureTheory in
    dsimp only
    letI := N.finiteHaar_add q
    let b := scatteringComplement R.A q u g
    let k := fun y => (coreFlatInsertion R P C
      (RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x))).val z
      (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (finiteScatteringRaw R.A q y)) *
        scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (amalgamation F R.A.zeta12 R.A.primitive_zeta12 b))
    have he : (fun y => (coreFlatInsertion R P C
        (RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x))).val z
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
          KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
            (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) *
          scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
            (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g))) = fun y => k (-y) :=
      funext (fun y => coreFlatInsertion_original_slice R P C _ q u hu y g z)
    rw [he, integral_neg_eq_self k (N.finiteHaar q), traceHaar_eq_smul_unit R N P C q μ hμ,
      integral_smul_measure,
      (coreFlatInsertion_scattering_stage_integral R P C t x b q hq hg μ hμ z hz).2,
      ENNReal.toReal_ofReal (PoissonS.integerVolume_pos F q).le]
    rfl

end Spectral
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
