module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ForwardImageEvaluation
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.AdelicFubini

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct MomentSources KPLiteralRaw
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPRankOneShellRepair
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (N : TraceHaarTransport R)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
attribute [local irreducible] coreFlatInsertion
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000

theorem scatteringComplement_at_slot (q : KPFinitePlace F) (u : KPAdeles F)
    (hu : adeleEval F (Sum.inr q) u = 0) (g : Raw R.A) :
    scatteringComplement R.A q u g (Sum.inr q) =
      KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) * g (Sum.inr q) := by
  simp only [scatteringComplement, RestrictedProduct.mul_apply,
    localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_same]
  change (_ * (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q))⁻¹) *
    KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) *
    KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (adeleEval F (Sum.inr q) u) *
    g (Sum.inr q) = _
  rw [hu, KPStandardLocalRootLifts.N_zero, mul_one]
  group

def scatteringSlotOutput (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (s : ℂ) (g : Raw R.A) (f : Plus R.A P C (Sum.inr q)) :
    LocalFiber F ζ hζ P C q :=
  (KPRankOneShellContinuation.transportToSections (q.adicCompletion F)
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
    (actualCanonicalContinued F q ζ hζ (C.canonical q) (C.polarization q) μ hμ .plus s)
    (integralSpectralSection R P C q f s)).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) * g (Sum.inr q)))

theorem scatteringSlotOutput_zero (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (g : Raw R.A) (f : Plus R.A P C (Sum.inr q)) :
    scatteringSlotOutput R P C q μ hμ 0 g f =
      (actualCanonicalForwardMap F ζ hζ q (C.canonical q) (C.polarization q) μ hμ f).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) * g (Sum.inr q))) := by
  have hf : integralSpectralSection R P C q f 0 = f := by
    apply Subtype.ext
    funext a
    rw [integralSpectralSection_value]
    simp
  unfold scatteringSlotOutput
  rw [hf]
  apply Subtype.ext
  funext h
  change (inducingAction (C.canonical q).borel (C.polarization q) .minus (-0)
    ((C.canonical q).iwasawa.borelPart _)
    ((actualCanonicalContinued F q ζ hζ (C.canonical q) (C.polarization q) μ hμ .plus 0
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0).symm f)).val
      ((C.canonical q).iwasawa.compactPart _))).val h = _
  rw [neg_zero]
  change _ = ((actualCanonicalForwardLinear F ζ hζ q
    (C.canonical q) (C.polarization q) μ hμ f).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) * g (Sum.inr q)))).val h
  rw [forwardIntegralLinear_eq_continuationWitness]
  rfl

theorem coreFlatInsertion_original_slice_kernel
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (u : KPAdeles F) (hu : adeleEval F (Sum.inr q) u = 0)
    (g : Raw R.A)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (z : ℂ) (hz : KPRankOneShellContinuation.convergenceHalfPlane .plus z)
    (hx : scatteringSlotOutput R P C q μ hμ z g (x ⟨Sum.inr q,hq⟩) = 0) :
    (∫ y : q.adicCompletion F, (coreFlatInsertion R P C
      (RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x))).val z
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
        (u + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) ∂N.finiteHaar q) = 0 := by
  let b := scatteringComplement R.A q u g
  obtain ⟨d, hd⟩ := exists_reference_stage R.A P C b
  let T : RestrictedTensorSimple.Level (bad R.A P C) :=
    ⟨t.val ∪ d.val, t.property.trans Finset.subset_union_left⟩
  have htT : t ≤ T := Finset.subset_union_left
  let X : ∀ j : T.val, Plus R.A P C j.val :=
    fun j => if hj : j.val ∈ t.val then x ⟨j.val,hj⟩ else plusReference R.A P C j.val
  have hXq : X ⟨Sum.inr q,htT hq⟩ = x ⟨Sum.inr q,hq⟩ := dif_pos hq
  have hT : ∀ v, v ∉ T.val → localValue R.A P C v (b v)
      (plusReference R.A P C v) = reference R.A P C v :=
    fun v hv => hd v (fun h => hv (Finset.mem_union_right _ h))
  have he : RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
      (bad R.A P C) t (PiTensorProduct.tprod ℂ x) =
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) T (PiTensorProduct.tprod ℂ X) := by
    have htrans : RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) t T htT (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ X := by
      unfold RestrictedTensorSimple.transition
      apply (RestrictedTensorSimple.insert_pure (Plus R.A P C) (plusReference R.A P C)
        t.val T.val htT x).trans
      congr 1
      funext j
      dsimp only [X]
      split_ifs <;> rfl
    exact (Module.DirectLimit.of_f (hij := htT)).symm.trans
      (congrArg (RestrictedTensorSimple.stageInclusion _ _ _ T) htrans)
  rw [he]
  rw [coreFlatInsertion_original_stage_integral R P C N T X q (htT hq) u hu g hT μ hμ z hz]
  have harg := scatteringComplement_at_slot R q u hu g
  have hout : (KPRankOneShellContinuation.transportToSections (q.adicCompletion F)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus z
      (actualCanonicalContinued F q ζ hζ (C.canonical q) (C.polarization q) μ hμ .plus z)
      (integralSpectralSection R P C q (X ⟨Sum.inr q,htT hq⟩) z)).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (b (Sum.inr q))) = 0 := by
    rw [hXq]
    change _ = _
    rw [show b (Sum.inr q) = _ from harg]
    exact hx
  rw [hout, map_zero, mul_zero, mul_zero]

theorem coreScattering_slot_kernel (N : TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val) (g : Raw R.A)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (z : ℂ) (hz : (1 / 3 : ℝ) < z.re)
    (hx : scatteringSlotOutput R P C q μ hμ z g (x ⟨Sum.inr q,hq⟩) = 0) :
    coreScattering R P C (RestrictedTensorSimple.stageInclusion _ _ _ t
      (PiTensorProduct.tprod ℂ x)) z
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) = 0 := by
  letI := N.finiteHaar_add q
  rw [coreScattering_fubini R P C N _ q z hz]
  have hlocal : KPRankOneShellContinuation.convergenceHalfPlane .plus z := by
    change -(1 / 6 : ℝ) < z.re
    linarith
  have he : (fun u : AdditiveCoordinate.Away F q =>
      ∫ y : q.adicCompletion F, (coreFlatInsertion R P C
        (RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x))).val z
        (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
          (u.val + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) *
          scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) ∂N.finiteHaar q) = 0 := by
    funext u
    exact coreFlatInsertion_original_slice_kernel R P C N t x q hq u.val u.property
      g μ hμ z hlocal hx
  rw [he]
  exact integral_zero _ _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
