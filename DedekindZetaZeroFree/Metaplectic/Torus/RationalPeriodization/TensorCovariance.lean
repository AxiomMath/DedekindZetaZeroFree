module

public import DedekindZetaZeroFree.Eisenstein.Induction.TorusCovariance
public import DedekindZetaZeroFree.Eisenstein.Induction.UnitaryModelEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators NNReal
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

def torusSlot (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) : ∀ p, Fiber R P C p →ₗ[ℂ] Fiber R P C p
  | Sum.inl w =>
    ((KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
      (u (Sum.inl w)).epsilon : ℂ) *
      (Real.rpow (KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ)/(d w : ℂ))) (1/6 : ℝ) : ℂ)) •
      LinearMap.id
  | Sum.inr q => localTau F R.A.zeta12 R.A.primitive_zeta12 P C q (t q)

abbrev localNorm := EisensteinReferenceSections.TorusNorms.localNorm F R.A.zeta12 R.A.primitive_zeta12 P C

theorem stage_toLeft (s : RestrictedTensorSimple.Level (bad R P C)) : s.val.toLeft = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro w
  exact Finset.mem_toLeft.mpr (s.property (arch_bad R P C w))

private theorem arch_action (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) (s : RestrictedTensorSimple.Level (bad R P C))
    (y : ∀ j : s.val, Fiber R P C j) :
    (∏ w : s.val.toLeft, torusSlot R P C u t a d (Sum.inl w.val)
      (y ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩)) =
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 (u (Sum.inl w)).epsilon : ℂ)) *
      (∏ w, (Real.rpow (localNorm R P C t a d (Sum.inl w)) (1/6 : ℝ) : ℂ)) *
      (∏ w : s.val.toLeft, y ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩) := by
  change (∏ w : s.val.toLeft,
    ((KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
      (u (Sum.inl w.val)).epsilon : ℂ) *
      (Real.rpow (localNorm R P C t a d (Sum.inl w.val)) (1/6 : ℝ) : ℂ)) * _) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hp (f : InfinitePlace F → ℂ) : (∏ w : s.val.toLeft, f w.val) = ∏ w, f w := by
    rw [Finset.prod_coe_sort, stage_toLeft R P C s]
  rw [hp (fun w => (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
    R.A.primitive_zeta12 (u (Sum.inl w)).epsilon : ℂ)),
    hp (fun w => (Real.rpow (localNorm R P C t a d (Sum.inl w)) (1/6 : ℝ) : ℂ))]
  rfl

theorem unitaryComparison_torus_stage
    (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix R w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 u) = e.val)
    (s : RestrictedTensorSimple.Level (bad R P C)) (y : ∀ j : s.val, Fiber R P C j)
    (htail : ∀ p, p ∉ s.val → torusSlot R P C u t a d p (reference R P C p) = reference R P C p) :
    unitaryComparison R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (fun j => torusSlot R P C u t a d j (y j)))) =
      ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) •
        KPGlobalTorusPeriodizationInverse.rightAction F R.A.zeta12 R.A.primitive_zeta12
          (productModel F R.A.zeta12 R.A.primitive_zeta12 P) e
          (unitaryComparison R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
            (PiTensorProduct.tprod ℂ y))) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨raw, tg, ag, dg, htg, hpg, heg⟩ := EisensteinReferenceSections.TorusNorms.raw_lifts F
    R.A.zeta12 R.A.primitive_zeta12 g
  rw [unitaryComparison_full_raw R P C s _ raw tg g htg heg]
  change _ = ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) *
    (unitaryComparison R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ y))).val.val (g * e)
  have hm q : (tg q * t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) ((raw * u) (Sum.inr q)) := by
    change (tg q).val * (t q).val = _
    rw [htg, ht, ← map_mul]
    rfl
  have hme : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 (raw * u)) = (g * e).val := by
    rw [map_mul, map_mul, heg, he]
    rfl
  rw [unitaryComparison_full_raw R P C s y (raw * u) (fun q => tg q * t q) (g * e) hm hme,
    arch_action R P C u t a d s y, EisensteinReferenceSections.SourceTorusEvaluation.phase_mul]
  let v q : LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C q :=
    if h : q ∈ s.val.toRight then y ⟨Sum.inr q, Finset.mem_toRight.mp h⟩
    else localReference F R.A.zeta12 R.A.primitive_zeta12 P C q
  let n q : ℂ := (Real.rpow (localNorm R P C t a d (Sum.inr q)) (1/6 : ℝ) : ℂ)
  have hl q : localUntwistedEvaluation F R.A.zeta12 R.A.primitive_zeta12 P C q
      (if h : q ∈ s.val.toRight then torusSlot R P C u t a d (Sum.inr q)
        (y ⟨Sum.inr q, Finset.mem_toRight.mp h⟩)
       else localReference F R.A.zeta12 R.A.primitive_zeta12 P C q) (tg q) =
      localUntwistedEvaluation F R.A.zeta12 R.A.primitive_zeta12 P C q (v q) (tg q * t q) * n q := by
    have hτ : (if h : q ∈ s.val.toRight then torusSlot R P C u t a d (Sum.inr q)
        (y ⟨Sum.inr q, Finset.mem_toRight.mp h⟩)
       else localReference F R.A.zeta12 R.A.primitive_zeta12 P C q) =
        localTau F R.A.zeta12 R.A.primitive_zeta12 P C q (t q) (v q) := by
      dsimp only [v]
      split_ifs with h
      · rfl
      · exact (htail (Sum.inr q) (fun hh => h (Finset.mem_toRight.mpr hh))).symm
    rw [hτ, EisensteinReferenceSections.SourceTorusEvaluation.untwisted_tau]
    rfl
  simp_rw [hl]
  obtain ⟨hns, hnorm⟩ := EisensteinReferenceSections.TorusNorms.given_raw_norm F R.A.zeta12
    R.A.primitive_zeta12 P C u t a d b e ht hp he
  have hroot : Function.HasFiniteMulSupport (fun p => (Real.rpow (localNorm R P C t a d p) (1/6 : ℝ) : ℂ)) :=
    hns.comp (g := fun x : ℝ => (Real.rpow x (1/6 : ℝ) : ℂ)) (by norm_num)
  have hnf : Function.HasFiniteMulSupport n := hroot.comp_of_injective Sum.inr_injective
  have hvs := local_evaluation_finiteSupport F R.A.zeta12 R.A.primitive_zeta12 P C s.val.toRight
    (by intro q hq; exact Finset.mem_toRight.mpr
          (s.property (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.finite_mem_badSet
            F R.A.zeta12 R.A.primitive_zeta12 P C q hq)))
    (fun q => y ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩)
    (raw * u) (fun q => tg q * t q) hm
  rw [finprod_mul_distrib hvs hnf]
  have hn : ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) =
      (∏ w, (Real.rpow (localNorm R P C t a d (Sum.inl w)) (1/6 : ℝ) : ℂ)) * ∏ᶠ q, n q := by
    have hcoe := MonoidHom.map_finprod Complex.ofRealHom.toMonoidHom
      (hns.comp (g := fun x : ℝ => Real.rpow x (1/6 : ℝ)) (by norm_num))
    rw [hnorm]
    exact hcoe.trans (EisensteinReferenceSections.RawSource.finprod_places F hroot)
  rw [hn]
  ring

theorem periodization_torus
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (f : KPGlobalTorusPeriodizationInverse.ProductUnitary F R.A.zeta12 R.A.primitive_zeta12 P)
    (g : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) *
      (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F R.A.zeta12
        R.A.primitive_zeta12 P (KPGlobalTorusPeriodizationInverse.rightAction F R.A.zeta12
          R.A.primitive_zeta12 (productModel F R.A.zeta12 R.A.primitive_zeta12 P) e f)).val.val g =
      (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F R.A.zeta12
        R.A.primitive_zeta12 P f).val.val (g * e) := by
  change ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) *
    ((KPGlobalTorusPeriodizationInverse.untwistRational F R.A.zeta12 R.A.primitive_zeta12).symm
      (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F R.A.zeta12 R.A.primitive_zeta12 P
        (KPGlobalTorusPeriodizationInverse.rightAction F R.A.zeta12 R.A.primitive_zeta12
          (productModel F R.A.zeta12 R.A.primitive_zeta12 P) e f))).val.val g =
    ((KPGlobalTorusPeriodizationInverse.untwistRational F R.A.zeta12 R.A.primitive_zeta12).symm
      (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F R.A.zeta12 R.A.primitive_zeta12 P f)).val.val (g * e)
  rw [KPGlobalTorusPeriodizationInverse.unitaryPeriodization_intertwines]
  rw [KPGlobalTorusPeriodizationInverse.retwistRational_formula,
    KPGlobalTorusPeriodizationInverse.rightAction_formula,
    KPGlobalTorusPeriodizationInverse.retwistRational_formula, map_mul, Units.val_mul]
  simp only [NNReal.coe_mul, Complex.ofReal_mul]
  ring

theorem comparisonSmooth_torus_stage
    (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix R w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 u) = e.val)
    (s : RestrictedTensorSimple.Level (bad R P C)) (y : ∀ j : s.val, Fiber R P C j)
    (htail : ∀ p, p ∉ s.val → torusSlot R P C u t a d p (reference R P C p) = reference R P C p)
    (g : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    (comparisonSmooth R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ (fun j => torusSlot R P C u t a d j (y j))))).val.val g =
      (comparisonSmooth R P C (RestrictedTensorSimple.stageInclusion _ _ _ s
        (PiTensorProduct.tprod ℂ y))).val.val (g * e) := by
  change (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F R.A.zeta12
    R.A.primitive_zeta12 P (unitaryComparison R P C _)).val.val g = _
  rw [unitaryComparison_torus_stage R P C u t a d b e ht hp he s y htail, map_smul]
  exact periodization_torus R P e _ g

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
