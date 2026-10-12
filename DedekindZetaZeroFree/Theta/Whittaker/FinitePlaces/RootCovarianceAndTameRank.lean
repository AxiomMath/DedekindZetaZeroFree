module

public import DedekindZetaZeroFree.Theta.Periods.DetectedTensorAssembly
public import DedekindZetaZeroFree.Theta.Whittaker.RootTranslationCovariance
public import DedekindZetaZeroFree.Theta.Whittaker.ImageRepresentationUniqueness

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

def finiteTrace (q : KPFinitePlace F) : Multiplicative (q.adicCompletion F) →ₜ* ℂˣ where
  toFun t := Circle.toUnits (localFiniteCharacter F q t.toAdd)
  map_one' := by simp
  map_mul' := by intro x y; simp [AddChar.map_add_eq_mul]
  continuous_toFun := by
    have hc : Continuous (Circle.toUnits : Circle → ℂˣ) := by
      rw [Units.continuous_iff]
      constructor
      · exact continuous_subtype_val
      · change Continuous (fun z : Circle => (z : ℂ)⁻¹)
        exact continuous_subtype_val.inv₀ (fun z : Circle => Circle.coe_ne_zero z)
    exact hc.comp ((continuous_localFiniteCharacter F q).comp continuous_toAdd)

@[simp] theorem finiteTrace_coe (q : KPFinitePlace F) (t : Multiplicative (q.adicCompletion F)) :
    (finiteTrace (F := F) q t : ℂ) = (localFiniteCharacter F q t.toAdd : ℂ) := rfl

theorem finiteTrace_ne_one (q : KPFinitePlace F) :
    (finiteTrace (F := F) q).toMonoidHom ≠ 1 := by
  intro h
  apply one_ne_zero (α := q.adicCompletion F)
  apply (localFiniteCharacter_nondegenerate F q 1).mp
  intro z
  have he := congrArg (fun χ : Multiplicative (q.adicCompletion F) →* ℂˣ =>
    (χ (Multiplicative.ofAdd z) : ℂ)) h
  apply Subtype.ext
  change (localFiniteCharacter F q z : ℂ) = 1 at he
  simpa only [one_mul, Circle.coe_one] using he

namespace TensorActions

theorem core_rational_root (D : TensorActions R N) (x) (t : F) (g : Group R) :
    D.coreMap x (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) t) * g) = D.coreMap x g := by
  rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact (D.toTensorHC.same_residue x).2.2.1 _ _

theorem finite_period_translate (D : TensorActions R N)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (g : Group R) :
    fourier R D.sources.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
          (D.finiteData q).haar (D.finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩)))))) g =
    fourier R D.sources.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ x)))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  have _hi := D.toTensorHC.integrable
    (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))
    (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a))
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with t
  rw [D.finite_intertwining q a s hq x, mul_assoc]

theorem finite_slice_root (D : TensorActions R N)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (t : q.adicCompletion F) (b : actualLocal R D.finiteData (Sum.inr q)) :
    (coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s).toLinearMap x ⟨Sum.inr q, hq⟩
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) =
      (localFiniteCharacter F q t : ℂ) *
        (coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s).toLinearMap x ⟨Sum.inr q, hq⟩ b := by
  let i : s.val := ⟨Sum.inr q, hq⟩
  let y := Function.update x i b
  let c := RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ y)
  have he := D.finite_period_translate s y q hq
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) 1
  have hu : Function.update y i
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) (y i)) =
      Function.update x i
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) := by
    simp [y]
  change fourier R D.sources.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ (Function.update x i _)))) 1 =
      (localFiniteCharacter F q t : ℂ) * fourier R D.sources.dq (D.coreMap c) 1
  rw [← hu]
  unfold KPPGLLocalCover.N at he ⊢
  dsimp only [i] at hu ⊢
  rw [he, one_mul, finite_root_injection]
  letI := D.sources.quotientHaar
  have h := fourier_left_root D.sources.dq (D.coreMap c) (D.core_rational_root c)
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) 1 (D.toTensorHC.integrable c 1)
  have ht : adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) = localFiniteCharacter F q t :=
    (adelicTraceQuotientCharacter_mk F _).trans (adelicTraceCharacter_finite_single F q t)
  simpa only [ht, mul_one, c] using h

def finiteWhittaker (D : TensorActions R N) (q : KPFinitePlace F) :
    Submodule ℂ (actualLocal R D.finiteData (Sum.inr q) →ₗ[ℂ] ℂ) :=
  RootEquivariantMaps
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer)
    (KPLocalJacquetImage.root (D.finiteData q).inducing.borel)
    (finiteTrace (F := F) q).toMonoidHom ℂ

theorem sliceLine_le_finiteWhittaker (D : TensorActions R N) (q : KPFinitePlace F) :
    D.toTensorHC.sliceLine (Sum.inr q) ≤ D.finiteWhittaker q := by
  apply Submodule.span_le.mpr
  rintro l ⟨s, x, hq, rfl⟩
  intro t b
  have hroot : KPLocalJacquetImage.root (D.finiteData q).inducing.borel t =
      KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t.toAdd :=
    ((D.finiteData q).inducing.openCell (D.finiteData q).inducing.polarization).upper_eq t.toAdd
  rw [hroot]
  exact D.finite_slice_root s x q hq t.toAdd b

theorem finite_slice_rank_le_one_of_tame (D : TensorActions R N) (q : KPFinitePlace F)
    (ht : (3 : (ValuativeRel.valuation (q.adicCompletion F)).integer) ∉
      IsLocalRing.maximalIdeal (ValuativeRel.valuation (q.adicCompletion F)).integer) :
    Module.rank ℂ (D.toTensorHC.sliceLine (Sum.inr q)) ≤ 1 := by
  exact (Submodule.rank_mono (D.sliceLine_le_finiteWhittaker q)).trans
    (ExteriorWhittakerValues.ActualWhittaker.rank_le_one F R.A.zeta12 R.A.primitive_zeta12
      q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer ht
      (finiteTrace (F := F) q) (finiteTrace_ne_one q))

end TensorActions
end DedekindZetaZeroFree.FourierContinuation

end
