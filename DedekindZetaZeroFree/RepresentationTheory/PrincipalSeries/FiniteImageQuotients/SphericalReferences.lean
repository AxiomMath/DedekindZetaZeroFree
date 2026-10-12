module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.FiniteImageQuotients.ActionCovariance
public import DedekindZetaZeroFree.Algebra.Fields.NaturalInverseNonvanishing
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.NonzeroIntegralCoordinate
public import DedekindZetaZeroFree.Theta.Whittaker.UnitDiagonalCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPRankOneShellRepair
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPExceptionalRaw.FiniteSource.GoodSphericalVector
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming normalized_reference → normalized_reference
open _root_.DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector renaming spherical_integrand_on_integer_ring → spherical_integrand_on_integer_ring
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem finite_spherical_forward_coordinate (q : KPFinitePlace F)
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hgood : valuation (LocalField F q) (6 : LocalField F q) = 1)
    (f : Plus R.A P C (Sum.inr q))
    (hf : ∀ k : KPTameCompact.K0 F q,
      IPlus (C.canonical q).borel (C.polarization q)
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (t : actualTorus F ζ hζ q) :
    ((actualCanonicalForwardMap F ζ hζ q (C.canonical q) (C.polarization q) (μ q) (hμ q) f).val 1).val t =
      (1 + (residueCardinality (LocalField F q) : ℂ)⁻¹) * (f.val 1).val t := by
  let S₀ := actualRawInducing F ζ hζ q (C.canonical q)
  rw [actualCanonicalForwardMap_eq_integral]
  simp only [mul_one]
  apply integral_eq_integer_ball_of_cubic_shells
  · simpa only [mul_one] using actualCanonicalForwardMap_integrable F ζ hζ q
      (C.canonical q) (C.polarization q) (μ q) (hμ q) f 1 t
  · calc
      _ = ∫ x in ((valuation (LocalField F q)).integer : Set (LocalField F q)),
          (f.val 1).val t ∂μ q := by
        apply setIntegral_congr_fun
          (IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1).measurableSet
        intro x hx
        exact congrArg (fun u : InducedModule (C.polarization q) => u.val t)
          (spherical_integrand_on_integer_ring F ζ hζ q S₀ ht (C.polarization q) f hf ⟨x,hx⟩)
      _ = _ := by simp [hμ, Measure.real]
  · intro n
    exact actual_compact_spherical_negative_shell_coordinate F ζ hζ q S₀ (μ q) (hμ q)
      ht hgood (C.polarization q) f hf n t

theorem finiteQuotientReference_one (q : KPFinitePlace F) (hq : q ∉ C.exceptional)
    (hgood : valuation (LocalField F q) (6 : LocalField F q) = 1) :
    (finiteQuotientReference R P C μ hμ (Sum.inr q)).val.val 1 =
      (1 + (residueCardinality (LocalField F q) : ℂ)⁻¹) •
        localReference F ζ hζ P C q := by
  let ht := (C.actual_compact q hq).choose
  have hfixed (k : KPTameCompact.K0 F q) :
      IPlus (C.canonical q).borel (C.polarization q)
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k)
        (plusReference R.A P C (Sum.inr q)) = plusReference R.A P C (Sum.inr q) := by
    have hk : actualGoodCompactSplit F ζ hζ q ht k ∈
        (C.canonical q).iwasawa.compact.toOpenSubgroup := by
      change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup :
        Subgroup (ActualCover F ζ hζ q))
      have hm : actualGoodCompactSplit F ζ hζ q ht k ∈
          (actualGoodCompactSplit F ζ hζ q ht).range := MonoidHom.mem_range.mpr ⟨k,rfl⟩
      exact Eq.mpr (congrArg (fun K : Subgroup (ActualCover F ζ hζ q) =>
        actualGoodCompactSplit F ζ hζ q ht k ∈ K) (C.actual_compact q hq).choose_spec) hm
    exact plusReference_fixed R.A P C q hq ⟨_,hk⟩
  apply Subtype.ext
  funext t
  change ((actualCanonicalForwardMap F ζ hζ q (C.canonical q) (C.polarization q)
    (μ q) (hμ q) (plusReference R.A P C (Sum.inr q))).val 1).val t = _
  rw [finite_spherical_forward_coordinate R P C μ hμ q ht hgood _ hfixed]
  have hone : (plusReference R.A P C (Sum.inr q)).val 1 = localReference F ζ hζ P C q := by
    simp only [plusReference, dif_pos hq]
    exact (normalized_reference R.A P C q hq).choose_spec.2
  rw [hone]
  rfl

theorem finiteQuotientReference_ne_zero (hC : C.exceptional = R.A.Sf)
    (v : KPHilbert.Place F) (hv : v ∉ bad R.A P C) :
    finiteQuotientReference R P C μ hμ v ≠ 0 := by
  cases v with
  | inl w =>
    exact False.elim (hv (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
  | inr q =>
    have hq : q ∉ C.exceptional := by
      simpa only [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad,
        Finset.inr_mem_disjSum] using hv
    have hqS : q ∉ R.A.Sf := by simpa only [hC] using hq
    intro hz
    have h := congrArg (fun f : FiniteQuotientFiber R P C μ hμ (Sum.inr q) =>
      f.val.val 1) hz
    rw [finiteQuotientReference_one R P C μ hμ q hq (ExteriorWhittakerValues.exterior_good_six ⟨q,hqS⟩)] at h
    have hs := smul_eq_zero.mp h
    rcases hs with hs | hs
    · exact one_add_nat_inv_ne_zero _ hs
    · exact EisensteinReferenceSections.TorusReference.localReference_ne_zero F ζ hζ P C q hs

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
