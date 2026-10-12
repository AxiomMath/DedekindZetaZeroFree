module

public import DedekindZetaZeroFree.Theta.Profiles.ExteriorReferenceIdentities
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.ArchimedeanChamber
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residues.HeightStages
public import DedekindZetaZeroFree.Theta.Profiles.ExteriorTensorEulerEnlargement

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem integer_reference_value (q : KPFinitePlace F) (hq : q ∉ C.exceptional)
    (x : KPTameCompact.O F q) :
    localValue R.A P C (.inr q)
      (KPStandardLocalRootLifts.W F ζ hζ (.inr q) *
        KPStandardLocalRootLifts.N F ζ hζ (.inr q) (x : KPTameCompact.K F q))
      (plusReference R.A P C (.inr q)) = reference R.A P C (.inr q) := by
  rw [CurrentExteriorReference.plusReference_eq_exterior R.A P C q hq]
  have h := ExteriorTensorHaar.actual_unsigned_integer_tail F ζ hζ P C q hq 0 x
  simpa only [FiniteSourceTransport.parameterSource_zero, localValue, reference,
    KPGlobalResidualConstruction.ScalarAbsorption.fullReference] using h

theorem box_integer (Q : Finset (KPFinitePlace F))
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q)
    (q : KPFinitePlace F) (hq : q ∉ Q) : x.2 q ∈ KPTameCompact.O F q := by
  change x.2 ∈ Set.range (KPAdditiveHaar.chartMap F Q) at hx
  rw [KPAdditiveHaar.chartMap_range] at hx
  have hi := hx q hq
  let : (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (LocalField F q)) Valued.v).le_one_iff_le_one.mpr hi

theorem chamber_raw_tail (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q) :
    ∀ j, j ∉ (cofactorSourceLevel R P C Q hQ).val →
      localValue R.A P C j (chamberRaw F ζ hζ x j) (plusReference R.A P C j) =
        reference R.A P C j := by
  intro j hj
  cases j with
  | inl w => exact False.elim (hj (by simp [cofactorSourceLevel]))
  | inr q =>
    have hq : q ∉ Q := by simpa [cofactorSourceLevel] using hj
    have hi := box_integer Q x hx q hq
    have hh := integer_reference_value R P C q (fun h => hq (hQ h)) ⟨x.2 q, hi⟩
    simp only [chamberRaw, RestrictedProduct.mul_apply,
      KPRationalAdelicSplitting.WTuple_eval, KPGlobalTorusFunctionData.rootTuple,
      RestrictedProduct.mk_apply, KPAdelicCoverRestrictedProduct.adeleEval] at *
    exact hh

theorem chamber_log_tail (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q) :
    ∀ j, j ∉ (cofactorSourceLevel R P C Q hQ).val →
      FaithfulSource.RepairedInducing.localLog R P C (chamberRaw F ζ hζ x) j = 0 := by
  intro j hj
  cases j with
  | inl w => exact False.elim (hj (by simp [cofactorSourceLevel]))
  | inr q =>
    have hq : q ∉ Q := by simpa [cofactorSourceLevel] using hj
    have hexc : q ∉ C.exceptional := fun h => hq (hQ h)
    let xi : KPTameCompact.O F q := ⟨x.2 q, box_integer Q x hx q hq⟩
    have hc := ExteriorTensorHaar.unsigned_integer_chamber_mem F ζ hζ P C q hexc xi
    have hm := ExteriorVectorHaar.canonical_compact_le_full F ζ hζ P C q hexc hc
    have hm' : KPPGLLocalCover.coverQuotient F ζ hζ (.inr q)
        (KPStandardLocalRootLifts.W F ζ hζ (.inr q) *
          KPStandardLocalRootLifts.N F ζ hζ (.inr q) (xi : KPTameCompact.K F q)) ∈
        (FaithfulSource.RepairedInducing.fullCompact R P C q).compact.toOpenSubgroup := by
      change _ ∈ ((FaithfulSource.RepairedInducing.fullCompact R P C q).compact.toOpenSubgroup :
        Subgroup (ActualCover F ζ hζ q))
      rw [FaithfulSource.RepairedInducing.fullCompact_eq]
      simpa only [ActualFullCompactTransport.fullCompactIwasawa_compact] using hm
    have hn := LocalCompactChange.forwardAbs_compact F ζ hζ q (C.canonical q)
      (FaithfulSource.RepairedInducing.fullCompact R P C q) ⟨_, hm'⟩
    change Real.log _ = 0
    simp only [chamberRaw, RestrictedProduct.mul_apply,
      KPRationalAdelicSplitting.WTuple_eval, KPGlobalTorusFunctionData.rootTuple,
      RestrictedProduct.mk_apply, KPAdelicCoverRestrictedProduct.adeleEval]
    exact (congrArg Real.log hn).trans Real.log_one

theorem chamber_height_stage (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q) :
    ThetaExpansion.iwasawaLogHeight R
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (chamberRaw F ζ hζ x))) =
      ∑ j : (cofactorSourceLevel R P C Q hQ).val,
        FaithfulSource.RepairedInducing.localLog R P C (chamberRaw F ζ hζ x) j :=
  current_height_stage R P C _ _ (chamber_log_tail R P C Q hQ x hx)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
