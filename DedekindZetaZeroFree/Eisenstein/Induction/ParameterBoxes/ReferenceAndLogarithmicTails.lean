module

public import DedekindZetaZeroFree.Eisenstein.Induction.ParameterBoxes.CompactTailFactorization

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct KPLocalExceptionalConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def fullLevel (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q) :
    RestrictedTensorSimple.Level (bad R P C) :=
  ⟨(LiteralSource.cofactorSourceLevel R P C Q hQ).val, by
    rw [show bad R P C = LiteralSource.bad R.A P C from
      PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad F ζ hζ P C]
    exact (LiteralSource.cofactorSourceLevel R P C Q hQ).property⟩

theorem box_right_reference_tail
    (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (y : KPAdeles F) (hy : y ∈ TraceBox.adelicBox F Q) (a : FaithfulSource.RepairedInducing.Raw R)
    (ha : ∀ q, q ∉ Q → KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q)) ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup) :
    ∀ p, p ∉ (fullLevel R P C Q hQ).val →
      localValue R N P C p ((chamberRaw F ζ hζ y * a) p)
        (plusReference R N P C p) = reference R P C p := by
  intro p hp
  cases p with
  | inl w => exact False.elim (hp (by simp [fullLevel,LiteralSource.cofactorSourceLevel]))
  | inr q =>
    have hq : q ∉ Q := by simpa [fullLevel,LiteralSource.cofactorSourceLevel] using hp
    have hb : Sum.inr q ∉ bad R P C := fun h => hp ((fullLevel R P C Q hQ).property h)
    have h := exterior_parameter_compact R N P C q hb 0
      (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (chamberRaw F ζ hζ y (.inr q)))
      ⟨_,ha q hq⟩
    have hf0 : finiteParameterInput R N P C q (fullCompact R P C q) 0
        (plusReference R N P C (.inr q)) = plusReference R N P C (.inr q) := by
      apply Subtype.ext
      funext g
      simpa only [zero_mul,Complex.exp_zero,one_smul] using
        finiteParameterInput_displacement R N P C q (fullCompact R P C q) 0
          (plusReference R N P C (.inr q)) g
    rw [hf0] at h
    change (plusReference R N P C (.inr q)).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) ((chamberRaw F ζ hζ y * a) (.inr q))) = _
    simp only [RestrictedProduct.mul_apply,map_mul]
    exact h.trans (chamber_raw_tail R P C Q hQ y hy (.inr q) hp)

theorem box_right_log_tail
    (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (y : KPAdeles F) (hy : y ∈ TraceBox.adelicBox F Q) (a : FaithfulSource.RepairedInducing.Raw R)
    (ha : ∀ q, q ∉ Q → KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q)) ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup) :
    ∀ p, p ∉ (fullLevel R P C Q hQ).val → localLog R P C (chamberRaw F ζ hζ y * a) p = 0 := by
  intro p hp
  cases p with
  | inl w => exact False.elim (hp (by simp [fullLevel,LiteralSource.cofactorSourceLevel]))
  | inr q =>
    have hq : q ∉ Q := by simpa [fullLevel,LiteralSource.cofactorSourceLevel] using hp
    have hqC : q ∉ C.exceptional := fun h => hq (hQ h)
    have h := LocalCompactChange.forwardAbs_mul_compact F ζ hζ q (C.canonical q)
      (fullCompact R P C q)
      (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (chamberRaw F ζ hζ y (.inr q)))
      ⟨_,good_compact_le_full R P C q hqC (ha q hq)⟩
    simp only [localLog,RestrictedProduct.mul_apply,map_mul,h]
    exact chamber_log_tail R P C Q hQ y hy (.inr q) hp

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
