module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.RestrictedTensorInsertionBounds
public import DedekindZetaZeroFree.Moments.Reflected.SmoothEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (s : RestrictedTensorSimple.Level (bad R P C))
variable (x : ∀ j : s.val, Plus R N P C j.val)

def extendedQuotient (t : RestrictedTensorSimple.Level (bad R P C)) :
    ∀ j : t.val, actualLocal R (imageData R N P C) j.val := fun j =>
  sourceQuotient R (imageData R N P C) j.val
    (if h : j.val ∈ s.val then x ⟨j.val,h⟩ else plusReference R N P C j.val)

def sourceSlot (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (v : complexCore) :
    PlusCore R N P C :=
  RestrictedTensorSimple.stageInclusion _ _ _ s
    (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ (ComplexLines.harmonicInverse v)))

theorem extendedQuotient_update (t : RestrictedTensorSimple.Level (bad R P C))
    (hst : s ≤ t) (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (v : complexCore) :
    sourceStageQuotient R (imageData R N P C) t.val
      (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C) (bad R P C)
        s t hst (PiTensorProduct.tprod ℂ
          (Function.update x ⟨Sum.inl w,hw⟩ (ComplexLines.harmonicInverse v)))) =
      PiTensorProduct.tprod ℂ
        (Function.update (extendedQuotient R N P C s x t) ⟨Sum.inl w,hst hw⟩ v) := by
  rw [show RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s t hst = RestrictedTensorSimple.insert (Plus R N P C)
      (plusReference R N P C) s.val t.val hst from rfl]
  rw [RestrictedTensorSimple.insert_pure]
  simp only [sourceStageQuotient, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j.val = Sum.inl w
  · have hji : j = ⟨Sum.inl w,hst hw⟩ := Subtype.ext hj
    subst j
    simp only [dif_pos hw, Function.update_self]
    apply Subtype.ext
    exact ComplexLines.harmonicInverse_pin v
  · have hji : j ≠ (⟨Sum.inl w,hst hw⟩ : t.val) := fun h => hj (congrArg Subtype.val h)
    rw [Function.update_of_ne hji]
    unfold extendedQuotient
    split_ifs with hs
    · rw [Function.update_of_ne (show (⟨j.val,hs⟩ : s.val) ≠ ⟨Sum.inl w,hw⟩ from
        fun h => hj (congrArg Subtype.val h))]
    · rfl

theorem current_upper_residue_slot_bound
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (K : Set (Raw R)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (v : complexCore) (a : Raw R), a ∈ K →
        ‖∫ u : KPAdditiveQuotient F,
          LiteralSource.coreResidue R P C (coreEquiv R N P C (sourceSlot R N P C s x w hw v))
            (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) *
              KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
                (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ a))
          ∂KPWildKernelUpperBound.quotientHaar F‖ ≤
        B * (orders.sup (chartSeminorm negativeParameter)) v.val := by
  obtain ⟨E,hsE,hCE,hfactor⟩ := current_upper_residue_factorization R N P C  s K hK
  let t := fullLevel R P C E hCE
  have hst : s ≤ t := sourceStage_le_fullLevel R P C s E hCE hsE
  obtain ⟨orders,B,hB,hb⟩ := CurrentMinusSlot.reflected_update_compact_bound R N P C t
    (extendedQuotient R N P C s x t) w (hst hw) K hK
  let c : ℂ := KPGlobalFiniteSIntertwiner.residueNormalizer F  ζ hζ E *
    (arithmeticStageScale R t.val : ℂ)
  refine ⟨orders,(1+‖c‖₊)*B,by positivity,?_⟩
  intro v a ha
  have he := hfactor a ha (PiTensorProduct.tprod ℂ
    (Function.update x ⟨Sum.inl w,hw⟩ (ComplexLines.harmonicInverse v)))
  change ‖_‖ ≤ _
  rw [show (∫ u : KPAdditiveQuotient F,
    LiteralSource.coreResidue R P C (coreEquiv R N P C (sourceSlot R N P C s x w hw v))
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) *
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ a))
      ∂KPWildKernelUpperBound.quotientHaar F) = _ from he]
  rw [parameterStage_zero, extendedQuotient_update]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, norm_mul]
  have hh := mul_le_mul_of_nonneg_left (hb v a ha) (norm_nonneg c)
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, coe_nnnorm]
  exact hh.trans (by
    have hp := mul_nonneg B.coe_nonneg (apply_nonneg (orders.sup (chartSeminorm negativeParameter)) v.val)
    nlinarith only [hp])
end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
