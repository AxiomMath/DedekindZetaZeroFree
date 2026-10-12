module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.FinitePlaceActions
public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.QuotientCompactCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages ThetaExpansion MomentSources TensorActionSource KPLiteralRaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem coreFlatInsertion_compact (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C))
    (z : ℂ) (g : Group R) :
    (coreFlatInsertion R P C (coreCompactSlot R.A P C w k x)).val z g =
      (coreFlatInsertion R P C x).val z
        (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) := by
  change Complex.exp _ * quotientCoreEvaluator R.A P C (coreCompactSlot R.A P C w k x) g =
    Complex.exp _ * quotientCoreEvaluator R.A P C x _
  rw [quotientCoreEvaluator_compact]
  have hh := height_compact R g
    ⟨KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k,
      (full_product_compact_iwasawa R).2.2 w k⟩
  rw [hh]

def coreResidueOfFamily
    (E NN : Flat F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) → ℂ → Functions R)
    (hg : ExceptionalGerm F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) E NN)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain) :
    RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) →ₗ[ℂ] Functions R :=
  (literalFlatResidue (full_product_compact_iwasawa R) E NN hg hm).comp (coreFlatInsertion R P C)

theorem coreResidueOfFamily_compact
    (E NN : Flat F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) → ℂ → Functions R)
    (hg : ExceptionalGerm F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) E NN)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain)
    (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C))
    (g : Group R) :
    coreResidueOfFamily R P C E NN hg hm (coreCompactSlot R.A P C w k x) g =
      coreResidueOfFamily R P C E NN hg hm x
        (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) := by
  have ht := literal_cleared_finite_transfer E NN hg hm
    (coreFlatInsertion R P C x)
    (fun _ : Fin 1 => coreFlatInsertion R P C (coreCompactSlot R.A P C w k x))
    (fun _ _ => (1 : ℂ)) (fun _ => analyticOnNhd_const)
    (KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)
    (by
      intro z hz a
      simp only [Fin.sum_univ_one, one_mul]
      rw [hg.1 _ z hz, hg.1 _ z hz]
      unfold eisenstein
      simp only [← mul_assoc, ← coreFlatInsertion_compact R P C w k x]) g
  change NN (coreFlatInsertion R P C (coreCompactSlot R.A P C w k x)) 0 g =
    NN (coreFlatInsertion R P C x) 0 _
  simpa only [Fin.sum_univ_one, one_mul] using ht.symm

theorem coreResidue_eq_owned_cleared
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)) :
    coreResidue R P C x =
      (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared
        (asLiteralFlat (coreFlatInsertion R P C x)) 0 := by
  change (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).residue
    (literalZeroProfileEquiv (full_product_compact_iwasawa R) (coreFlatInsertion R P C x)) = _
  exact LiteralResidueFamily.residue_flat _ _

theorem coreResidue_eq_ofFamily :
    coreResidue R P C = coreResidueOfFamily R P C
      (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).E
      (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).cleared
      (ownedLiteralResidueFamily (full_product_compact_iwasawa R)).germ
      (fun f g => ((ownedLiteralResidueFamily (full_product_compact_iwasawa R)).normal f g).meromorphicOn) := by
  apply LinearMap.ext
  intro x
  funext g
  exact congrFun (coreResidue_eq_owned_cleared R P C x) g

theorem coreResidue_compact (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C))
    (g : Group R) :
    coreResidue R P C (coreCompactSlot R.A P C w k x) g =
      coreResidue R P C x
        (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) := by
  rw [coreResidue_eq_ofFamily]
  exact coreResidueOfFamily_compact R P C _ _ _ _ w k x g

theorem coreResidue_stage_compact (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (hw : Sum.inl w ∈ s.val)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) (g : Group R) :
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ (plusReference R.A P C)
      (bad R.A P C) s (compactSlot R.A P C s.val w hw k x)) g =
    coreResidue R P C (RestrictedTensorSimple.stageInclusion _ (plusReference R.A P C)
      (bad R.A P C) s x)
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) := by
  have h := coreResidue_compact R P C w k
    (RestrictedTensorSimple.stageInclusion _ (plusReference R.A P C) (bad R.A P C) s x) g
  rw [coreCompactSlot_stage] at h
  exact h

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
