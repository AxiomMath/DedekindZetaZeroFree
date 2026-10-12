module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.RestrictedEvaluationCompactBounds
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.CoreCompactCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open NumberField IsDedekindDomain MomentSources KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
open KPGlobalResidualConstruction LiteralSource TensorActionSource ThetaExpansion KPLiteralRaw
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming pureComponent → pureComponent
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming exists_pure_product_level → exists_pure_product_level
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming pure_raw_fixed → pure_raw_fixed
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000

 theorem source_slot_uniform_level
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀ j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (v : complexCore) g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        quotientCoreEvaluator R.A P C (restrictedSlotTensor R.A P C s x w hw v) (g*u) =
          quotientCoreEvaluator R.A P C (restrictedSlotTensor R.A P C s x w hw v) g := by
  obtain ⟨D,hD⟩ := exists_pure_product_level R.A P C s x
  have hc := ActualFiniteFactor.productSubgroup_compact_open F ζ hζ D
  rw [EisensteinReferenceSections.SourceLevels.finite_eq F ζ hζ] at hc
  let J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨⟨(ActualFiniteFactor.productSubgroup F ζ hζ D).comap
      (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype,hc.2⟩,hc.1⟩
  refine ⟨J,?_⟩
  intro v g j hj
  obtain ⟨u,hu,heu⟩ := hj
  obtain ⟨raw,hr,he⟩ := hu
  have hj' : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = j := he.trans heu
  rw [← hj']
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreValue R.A P C (restrictedSlotTensor R.A P C s x w hw v)
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) *
          scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)) = _
      rw [← map_mul, ← map_mul, quotientCoreValue_raw]
      change rawCoreInsertion R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
        (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ (harmonicInverse v)))) (g*raw) = _
      apply pure_raw_fixed R.A P C s _ g raw hr.1
      intro q
      have hp : pureComponent R.A P C s
          (Function.update x ⟨Sum.inl w,hw⟩ (harmonicInverse v)) (.inr q) =
            pureComponent R.A P C s x (.inr q) := by
        unfold pureComponent
        split_ifs
        · exact Function.update_of_ne (by intro h; cases congrArg Subtype.val h) _ _
        · rfl
      rw [hp,map_mul]
      exact hD q ⟨_,Subgroup.mem_iInf.mp hr.2 q⟩ _

private theorem core_residue_right_fixed
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C))
    (u : Group R)
    (hf : ∀ z g, (coreFlatInsertion R P C x).val z (g*u) = (coreFlatInsertion R P C x).val z g)
    (g : Group R) : coreResidue R P C x (g*u) = coreResidue R P C x g := by
  let A := ownedLiteralResidueFamily (full_product_compact_iwasawa R)
  have ht := literal_cleared_finite_transfer A.E A.cleared A.germ
    (fun f g => (A.normal f g).meromorphicOn) (coreFlatInsertion R P C x)
    (fun _ : Fin 1 => coreFlatInsertion R P C x)
    (fun _ _ => (1 : ℂ)) (fun _ => analyticOnNhd_const) u
    (by
      intro z hz a
      simp only [Fin.sum_univ_one,one_mul]
      exact (A.germ.1 _ z hz (a*u)).trans ((show
        KPLiteralRaw.eisenstein F ζ hζ (fullProductCompact R) (coreFlatInsertion R P C x) z (a*u) =
          KPLiteralRaw.eisenstein F ζ hζ (fullProductCompact R) (coreFlatInsertion R P C x) z a from by
            unfold KPLiteralRaw.eisenstein
            simp only [← mul_assoc,hf]).trans (A.germ.1 _ z hz a).symm)) g
  rw [coreResidue_eq_owned_cleared]
  simpa only [Fin.sum_univ_one,one_mul] using ht

theorem restrictedSlot_uniform_residue_level
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀ j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (v : complexCore) g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) (g*u) =
          coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g := by
  obtain ⟨J,hJ⟩ := source_slot_uniform_level R P C s x w hw
  let L := EisensteinReferenceSections.SourceLevels.level F ζ hζ P C
  let U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨J.toOpenSubgroup ⊓ L.toOpenSubgroup,J.isCompact.inter_right L.toOpenSubgroup.isClosed⟩
  refine ⟨U,?_⟩
  intro v g u hu
  have huJ : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J :=
    Subgroup.map_mono inf_le_left hu
  have huL : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ L :=
    Subgroup.map_mono inf_le_right hu
  have huK : u ∈ fullProductCompact R := by
    rw [EisensteinReferenceSections.SourceLevels.globalLevel_eq] at huL
    exact EisensteinReferenceSections.SourceLevels.refined_compact_le R P C huL
  apply core_residue_right_fixed R P C _ u _ g
  intro z a
  change Complex.exp _ * quotientCoreEvaluator R.A P C _ (a*u) =
    Complex.exp _ * quotientCoreEvaluator R.A P C _ a
  rw [hJ v a u huJ, DedekindZetaZeroFree.FourierContinuation.LiteralSource.height_compact R a ⟨u,huK⟩]
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
