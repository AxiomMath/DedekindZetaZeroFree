module

public import DedekindZetaZeroFree.Theta.Unfolding.FactorizationAndMellinNormalizationData
public import DedekindZetaZeroFree.Theta.Whittaker.SphericalCRTProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency true
open scoped NumberField Classical
namespace DedekindZetaZeroFree.ExteriorWhittakerValues
open NumberField IsDedekindDomain ValuativeRel
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : MomentSources.AdmissibleFlatSources R} {T : MomentSources.Realization R Q}

theorem exterior_good_six (p : ThetaBranch.ExteriorPrime R.A) :
    valuation (p.val.adicCompletion F) (6 : p.val.adicCompletion F) = 1 :=
  (KPHilbert.tame_place_iff F p.val).mpr
    (fun h => p.property (R.A.above_six p.val h))

theorem exterior_not_bad (p : ThetaBranch.ExteriorPrime R.A) :
    ¬ KPAdelicCoverRestrictedProduct.Bad F p.val := by
  have hu : IsUnit (6 : KPTameCompact.O F p.val) :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (p.val.adicCompletion F)))).mpr
      (by rw [map_ofNat]; exact exterior_good_six p)
  letI : Nontrivial (KPTameCompact.O F p.val ⧸ KPTameCompact.p F p.val) := by
    change Nontrivial (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer)
    infer_instance
  intro h
  have hz : (6 : KPTameCompact.O F p.val ⧸ KPTameCompact.p F p.val) = 0 := by
    apply (ringChar.spec _ 6).mpr
    rcases h with h | h <;> rw [h] <;> norm_num
  have hh := hu.map (Ideal.Quotient.mk (KPTameCompact.p F p.val))
  rw [map_ofNat, hz] at hh
  exact not_isUnit_zero hh

theorem exterior_unit_diagonal_mem (p : ThetaBranch.ExteriorPrime R.A)
    (u : KPHilbert.LocalIntegerUnits F p.val) :
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPHilbert.integerUnitInclusion F p.val u) ∈
        KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr p.val) := by
  have hn := exterior_not_bad p
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12
    R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hn]
  refine ⟨KPStandardLocalRootLifts.integralA F p.val u, ?_⟩
  exact (KPStandardLocalRootLifts.A_eq_compact F R.A.zeta12
    R.A.primitive_zeta12 p.val (fun h => hn (Or.inr h)) u).symm

theorem exterior_reference_unit_fixed (D : MomentSources.SourceFactorization R Q T)
    (p : ThetaBranch.ExteriorPrime R.A) (u : KPHilbert.LocalIntegerUnits F p.val) :
    KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
      (D.finiteData p.val).inducing.polarization (D.finiteData p.val).haar
      (D.finiteData p.val).haar_integer
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (KPHilbert.integerUnitInclusion F p.val u)) (D.references (Sum.inr p.val)) =
      D.references (Sum.inr p.val) :=
  (D.spherical_reference p.val p.property).2 _ (exterior_unit_diagonal_mem p u)

private theorem representation_unit_covariance {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (ell : V →ₗ[ℂ] ℂ) (v : V) (x y xy z : G) (c : ℂ)
    (hxy : x * y = z * xy) (hg : ∀ w, ρ z w = c • w)
    (hy : ρ y v = v) (a : ℂˣ) (e : ℤ) (hc : c = (a : ℂ) ^ (-2 * e)) :
    ell (ρ xy v) = (a : ℂ) ^ (2 * e) * ell (ρ x v) := by
  have hm := congrArg (fun g => ρ g v) hxy
  simp only [map_mul, Module.End.mul_apply, hy, hg] at hm
  have hh := congrArg ell hm
  simp only [map_smul, smul_eq_mul] at hh
  rw [hc] at hh
  rw [hh, ← mul_assoc, ← zpow_add₀ a.ne_zero]
  simp

theorem exterior_unit_covariance (D : MomentSources.SourceFactorization R Q T)
    (p : ThetaBranch.ExteriorPrime R.A) (π : (p.val.adicCompletion F)ˣ)
    (hπ : KPHilbert.ordinaryValuation F p.val π = 1)
    (e : ℤ) (u : KPHilbert.LocalIntegerUnits F p.val) :
    let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
      (D.finiteData p.val).inducing.polarization (D.finiteData p.val).haar
      (D.finiteData p.val).haar_integer
    D.ell (Sum.inr p.val) (ρ
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (π ^ e * KPHilbert.integerUnitInclusion F p.val u)) (D.references (Sum.inr p.val))) =
      (KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12
        (KPHilbert.residueSixCharacter F p.val R.A.zeta12 R.A.primitive_zeta12
          (exterior_good_six p) u) : ℂ) ^ (2 * e) *
      D.ell (Sum.inr p.val) (ρ
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (π ^ e))
        (D.references (Sum.inr p.val))) := by
  dsimp only
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
    R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
    (D.finiteData p.val).inducing.polarization (D.finiteData p.val).haar
    (D.finiteData p.val).haar_integer
  let a : ℂˣ := KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12
    (KPHilbert.residueSixCharacter F p.val R.A.zeta12 R.A.primitive_zeta12
      (exterior_good_six p) u)
  have hc : KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr p.val) (π ^ e) (KPHilbert.integerUnitInclusion F p.val u) =
        (a : ℂ) ^ (-2 * e) := by
    have hh := KPSourceConvention.sourceC_valuation_units F R.A.zeta12
      R.A.primitive_zeta12 p.val (exterior_good_six p) π hπ 1 u e 0
    simpa [a, KPHilbert.integerUnitInclusion] using hh
  apply representation_unit_covariance ρ (D.ell (Sum.inr p.val))
    (D.references (Sum.inr p.val))
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (π ^ e))
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPHilbert.integerUnitInclusion F p.val u))
    _ _ _ (KPPGLLocalCover.A_mul F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (π ^ e) (KPHilbert.integerUnitInclusion F p.val u))
    (KPRankOneShellRepair.actualCanonicalImage_ordinary_genuine F R.A.zeta12
      R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
      (D.finiteData p.val).inducing.polarization (D.finiteData p.val).haar
      (D.finiteData p.val).haar_integer _)
    (exterior_reference_unit_fixed D p u) a e hc

end DedekindZetaZeroFree.ExteriorWhittakerValues

end
