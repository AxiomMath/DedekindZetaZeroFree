module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarSections.FlatInsertion
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CompactModels.ExponentialPolynomialCorrection

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPAdelicCoverRestrictedProduct
open ThetaExpansion MomentSources
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem canonical_projection (q : KPFinitePlace F) (g : ActualCover F ζ hζ q) :
    (C.canonical q).borel.projection g = KPLocalSmoothRepresentation.projection F ζ hζ q g := by
  induction g using QuotientGroup.induction_on with
  | H g => exact ((C.canonical q).openCell (C.polarization q)).projection_eq g

theorem finite_borel_ratio (q : KPFinitePlace F) (b : (C.canonical q).borel.B)
    (hb : b.val ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q) :
    (C.canonical q).borel.coordinate ((C.canonical q).borel.retract b) =
      KPRankOneInduction.borelRatio F q
        ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b,hb⟩ := by
  let T := C.canonical q
  let r := (KPRankOneInduction.borelRatio F q).comp
    ((KPRankOneInduction.borelProjection F q (KPLocalSmoothRepresentation.projection F ζ hζ q)).comp
      { toFun := fun b : T.borel.B => (⟨b.val, by
          change b.val ∈ actualBorel F ζ hζ q
          rw [← T.borel_eq]
          exact b.property⟩ : KPLocalSmoothRepresentation.Borel F ζ hζ q)
        map_one' := rfl
        map_mul' := fun _ _ => rfl })
  have ht (t : actualTorus F ζ hζ q) : r (T.borel.torus t) = T.borel.coordinate t := by
    apply Units.ext
    have hp := T.borel.torus_projection t
    rw [canonical_projection R P C] at hp
    dsimp only [r, MonoidHom.comp_apply]
    rw [KPRankOneInduction.borelRatio_eq F q _
      (KubotaRankTwo.d (LocalField F q) (T.borel.coordinate t) 1) hp.symm]
    · simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hn (x : Multiplicative (LocalField F q)) : r (T.borel.upperRoot x) = 1 := by
    apply Units.ext
    have hp := T.borel.upperRoot_projection x
    rw [canonical_projection R P C] at hp
    dsimp only [r, MonoidHom.comp_apply]
    rw [KPRankOneInduction.borelRatio_eq F q _ (KubotaRankTwo.n (LocalField F q) x.toAdd) hp.symm]
    · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  change _ = r b
  obtain ⟨x,hx⟩ := T.borel.borel_decomposition b
  conv_rhs => rw [hx,map_mul,ht,hn,mul_one]

def finiteIntegralIwasawa (q : KPFinitePlace F) : IwasawaData (C.canonical q).borel :=
  (ActualFiniteBorel.actual_compact_iwasawa F ζ hζ q
    (ActualFiniteBorel.chartDepth F ζ hζ q) (ActualFiniteBorel.chartDepth_admissible F ζ hζ q)
    (C.canonical q).heisenberg (C.canonical q).borel (C.canonical q).borel_eq
    (finite_borel_ratio R P C q)).choose

theorem finiteIntegralIwasawa_compact (q : KPFinitePlace F) :
    ((finiteIntegralIwasawa R P C q).compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) =
      KPRankOneCartanGeometry.coveredK0 F ζ hζ q := by
  have hJ := (ActualFiniteBorel.actual_compact_iwasawa F ζ hζ q
    (ActualFiniteBorel.chartDepth F ζ hζ q) (ActualFiniteBorel.chartDepth_admissible F ζ hζ q)
    (C.canonical q).heisenberg (C.canonical q).borel (C.canonical q).borel_eq
    (finite_borel_ratio R P C q)).choose_spec
  change (finiteIntegralIwasawa R P C q).compact = _ at hJ
  rw [hJ]
  rfl

theorem finiteMax_mem_integral (q : KPFinitePlace F)
    (k : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (hk : k ∈ iwasawaCompactFactor R (Sum.inr q)) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) k ∈
      (finiteIntegralIwasawa R P C q).compact.toOpenSubgroup := by
  change _ ∈ (finiteIntegralIwasawa R P C q).compact.toOpenSubgroup.toSubgroup
  rw [finiteIntegralIwasawa_compact]
  apply (PrincipalOfKP.integralRawCompact_projection F ζ hζ q ▸
    Subgroup.mem_map.mpr ?_)
  refine ⟨k, ?_, rfl⟩
  by_cases hb : Bad F q
  · simpa only [iwasawaCompactFactor, if_pos hb, integralRawCompact,
      PrincipalOfKP.integralRawCompact] using hk
  · apply PrincipalOfKP.finiteCompact_le_integralRawCompact F ζ hζ q
    simpa only [iwasawaCompactFactor, if_neg hb] using hk

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
