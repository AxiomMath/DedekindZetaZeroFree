module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RationalFibers.FiniteStageParameterKernel

@[expose] public section

noncomputable section
open scoped Classical NumberField Matrix
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages KPLocalPrincipalSeries KPLocalExceptionalConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

private theorem canonical_projection (q : KPFinitePlace F)
    (g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :
    (C.canonical q).borel.projection g =
      KPLocalSmoothRepresentation.projection F R.A.zeta12 R.A.primitive_zeta12 q g := by
  induction g using QuotientGroup.induction_on with
  | _ g => exact ((C.canonical q).openCell (C.polarization q)).projection_eq g

theorem canonical_borel_ratio (q : KPFinitePlace F) (b : (C.canonical q).borel.B)
    (hb : (b : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) ∈
      KPLocalSmoothRepresentation.Borel F R.A.zeta12 R.A.primitive_zeta12 q) :
    (C.canonical q).borel.coordinate ((C.canonical q).borel.retract b) =
      KPRankOneInduction.borelRatio F q
        ⟨KPLocalSmoothRepresentation.projection F R.A.zeta12 R.A.primitive_zeta12 q b, hb⟩ := by
  let B := C.canonical q
  let r := (KPRankOneInduction.borelRatio F q).comp
    ((KPRankOneInduction.borelProjection F q
      (KPLocalSmoothRepresentation.projection F R.A.zeta12 R.A.primitive_zeta12 q)).comp
      { toFun := fun b : B.borel.B =>
          (⟨b.val, by
            change b.val ∈ actualBorel F R.A.zeta12 R.A.primitive_zeta12 q
            rw [← B.borel_eq]
            exact b.property⟩ :
            KPLocalSmoothRepresentation.Borel F R.A.zeta12 R.A.primitive_zeta12 q)
        map_one' := rfl
        map_mul' := fun _ _ => rfl })
  have ht (t : actualTorus F R.A.zeta12 R.A.primitive_zeta12 q) :
      r (B.borel.torus t) = B.borel.coordinate t := by
    apply Units.ext
    have hp := B.borel.torus_projection t
    rw [canonical_projection R P C] at hp
    dsimp only [r, MonoidHom.comp_apply]
    rw [KPRankOneInduction.borelRatio_eq F q _
      (KubotaRankTwo.d (LocalField F q) (B.borel.coordinate t) 1) hp.symm]
    · simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hn (x : Multiplicative (LocalField F q)) : r (B.borel.upperRoot x) = 1 := by
    apply Units.ext
    have hp := B.borel.upperRoot_projection x
    rw [canonical_projection R P C] at hp
    dsimp only [r, MonoidHom.comp_apply]
    rw [KPRankOneInduction.borelRatio_eq F q _
      (KubotaRankTwo.n (LocalField F q) x.toAdd) hp.symm]
    · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  change _ = r b
  obtain ⟨x, hx⟩ := B.borel.borel_decomposition b
  conv_rhs => rw [hx, map_mul, ht, hn, mul_one]

theorem fullCompact_exists (q : KPFinitePlace F) :
    ∃ J : IwasawaData (C.canonical q).borel,
      (J.compact.toOpenSubgroup : Subgroup (ActualCover F R.A.zeta12 R.A.primitive_zeta12 q)) =
        KPRankOneCartanGeometry.coveredK0 F R.A.zeta12 R.A.primitive_zeta12 q := by
  obtain ⟨J, hJ⟩ := ActualFiniteBorel.actual_compact_iwasawa F R.A.zeta12 R.A.primitive_zeta12 q
    (ActualFiniteBorel.chartDepth F R.A.zeta12 R.A.primitive_zeta12 q)
    (ActualFiniteBorel.chartDepth_admissible F R.A.zeta12 R.A.primitive_zeta12 q)
    (C.canonical q).heisenberg (C.canonical q).borel (C.canonical q).borel_eq
    (canonical_borel_ratio R P C q)
  exact ⟨J, by rw [hJ]; rfl⟩

def fullCompact (q : KPFinitePlace F) : IwasawaData (C.canonical q).borel :=
  (fullCompact_exists R P C q).choose

theorem fullCompact_eq (q : KPFinitePlace F) :
    ((fullCompact R P C q).compact.toOpenSubgroup :
      Subgroup (ActualCover F R.A.zeta12 R.A.primitive_zeta12 q)) =
        KPRankOneCartanGeometry.coveredK0 F R.A.zeta12 R.A.primitive_zeta12 q :=
  (fullCompact_exists R P C q).choose_spec

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
