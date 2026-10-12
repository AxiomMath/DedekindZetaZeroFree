module

public import DedekindZetaZeroFree.Metaplectic.Iwasawa.FiniteIntegralDecomposition

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPAdelicCoverRestrictedProduct
open ThetaExpansion MomentSources
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open _root_.DedekindZetaZeroFree.KPLocalTameValuationWhittakerBasis.RawSectionBridge renaming localAbs_norm → localAbs_norm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem raw_projected (raw : Raw R.A) :
    pglProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)) =
      QuotientGroup.mk' (scalarSubgroup F) (restrictedProjection F ζ hζ raw) := by
  simp only [pglProjection, scalarQuotient, projection_amalgamation,
    QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.comp_apply]

theorem raw_borel_upper (raw : Raw R.A)
    (hb : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) ∈ KPGlobalTorusFunctionData.borel F ζ hζ) :
    (restrictedProjection F ζ hζ raw) 1 0 = 0 := by
  obtain ⟨B,hB,hB10⟩ := hb
  have he : QuotientGroup.mk' (scalarSubgroup F) (restrictedProjection F ζ hζ raw) =
      QuotientGroup.mk' (scalarSubgroup F) B := by rw [← raw_projected, hB]
  obtain ⟨z,hz,hzA⟩ := (QuotientGroup.mk'_eq_mk' (N := scalarSubgroup F)).mp he
  obtain ⟨s,rfl⟩ := hz
  have h := congrArg (fun M : AdelicGL2 F => M 1 0) hzA
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
    hB10, mul_zero, add_zero, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h
  exact (IsUnit.mul_left_eq_zero ⟨s,rfl⟩).mp h

theorem raw_upperRatio_eval (raw : Raw R.A)
    (hu : (restrictedProjection F ζ hζ raw) 1 0 = 0) (v : KPHilbert.Place F) :
    (KPGlobalCubicIdelePairing.ideleEval F v
      (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
        (restrictedProjection F ζ hζ raw) hu) : KPHilbert.Completion F v) =
      (raw v).g 0 0 / (raw v).g 1 1 := by
  let A := restrictedProjection F ζ hζ raw
  have hentry (i j : Fin 2) : adeleEval F v (A i j) = (raw v).g i j := by
    have h := restrictedProjection_eval F ζ hζ raw v
    have he := congrArg (fun M : KPLocalCover.LocalGL2 F v => M i j) h
    simpa only [A, matrixEval, Matrix.GeneralLinearGroup.map_apply, KPLocalCover.projection_apply] using he
  change ((Units.map (adeleEval F v).toMonoidHom)
    (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F A hu) : KPHilbert.Completion F v) = _
  unfold KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio
  rw [map_mul,map_inv,Units.val_mul,Units.val_inv_eq_inv_val]
  simp only [Units.coe_map,IsUnit.unit_spec]
  change adeleEval F v (A 0 0) * (adeleEval F v (A 1 1))⁻¹ = _
  exact (congrArg₂ (fun a b : KPHilbert.Completion F v => a*b⁻¹)
    (hentry 0 0) (hentry 1 1)).trans (div_eq_mul_inv _ _).symm

 theorem raw_upper_eval (raw : Raw R.A)
    (hu : (restrictedProjection F ζ hζ raw) 1 0 = 0) (v : KPHilbert.Place F) :
    (raw v).g 1 0 = 0 := by
  have h := restrictedProjection_eval F ζ hζ raw v
  have he := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 1 0) h
  change adeleEval F v ((restrictedProjection F ζ hζ raw) 1 0) = (raw v).g 1 0 at he
  rw [hu,map_zero] at he
  exact he.symm

theorem finite_borel_forwardAbs (q : KPFinitePlace F) (J : IwasawaData (C.canonical q).borel)
    (raw : Raw R.A) (hu : (restrictedProjection F ζ hζ raw) 1 0 = 0) :
    LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q) J
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) =
      ((KPGlobalCenterRationalCharacterModulus.localAbsUnit F (Sum.inr q)
        (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q)
          (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
            (restrictedProjection F ζ hζ raw) hu)) : NNReal) : ℝ) := by
  have hb : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)) ∈
      (C.canonical q).borel.B := by
    rw [(C.canonical q).borel_eq]
    exact ⟨(raw (Sum.inr q)).g,rfl,raw_upper_eval R raw hu (Sum.inr q)⟩
  let b : (C.canonical q).borel.B := ⟨_,hb⟩
  have hmem : b.val ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q := by
    change b.val ∈ actualBorel F ζ hζ q
    rw [← (C.canonical q).borel_eq]
    exact b.property
  have hc : (C.canonical q).borel.coordinate ((C.canonical q).borel.retract b) =
      KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q)
        (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
          (restrictedProjection F ζ hζ raw) hu) := by
    rw [finite_borel_ratio R P C q b hmem]
    apply Units.ext
    rw [raw_upperRatio_eval]
    exact KPRankOneInduction.borelRatio_eq F q _ (raw (Sum.inr q)).g rfl
      (raw_upper_eval R raw hu (Sum.inr q))
  have hf := LocalCompactChange.forwardAbs_factorization F ζ hζ q (C.canonical q) J b
    (1 : J.compact.toOpenSubgroup)
  simp only [Subgroup.coe_one,mul_one] at hf
  rw [hf,hc,localAbs_norm F q]
  rfl

theorem raw_borel_norm_product (raw : Raw R.A)
    (hb : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) ∈ KPGlobalTorusFunctionData.borel F ζ hζ) :
    let hu := raw_borel_upper R raw hb
    let u := KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
      (restrictedProjection F ζ hζ raw) hu
    Function.HasFiniteMulSupport (fun v => KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
      (KPGlobalCubicIdelePairing.ideleEval F v u)) ∧
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (fullProductIwasawaData R)
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)) =
      ∏ᶠ v, KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
        (KPGlobalCubicIdelePairing.ideleEval F v u) := by
  dsimp only
  let g := scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)
  let hu := raw_borel_upper R raw hb
  let u := KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F (restrictedProjection F ζ hζ raw) hu
  obtain ⟨t,x,ht⟩ := KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization F ζ hζ ⟨g,hb⟩
  have hr : u = KPGlobalTorusFunctionData.p F ζ hζ t := by
    apply KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio_torus_root F ζ hζ t x
    rw [← ht]
    exact (raw_projected R raw).symm
  have hp := KPGlobalCenterRationalCharacterModulus.idele_abs_finite_product F
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) hζ) u
  refine ⟨hp.1,?_⟩
  rw [hp.2,hr]
  have hn := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ (fullProductIwasawaData R) t x
    (1 : (fullProductIwasawaData R).K)
  simpa only [Subgroup.coe_one,mul_one,← ht,KPGlobalTorusFunctionData.delta,MonoidHom.comp_apply] using hn

theorem height_raw_borel_finsum (raw : Raw R.A)
    (hb : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) ∈ KPGlobalTorusFunctionData.borel F ζ hζ) :
    let hu := raw_borel_upper R raw hb
    let u := KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F (restrictedProjection F ζ hζ raw) hu
    iwasawaLogHeight R (scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)) =
      ∑ᶠ v, Real.log ((KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
        (KPGlobalCubicIdelePairing.ideleEval F v u) : NNReal) : ℝ) := by
  dsimp only
  unfold iwasawaLogHeight
  rw [(raw_borel_norm_product R raw hb).2]
  have hc := MonoidHom.map_finprod (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom NNReal))
    (raw_borel_norm_product R raw hb).1
  let f v := KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
    (KPGlobalCubicIdelePairing.ideleEval F v
      (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
        (restrictedProjection F ζ hζ raw) (raw_borel_upper R raw hb)))
  change (((∏ᶠ v, f v : NNRealˣ) : NNReal) : ℝ) =
    ∏ᶠ v, (((f v : NNRealˣ) : NNReal) : ℝ) at hc
  change Real.log (((∏ᶠ v, f v : NNRealˣ) : NNReal) : ℝ) = _
  rw [hc]
  apply Real.log_finprod
  intro v
  exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
