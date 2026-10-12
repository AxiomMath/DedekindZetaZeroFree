module

public import DedekindZetaZeroFree.Metaplectic.Iwasawa.BorelNormProduct

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

def rawLocalLog (raw : Raw R.A) : KPHilbert.Place F → ℝ
  | Sum.inl w => 2 * Real.log (KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R.A w (raw (Sum.inl w))))
  | Sum.inr q => Real.log (LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q)
      (finiteIntegralIwasawa R P C q)
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))))

private theorem arch_upper_abs (raw : Raw R.A)
    (hu : (restrictedProjection F ζ hζ raw) 1 0 = 0) (w : InfinitePlace F) :
    ((KPGlobalCenterRationalCharacterModulus.localAbsUnit F (Sum.inl w)
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inl w)
        (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
          (restrictedProjection F ζ hζ raw) hu)) : NNReal) : ℝ) =
      (KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R.A w (raw (Sum.inl w)))) ^ 2 := by
  let E := InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)
  let g := complexMatrix R.A w (raw (Sum.inl w))
  have hn (z : w.Completion) : ‖E z‖ = ‖z‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (R.A.complex_place w)).isometry.norm_map_of_map_zero (map_zero E) z
  have h10 : g 1 0 = 0 := by
    change E ((raw (Sum.inl w)).g 1 0) = 0
    rw [raw_upper_eval R raw hu,map_zero]
  have hd : g 1 1 ≠ 0 := by
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
    simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using
      (right_ne_zero_of_mul (show g 0 0 * g 1 1 ≠ 0 by
        simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using hdet))
  change ‖(KPGlobalCubicIdelePairing.ideleEval F (Sum.inl w)
    (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
      (restrictedProjection F ζ hζ raw) hu) : w.Completion)‖ ^ 2 = _
  rw [raw_upperRatio_eval R raw hu,← hn,map_div₀]
  change ‖g 0 0 / g 1 1‖ ^ 2 = (KPComplexIntertwinerParameterMajorant.rowRatio g) ^ 2
  congr 1
  unfold KPComplexIntertwinerParameterMajorant.rowRatio KPCplxPrincipalSeriesCharts.bottomRowNormSq
  change ‖g 0 0 / g 1 1‖ = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ / (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)
  rw [Matrix.det_fin_two,h10]
  simp only [mul_zero,sub_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add,norm_mul,norm_div]
  field_simp

private theorem raw_borel_log_eq (raw : Raw R.A)
    (hb : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) ∈ KPGlobalTorusFunctionData.borel F ζ hζ) (v : KPHilbert.Place F) :
    rawLocalLog R P C raw v = Real.log
      ((KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
        (KPGlobalCubicIdelePairing.ideleEval F v
          (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
            (restrictedProjection F ζ hζ raw) (raw_borel_upper R raw hb))) : NNReal) : ℝ) := by
  cases v with
  | inl w =>
    rw [arch_upper_abs R raw (raw_borel_upper R raw hb) w,Real.log_pow]
    rfl
  | inr q =>
    change Real.log (LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q)
      (finiteIntegralIwasawa R P C q)
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))) = _
    rw [finite_borel_forwardAbs R P C q _ raw (raw_borel_upper R raw hb)]

private theorem raw_borel_log_support (raw : Raw R.A)
    (hb : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) ∈ KPGlobalTorusFunctionData.borel F ζ hζ) :
    Function.HasFiniteSupport (rawLocalLog R P C raw) := by
  apply ((raw_borel_norm_product R raw hb).1).subset
  intro v hv
  contrapose! hv
  simp only [Function.mem_support, not_not]
  rw [raw_borel_log_eq R P C raw hb v]
  have hval : KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
      (KPGlobalCubicIdelePairing.ideleEval F v
        (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F
          (restrictedProjection F ζ hζ raw) (raw_borel_upper R raw hb))) = 1 := by
        simpa only [Function.mem_mulSupport, not_not] using hv
  simp [hval]

private theorem rawLocalLog_mul_compact (raw k : Raw R.A)
    (hk : k ∈ fullProductCompactPreimage R) :
    rawLocalLog R P C (raw*k) = rawLocalLog R P C raw := by
  funext v
  cases v with
  | inl w =>
    have hmem := archMax_matrix R w (k (Sum.inl w)) (hk (Sum.inl w))
    obtain ⟨u,hu⟩ := hmem
    have hm : complexMatrix R.A w ((raw*k) (Sum.inl w)) =
        complexMatrix R.A w (raw (Sum.inl w)) * complexMatrix R.A w (k (Sum.inl w)) := map_mul _ _ _
    change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding u) =
      Matrix.ProjGenLinGroup.mk (complexMatrix R.A w (k (Sum.inl w))) at hu
    have hmul : Matrix.ProjGenLinGroup.mk (complexMatrix R.A w (raw (Sum.inl w)) *
        KPCplxCharacterHaar.complexSU2Embedding u) =
      Matrix.ProjGenLinGroup.mk (complexMatrix R.A w ((raw*k) (Sum.inl w))) := by
      rw [hm,map_mul,map_mul,hu]
    have hlog := HeightGeometry.complexMatrixLogNorm_eq_of_mk_eq _ _ hmul
    change Real.log ((KPComplexIntertwinerParameterMajorant.rowRatio
      (complexMatrix R.A w (raw (Sum.inl w)) * KPCplxCharacterHaar.complexSU2Embedding u)) ^ 2) =
      Real.log ((KPComplexIntertwinerParameterMajorant.rowRatio
        (complexMatrix R.A w ((raw*k) (Sum.inl w)))) ^ 2) at hlog
    rw [RepresentationTheory.KPComplexStandardIntertwinerGermProve.rowRatio_mul_su2,
      Real.log_pow,Real.log_pow] at hlog
    exact hlog.symm
  | inr q =>
    change Real.log (LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q) (finiteIntegralIwasawa R P C q)
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)*k (Sum.inr q)))) = _
    rw [map_mul,LocalCompactChange.forwardAbs_mul_compact F ζ hζ q (C.canonical q)
      (finiteIntegralIwasawa R P C q) _ ⟨_,finiteMax_mem_integral R P C q _ (hk (Sum.inr q))⟩]
    rfl

theorem rawLocalLog_finite_and_height (raw : Raw R.A) :
    Function.HasFiniteSupport (rawLocalLog R P C raw) ∧
    iwasawaLogHeight R (scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)) =
      ∑ᶠ v, rawLocalLog R P C raw v := by
  let Q := (scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)
  obtain ⟨t,x,k,hg⟩ := (fullProductIwasawaData R).decomposition (Q raw)
  obtain ⟨rk,hrk,hr⟩ := k.property
  change Q rk = k.val at hr
  let b := raw*rk⁻¹
  have he : raw = b*rk := by simp [b]
  have hb : Q b ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
    change Q (raw*rk⁻¹) ∈ _
    rw [map_mul,map_inv,hr,hg,mul_assoc,mul_inv_cancel,mul_one]
    exact (KPGlobalTorusFunctionData.borel F ζ hζ).mul_mem
      (ActualBorelRetraction.torusInBorel F ζ hζ t).property
      (ActualBorelRetraction.rootInBorel F ζ hζ x).property
  have hlogs : rawLocalLog R P C raw = rawLocalLog R P C b := by
    rw [he]
    exact rawLocalLog_mul_compact R P C b rk hrk
  refine ⟨hlogs ▸ raw_borel_log_support R P C b hb, ?_⟩
  have hheight : iwasawaLogHeight R (Q raw) = iwasawaLogHeight R (Q b) := by
    rw [he,map_mul,hr]
    exact height_compact R _ k
  change iwasawaLogHeight R (Q raw) = _
  rw [hheight,hlogs]
  change iwasawaLogHeight R (scalarQuotient F ζ hζ (amalgamation F ζ hζ b)) = _
  rw [height_raw_borel_finsum R b hb]
  exact finsum_congr (fun v => (raw_borel_log_eq R P C b hb v).symm)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
