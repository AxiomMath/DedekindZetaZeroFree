module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.FiberProductFormula

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

theorem fiberEvaluation_left (f : ∀ v, Plus A P C v) (u g : Raw A) (q : KPFinitePlace F)
    (x t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : t.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q))) :
    fiberEvaluation A P C f (u * g) q x =
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t)) (2/3 : ℝ) : ℂ) *
      fiberEvaluation A P C f g q (x * t) := by
  unfold fiberEvaluation
  change localUntwistedEvaluation F ζ hζ P C q
    (localValue A P C (Sum.inr q) (u (Sum.inr q) * g (Sum.inr q)) (f (Sum.inr q))) x = _
  rw [localValue_finite_torus A P C q _ _ _ t ht, EisensteinReferenceSections.LocalTorus.finite_deltaHalf]
  change (Real.rpow _ (1/2 : ℝ) : ℂ) *
    ((localTau F ζ hζ P C q t _).val x) / _ = _
  rw [mul_div_assoc]
  change (Real.rpow _ (1/2 : ℝ) : ℂ) * localUntwistedEvaluation F ζ hζ P C q
    (localTau F ζ hζ P C q t _) x = _
  rw [EisensteinReferenceSections.SourceTorusEvaluation.untwisted_tau]
  have hpos : 0 < ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t) : ℝ≥0) : ℝ) := by
    exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F _ _
  have hh := EisensteinReferenceSections.SourceTorusCovariance.rpow_factor _ hpos
  rw [← hh]
  ring

private theorem archValues_left (f : ∀ v, Plus A P C v) (u g : Raw A)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (hp : ∀ w, complexMatrix A w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w)) :
    archValues A P C f (u * g) =
      (∏ w, (Real.rpow (KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ)/(d w : ℂ))) (2/3 : ℝ) : ℂ)) *
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (u (Sum.inl w)).epsilon : ℂ)) *
      archValues A P C f g := by
  unfold archValues
  simp_rw [show ∀ w, (u*g) (Sum.inl w) = u (Sum.inl w)*g (Sum.inl w) from fun _ => rfl,
    localValue_arch_torus A P C _ _ _ _ _ _ _ (hp _)]
  simp only [KPCplxPrincipalSeriesCharts.inductionWeight, KPCplxPrincipalSeriesCharts.positiveParameter]
  norm_num
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

theorem rawCoreFiber_pure_torus (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (u g : Raw A)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hg : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (hug : ∀ v, v ∉ s.val → localValue A P C v ((u*g) v) (plusReference A P C v) = reference A P C v)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix A w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    rawCoreFiber A P C (u*g) (RestrictedTensorSimple.stageInclusion (Plus A P C)
      (plusReference A P C) (bad A P C) s (PiTensorProduct.tprod ℂ x)) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) •
      KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ (productModel F ζ hζ P) e
        (rawCoreFiber A P C g (RestrictedTensorSimple.stageInclusion (Plus A P C)
          (plusReference A P C) (bad A P C) s (PiTensorProduct.tprod ℂ x))) := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  obtain ⟨raw, tz, az, dz, htz, hpz, hez⟩ := EisensteinReferenceSections.TorusNorms.raw_lifts F ζ hζ z
  have hmul q : (tz q*t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      ((raw*u) (Sum.inr q)) := by
    change (tz q).val*(t q).val = _
    rw [htz, ht, ← map_mul]
    rfl
  have hemul : scalarQuotient F ζ hζ (amalgamation F ζ hζ (raw*u)) = (z*e).val := by
    rw [map_mul, map_mul, hez, he]
    rfl
  change _ = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
    ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) * _
  rw [KPGlobalTorusPeriodizationInverse.rightAction_formula]
  rw [rawCoreFiber_pure_formula A P C s x (u*g) raw tz z hug htz hez,
    rawCoreFiber_pure_formula A P C s x g (raw*u) (fun q => tz q*t q) (z*e) hg hmul hemul,
    archValues_left A P C _ u g a d b hp, EisensteinReferenceSections.SourceTorusEvaluation.phase_mul]
  let n q : ℂ := (Real.rpow (EisensteinReferenceSections.TorusNorms.localNorm F ζ hζ P C t a d (Sum.inr q)) (2/3 : ℝ) : ℂ)
  have hl q : fiberEvaluation A P C (pureSections A P C s x) (u*g) q (tz q) =
      n q * fiberEvaluation A P C (pureSections A P C s x) g q (tz q*t q) :=
    fiberEvaluation_left A P C _ u g q _ _ (ht q)
  simp_rw [hl]
  have hp' : ∀ w, EisensteinReferenceSections.LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w) := hp
  have hs := (EisensteinReferenceSections.TorusNorms.given_raw_norm F ζ hζ P C u t a d b e ht hp' he).1
  have hns : Function.HasFiniteMulSupport n :=
    (hs.comp (g := fun r : ℝ => (Real.rpow r (2/3 : ℝ) : ℂ)) (by norm_num)).comp_of_injective Sum.inr_injective
  have hvs := fiberEvaluation_finiteSupport A P C s x g (raw*u) (fun q => tz q*t q) hg hmul
  rw [finprod_mul_distrib hns hvs]
  have hm := EisensteinReferenceSections.SourceTorusCovariance.multiplier F ζ hζ P C u t a d b e ht hp' he
  change (∏ w, (Real.rpow (KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ)/(d w : ℂ))) (2/3 : ℝ) : ℂ)) *
    ∏ᶠ q, n q = _ at hm
  rw [← hm]
  ring
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
