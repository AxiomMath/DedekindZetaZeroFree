module

public import DedekindZetaZeroFree.Eisenstein.Induction.TorusEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusCovariance
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 theorem rpow_factor (x : ℝ) (hx : 0 < x) :
    (Real.rpow x (1/2 : ℝ) : ℂ) * (Real.rpow x (1/6 : ℝ) : ℂ) =
      (Real.rpow x (2/3 : ℝ) : ℂ) := by
  simp only [Real.rpow_eq_pow]
  rw [← Complex.ofReal_mul, ← Real.rpow_add hx]
  norm_num

 theorem localNorm_pos (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (v : KPHilbert.Place F) :
    0 < TorusNorms.localNorm F ζ hζ P C t a d v := by
  cases v with
  | inr q => exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) _
  | inl w => exact pow_pos (norm_pos_iff.mpr (div_ne_zero (a w).ne_zero (d w).ne_zero)) 2

 theorem archProduct_left (u g : RestrictedCover F ζ hζ)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (hp : ∀ w, LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w)) :
    RawSource.archProduct F ζ hζ (u*g) =
      (∏ w, (Real.rpow (KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ)/(d w : ℂ))) (2/3 : ℝ) : ℂ)) *
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (u (Sum.inl w)).epsilon : ℂ)) *
      RawSource.archProduct F ζ hζ g := by
  unfold RawSource.archProduct
  simp_rw [show ∀ w, ((u*g) (Sum.inl w)) = u (Sum.inl w)*g (Sum.inl w) from fun _ => rfl,
    LocalTorus.arch F ζ hζ _ _ _ _ _ _ (hp _)]
  simp only [KPCplxPrincipalSeriesCharts.inductionWeight,
    KPCplxPrincipalSeriesCharts.positiveParameter]
  norm_num
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

 theorem multiplier (u : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    (∏ w, (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d (Sum.inl w)) (2/3 : ℝ) : ℂ)) *
      ∏ᶠ q, (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d (Sum.inr q)) (2/3 : ℝ) : ℂ) =
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) := by
  obtain ⟨hs, hn⟩ := TorusNorms.given_raw_norm F ζ hζ P C u t a d b e ht hp he
  have hroot : Function.HasFiniteMulSupport (fun v =>
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (1/6 : ℝ) : ℂ)) :=
    hs.comp (g := fun x : ℝ => (Real.rpow x (1/6 : ℝ) : ℂ)) (by norm_num)
  have hweight : Function.HasFiniteMulSupport (fun v =>
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (2/3 : ℝ) : ℂ)) :=
    hs.comp (g := fun x : ℝ => (Real.rpow x (2/3 : ℝ) : ℂ)) (by norm_num)
  rw [← RawSource.finprod_places F hweight]
  have hw (v : KPHilbert.Place F) :
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (2/3 : ℝ) : ℂ) =
      (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (1/6 : ℝ) : ℂ) ^ (4 : ℕ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (le_of_lt (localNorm_pos F ζ hζ P C t a d v))]
    norm_num
  simp_rw [hw]
  rw [← finprod_pow hroot 4]
  have hnC : ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) =
      ∏ᶠ v, (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d v) (1/6 : ℝ) : ℂ) := by
    rw [show ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) =
      ((((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℝ)) : ℂ) from rfl, hn]
    exact MonoidHom.map_finprod Complex.ofRealHom.toMonoidHom
      (hs.comp (g := fun x : ℝ => Real.rpow x (1/6 : ℝ)) (by norm_num))
  rw [← hnC]
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ e =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ) ^ (3 : ℕ) := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    rw [Real.sqrt_eq_rpow]
    have hν : (((KPGlobalTorusFunctionData.delta F ζ hζ e : ℝ≥0) : ℝ)) =
        (((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℝ)) ^ (6 : ℕ) := by
      simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
        KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map,
        NNReal.rpowMonoidHom_apply, NNReal.coe_rpow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hν, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hhalf]
  ring

 theorem raw_torus (u g : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    RawSource.value F ζ hζ P C (u*g) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) •
      KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
        (productModel F ζ hζ P) e (RawSource.value F ζ hζ P C g) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨raw, tx, ax, dx, htx, hpx, hex⟩ := TorusNorms.raw_lifts F ζ hζ x
  have hmul q : (tx q*t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      ((raw*u) (Sum.inr q)) := by
    change (tx q).val*(t q).val = _
    rw [htx, ht, ← map_mul]
    rfl
  have hemul : scalarQuotient F ζ hζ (amalgamation F ζ hζ (raw*u)) = (x*e).val := by
    rw [map_mul, map_mul, hex, he]
    rfl
  change (RawSource.value F ζ hζ P C (u*g)).val.val x =
    (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) *
    (RawSource.value F ζ hζ P C g).val.val (x*e)
  rw [SourceTorusEvaluation.formula F ζ hζ P C (u*g) raw tx x htx hex,
    SourceTorusEvaluation.formula F ζ hζ P C g (raw*u) (fun q => tx q*t q) (x*e) hmul hemul,
    archProduct_left F ζ hζ u g a d b hp, SourceTorusEvaluation.phase_mul]
  let n q : ℂ := (Real.rpow (TorusNorms.localNorm F ζ hζ P C t a d (Sum.inr q)) (2/3 : ℝ) : ℂ)
  have hl q : SourceTorusEvaluation.evaluation F ζ hζ P C (u*g) q (tx q) =
      n q * SourceTorusEvaluation.evaluation F ζ hζ P C g q (tx q*t q) := by
    rw [SourceTorusEvaluation.evaluation_left F ζ hζ P C u g q (tx q) (t q) (ht q)]
    have hpos := localNorm_pos F ζ hζ P C t a d (Sum.inr q)
    change 0 < ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate (t q)) : ℝ≥0) : ℝ) at hpos
    rw [rpow_factor _ hpos]
    rfl
  simp_rw [hl]
  have hs := (TorusNorms.given_raw_norm F ζ hζ P C u t a d b e ht hp he).1
  have hns : Function.HasFiniteMulSupport n :=
    (hs.comp (g := fun x : ℝ => (Real.rpow x (2/3 : ℝ) : ℂ)) (by norm_num)).comp_of_injective Sum.inr_injective
  have hvs := SourceTorusEvaluation.evaluation_finiteSupport F ζ hζ P C g (raw*u)
    (fun q => tx q*t q) hmul
  rw [finprod_mul_distrib hns hvs]
  have hm := multiplier F ζ hζ P C u t a d b e ht hp he
  change (∏ w, (Real.rpow (KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ)/(d w : ℂ))) (2/3 : ℝ) : ℂ)) *
    ∏ᶠ q, n q = _ at hm
  rw [← hm]
  ring

 theorem quotient_torus (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    RawSource.quotientValue F ζ hζ P C (e.val*g) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) •
      KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
        (productModel F ζ hζ P) e (RawSource.quotientValue F ζ hζ P C g) := by
  obtain ⟨u,t,a,d,ht,hp,he⟩ := TorusNorms.raw_lifts F ζ hζ e
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      rw [← he]
      change RawSource.quotientValue F ζ hζ P C
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ u) *
          scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) = _
      rw [← map_mul, ← map_mul, RawSource.quotientValue_raw]
      exact raw_torus F ζ hζ P C u g t a d (fun _ => 0) e ht hp he

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusCovariance

end
