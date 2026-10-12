module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ArchimedeanRootCovariance

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option warn.classDefReducibility false
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteInsertion
open KPLiteralRaw KPAdelicCoverRestrictedProduct
open KPLiteralScalarHCCompactOrbit
open KPLiteralScalarHCSliceCharts
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
attribute [local instance] pglLocalTopology localTopology

def finiteGroupInsertion (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    KPLocalExceptionalConstruction.ActualCover F ζ hζ q →* KPLiteralRaw.G F ζ hζ :=
  (local_pgl_injection F ζ hζ (Sum.inr q)).choose

theorem finiteGroupInsertion_raw (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    finiteGroupInsertion F ζ hζ q (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a) =
      scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) a) :=
  (local_pgl_injection F ζ hζ (Sum.inr q)).choose_spec.2.2 a

theorem finiteGroupInsertion_continuous (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Continuous (finiteGroupInsertion F ζ hζ q) :=
  (local_pgl_injection F ζ hζ (Sum.inr q)).choose_spec.2.1

theorem finiteGroupInsertion_mem (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :
    finiteGroupInsertion F ζ hζ q a ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    change finiteGroupInsertion F ζ hζ q
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a) ∈ _
    rw [finiteGroupInsertion_raw]
    refine ⟨localToRestricted F ζ hζ (Sum.inr q) a, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    change localToRestricted F ζ hζ (Sum.inr q) a (Sum.inl w) = 1
    simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply]

def finiteInsertion (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    KPLocalExceptionalConstruction.ActualCover F ζ hζ q →*
      KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  (finiteGroupInsertion F ζ hζ q).codRestrict _ (finiteGroupInsertion_mem F ζ hζ q)

theorem finiteInsertion_value (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :
    (finiteInsertion F ζ hζ q a).val = finiteGroupInsertion F ζ hζ q a := rfl

theorem finiteInsertion_continuous (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Continuous (finiteInsertion F ζ hζ q) :=
  (finiteGroupInsertion_continuous F ζ hζ q).subtype_mk _

def insertionLevel (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    OpenSubgroup (KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :=
  J.toOpenSubgroup.comap (finiteInsertion F ζ hζ q) (finiteInsertion_continuous F ζ hζ q)

variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)

section PolarizedTorusLift
open KPGlobalProductPolarizationCharacter
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

open _root_.DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter renaming localRatioValue_eq → localRatioValue_eq
open _root_.DedekindZetaZeroFree.ProductPolarization renaming baseEval → baseEval
open _root_.DedekindZetaZeroFree.ProductPolarization renaming eval_diagonal → eval_diagonal
open _root_.DedekindZetaZeroFree.ProductPolarization renaming diagonal_formula → diagonal_formula

private theorem raw_diagonal (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (r : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (hr : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) r ∈ localTorus F ζ hζ (Sum.inr q)) :
    r.g 1 0 = 0 ∧ r.g 0 1 = 0 := by
  obtain ⟨y, hy⟩ := hr
  change KPPGLLocalCover.baseQuotient F (Sum.inr q) (diagonalHom F (Sum.inr q) y) =
    KPPGLLocalCover.baseQuotient F (Sum.inr q) r.g at hy
  simp only [KPPGLLocalCover.baseQuotient] at hy
  rw [QuotientGroup.mk'_eq_mk'] at hy
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := hy
  rw [← hz]
  constructor <;> simp [diagonalHom, KubotaRankTwo.d, KPScalarSplitCentral.scalarMatrix,
    Matrix.mul_apply, Fin.sum_univ_two]

private theorem global_raw_ratio
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (r : RestrictedCover F ζ hζ)
    (he : e.val = scalarQuotient F ζ hζ (amalgamation F ζ hζ r))
    (v : KPHilbert.Place F)
    (t : localTorus F ζ hζ v)
    (ht : t.val = KPPGLLocalCover.coverQuotient F ζ hζ v (r v)) :
    localRatio F ζ hζ v t = KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e) := by
  have hproj : pglProjection F ζ hζ e.val =
      KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.p F ζ hζ e) :=
    (diagonal_formula F ⟨_, e.property⟩).symm
  have h := congrArg (baseEval F v) hproj
  rw [he, eval_diagonal] at h
  change KPPGLLocalCover.baseQuotient F v
      (matrixEval F v (restrictedProjection F ζ hζ r)) = _ at h
  rw [restrictedProjection_eval] at h
  symm
  apply localRatioValue_eq F ζ hζ v
  rw [ht]
  exact h.symm

private theorem polarized_torus_geometry
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : (C₀.polarization q).L.comap (C₀.canonical q).heisenberg.π) :
    ∃ (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData),
      b.val.val = (finiteInsertion F ζ hζ q a.val.val).val ∧
      (∀ v : KPHilbert.Place F, v ≠ Sum.inr q → x.val v = 1) ∧
      scalarQuotient F ζ hζ (amalgamation F ζ hζ x.val) = b.val.val ∧
      a.val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q)) := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inr q)) a.val.val
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) r = a.val.val at hr
  have hmatch : a.val.val ∈ (localPreimage F ζ hζ (Sum.inr q)
      (P.localData.localData (Sum.inr q)).L).map (localTorus F ζ hζ (Sum.inr q)).subtype := by
    rw [← C₀.subgroup_matches q]
    exact Subgroup.mem_map.mpr ⟨a.val, a.property, rfl⟩
  obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp hmatch
  have hdr : r.g 1 0 = 0 ∧ r.g 0 1 = 0 := raw_diagonal F ζ hζ q r (hr ▸ hta ▸ t.property)
  let R := localToRestricted F ζ hζ (Sum.inr q) r
  have hs : ∀ v : KPHilbert.Place F, v ≠ Sum.inr q → R v = 1 := by
    intro v hv
    simp [R, localToRestricted, RestrictedProduct.coe_mulSingle_apply, hv]
  have hq : R (Sum.inr q) = r := by
    simp [R, localToRestricted, RestrictedProduct.coe_mulSingle_apply]
  have hd : (restrictedProjection F ζ hζ R) 1 0 = 0 ∧ (restrictedProjection F ζ hζ R) 0 1 = 0 := by
    constructor
    all_goals
      apply Prod.ext
      · funext w
        change (R (Sum.inl w)).g _ _ = 0
        rw [hs (Sum.inl w) (by simp)]
        simp
      · apply RestrictedProduct.ext
        intro p
        change (R (Sum.inr p)).g _ _ = 0
        by_cases hp : p = q
        · subst p
          rw [hq]
          first | exact hdr.1 | exact hdr.2
        · rw [hs (Sum.inr p) (by simpa using hp)]
          simp
  let e : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ R), restrictedProjection F ζ hζ R, rfl, hd⟩
  have heb : e ∈ B F ζ hζ P.localData := by
    change ∀ v, KPGlobalCubicIdelePairing.localClass F v
      (KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e)) ∈ (P.localData.localData v).L
    intro v
    by_cases hv : v = Sum.inr q
    · subst v
      rw [← global_raw_ratio F ζ hζ e R rfl _ t (hta.trans (hr.symm.trans (congrArg _ hq.symm)))]
      exact ht
    · rw [← global_raw_ratio F ζ hζ e R rfl v 1 (by rw [hs v hv, map_one]; rfl)]
      simp only [map_one]
      exact Subgroup.one_mem _
  let b : B F ζ hζ P.localData := ⟨e, heb⟩
  let x : rawB F ζ hζ P.localData := ⟨R, Subgroup.mem_map.mpr ⟨e, heb, rfl⟩⟩
  refine ⟨b, x, ?_, hs, rfl, ?_⟩
  · change scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) r) = finiteGroupInsertion F ζ hζ q a.val.val
    rw [← hr, finiteGroupInsertion_raw]
  · change a.val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (R (Sum.inr q))
    rw [hq, hr]

open _root_.DedekindZetaZeroFree.KPGlobalTorusFiniteStages renaming rawLocalScalarData → rawLocalScalarData
open _root_.DedekindZetaZeroFree.ProductPolarization renaming normalizedLocalAbs_norm → normalizedLocalAbs_norm

private theorem polarized_torus_deltaHalf
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : (C₀.polarization q).L.comap (C₀.canonical q).heisenberg.π)
    (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData)
    (hs : ∀ v : KPHilbert.Place F, v ≠ Sum.inr q → x.val v = 1)
    (hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x.val) = b.val.val)
    (ha : a.val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q))) :
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val =
      KPLocalPrincipalSeries.deltaHalf (C₀.canonical q).borel ((C₀.canonical q).borel.torus a.val) := by
  let t : localTorus F ζ hζ (Sum.inr q) := ⟨a.val.val, by
    rw [← KPGlobalTorusFiniteStages.actual_local_torus_eq F ζ hζ q]
    exact a.val.property⟩
  have hratio := global_raw_ratio F ζ hζ b.val x.val hx.symm (Sum.inr q) t ha
  have hnorm := KPGlobalTorusTensorFibers.raw_local_coordinate_norm_matches
    F ζ hζ P.localData P.adjustment (rawLocalScalarData F ζ hζ P C₀) q a.val t rfl
  letI := primitive12_totallyComplex F ζ hζ
  have hp := KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.idele_localAbs_finprod
    F (KPGlobalTorusFunctionData.p F ζ hζ b.val)
  have hsingle : (∏ᶠ v : KPHilbert.Place F, Units.mk0
      (KPGlobalCenterRationalCharacterExtension.localAbs F v
        (KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ b.val)))
      (ne_of_gt (KPGlobalCenterRationalCharacterExtension.localAbs_pos F v _))) =
      Units.mk0 (KPGlobalCenterRationalCharacterExtension.localAbs F (Sum.inr q)
        (localRatio F ζ hζ (Sum.inr q) t))
      (ne_of_gt (KPGlobalCenterRationalCharacterExtension.localAbs_pos F (Sum.inr q) _)) := by
    rw [finprod_eq_single (a := Sum.inr q)]
    · rw [← hratio]
    · intro v hv
      have hv1 : KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ b.val) = 1 := by
        rw [← global_raw_ratio F ζ hζ b.val x.val hx.symm v 1 (by rw [hs v hv, map_one]; rfl), map_one]
      rw [hv1]
      apply Units.ext
      cases v <;> simp [KPGlobalCenterRationalCharacterExtension.localAbs]
  have hd : (((KPGlobalTorusFunctionData.delta F ζ hζ b.val : ℝ≥0) : ℝ)) =
      KPLocalPrincipalSeries.localAbs (q.adicCompletion F) ((C₀.canonical q).borel.coordinate a.val) := by
    change (((KPGlobalTorusFunctionData.ideleAbs F (KPGlobalTorusFunctionData.p F ζ hζ b.val) : ℝ≥0) : ℝ)) = _
    rw [← hp, hsingle]
    change ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) (localRatio F ζ hζ (Sum.inr q) t) : ℝ≥0) : ℝ) = _
    rw [← hnorm, normalizedLocalAbs_norm F q]
    rfl
  rw [KPGlobalTorusFunctionData.deltaHalf, hd, KPLocalPrincipalSeries.deltaHalf,
    (C₀.canonical q).borel.retract_torus, KPLocalPrincipalSeries.normPower,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    KPLocalPrincipalSeriesNormWeights.exp_mul_log_real (KPLocalPrincipalSeries.localAbs_pos _ _) _,
    Real.sqrt_eq_rpow]

theorem polarized_torus_lift
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : (C₀.polarization q).L.comap (C₀.canonical q).heisenberg.π) :
    ∃ (b : B F ζ hζ P.localData) (x : rawB F ζ hζ P.localData),
      b.val.val = (finiteInsertion F ζ hζ q a.val.val).val ∧
      (∀ v : KPHilbert.Place F, v ≠ Sum.inr q → x.val v = 1) ∧
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val ∧
      a.val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x.val (Sum.inr q)) ∧
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val =
        KPLocalPrincipalSeries.deltaHalf (C₀.canonical q).borel
          ((C₀.canonical q).borel.torus a.val) := by
  obtain ⟨b, x, hb, hs, hx, ha⟩ := polarized_torus_geometry F ζ hζ P C₀ q a
  exact ⟨b, x, hb, hs, hx, ha, polarized_torus_deltaHalf F ζ hζ P C₀ q a b x hs hx ha⟩
end PolarizedTorusLift

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteInsertion

end
