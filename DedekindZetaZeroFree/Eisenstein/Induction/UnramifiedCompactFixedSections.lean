module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction
public import DedekindZetaZeroFree.Metaplectic.Torus.TameValuationCoordinates

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable (S : RawFiniteInducingData F ζ hζ q)

def actual_split_compact_level
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    CompactOpenLevel (ActualCover F ζ hζ q) := by
  let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
  have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
  let k := KPGoodCompactSplitting.kStar F ζ hζ q ht
  let p := KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
  have hk : IsCompact (Set.range k) :=
    KPGoodCompactSplitting.kStar_compact_image F ζ hζ q ht m hm
  have ho : IsOpen (Set.range k) :=
    KPGoodCompactSplitting.kStar_open_image F ζ hζ q ht m hm
  have hq : Continuous p := QuotientGroup.continuous_mk
  have hqo : IsOpenMap p := QuotientGroup.isOpenMap_coe
  have he : Set.range (p.comp k) = p '' Set.range k := by
    simp [MonoidHom.comp_apply, Set.range_comp]
  refine { toOpenSubgroup := {
    toSubgroup := (p.comp k).range
    isOpen' := ?_ }, isCompact := ?_ }
  · change IsOpen (Set.range (p.comp k))
    rw [he]
    exact hqo _ ho
  · change IsCompact (Set.range (p.comp k))
    rw [he]
    exact hk.image hq

@[simp] theorem actual_split_compact_level_subgroup
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ((actual_split_compact_level F ζ hζ q ht).toOpenSubgroup :
      Subgroup (ActualCover F ζ hζ q)) =
      (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
        (KPGoodCompactSplitting.kStar F ζ hζ q ht)).range) := rfl

theorem actual_split_compact_factor (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (g : ActualCover F ζ hζ q) :
    ∃ b : S.borel.B, ∃ k : (actual_split_compact_level F ζ hζ q ht).toOpenSubgroup,
      g = (b : ActualCover F ζ hζ q) * (k : ActualCover F ζ hζ q) := by
  letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
    @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
      (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g)
  obtain ⟨r, hr⟩ := ActualFiniteBorel.IwasawaProof.triangularize F q G
  let K := ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht)) r⁻¹
  have hkmem : K ∈ (actual_split_compact_level F ζ hζ q ht).toOpenSubgroup := ⟨r⁻¹, rfl⟩
  have hb : g * K⁻¹ ∈ S.borel.B := by
    rw [S.borel_eq]
    change KPLocalSmoothRepresentation.projection F ζ hζ q (g * K⁻¹) ∈
      KPRankOneInduction.upperBorel F q
    refine ⟨G * KPTameCompact.inclusion F q r, ?_, hr⟩
    change Matrix.ProjGenLinGroup.mk (G * KPTameCompact.inclusion F q r) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q
        (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) (g * K⁻¹))
    rw [(KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).map_mul,
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).map_inv, ← hG]
    change _ = KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.baseQuotient F (Sum.inr q) G *
        (KPPGLLocalCover.baseQuotient F (Sum.inr q)
          (KPTameCompact.inclusion F q r⁻¹))⁻¹)
    rw [map_mul, map_inv, map_inv, inv_inv]
    rfl
  refine ⟨⟨g * K⁻¹, hb⟩, ⟨K, hkmem⟩, ?_⟩
  simp

 abbrev rawSplit
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :=
  (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht)
 abbrev rawCompact
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :=
  (rawSplit F ζ hζ q ht).range

theorem actual_split_compact_retract
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (b : S.borel.B)
    (hb : b.val ∈ (actual_split_compact_level F ζ hζ q ht).toOpenSubgroup) :
    S.borel.retract b ∈
      (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
        (KPGoodCompactSplitting.kStar F ζ hζ q ht)).range).comap
          (Subgroup.subtype (actualTorus F ζ hζ q)) := by
  obtain ⟨k, hk⟩ := hb
  have hbB : b.val ∈ actualBorel F ζ hζ q := S.borel_eq ▸ b.property
  obtain ⟨A, hA, hA10⟩ := hbB
  have hp : Matrix.ProjGenLinGroup.mk (KPTameCompact.inclusion F q k) =
      KPLocalSmoothRepresentation.projection F ζ hζ q b.val := by
    rw [← hk]; rfl
  obtain ⟨u, he⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (hp.trans hA.symm)
  have hz : (KPTameCompact.inclusion F q k) 1 0 = 0 := by
    have he10 := congrArg (fun C : KPRankOneInduction.GL2 F q => C 1 0) he
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.reduceEq, if_true, if_false, mul_zero, zero_add, add_zero, hA10] at he10
    exact (mul_eq_zero.mp he10).resolve_right u.ne_zero
  have hki : k 1 0 = 0 := by
    apply Subtype.ext
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using hz
  have hdet : IsUnit (k 0 0 * k 1 1) := by
    simpa [Matrix.det_fin_two, hki] using k.det.isUnit
  let a : (KPTameCompact.O F q)ˣ := (isUnit_of_mul_isUnit_left hdet).unit
  have ha : (a : KPTameCompact.O F q) = k 0 0 := (isUnit_of_mul_isUnit_left hdet).unit_spec
  let t : KPTameCompact.O F q := - (a⁻¹ : (KPTameCompact.O F q)ˣ) * k 0 1
  let d := k * KPStandardLocalRootLifts.integralN F q t
  have hd10 : (KPTameCompact.inclusion F q d) 1 0 = 0 := by
    simp [d, map_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, KPStandardLocalRootLifts.integralN, KPTameCompact.inclusion,
      KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hki]
  have hd01 : (KPTameCompact.inclusion F q d) 0 1 = 0 := by
    have hai : k 0 0 * ((a⁻¹ : (KPTameCompact.O F q)ˣ) : KPTameCompact.O F q) = 1 := by
      rw [← ha]; exact Units.mul_inv a
    have hdt : k 0 0 * t + k 0 1 = 0 := by
      dsimp [t]
      rw [← mul_assoc, mul_neg, hai]
      simp
    change ((KPTameCompact.O F q).subtype ((d 0 1))) = 0
    rw [show d 0 1 = 0 by
      simpa [d, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.integralN] using hdt]
    rfl
  let D := rawSplit F ζ hζ q ht d
  have hD : D ∈ actualTorus F ζ hζ q := by
    exact ⟨KPTameCompact.inclusion F q d, rfl, hd10, hd01⟩
  let j : actualTorus F ζ hζ q := ⟨D, hD⟩
  have hn : (S.borel.upperRoot (Multiplicative.ofAdd (t : LocalField F q)) :
      ActualCover F ζ hζ q) = rawSplit F ζ hζ q ht
        (KPStandardLocalRootLifts.integralN F q t) := by
    rw [(S.openCell S.polarization).upper_eq]
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (t : LocalField F q)) = _
    rw [KPStandardLocalRootLifts.N_eq_compact F ζ hζ q ht t]
    rfl
  have hbj : b * S.borel.upperRoot (Multiplicative.ofAdd (t : LocalField F q)) =
      S.borel.torus j := by
    apply Subtype.ext
    rw [S.torus_full]
    change b.val * _ = D
    rw [hn, ← hk]
    exact (rawSplit F ζ hζ q ht).map_mul _ _ |>.symm
  have hr : S.borel.retract b = j := by
    have h := congrArg S.borel.retract hbj
    simpa only [map_mul, S.borel.retract_upperRoot, mul_one,
      S.borel.retract_torus] using h
  change (S.borel.retract b : ActualCover F ζ hζ q) ∈ rawCompact F ζ hζ q ht
  rw [hr]
  exact ⟨d, rfl⟩

private lemma raw_split_projection (g : ActualCover F ζ hζ q) :
    S.borel.projection g = KPLocalSmoothRepresentation.projection F ζ hζ q g := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
  exact (S.openCell S.polarization).projection_eq r

private lemma raw_split_ratio (b : S.borel.B) :
    S.borel.coordinate (S.borel.retract b) =
      KPRankOneInduction.borelRatio F q
        ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b.val,
          show b.val ∈ actualBorel F ζ hζ q from S.borel_eq ▸ b.property⟩ := by
  obtain ⟨x, hx⟩ := S.borel.borel_decomposition b
  let y := S.borel.coordinate (S.borel.retract b)
  let G := KubotaRankTwo.d (LocalField F q) y 1 *
    KubotaRankTwo.n (LocalField F q) (Multiplicative.toAdd x)
  have hG : Matrix.ProjGenLinGroup.mk G =
      KPLocalSmoothRepresentation.projection F ζ hζ q b.val := by
    rw [← raw_split_projection F ζ hζ q S]
    have hp := congrArg (fun c : S.borel.B => S.borel.projection c.val) hx
    simpa only [G, y, Subgroup.coe_mul, map_mul, S.borel.torus_projection,
      S.borel.upperRoot_projection] using hp.symm
  have h10 : G 1 0 = 0 := by
    simp [G, KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  apply Units.ext
  symm
  rw [KPRankOneInduction.borelRatio_eq F q _ G hG h10]
  simp [G, KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, y]

private lemma raw_split_intersection_norm
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (b : S.borel.B) (hb : b.val ∈ rawCompact F ζ hζ q ht) :
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract b)) = 1 := by
  rw [raw_split_ratio F ζ hζ q S]
  have hbb : b.val ∈ actualBorel F ζ hζ q := S.borel_eq ▸ b.property
  have hc : b.val ∈ KPRankOneCartanGeometry.coveredK0 F ζ hζ q := by
    obtain ⟨k, hk⟩ := hb
    exact ⟨k, hk ▸ rfl⟩
  exact ActualFiniteBorel.IwasawaProof.covered_intersection F ζ hζ q ⟨b.val, hbb⟩ hc

theorem actual_split_compact_iwasawa
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ I : IwasawaData S.borel,
      (I.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) =
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)).range) := by
  classical
  let L := actual_split_compact_level F ζ hζ q ht
  have hex (g : ActualCover F ζ hζ q) :
      ∃ b : S.borel.B, ∃ k : L.toOpenSubgroup, g = b.val * k.val :=
    actual_split_compact_factor F ζ hζ q S ht g
  let bp (g : ActualCover F ζ hζ q) : S.borel.B :=
    if hg : g ∈ L.toOpenSubgroup then 1 else Classical.choose (hex g)
  let kp (g : ActualCover F ζ hζ q) : L.toOpenSubgroup :=
    if hg : g ∈ L.toOpenSubgroup then ⟨g, hg⟩
    else Classical.choose (Classical.choose_spec (hex g))
  refine ⟨{
    compact := L
    borelPart := bp
    compactPart := kp
    decomposition := ?_
    borelPart_compact := ?_
    compactPart_compact := ?_
    intersection_norm := ?_ }, rfl⟩
  · intro g
    by_cases hg : g ∈ L.toOpenSubgroup
    · simp [bp, kp, hg]
    · simpa [bp, kp, hg] using
        Classical.choose_spec (Classical.choose_spec (hex g))
  · intro k
    simp [bp, k.property]
  · intro k
    simp [kp, k.property]
  · intro b hb
    exact raw_split_intersection_norm F ζ hζ q S ht b hb

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
