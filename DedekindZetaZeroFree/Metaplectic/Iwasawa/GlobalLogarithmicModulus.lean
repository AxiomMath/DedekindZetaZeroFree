module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.CompactLevelAndTwists
public import DedekindZetaZeroFree.Metaplectic.Iwasawa.IntegralCompact

@[expose] public section

noncomputable section
open scoped Classical NumberField Matrix NNReal
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages KPLocalPrincipalSeries KPLocalExceptionalConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open ThetaExpansion KPAdelicCoverRestrictedProduct
open _root_.DedekindZetaZeroFree.ThetaExpansion renaming height_compact → height_compact
open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming borel_root → borel_root
open _root_.DedekindZetaZeroFree.KPLocalTameValuationWhittakerBasis.RawSectionBridge renaming localAbs_norm → localAbs_norm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

private theorem projected_raw (raw : Raw R) :
    pglProjection F R.A.zeta12 R.A.primitive_zeta12
      (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw)) =
    QuotientGroup.mk' (scalarSubgroup F)
      (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) := by
  simp only [pglProjection, scalarQuotient, projection_amalgamation,
    QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.comp_apply]

 theorem raw_borel_upper (raw : Raw R)
    (hb : scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw) ∈
        KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12) :
    (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0 = 0 := by
  obtain ⟨B, hB, hB10⟩ := hb
  have he : QuotientGroup.mk' (scalarSubgroup F)
      (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) =
        QuotientGroup.mk' (scalarSubgroup F) B := by
    rw [← projected_raw R, hB]
  obtain ⟨z, hz, hzA⟩ := (QuotientGroup.mk'_eq_mk' (N := scalarSubgroup F)).mp he
  obtain ⟨s, rfl⟩ := hz
  have h := congrArg (fun M : AdelicGL2 F => M 1 0) hzA
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
    hB10, mul_zero, add_zero, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h
  exact (IsUnit.mul_left_eq_zero ⟨s, rfl⟩).mp h

 theorem raw_upper_eval (raw : Raw R)
    (hu : (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0 = 0)
    (v : KPHilbert.Place F) : (raw v).g 1 0 = 0 := by
  have h := restrictedProjection_eval F R.A.zeta12 R.A.primitive_zeta12 raw v
  have he := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 1 0) h
  change adeleEval F v ((restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0) =
    (raw v).g 1 0 at he
  rw [hu, map_zero] at he
  exact he.symm

 theorem upperRatio_eval (raw : Raw R)
    (hu : (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0 = 0)
    (v : KPHilbert.Place F) :
    (KPGlobalCubicIdelePairing.ideleEval F v
      (KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
        (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu) :
        KPHilbert.Completion F v) = (raw v).g 0 0 / (raw v).g 1 1 := by
  let A := restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw
  have hentry (i j : Fin 2) : adeleEval F v (A i j) = (raw v).g i j := by
    have h := restrictedProjection_eval F R.A.zeta12 R.A.primitive_zeta12 raw v
    have he := congrArg (fun M : KPLocalCover.LocalGL2 F v => M i j) h
    simpa only [A, matrixEval, Matrix.GeneralLinearGroup.map_apply,
      KPLocalCover.projection_apply] using he
  change ((Units.map (adeleEval F v).toMonoidHom)
    (KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F A hu) : KPHilbert.Completion F v) = _
  unfold KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  simp only [Units.coe_map, IsUnit.unit_spec]
  change adeleEval F v (A 0 0) * (adeleEval F v (A 1 1))⁻¹ = _
  exact (congrArg₂ (fun a b : KPHilbert.Completion F v => a*b⁻¹)
    (hentry 0 0) (hentry 1 1)).trans (div_eq_mul_inv _ _).symm

 theorem canonical_coordinate_upperRatio (q : KPFinitePlace F) (raw : Raw R)
    (hu : (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0 = 0)
    (b : (C.canonical q).borel.B)
    (hb : (b : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) =
      KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (raw (.inr q))) :
    (C.canonical q).borel.coordinate ((C.canonical q).borel.retract b) =
      KPGlobalCubicIdelePairing.ideleEval F (.inr q)
        (KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
          (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu) := by
  have hmem : (b : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) ∈
      KPLocalSmoothRepresentation.Borel F R.A.zeta12 R.A.primitive_zeta12 q := by
    change _ ∈ actualBorel F R.A.zeta12 R.A.primitive_zeta12 q
    rw [← (C.canonical q).borel_eq]
    exact b.property
  rw [canonical_borel_ratio R P C q b hmem]
  apply Units.ext
  rw [upperRatio_eval R]
  apply KPRankOneInduction.borelRatio_eq F q _ (raw (.inr q)).g
  · change Matrix.ProjGenLinGroup.mk (raw (.inr q)).g =
      KPLocalSmoothRepresentation.projection F R.A.zeta12 R.A.primitive_zeta12 q b
    rw [hb]; rfl
  · exact raw_upper_eval R raw hu (.inr q)

 theorem raw_upper_forwardAbs (q : KPFinitePlace F) (J : IwasawaData (C.canonical q).borel)
    (raw : Raw R) (hu : (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0 = 0) :
    LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q (C.canonical q) J
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (raw (.inr q))) =
    ((KPGlobalCenterRationalCharacterModulus.localAbsUnit F (.inr q)
      (KPGlobalCubicIdelePairing.ideleEval F (.inr q)
        (KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
          (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu)) : ℝ≥0) : ℝ) := by
  have hmem : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q)
      (raw (.inr q)) ∈ (C.canonical q).borel.B := by
    rw [(C.canonical q).borel_eq]
    exact ⟨(raw (.inr q)).g, rfl, raw_upper_eval R raw hu (.inr q)⟩
  let b : (C.canonical q).borel.B := ⟨_, hmem⟩
  have hf := LocalCompactChange.forwardAbs_factorization F R.A.zeta12 R.A.primitive_zeta12 q
    (C.canonical q) J b (1 : J.compact.toOpenSubgroup)
  simp only [Subgroup.coe_one, mul_one] at hf
  rw [hf, canonical_coordinate_upperRatio R P C q raw hu b rfl, localAbs_norm F q]
  rfl

 theorem raw_borel_norm_product (raw : Raw R)
    (hb : scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw) ∈
        KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12) :
    let hu := raw_borel_upper R raw hb
    let u := KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
      (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu
    Function.HasFiniteMulSupport (fun v => KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
      (KPGlobalCubicIdelePairing.ideleEval F v u)) ∧
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F R.A.zeta12 R.A.primitive_zeta12
      (fullProductIwasawaData R) (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw)) =
    ∏ᶠ v, KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
      (KPGlobalCubicIdelePairing.ideleEval F v u) := by
  dsimp only
  let g := scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw)
  let hu := raw_borel_upper R raw hb
  let u := KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
    (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu
  obtain ⟨t, x, ht⟩ := KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization
    F R.A.zeta12 R.A.primitive_zeta12 ⟨g, hb⟩
  have hr : u = KPGlobalTorusFunctionData.p F R.A.zeta12 R.A.primitive_zeta12 t := by
    apply KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio_torus_root
      F R.A.zeta12 R.A.primitive_zeta12 t x
    rw [← ht]
    exact (projected_raw R raw).symm
  have hp := KPGlobalCenterRationalCharacterModulus.idele_abs_finite_product F
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) R.A.primitive_zeta12) u
  refine ⟨hp.1, ?_⟩
  rw [hp.2, hr]
  change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F R.A.zeta12 R.A.primitive_zeta12
    (fullProductIwasawaData R) g = _
  have hnorm := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula
    F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) t x (1 : fullProductCompact R)
  simpa only [Subgroup.coe_one, mul_one, KPGlobalTorusFunctionData.delta,
    MonoidHom.comp_apply, ← ht] using hnorm

 theorem upper_arch_abs_eq_rowRatio_sq (raw : Raw R)
    (hu : (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) 1 0 = 0)
    (w : InfinitePlace F) :
    ((KPGlobalCenterRationalCharacterModulus.localAbsUnit F (.inl w)
      (KPGlobalCubicIdelePairing.ideleEval F (.inl w)
        (KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
          (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu)) : ℝ≥0) : ℝ) =
      KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R w (raw (.inl w))) ^ 2 := by
  let E := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)
  let g := complexMatrix R w (raw (.inl w))
  have hn (z : w.Completion) : ‖E z‖ = ‖z‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).isometry.norm_map_of_map_zero (map_zero E) z
  have h10 : g 1 0 = 0 := by
    change E ((raw (.inl w)).g 1 0) = 0
    rw [raw_upper_eval R raw hu, map_zero]
  change ‖(KPGlobalCubicIdelePairing.ideleEval F (.inl w)
    (KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
      (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu) : w.Completion)‖ ^ 2 = _
  rw [upperRatio_eval R, ← hn, map_div₀]
  change ‖g 0 0 / g 1 1‖ ^ 2 = (KPComplexIntertwinerParameterMajorant.rowRatio g)^2
  congr 1
  unfold KPComplexIntertwinerParameterMajorant.rowRatio KPCplxPrincipalSeriesCharts.bottomRowNormSq
  change ‖g 0 0 / g 1 1‖ = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ / (‖g 1 0‖^2 + ‖g 1 1‖^2)
  rw [Matrix.det_fin_two, h10]
  simp only [mul_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, norm_mul, norm_div]
  field_simp

private theorem finsum_places_split (f : KPHilbert.Place F → ℝ)
    (hf : Function.HasFiniteSupport f) :
    (∑ᶠ v, f v) = (∑ w : InfinitePlace F, f (.inl w)) + ∑ᶠ q : KPFinitePlace F, f (.inr q) := by
  let T := hf.toFinset
  have hs : Function.support f ⊆ (T : Set (KPHilbert.Place F)) := fun _ h => hf.mem_toFinset.mpr h
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  congr 1
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro w hw hnot
    by_contra hn
    exact hnot (Finset.mem_toLeft.mpr (hs hn))
  · symm
    apply finsum_eq_sum_of_support_subset
    intro q hq
    exact Finset.mem_toRight.mpr (hs hq)

theorem raw_borel_height_local_logs (raw : Raw R)
    (hb : scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw) ∈
        KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12) :
    iwasawaLogHeight R (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw)) =
      (∑ w : InfinitePlace F, 2 * Real.log
        (KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R w (raw (.inl w))))) +
      ∑ᶠ q : KPFinitePlace F, Real.log
        (LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q (C.canonical q)
          (fullCompact R P C q)
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (raw (.inr q)))) := by
  let hu := raw_borel_upper R raw hb
  let u := KPGlobalTorusBorelTwistCompatibility.iwasawaUpperRatio F
    (restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 raw) hu
  let a v := KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
    (KPGlobalCubicIdelePairing.ideleEval F v u)
  let f v := Real.log ((a v : ℝ≥0) : ℝ)
  have ha : Function.HasFiniteMulSupport a := (raw_borel_norm_product R raw hb).1
  have hf : Function.HasFiniteSupport f := by
    apply ha.subset
    intro v hv
    contrapose! hv
    have h : a v = 1 := by simpa only [Function.mem_mulSupport, not_not] using hv
    simp [f, h]
  unfold iwasawaLogHeight
  rw [(raw_borel_norm_product R raw hb).2]
  have hc := MonoidHom.map_finprod
    (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom ℝ≥0)) ha
  change (((∏ᶠ v, a v : (ℝ≥0)ˣ) : ℝ≥0) : ℝ) = ∏ᶠ v, ((a v : ℝ≥0) : ℝ) at hc
  change Real.log (((∏ᶠ v, a v : (ℝ≥0)ˣ) : ℝ≥0) : ℝ) = _
  rw [hc, Real.log_finprod (fun v => by exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (a v))))]
  change (∑ᶠ v, f v) = _
  rw [finsum_places_split f hf]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    dsimp only [f, a, u]
    rw [upper_arch_abs_eq_rowRatio_sq R raw hu w]
    exact Real.log_pow _ 2
  · apply finsum_congr
    intro q
    dsimp only [f, a, u]
    rw [raw_upper_forwardAbs R P C q (fullCompact R P C q) raw hu]

 def complexMatrixHom (w : InfinitePlace F) :
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inl w) →*
      KPCplxCharacterHaar.ComplexGL2 :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).toRingHom).comp
    (KPLocalCover.projection F R.A.zeta12 R.A.primitive_zeta12 (.inl w))

private theorem arch_compact_matrix_mem_su2 (w : InfinitePlace F)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inl w))
    (hk : k ∈ complexSU2Compact R w) :
    complexMatrixHom R w k ∈ KPCplxCharacterHaar.complexSU2Embedding.range := by
  have hle : complexSU2Compact R w ≤
      KPCplxCharacterHaar.complexSU2Embedding.range.comap (complexMatrixHom R w) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (KPCplxCharacterHaar.complexSU2Embedding u) i j =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w))
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm
          ((KPCplxCharacterHaar.complexSU2Embedding u) i j))
    exact (RingEquiv.apply_symm_apply _ _).symm
  exact hle hk

 theorem rowRatio_mul_compact (w : InfinitePlace F)
    (g k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inl w))
    (hk : k ∈ complexSU2Compact R w) :
    KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R w (g*k)) =
      KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R w g) := by
  obtain ⟨u, hu⟩ := arch_compact_matrix_mem_su2 R w k hk
  change KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrixHom R w (g*k)) = _
  rw [map_mul, ← hu]
  exact RepresentationTheory.KPComplexStandardIntertwinerGermProve.rowRatio_mul_su2 _ u

 theorem finite_compact_mem_full (q : KPFinitePlace F)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inr q))
    (hk : k ∈ iwasawaCompactFactor R (.inr q)) :
    KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) k ∈
      (fullCompact R P C q).compact.toOpenSubgroup := by
  change _ ∈ (fullCompact R P C q).compact.toOpenSubgroup.toSubgroup
  rw [fullCompact_eq R P C q]
  by_cases hq : Bad F q
  · simp only [iwasawaCompactFactor, if_pos hq] at hk
    obtain ⟨u, hu⟩ := hk
    change KPPGLLocalCover.projection F R.A.zeta12 R.A.primitive_zeta12 (.inr q) _ ∈ KPRankOneCartanGeometry.K0 F q
    rw [KPPGLLocalCover.projection_coverQuotient]
    exact ⟨u, congrArg (KPPGLLocalCover.baseQuotient F (.inr q)) hu⟩
  · simp only [iwasawaCompactFactor, if_neg hq, finiteCompact, dif_neg hq, MonoidHom.mem_range] at hk
    obtain ⟨u, rfl⟩ := hk
    change KPPGLLocalCover.projection F R.A.zeta12 R.A.primitive_zeta12 (.inr q) _ ∈ KPRankOneCartanGeometry.K0 F q
    rw [KPPGLLocalCover.projection_coverQuotient]
    exact ⟨u, rfl⟩

theorem height_raw_local_logs (raw : Raw R) :
    iwasawaLogHeight R (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw)) =
      (∑ w : InfinitePlace F, 2 * Real.log
        (KPComplexIntertwinerParameterMajorant.rowRatio (complexMatrix R w (raw (.inl w))))) +
      ∑ᶠ q : KPFinitePlace F, Real.log
        (LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q (C.canonical q)
          (fullCompact R P C q)
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (raw (.inr q)))) := by
  obtain ⟨t, x, k, hg⟩ := (fullProductIwasawaData R).decomposition
    (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw))
  obtain ⟨rk, hrk, hr⟩ := k.property
  change scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12 rk) = k.val at hr
  let b := raw*rk⁻¹
  have he : raw = b*rk := by simp [b]
  have hb : scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 b) ∈
      KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12 := by
    dsimp only [b]
    rw [map_mul, map_inv, map_mul, map_inv, hr, hg, mul_assoc, mul_inv_cancel, mul_one]
    have ht : t.val ∈ KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12 := by
      obtain ⟨A, hA, h10, h01⟩ := t.property
      exact ⟨A, hA, h10⟩
    have hx : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x ∈
        KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12 := by
      exact borel_root F R.A.zeta12 R.A.primitive_zeta12 x
    exact Subgroup.mul_mem _ ht hx
  rw [he, map_mul, map_mul, hr, height_compact R _ k]
  refine (raw_borel_height_local_logs R P C b hb).trans ?_
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    change 2 * Real.log _ = 2 * Real.log (KPComplexIntertwinerParameterMajorant.rowRatio
      (complexMatrix R w (b (.inl w)*rk (.inl w))))
    rw [rowRatio_mul_compact R w _ _ (hrk (.inl w))]
  · apply finsum_congr
    intro q
    have hm : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) ((b*rk) (.inr q)) =
        KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (b (.inr q)) *
        KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (rk (.inr q)) := map_mul _ _ _
    rw [hm, LocalCompactChange.forwardAbs_mul_compact F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (fullCompact R P C q) _ ⟨_, finite_compact_mem_full R P C q _ (hrk (.inr q))⟩]

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
