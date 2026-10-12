module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellTestVector
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TorusEquivariantQuotient
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OrdinaryBruhatCellFiltration

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalJacquetImage
open KPJacquetExceptionalFactorSeparation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable (S : RawFiniteInducingData F ζ hζ q)

section ModelTransport
open KPLocalSmoothRepresentation
open scoped NNReal
variable (w : HeightOneSpectrum (𝓞 F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (R : RawFiniteInducingData F ζ hζ w) (P : Polarization R.heisenberg)
private theorem localAbs_norm (y : (KPRankOneInduction.LocalField F w)ˣ) :
 localAbs (KPRankOneInduction.LocalField F w) y = ‖(y : KPRankOneInduction.LocalField F w)‖ := by
 let K := KPRankOneInduction.LocalField F w
 let μ : Measure K := Measure.addHaar
 letI : (Valued.v (R := K) (Γ₀ := WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _
 have h := (IntrinsicHaarScaling.map_mul K μ (y : K) y.ne_zero).symm.trans
  (CompletionHaarModule.map_mul F w μ y)
 have ha : IntrinsicHaarScaling.abs K (y : K) = localAbs K y := by
  simp only [IntrinsicHaarScaling.abs, if_neg y.ne_zero, IntrinsicHaarScaling.residueCard,
   localAbs, residueCardinality, Real.rpow_intCast]
 have hp := localAbs_pos K y
 rw [ha, ← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr y.ne_zero)] at h
 have hh := congrArg (fun ν : Measure K => ν ((valuation K).integer : Set K)) h
 simp only [Measure.smul_apply, smul_eq_mul] at hh
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 have h0 : μ ((valuation K).integer : Set K) ≠ 0 :=
  by
   have he : ((valuation K).integer : Set K) = ((Valued.v (R := K) (Γ₀ := WithZero (Multiplicative ℤ))).integer : Set K) := by
    ext x
    change valuation K x ≤ 1 ↔ Valued.v x ≤ 1
    exact (Valuation.vle_one_iff (valuation K)).symm.trans (Valuation.vle_one_iff Valued.v)
   rw [he]
   exact (Valued.isOpen_integer K).measure_ne_zero μ ⟨0, by simp⟩
 have ht : μ ((valuation K).integer : Set K) ≠ ⊤ :=
  (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
 have hi := (ENNReal.mul_right_inj h0 ht).mp (by simpa only [mul_comm] using hh)
 have hi' := congrArg ENNReal.toReal hi
 simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le),
  ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))] at hi'
 exact inv_injective hi'
theorem projection_binding (g : FiniteCover F ζ hζ w) :
 R.borel.projection g = projection F ζ hζ w g := by
 obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inr w)) g
 exact (R.openCell R.polarization).projection_eq g

theorem raw_modulus_binding (h : Torus F ζ hζ w) :
 (((dB F ζ hζ w (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ) : ℂ) = deltaHalf R.borel (R.borel.torus h) := by
 have hp : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (KPRankOneInduction.LocalField F w) (R.borel.coordinate h) 1) = projection F ζ hζ w h.val := by
  rw [← R.torus_full h, ← projection_binding F ζ hζ w R]
  exact (R.borel.torus_projection h).symm
 have hd := KPRankOneInduction.deltaB_eq F w (projection F ζ hζ w)
   (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ w m hm h)
   (KubotaRankTwo.d (KPRankOneInduction.LocalField F w) (R.borel.coordinate h) 1) hp (by simp [KubotaRankTwo.coe_d])
 simp only [KubotaRankTwo.coe_d, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.head_cons, Matrix.head_fin_const, div_one] at hd
 change (((KPRankOneInduction.halfModulus (deltaB F ζ hζ w)
  (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ) : ℂ) = _
 rw [KPRankOneInduction.halfModulus_eq, hd]
 simp only [Units.val_one, div_one]
 unfold deltaHalf
 rw [R.borel.retract_torus]
 unfold normPower
 rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
  KPLocalPrincipalSeriesNormWeights.exp_mul_log_real (localAbs_pos _ _), localAbs_norm F w,
  Real.sqrt_eq_rpow]

 def borelBridge : R.borel.B ≃* Borel F ζ hζ w :=
  MulEquiv.subgroupCongr R.borel_eq

include hm in
private theorem retraction_binding (b : R.borel.B) :
    KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
      (borelBridge F ζ hζ w R b) = R.borel.retract b := by
  obtain ⟨x, hx⟩ := R.borel.borel_decomposition b
  have he : (borelBridge F ζ hζ w R b : FiniteCover F ζ hζ w) =
      (R.borel.retract b : FiniteCover F ζ hζ w) *
        upperRoot F ζ hζ w x := by
    have hv := congrArg Subtype.val hx
    simp only [Subgroup.coe_mul] at hv
    rw [R.torus_full] at hv
    have hn := (R.openCell R.polarization).upper_eq (Multiplicative.toAdd x)
    change (R.borel.upperRoot x : FiniteCover F ζ hζ w) = upperRoot F ζ hζ w x at hn
    rw [hn] at hv
    exact hv
  let q := KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
  have hb : borelBridge F ζ hζ w R b =
      KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ w m hm (R.borel.retract b) *
        ⟨upperRoot F ζ hζ w x,
          KPLocalInductionJacquetReciprocity.upperRoot_mem_borel F ζ hζ w x⟩ :=
    Subtype.ext he
  rw [hb, map_mul, KPLocalInductionJacquetReciprocity.borelRetraction_torus,
    KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot, mul_one]

include hm in
private theorem full_modulus_binding (b : R.borel.B) :
    (((dB F ζ hζ w (borelBridge F ζ hζ w R b) : ℝ≥0) : ℝ) : ℂ) =
      inducingScalar R.borel 0 b := by
  rw [← KPLocalInductionJacquetReciprocity.dB_retraction F ζ hζ w m hm,
    retraction_binding F ζ hζ w m hm R, raw_modulus_binding F ζ hζ w m hm R]
  simp [inducingScalar, deltaHalf, normPower, R.borel.retract_torus]

theorem raw_principal_series_equiv_core (ε : Sign) :
    letI : AddCommGroup (sectionSpace R.borel P ε 0) := inferInstance
    let τ : Representation ℂ (Torus F ζ hζ w) (InducedModule P) :=
      match ε with
      | .plus => tau P
      | .minus => weylConjugate P R.borel.weyl
    Nonempty ((principalSeries R.borel P ε 0).Equiv
      (KPLocalInductionJacquetReciprocity.inducedAction F ζ hζ w m hm τ)) := by
  let τ : Representation ℂ (Torus F ζ hζ w) (InducedModule P) :=
    match ε with
    | .plus => tau P
    | .minus => weylConjugate P R.borel.weyl
  change Nonempty ((principalSeries R.borel P ε 0).Equiv
    (KPLocalInductionJacquetReciprocity.inducedAction F ζ hζ w m hm τ))
  have ht : KPRankOneOpenCellKernel.coverTopology F ζ hζ w =
      finiteCoverTopology F ζ hζ w m :=
    KPPGLLocalCover.finiteTopology_independent F ζ hζ w _ m
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ w) hm
  let B := Borel F ζ hζ w
  let q := KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
  let σ := inflatedRepresentation F ζ hζ w q τ
  let EQ := letI := finiteCoverTopology F ζ hζ w m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
    EqSections B σ (dB F ζ hζ w)
  let IND := PrincipalSeries F ζ hζ w m q τ
  have ha (b : R.borel.B) (v : InducedModule P) :
      inducingAction R.borel P ε 0 b v =
        normalizedSectionRepresentation B σ (dB F ζ hζ w)
          (borelBridge F ζ hζ w R b) v := by
    change inducingScalar R.borel 0 b • borelAction R.borel P ε b v =
      (((dB F ζ hζ w (borelBridge F ζ hζ w R b) : ℝ≥0) : ℝ) : ℂ) •
        τ (q (borelBridge F ζ hζ w R b)) v
    rw [full_modulus_binding F ζ hζ w m hm R,
      retraction_binding F ζ hζ w m hm R]
    cases ε <;> rfl
  have hc (f : FiniteCover F ζ hζ w → InducedModule P) :
      (∀ (b : R.borel.B) (g : FiniteCover F ζ hζ w),
        f (b.val * g) = inducingAction R.borel P ε 0 b (f g)) ↔
      f ∈ EQ := by
    constructor
    · intro hf b g
      obtain ⟨b, rfl⟩ := (borelBridge F ζ hζ w R).surjective b
      exact (hf b g).trans (ha b (f g))
    · intro hf b g
      exact (hf (borelBridge F ζ hζ w R b) g).trans (ha b (f g)).symm
  have hs (f : EQ) :
      SmoothVector vectorRightTranslation f.val ↔ f ∈ IND := by
    let rightFixed (t : TopologicalSpace (FiniteCover F ζ hζ w)) :=
      @Exists (@OpenSubgroup (FiniteCover F ζ hζ w) _ t)
        (fun J => ∀ j ∈ J, ∀ x, f.val (x * j) = f.val x)
    have hsource : SmoothVector vectorRightTranslation f.val ↔
        rightFixed (KPRankOneOpenCellKernel.coverTopology F ζ hζ w) := by
      constructor
      · rintro ⟨J, hJ⟩
        exact ⟨J, fun j hj x => congrFun (hJ j hj) x⟩
      · rintro ⟨J, hJ⟩
        exact ⟨J, fun j hj => funext (hJ j hj)⟩
    rw [hsource]
    rw [show rightFixed (KPRankOneOpenCellKernel.coverTopology F ζ hζ w) =
      rightFixed (finiteCoverTopology F ζ hζ w m) from congrArg rightFixed ht]
    change rightFixed (finiteCoverTopology F ζ hζ w m) ↔ _
    letI := finiteCoverTopology F ζ hζ w m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
    change rightFixed (finiteCoverTopology F ζ hζ w m) ↔
      f ∈ smoothSubmodule (eqSectionsRepresentation B σ (dB F ζ hζ w))
    rw [mem_smoothSubmodule]
    constructor
    · rintro ⟨J, hJ⟩
      exact ⟨J, fun j hj => Subtype.ext (funext (hJ j hj))⟩
    · rintro ⟨J, hJ⟩
      exact ⟨J, fun j hj x => congrFun (congrArg Subtype.val (hJ j hj)) x⟩
  let e : sectionSpace R.borel P ε 0 ≃ₗ[ℂ] IND :=
    { toFun := fun f => ⟨⟨f.val, (hc f.val).mp f.property.1⟩,
        (hs ⟨f.val, (hc f.val).mp f.property.1⟩).mp f.property.2⟩
      invFun := fun f => ⟨f.val.val, (hc f.val.val).mpr f.val.property,
        (hs f.val).mpr f.property⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  ext f x
  rfl

 theorem root_binding (x : Multiplicative (LocalField F w)) :
    root R.borel x = upperRoot F ζ hζ w x := by
  exact (R.openCell R.polarization).upper_eq (Multiplicative.toAdd x)

def raw_jacquet_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (ActualCover F ζ hζ w) V}
    {σ : Representation ℂ (ActualCover F ζ hζ w) W} (e : ρ.Equiv σ) :
    (jacquetRepresentation R.borel ρ).Equiv
      (KPLocalInductionJacquetReciprocity.jacquetAction F ζ hζ w σ) := by
  let ρN : Representation ℂ (Multiplicative (LocalField F w)) V := ρ.comp (root R.borel)
  let σN : Representation ℂ (Multiplicative (LocalField F w)) W := rootTwistedRepresentation σ (upperRoot F ζ hζ w) 1
  let fN : ρN.IntertwiningMap σN :=
    ⟨e.toLinearEquiv.toLinearMap, by
      intro x; ext v
      simpa [ρN, σN, rootTwistedRepresentation, root_binding F ζ hζ w R] using
        (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap (root R.borel x) v)
    ⟩
  let gN : σN.IntertwiningMap ρN :=
    ⟨e.symm.toLinearEquiv.toLinearMap, by
      intro x; ext v
      simpa [ρN, σN, rootTwistedRepresentation, root_binding F ζ hζ w R] using
        (Representation.IntertwiningMap.isIntertwining σ ρ e.symm.toIntertwiningMap (root R.borel x) v)
    ⟩
  let f := Representation.Coinvariants.map ρN σN fN
  let g := Representation.Coinvariants.map σN ρN gN
  let el : Representation.Coinvariants ρN ≃ₗ[ℂ] Representation.Coinvariants σN :=
    { toLinearMap := f
      invFun := g
      left_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρN x
        change Representation.Coinvariants.mk ρN (e.symm (e v)) = _
        simp
      right_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σN x
        change Representation.Coinvariants.mk σN (e (e.symm v)) = _
        simp }
  refine Representation.Equiv.mk el ?_
  intro h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρN x
  change Representation.Coinvariants.mk σN (e (ρ (R.borel.torus h : ActualCover F ζ hζ w) v)) =
    Representation.Coinvariants.mk σN (σ h.val (e v))
  rw [R.torus_full]
  exact congrArg (Representation.Coinvariants.mk σN)
    (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap h.val v)

theorem raw_alpha_binding (h : actualTorus F ζ hζ w) :
    KPJacquetOpenCell.alpha F ζ hζ w h = R.borel.weyl h := by
  apply Subtype.ext
  have hw : (KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹ =
      KPPGLLocalCover.W F ζ hζ (Sum.inr w) :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr w))
  have hc : Commute (KPPGLLocalCover.A F ζ hζ (Sum.inr w) (-1)) h.val := by
    have he : KPPGLLocalCover.A F ζ hζ (Sum.inr w) (-1) =
        ((R.borel.cubeLift (-1) : actualTorus F ζ hζ w) : ActualCover F ζ hζ w) := by
      simpa only [pow_succ, pow_zero, one_mul, neg_mul_neg, mul_neg, mul_one, neg_neg] using (R.cube_actual (-1)).symm
    rw [he]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp
      (R.heisenberg.central (R.borel.cubeLift (-1)).property) h).symm)
  rw [← R.torus_full (R.borel.weyl h), R.borel.weyl_from_lift,
    (R.openCell R.polarization).weyl_eq, R.torus_full]
  simp only [KPRankOneOpenCellKernel.signedWeyl, KPRankOneOpenCellKernel.signedWeylRaw, map_mul]
  change KPPGLLocalCover.W F ζ hζ (Sum.inr w) * h.val *
    (KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹ =
    (KPPGLLocalCover.A F ζ hζ (Sum.inr w) (-1) * KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹ *
      h.val * (KPPGLLocalCover.A F ζ hζ (Sum.inr w) (-1) * KPPGLLocalCover.W F ζ hζ (Sum.inr w))
  rw [mul_inv_rev, hw]
  simp only [mul_assoc]
  rw [← mul_assoc (KPPGLLocalCover.A F ζ hζ (Sum.inr w) (-1))⁻¹ h.val,
    hc.inv_left.eq]
  simp only [mul_assoc, inv_mul_cancel_left]

end ModelTransport

section WeightAdapters
open scoped NNReal
open KPLocalSmoothRepresentation
variable (w : HeightOneSpectrum (𝓞 F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (S : RawFiniteInducingData F ζ hζ w)
  (P : Polarization S.heisenberg)
 local instance instFiniteDimensionalComplexExceptionalPlusInducedModule : FiniteDimensional ℂ (InducedModule P) :=
  tau_moduleFinite S.heisenberg P
include hm in
private theorem raw_smooth :
    let ρ := tau P
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation ρ := by
  have ht := KPPGLLocalCover.finiteTopology_independent F ζ hζ w m
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ w) hm
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ w)
  change @SmoothRepresentation _ _ _
    (@instTopologicalSpaceSubtype _ _ (KPPGLLocalCover.finiteTopology F ζ hζ w m)) _ _ _
  rw [ht]
  exact tau_smooth S.heisenberg P

 def comparisonTorus : Torus F ζ hζ w :=
 ⟨S.borel.liftedW⁻¹ * (KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹, by
  let A := (KubotaRankTwo.w (KPRankOneInduction.LocalField F w))⁻¹ *
    (KPStandardLocalRootLifts.weylSwap (KPRankOneInduction.LocalField F w))⁻¹
  refine ⟨A, ?_, ?_, ?_⟩
  · change Matrix.ProjGenLinGroup.mk A = projection F ζ hζ w _
    simp only [map_mul, map_inv]
    rw [← projection_binding F ζ hζ w S S.borel.liftedW,
      S.borel.liftedW_projection]
    dsimp [A]
    rw [map_mul, map_inv, map_inv]
    rfl
  · dsimp [A]
    simp [KubotaRankTwo.w, Matrix.inv_def,
     Matrix.adjugate_fin_two, KPStandardLocalRootLifts.weylSwap, Units.val_mul,
     Matrix.mul_apply, Fin.sum_univ_two]
  · dsimp [A]
    simp [KubotaRankTwo.w, Matrix.inv_def,
     Matrix.adjugate_fin_two, KPStandardLocalRootLifts.weylSwap, Units.val_mul,
     Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem weyl_comparison (h : Torus F ζ hζ w) :
 comparisonTorus F ζ hζ w S * KPJacquetOpenCell.alpha F ζ hζ w h =
 S.borel.weyl h * comparisonTorus F ζ hζ w S := by
 apply Subtype.ext
 have he := S.borel.weyl_from_lift h
 rw [S.torus_full, S.torus_full] at he
 change (_ * _) * (_ * h.val * _) = (S.borel.weyl h).val * (_ * _)
 rw [he]
 group

 theorem scalar_weight (h : Torus F ζ hζ w) :
    (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) : ℂ) =
      inducingScalar S.borel 0 (S.borel.torus h) := by
  simp only [inducingScalar, normPower, zero_mul, Complex.exp_zero, mul_one]
  rw [← raw_modulus_binding F ζ hζ w m hm S]
  change _ = (((KPRankOneInduction.halfModulus (deltaB F ζ hζ w)
    (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ) : ℂ)
  rw [KPRankOneInduction.halfModulus_eq]
  rfl

 local instance instNormedAddCommGroupExceptionalPlusInducedModule : NormedAddCommGroup (InducedModule P) :=
  let e := (Module.finBasis ℂ (InducedModule P)).equivFun
  NormedAddCommGroup.induced _ _ e e.injective
 local instance instNormedSpaceComplexExceptionalPlusInducedModule : NormedSpace ℂ (InducedModule P) :=
  let e := (Module.finBasis ℂ (InducedModule P)).equivFun
  NormedSpace.induced ℂ _ _ e

 def openWeightEquiv :
    (KPJacquetOrdinaryCell.openWeight F ζ hζ w m hm (tau P)).Equiv
      (factorMinus S.borel P) := by
  let k := comparisonTorus F ζ hζ w S
  refine Representation.Equiv.mk
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((tau P).asGroupHom k)) ?_
  intro h
  apply LinearMap.ext
  intro v
  change tau P k ((Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) : ℂ) •
    tau P (KPJacquetOpenCell.alpha F ζ hζ w h) v) =
      inducingScalar S.borel 0 (S.borel.torus h) •
        tau P (S.borel.weyl (S.borel.retract (S.borel.torus h))) (tau P k v)
  rw [scalar_weight F ζ hζ w m hm S, S.borel.retract_torus, map_smul]
  congr 1
  have he := congrArg (fun t => tau P t v) (weyl_comparison F ζ hζ w S h)
  simpa only [map_mul, Module.End.mul_apply] using he

 def closedWeightEquiv :
    (KPJacquetOrdinaryCell.closedWeight F ζ hζ w m hm (tau P)).Equiv
      (factorPlus S.borel P) := by
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_
  intro h
  apply LinearMap.ext
  intro v
  change (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) : ℂ) • tau P h v =
    inducingScalar S.borel 0 (S.borel.torus h) •
      tau P (S.borel.retract (S.borel.torus h)) v
  rw [scalar_weight F ζ hζ w m hm S, S.borel.retract_torus]

end WeightAdapters

theorem independent_plus_jacquet_short_exact (P : Polarization S.heisenberg) : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    exact ∃ (i : (factorMinus S.borel P).IntertwiningMap
        (jacquetRepresentation S.borel (IPlus S.borel P)))
      (p : (jacquetRepresentation S.borel (IPlus S.borel P)).IntertwiningMap
        (factorPlus S.borel P)),
      Function.Injective i ∧ Function.Surjective p ∧ Function.Exact i p := by
  letI : FiniteDimensional ℂ (InducedModule P) := tau_moduleFinite S.heisenberg P
  let eb := (Module.finBasis ℂ (InducedModule P)).equivFun
  letI : NormedAddCommGroup (InducedModule P) :=
    NormedAddCommGroup.induced _ _ eb eb.injective
  letI : NormedSpace ℂ (InducedModule P) := NormedSpace.induced ℂ _ _ eb
  let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
  have hm : KPLocalChartTopology.MatrixChartDepth F q m :=
    KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
  have hs := raw_smooth F ζ hζ q m hm S P
  let μ : Measure (LocalField F q) := Measure.addHaar
  obtain ⟨e⟩ := raw_principal_series_equiv_core F ζ hζ q m hm S P .plus
  let E := raw_jacquet_equiv F ζ hζ q S
    (V := sectionSpace S.borel P .plus 0)
    (W := KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ q m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ q) (tau P))
    (ρ := IPlus S.borel P)
    (σ := KPLocalInductionJacquetReciprocity.inducedAction F ζ hζ q m hm (tau P)) e
  let O := openWeightEquiv F ζ hζ q m hm S P
  let C := closedWeightEquiv F ζ hζ q m hm S P
  let i₀ : (KPJacquetOrdinaryCell.openWeight F ζ hζ q m hm (tau P)).IntertwiningMap
      (KPJacquetOrdinaryCell.torusAction F ζ hζ q m hm (tau P)) :=
    { toLinearMap := KPJacquetOrdinaryCell.openInjection F ζ hζ q m hm (tau P) hs μ
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        exact (KPJacquetOrdinaryCell.ordinary_cell_short_exact F ζ hζ q m hm (tau P) hs μ).2.2.2.1 h v }
  let p₀ : (KPJacquetOrdinaryCell.torusAction F ζ hζ q m hm (tau P)).IntertwiningMap
      (KPJacquetOrdinaryCell.closedWeight F ζ hζ q m hm (tau P)) :=
    { toLinearMap := KPJacquetOrdinaryCell.closedProjection F ζ hζ q m hm (tau P)
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro v
        exact (KPJacquetOrdinaryCell.ordinary_cell_short_exact F ζ hζ q m hm (tau P) hs μ).2.2.2.2 h v }
  let i := E.symm.toIntertwiningMap.comp (i₀.comp O.symm.toIntertwiningMap)
  let p := C.toIntertwiningMap.comp (p₀.comp E.toIntertwiningMap)
  obtain ⟨hi, hex, hp, _, _⟩ :=
    KPJacquetOrdinaryCell.ordinary_cell_short_exact F ζ hζ q m hm (tau P) hs μ
  refine ⟨i, p, ?_, ?_, ?_⟩
  · exact E.symm.injective.comp (hi.comp O.symm.injective)
  · exact C.surjective.comp (hp.comp E.surjective)
  · intro x
    change C (p₀ (E x)) = 0 ↔ ∃ v, E.symm (i₀ (O.symm v)) = x
    constructor
    · intro hx
      have hx₀ : p₀ (E x) = 0 := C.injective (by simpa using hx)
      have hmem : E x ∈ LinearMap.range i₀.toLinearMap := by
        rw [hex]
        exact hx₀
      obtain ⟨v, hv⟩ := hmem
      refine ⟨O v, ?_⟩
      rw [O.symm_apply_apply]
      exact (congrArg E.symm hv).trans (E.symm_apply_apply x)
    · rintro ⟨v, rfl⟩
      have hmem : i₀ (O.symm v) ∈ LinearMap.ker p₀.toLinearMap := by
        rw [← hex]
        exact ⟨O.symm v, rfl⟩
      change p₀ (i₀ (O.symm v)) = 0 at hmem
      simp only [E.apply_symm_apply, hmem, map_zero]

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps
