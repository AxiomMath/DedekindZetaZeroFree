module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OrdinaryBruhatCellFiltration
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TwistedOpenCellIsomorphism
public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData
public import DedekindZetaZeroFree.Metaplectic.Torus.TameValuationCoordinates

@[expose] public section

section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPLocalTameValuationWhittakerBasis.RawSectionBridge

open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ v)
  (P : Polarization S.heisenberg)

def rawCoefficient : Sign → Representation ℂ (actualTorus F ζ hζ v) (InducedModule P)
  | .plus => tau P
  | .minus => weylConjugate P S.borel.weyl

abbrev rawInduced (ε : Sign) := sectionSpace S.borel P ε 0

private theorem coefficient_smooth_canonical (ε : Sign) :
    SmoothRepresentation (rawCoefficient F ζ hζ v S P ε) := by
  cases ε with
  | plus => exact tau_smooth S.heisenberg P
  | minus =>
    intro b
    obtain ⟨J, hJ⟩ := tau_smooth S.heisenberg P b
    refine ⟨J.comap S.borel.weyl.toMulEquiv.toMonoidHom S.borel.weyl.continuous, ?_⟩
    intro j hj
    exact hJ (S.borel.weyl j) hj

theorem coefficient_smooth_at_depth (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F v m) (ε : Sign) :
    letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m
    SmoothRepresentation (rawCoefficient F ζ hζ v S P ε) := by
  have ht : KPRankOneOpenCellKernel.coverTopology F ζ hζ v =
      KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m :=
    KPPGLLocalCover.finiteTopology_independent F ζ hζ v _ m
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v) hm
  change @SmoothRepresentation _ _ _
    (TopologicalSpace.induced Subtype.val
      (KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m)) _ _ _
  rw [← ht]
  exact coefficient_smooth_canonical F ζ hζ v S P ε

section Equivalence
open KPLocalSmoothRepresentation
open scoped NNReal
open MeasureTheory
variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)

theorem localAbs_norm (y : (KPRankOneInduction.LocalField F v)ˣ) :
 localAbs (KPRankOneInduction.LocalField F v) y = ‖(y : KPRankOneInduction.LocalField F v)‖ := by
 let K := KPRankOneInduction.LocalField F v
 let μ : Measure K := Measure.addHaar
 letI : (Valued.v (R := K) (Γ₀ := WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _
 have h := (IntrinsicHaarScaling.map_mul K μ (y : K) y.ne_zero).symm.trans
  (CompletionHaarModule.map_mul F v μ y)
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
private theorem projection_binding (g : FiniteCover F ζ hζ v) :
 S.borel.projection g = projection F ζ hζ v g := by
 obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inr v)) g
 exact (S.openCell S.polarization).projection_eq g

private theorem modulus_binding (h : Torus F ζ hζ v) :
 (((dB F ζ hζ v (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ v m hm h) : ℝ≥0) : ℝ) : ℂ) = deltaHalf S.borel (S.borel.torus h) := by
 have hp : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (KPRankOneInduction.LocalField F v) (S.borel.coordinate h) 1) = projection F ζ hζ v h.val := by
  rw [← S.torus_full h, ← projection_binding F ζ hζ v S]
  exact (S.borel.torus_projection h).symm
 have hd := KPRankOneInduction.deltaB_eq F v (projection F ζ hζ v)
   (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ v m hm h)
   (KubotaRankTwo.d (KPRankOneInduction.LocalField F v) (S.borel.coordinate h) 1) hp (by simp [KubotaRankTwo.coe_d])
 simp only [KubotaRankTwo.coe_d, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.head_cons, Matrix.head_fin_const, div_one] at hd
 change (((KPRankOneInduction.halfModulus (deltaB F ζ hζ v)
  (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ v m hm h) : ℝ≥0) : ℝ) : ℂ) = _
 rw [KPRankOneInduction.halfModulus_eq, hd]
 simp only [Units.val_one, div_one]
 unfold deltaHalf
 rw [S.borel.retract_torus]
 unfold normPower
 rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
  KPLocalPrincipalSeriesNormWeights.exp_mul_log_real (localAbs_pos _ _), localAbs_norm F v,
  Real.sqrt_eq_rpow]

 def borelBridge : S.borel.B ≃* Borel F ζ hζ v :=
  MulEquiv.subgroupCongr S.borel_eq

include hm in
 theorem retraction_binding (b : S.borel.B) :
    KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v
      (borelBridge F ζ hζ v S b) = S.borel.retract b := by
  obtain ⟨x, hx⟩ := S.borel.borel_decomposition b
  have he : (borelBridge F ζ hζ v S b : FiniteCover F ζ hζ v) =
      (S.borel.retract b : FiniteCover F ζ hζ v) *
        upperRoot F ζ hζ v x := by
    have hv := congrArg Subtype.val hx
    simp only [Subgroup.coe_mul] at hv
    rw [S.torus_full] at hv
    have hn := (S.openCell S.polarization).upper_eq (Multiplicative.toAdd x)
    change (S.borel.upperRoot x : FiniteCover F ζ hζ v) = upperRoot F ζ hζ v x at hn
    rw [hn] at hv
    exact hv
  let q := KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v
  have hb : borelBridge F ζ hζ v S b =
      KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ v m hm (S.borel.retract b) *
        ⟨upperRoot F ζ hζ v x,
          KPLocalInductionJacquetReciprocity.upperRoot_mem_borel F ζ hζ v x⟩ :=
    Subtype.ext he
  rw [hb, map_mul, KPLocalInductionJacquetReciprocity.borelRetraction_torus,
    KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot, mul_one]

include hm in
 theorem full_modulus_binding (b : S.borel.B) :
    (((dB F ζ hζ v (borelBridge F ζ hζ v S b) : ℝ≥0) : ℝ) : ℂ) =
      inducingScalar S.borel 0 b := by
  rw [← KPLocalInductionJacquetReciprocity.dB_retraction F ζ hζ v m hm,
    retraction_binding F ζ hζ v S m hm, modulus_binding F ζ hζ v S m hm]
  simp [inducingScalar, deltaHalf, normPower, S.borel.retract_torus]

def equiv (ε : Sign) :
    PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (rawCoefficient F ζ hζ v S P ε) ≃ₗ[ℂ] rawInduced F ζ hζ v S P ε := by
  let τ := rawCoefficient F ζ hζ v S P ε
  have ht : KPRankOneOpenCellKernel.coverTopology F ζ hζ v =
      finiteCoverTopology F ζ hζ v m :=
    KPPGLLocalCover.finiteTopology_independent F ζ hζ v _ m
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v) hm
  let B := Borel F ζ hζ v
  let q := KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v
  let σ := inflatedRepresentation F ζ hζ v q τ
  let EQ := letI := finiteCoverTopology F ζ hζ v m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ v m hm).2.2.1
    EqSections B σ (dB F ζ hζ v)
  let IND := PrincipalSeries F ζ hζ v m q τ
  have ha (b : S.borel.B) (bvec : InducedModule P) :
      inducingAction S.borel P ε 0 b bvec =
        normalizedSectionRepresentation B σ (dB F ζ hζ v)
          (borelBridge F ζ hζ v S b) bvec := by
    change inducingScalar S.borel 0 b • borelAction S.borel P ε b bvec =
      (((dB F ζ hζ v (borelBridge F ζ hζ v S b) : ℝ≥0) : ℝ) : ℂ) •
        τ (q (borelBridge F ζ hζ v S b)) bvec
    rw [full_modulus_binding F ζ hζ v S m hm,
      retraction_binding F ζ hζ v S m hm]
    cases ε <;> rfl
  have hc (f : FiniteCover F ζ hζ v → InducedModule P) :
      (∀ (b : S.borel.B) (g : FiniteCover F ζ hζ v),
        f (b.val * g) = inducingAction S.borel P ε 0 b (f g)) ↔
      f ∈ EQ := by
    constructor
    · intro hf b g
      obtain ⟨b, rfl⟩ := (borelBridge F ζ hζ v S).surjective b
      exact (hf b g).trans (ha b (f g))
    · intro hf b g
      exact (hf (borelBridge F ζ hζ v S b) g).trans (ha b (f g)).symm
  have hs (f : EQ) :
      SmoothVector vectorRightTranslation f.val ↔ f ∈ IND := by
    let rightFixed (t : TopologicalSpace (FiniteCover F ζ hζ v)) :=
      @Exists (@OpenSubgroup (FiniteCover F ζ hζ v) _ t)
        (fun J => ∀ j ∈ J, ∀ x, f.val (x * j) = f.val x)
    have hsource : SmoothVector vectorRightTranslation f.val ↔
        rightFixed (KPRankOneOpenCellKernel.coverTopology F ζ hζ v) := by
      constructor
      · rintro ⟨J, hJ⟩
        exact ⟨J, fun j hj x => congrFun (hJ j hj) x⟩
      · rintro ⟨J, hJ⟩
        exact ⟨J, fun j hj => funext (hJ j hj)⟩
    rw [hsource]
    rw [show rightFixed (KPRankOneOpenCellKernel.coverTopology F ζ hζ v) =
      rightFixed (finiteCoverTopology F ζ hζ v m) from congrArg rightFixed ht]
    change rightFixed (finiteCoverTopology F ζ hζ v m) ↔ _
    letI := finiteCoverTopology F ζ hζ v m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ v m hm).2.2.1
    change rightFixed (finiteCoverTopology F ζ hζ v m) ↔
      f ∈ smoothSubmodule (eqSectionsRepresentation B σ (dB F ζ hζ v))
    rw [mem_smoothSubmodule]
    constructor
    · rintro ⟨J, hJ⟩
      exact ⟨J, fun j hj => Subtype.ext (funext (hJ j hj))⟩
    · rintro ⟨J, hJ⟩
      exact ⟨J, fun j hj x => congrFun (congrArg Subtype.val (hJ j hj)) x⟩
  let e : sectionSpace S.borel P ε 0 ≃ₗ[ℂ] IND :=
    { toFun := fun f => ⟨⟨f.val, (hc f.val).mp f.property.1⟩,
        (hs ⟨f.val, (hc f.val).mp f.property.1⟩).mp f.property.2⟩
      invFun := fun f => ⟨f.val.val, (hc f.val.val).mpr f.val.property,
        (hs f.val).mpr f.property⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact e.symm

theorem equiv_value (ε : Sign)
    (f : PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (rawCoefficient F ζ hζ v S P ε)) (g : ActualCover F ζ hζ v) :
    (equiv F ζ hζ v S P m hm ε f).val g = f.val.val g := by
  rfl

end Equivalence

end DedekindZetaZeroFree.KPLocalTameValuationWhittakerBasis.RawSectionBridge

end

end

section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPLocalTameValuationWhittakerBasis

open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F))

 abbrev K := LocalField F v

abbrev IsTame : Prop :=
  ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3

def IsCanonicalTamePolarization (S : CanonicalFiniteInducingData F ζ hζ v)
    (P : Polarization S.heisenberg) : Prop :=
  P.L = (KPTameValuationCoordinates.unitCubeClasses (K F v)).comap
    S.cubeClassEquiv.toMonoidHom

def eta (π : (K F v)ˣ) (j : Fin 3) : actualTorus F ζ hζ v :=
  ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ (j.val : ℤ)), by
    refine ⟨KubotaRankTwo.d (K F v) (π ^ (j.val : ℤ)) 1, ?_, ?_, ?_⟩
    · rfl
    · simp [KubotaRankTwo.d]
    · simp [KubotaRankTwo.d]⟩

def coefficient (S : CanonicalFiniteInducingData F ζ hζ v)
    (P : Polarization S.heisenberg) : KPLocalPrincipalSeries.Sign →
      Representation ℂ (actualTorus F ζ hζ v) (InducedModule P)
  | .plus => tau P
  | .minus => weylConjugate P S.borel.weyl

abbrev induced (S : CanonicalFiniteInducingData F ζ hζ v)
    (P : Polarization S.heisenberg) (ε : KPLocalPrincipalSeries.Sign) :=
  sectionSpace S.borel P ε 0

abbrev Jacquet (S : CanonicalFiniteInducingData F ζ hζ v)
    (P : Polarization S.heisenberg) (ε : KPLocalPrincipalSeries.Sign)
    (ψ : Multiplicative (K F v) →* ℂˣ) :=
  KPCoinvariants.Coinvariants (V := induced F ζ hζ v S P ε)
    ((principalSeries S.borel P ε 0).comp
      (S.borel.B.subtype.comp S.borel.upperRoot)) ψ

def ConductorIntegers (π : (K F v)ˣ)
    (ψ : Multiplicative (K F v) →* ℂˣ) : Prop :=
  (∀ x : (valuation (K F v)).integer,
    ψ (Multiplicative.ofAdd (x : K F v)) = 1) ∧
  ∃ x : (valuation (K F v)).integer,
    ψ (Multiplicative.ofAdd ((x : K F v) / (π : K F v))) ≠ 1

private theorem tame_three_not_mem (ht : IsTame F v) :
    (3 : (valuation (K F v)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (K F v)).integer := by
  letI : (KPTameCompact.p F v).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  letI : Field (KPTameCompact.O F v ⧸ KPTameCompact.p F v) :=
    Ideal.Quotient.field _
  let q := Ideal.Quotient.mk (KPTameCompact.p F v)
  letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hu : IsUnit (3 : KPTameCompact.O F v) := by
    apply isUnit_of_map_unit q
    apply isUnit_iff_ne_zero.mpr
    simpa only [q, map_ofNat, Nat.cast_ofNat] using
      CharP.cast_ne_zero_of_ne_of_prime
        (KPTameCompact.O F v ⧸ KPTameCompact.p F v) Nat.prime_three ht
  exact (IsLocalRing.notMem_maximalIdeal.mpr hu)

theorem exists_canonical_tame_polarization
    (S : CanonicalFiniteInducingData F ζ hζ v) (ht : IsTame F v) :
    ∃ P : Polarization S.heisenberg, IsCanonicalTamePolarization F ζ hζ v S P := by
  classical
  let L := (KPTameValuationCoordinates.unitCubeClasses (K F v)).comap
    S.cubeClassEquiv.toMonoidHom
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F v)).symm
      (WithZero.exp (-1 : ℤ)))
  have hp' : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F v)
      (valuation (K F v) p) = WithZero.exp (-1 : ℤ) := by
    rw [hp]; exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F v)).apply_symm_apply _
  have hpne : p ≠ 0 := by
    intro h
    have h0 : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by simpa [h] using hp'
    exact WithZero.exp_ne_zero h0.symm
  let π : (K F v)ˣ := Units.mk0 p hpne
  obtain ⟨e, he, hj⟩ := KPTameValuationCoordinates.valuation_quotient_coordinates
    (K F v) (algebraMap F (K F v) ζ)
    (hζ.map_of_injective (algebraMap F (K F v)).injective)
    (tame_three_not_mem F v ht) π hp'
  have hmap : L.map S.cubeClassEquiv.toMonoidHom =
      KPTameValuationCoordinates.unitCubeClasses (K F v) :=
    Subgroup.map_comap_eq_self_of_surjective S.cubeClassEquiv.surjective _
  let c := (QuotientGroup.congr L
    (KPTameValuationCoordinates.unitCubeClasses (K F v)) S.cubeClassEquiv hmap).trans e
  have hindex : L.index = 3 := by
    rw [Subgroup.index_eq_card, Nat.card_congr c.toEquiv]
    change Nat.card (ZMod 3) = 3
    simp
  have hcard : Nat.card S.D = 9 := by
    rw [Nat.card_congr S.cubeClassEquiv.toEquiv]
    exact KPLocalTorus.card_cubeClasses_tame (K F v)
      ((algebraMap F (K F v) ζ) ^ 4)
      ((hζ.map_of_injective (algebraMap F (K F v)).injective).pow (by decide) (by decide))
      (tame_three_not_mem F v ht)
  have hLcard : Nat.card L = 3 := by
    have h := L.card_mul_index
    rw [hindex, hcard] at h
    omega
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsCyclic L := isCyclic_of_prime_card hLcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L)
  have hiso : FinitePolarization.IsIsotropic S.heisenberg.pairing L := by
    intro x hx y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have hn' : (g : S.D) ^ n = x := congrArg Subtype.val hn
    have hk' : (g : S.D) ^ k = y := congrArg Subtype.val hk
    rw [← hn', ← hk']
    simp [map_zpow, MonoidHom.zpow_apply, S.heisenberg.alternating]
  have hne : {M : Subgroup S.D | L ≤ M ∧
      FinitePolarization.IsIsotropic S.heisenberg.pairing M}.Nonempty :=
    ⟨L, le_rfl, hiso⟩
  obtain ⟨M, hM, hmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {M : Subgroup S.D | L ≤ M ∧
      FinitePolarization.IsIsotropic S.heisenberg.pairing M}) hne
  have hMmax : FinitePolarization.IsMaximalIsotropic S.heisenberg.pairing M :=
    ⟨hM.2, fun N hMN hN => le_antisymm (hmax ⟨hM.1.trans hMN, hN⟩ hMN) hMN⟩
  have hMi : M.index = 3 := by
    rw [KPLocalHeisenbergPolarization.maximal_isotropic_index S.heisenberg.pairing
      S.heisenberg.alternating S.heisenberg.perfect M hMmax, hcard]
    exact Nat.sqrt_eq 3
  have hMc : Nat.card M = 3 := by
    have h := M.card_mul_index
    rw [hMi, hcard] at h
    omega
  have hLM : L = M := Subgroup.eq_of_le_of_card_ge hM.1 (by omega)
  have hLmax : FinitePolarization.IsMaximalIsotropic S.heisenberg.pairing L :=
    hLM ▸ hMmax
  have hA := KPLocalPolarization.preimage_maximal_abelian S.heisenberg.π
    S.heisenberg.quotient_surjective S.heisenberg.pairing
    S.heisenberg.detects_commutation L hLmax
  have hCA : S.heisenberg.C ≤ L.comap S.heisenberg.π := by
    intro x hx
    change S.heisenberg.π x ∈ L
    have hxk : x ∈ S.heisenberg.π.ker := by rwa [S.heisenberg.quotient_kernel]
    rw [MonoidHom.mem_ker] at hxk
    rw [hxk]
    exact L.one_mem
  obtain ⟨ωL, hωL⟩ := KPLocalPolarization.continuous_character_extension
    S.heisenberg.C (L.comap S.heisenberg.π) hCA S.heisenberg.center_open
    hA.1 S.heisenberg.ω
  exact ⟨⟨L, hLmax, ωL, hωL⟩, rfl⟩

theorem actual_valuation_quotient
    (S : CanonicalFiniteInducingData F ζ hζ v)
    (P : Polarization S.heisenberg)
    (ht : IsTame F v) (hP : IsCanonicalTamePolarization F ζ hζ v S P)
    (π : (K F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F v)
      (valuation (K F v) (π : K F v)) = WithZero.exp (-1 : ℤ)) :
    ∃ e : (S.D ⧸ P.L) ≃* Multiplicative (ZMod 3),
      (∀ t : actualTorus F ζ hζ v,
        e (QuotientGroup.mk' P.L (S.heisenberg.π t)) =
          Multiplicative.ofAdd
            (KPCubicExpansion.valuationExponent (K F v) (S.borel.coordinate t) : ZMod 3)) ∧
      (∀ j : Fin 3,
        e (QuotientGroup.mk' P.L (S.heisenberg.π (eta F ζ hζ v π j))) =
          Multiplicative.ofAdd (j.val : ZMod 3)) := by
  obtain ⟨e, he, hj⟩ := KPTameValuationCoordinates.valuation_quotient_coordinates
    (K F v) (algebraMap F (K F v) ζ)
    (hζ.map_of_injective (algebraMap F (K F v)).injective)
    (tame_three_not_mem F v ht) π hπ
  have hmap : P.L.map S.cubeClassEquiv.toMonoidHom =
      KPTameValuationCoordinates.unitCubeClasses (K F v) := by
    rw [hP, Subgroup.map_comap_eq_self_of_surjective S.cubeClassEquiv.surjective]
  let c := QuotientGroup.congr P.L
    (KPTameValuationCoordinates.unitCubeClasses (K F v)) S.cubeClassEquiv hmap
  refine ⟨c.trans e, ?_, ?_⟩
  · intro t
    change e (c (QuotientGroup.mk' P.L (S.heisenberg.π t))) = _
    change e ((QuotientGroup.mk' (KPTameValuationCoordinates.unitCubeClasses (K F v)))
      (S.cubeClassEquiv (S.heisenberg.π _))) = _
    rw [S.cube_class]
    exact he (S.borel.coordinate t)
  · intro j
    change e (c (QuotientGroup.mk' P.L (S.heisenberg.π (eta F ζ hζ v π j)))) = _
    change e ((QuotientGroup.mk' (KPTameValuationCoordinates.unitCubeClasses (K F v)))
      (S.cubeClassEquiv (S.heisenberg.π _))) = _
    rw [S.cube_class,
      S.coordinate_lift (eta F ζ hζ v π j) (π ^ (j.val : ℤ)) rfl]
    exact hj j

section WhittakerCoordinates

variable (S : CanonicalFiniteInducingData F ζ hζ v)
  (P : Polarization S.heisenberg)
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)

local instance : FiniteDimensional ℂ (InducedModule P) :=
  tau_moduleFinite S.heisenberg P

local instance (ε : KPLocalPrincipalSeries.Sign) :
    AddCommGroup (induced F ζ hζ v S P ε) := Submodule.addCommGroup _

local instance (ε : KPLocalPrincipalSeries.Sign) :
    Module ℂ (induced F ζ hζ v S P ε) := Submodule.module _

def actualSectionEquiv (hm : KPLocalChartTopology.MatrixChartDepth F v m)
    (ε : KPLocalPrincipalSeries.Sign) :
    KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (coefficient F ζ hζ v S P ε) ≃ₗ[ℂ] induced F ζ hζ v S P ε := by
  exact RawSectionBridge.equiv F ζ hζ v S P m hm ε

theorem actualSectionEquiv_value (ε : KPLocalPrincipalSeries.Sign)
    (f : KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (coefficient F ζ hζ v S P ε)) (g : ActualCover F ζ hζ v) :
    (actualSectionEquiv F ζ hζ v S P m hm ε f).val g = f.val.val g := by
  exact RawSectionBridge.equiv_value F ζ hζ v S P m hm ε f g

theorem coefficient_smooth (hm : KPLocalChartTopology.MatrixChartDepth F v m)
    (ε : KPLocalPrincipalSeries.Sign) :
    letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m
    SmoothRepresentation (coefficient F ζ hζ v S P ε) := by
  exact RawSectionBridge.coefficient_smooth_at_depth F ζ hζ v S P m hm ε

def jacquetMk (ε : KPLocalPrincipalSeries.Sign)
    (ψ : Multiplicative (K F v) →* ℂˣ) :
    induced F ζ hζ v S P ε →ₗ[ℂ] Jacquet F ζ hζ v S P ε ψ := by
  exact Representation.Coinvariants.mk (k := ℂ) (G := Multiplicative (K F v))
    (V := induced F ζ hζ v S P ε)
    (KPCoinvariants.twistedRepresentation (V := induced F ζ hζ v S P ε)
      ((principalSeries S.borel P ε 0).comp
        (S.borel.B.subtype.comp S.borel.upperRoot)) ψ)

theorem actualSectionEquiv_upperRoot (ε : KPLocalPrincipalSeries.Sign)
    (x : Multiplicative (K F v))
    (f : KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (coefficient F ζ hζ v S P ε)) :
    actualSectionEquiv F ζ hζ v S P m hm ε
      (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ v m hm
        (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ v
          (coefficient F ζ hζ v S P ε))
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ v x) f) =
      principalSeries S.borel P ε 0 (S.borel.upperRoot x)
        (actualSectionEquiv F ζ hζ v S P m hm ε f) := by
  apply Subtype.ext
  funext g
  rw [actualSectionEquiv_value]
  change f.val.val (g * KPLocalSmoothRepresentation.upperRoot F ζ hζ v x) =
    (actualSectionEquiv F ζ hζ v S P m hm ε f).val
      (g * (S.borel.upperRoot x : ActualCover F ζ hζ v))
  rw [actualSectionEquiv_value]
  have hn : (S.borel.upperRoot x : ActualCover F ζ hζ v) =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ v x :=
    (S.openCell P).upper_eq x.toAdd
  rw [hn]

def openCellClass (ε : KPLocalPrincipalSeries.Sign)
    (ψ : Multiplicative (K F v) →* ℂˣ)
    (φ : KPJacquetOpenCell.TestFunctions F v (E := InducedModule P)) :
    Jacquet F ζ hζ v S P ε ψ :=
  jacquetMk F ζ hζ v S P ε ψ
    (actualSectionEquiv F ζ hζ v S P m hm ε
      (KPJacquetOpenCell.ext_w F ζ hζ v m hm
        (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ v
          (coefficient F ζ hζ v S P ε))
        (KPJacquetTwistedCell.coefficient_smooth F ζ hζ v m hm
          (coefficient F ζ hζ v S P ε)
          (coefficient_smooth F ζ hζ v S P m hm ε)) φ))

theorem inducing_evaluation_coordinates
    (ht : IsTame F v) (hP : IsCanonicalTamePolarization F ζ hζ v S P)
    (π : (K F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F v)
      (valuation (K F v) (π : K F v)) = WithZero.exp (-1 : ℤ)) :
    ∃ e : InducedModule P ≃ₗ[ℂ] (Fin 3 → ℂ),
      ∀ b : InducedModule P, ∀ j : Fin 3,
        e b j = b.val (eta F ζ hζ v π j) := by
  classical
  obtain ⟨e, he, hj⟩ := actual_valuation_quotient F ζ hζ v S P ht hP π hπ
  let q : actualTorus F ζ hζ v →* Multiplicative (ZMod 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' P.L).comp S.heisenberg.π)
  let r (d : Multiplicative (ZMod 3)) : actualTorus F ζ hζ v :=
    eta F ζ hζ v π d.toAdd
  have hr (d : Multiplicative (ZMod 3)) : q (r d) = d := by
    change e ((QuotientGroup.mk' P.L) (S.heisenberg.π
      (eta F ζ hζ v π d.toAdd))) = d
    erw [hj]
    change Multiplicative.ofAdd ((d.toAdd.val : ℕ) : ZMod 3) = d
    apply congrArg Multiplicative.ofAdd
    change ((d.toAdd.val : ℕ) : ZMod 3) = d.toAdd
    exact ZMod.natCast_zmod_val d.toAdd
  let a (x : actualTorus F ζ hζ v) : P.L.comap S.heisenberg.π :=
    ⟨x * (r (q x))⁻¹, by
      change S.heisenberg.π (x * (r (q x))⁻¹) ∈ P.L
      apply (QuotientGroup.eq_one_iff _).mp
      apply e.injective
      change q (x * (r (q x))⁻¹) = e 1
      erw [map_mul, map_inv, hr, mul_inv_cancel, map_one]⟩
  have hq (b : P.L.comap S.heisenberg.π) : q b = 1 := by
    change e ((QuotientGroup.mk' P.L) (S.heisenberg.π b)) = 1
    have hb : (QuotientGroup.mk' P.L) (S.heisenberg.π b) = 1 :=
      (QuotientGroup.eq_one_iff (S.heisenberg.π b)).mpr b.property
    exact (congrArg e hb).trans e.map_one
  have ha (b : P.L.comap S.heisenberg.π) (x : actualTorus F ζ hζ v) :
      a ((b : actualTorus F ζ hζ v) * x) = b * a x := by
    apply Subtype.ext
    simp [a, map_mul, hq, mul_assoc]
  have har (d : Multiplicative (ZMod 3)) : a (r d) = 1 := by
    apply Subtype.ext
    simp [a, hr]
  refine ⟨{
    toFun := fun f j => f.val (r (Multiplicative.ofAdd j))
    invFun := fun f => ⟨fun x => (P.ωL (a x) : ℂ) * f (q x).toAdd, ?_⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    left_inv := ?_
    right_inv := ?_ }, fun b j => rfl⟩
  · intro b x
    simp [ha, map_mul, hq, mul_assoc]
  · intro f
    apply Subtype.ext
    funext x
    have hax : (a x : actualTorus F ζ hζ v) * r (q x) = x := by
      dsimp [a]; simp
    exact (f.property (a x) (r (q x))).symm.trans (by rw [hax])
  · intro f
    funext j
    simp only [har, hr, map_one, Units.val_one, one_mul]
    rfl

 def coinvariantsEquivOfIntertwiner
    {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : V ≃ₗ[ℂ] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) :
    Representation.Coinvariants ρ ≃ₗ[ℂ] Representation.Coinvariants σ := by
  let f : ρ.IntertwiningMap σ :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := fun g => LinearMap.ext (he g) }
  let r : σ.IntertwiningMap ρ :=
    { toLinearMap := e.symm.toLinearMap
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro y
        apply e.injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        rw [he, e.apply_symm_apply] }
  exact
    { toLinearMap := Representation.Coinvariants.map ρ σ f
      invFun := Representation.Coinvariants.map σ ρ r
      left_inv := by
        intro x
        induction x using Representation.Coinvariants.induction_on with
        | h x =>
          change Representation.Coinvariants.mk _ (e.symm (e _)) = _
          rw [e.symm_apply_apply]

      right_inv := by
        intro y
        induction y using Representation.Coinvariants.induction_on with
        | h y =>
          change Representation.Coinvariants.mk σ (e (e.symm y)) = _
          rw [e.apply_symm_apply] }

set_option maxHeartbeats 4000000 in

theorem actual_whittaker_dual_bases
    (ht : IsTame F v) (hP : IsCanonicalTamePolarization F ζ hζ v S P)
    (π : (K F v)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F v)
      (valuation (K F v) (π : K F v)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (K F v) →* ℂˣ) (hψ : Continuous ψ) (hψne : ψ ≠ 1)
    (hcond : ConductorIntegers F v π ψ)
    (μ : MeasureTheory.Measure (K F v)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (K F v)).integer : Set (K F v)) = 1)
    (ε : KPLocalPrincipalSeries.Sign) :
    ∃ (b : Module.Basis (Fin 3) ℂ (Jacquet F ζ hζ v S P ε ψ))
      (ell : Module.Basis (Fin 3) ℂ (Module.Dual ℂ (Jacquet F ζ hζ v S P ε ψ))),
      (∀ i j : Fin 3, ell i (b j) = if i = j then 1 else 0) ∧
      (∀ (φ : KPJacquetOpenCell.TestFunctions F v (E := InducedModule P))
        (j : Fin 3),
        ell j (openCellClass F ζ hζ v S P m hm ε ψ φ) =
          ∫ x, ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) *
            (KPJacquetStepFunction.value φ x).val (eta F ζ hζ v π j) ∂μ) := by
  classical
  obtain ⟨c, hc⟩ := inducing_evaluation_coordinates F ζ hζ v S P ht hP π hπ
  letI : NormedAddCommGroup (InducedModule P) :=
    NormedAddCommGroup.induced _ (Fin 3 → ℂ) c.toAddEquiv c.injective
  letI : NormedSpace ℂ (InducedModule P) :=
    NormedSpace.induced ℂ _ (Fin 3 → ℂ) c.toLinearMap
  letI : TopologicalSpace (InducedModule P) :=
    (inferInstance : MetricSpace (InducedModule P)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (coefficient F ζ hζ v S P ε)) := Submodule.addCommGroup _
  letI : Module ℂ (KPLocalSmoothRepresentation.PrincipalSeries F ζ hζ v m
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ v)
      (coefficient F ζ hζ v S P ε)) := Submodule.module _
  let t := actualSectionEquiv F ζ hζ v S P m hm ε
  let ρ := rootTwistedRepresentation
    (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ v m hm
      (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ v
        (coefficient F ζ hζ v S P ε)))
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ v) ψ
  let σ := KPCoinvariants.twistedRepresentation
    ((principalSeries S.borel P ε 0).comp
      (S.borel.B.subtype.comp S.borel.upperRoot)) ψ
  have ht : ∀ x f, t (ρ x f) = σ x (t f) := by
    intro x f
    change t ((↑(ψ x)⁻¹ : ℂ) • _) = (ψ x : ℂ)⁻¹ • _
    rw [map_smul, Units.val_inv_eq_inv_val]
    congr 1
    exact actualSectionEquiv_upperRoot F ζ hζ v S P m hm ε x f
  let q := coinvariantsEquivOfIntertwiner t ht
  let a := KPJacquetTwistedCell.coefficientEquiv F ζ hζ v m hm
    (coefficient F ζ hζ v S P ε) (coefficient_smooth F ζ hζ v S P m hm ε)
    ψ hψ hψne μ
  let e : Jacquet F ζ hζ v S P ε ψ ≃ₗ[ℂ] (Fin 3 → ℂ) :=
    q.symm.trans (a.trans c)
  let b := Module.Basis.ofEquivFun e
  refine ⟨b, b.dualBasis, ?_, ?_⟩
  · intro i j
    simp [Module.Basis.dualBasis_apply, Finsupp.single_apply, eq_comm]
  · intro φ j
    rw [Module.Basis.dualBasis_apply, Module.Basis.ofEquivFun_repr_apply]
    change c (a (q.symm (openCellClass F ζ hζ v S P m hm ε ψ φ))) j = _
    have hq : q.symm (openCellClass F ζ hζ v S P m hm ε ψ φ) =
        KPJacquetTwistedCell.openCellMap F ζ hζ v m hm
          (coefficient F ζ hζ v S P ε) (coefficient_smooth F ζ hζ v S P m hm ε) ψ
          (KPJacquetOpenTestFunction.coinvariantsMk ψ φ) := by
      apply q.injective
      rw [q.apply_symm_apply, KPJacquetTwistedCell.openCellMap_mk]
      rfl
    rw [hq]
    rw [KPJacquetTwistedCell.coefficientEquiv_openCell_mk]
    let L : InducedModule P →ₗ[ℂ] ℂ :=
      (LinearMap.proj j).comp c.toLinearMap
    have hL := (L.toContinuousLinearMap).integral_comp_comm
      (KPJacquetStepFunction.integrable_inverse_character_smul φ ψ hψ μ)
    change L (∫ x, (ψ (Multiplicative.ofAdd x) : ℂ)⁻¹ •
      KPJacquetStepFunction.value φ x ∂μ) = _
    change (∫ x, L ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹ •
      KPJacquetStepFunction.value φ x) ∂μ) =
      L (∫ x, (ψ (Multiplicative.ofAdd x) : ℂ)⁻¹ •
        KPJacquetStepFunction.value φ x ∂μ) at hL
    rw [← hL]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    change L ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹ •
      KPJacquetStepFunction.value φ x) = _
    rw [map_smul]
    change (ψ (Multiplicative.ofAdd x) : ℂ)⁻¹ *
      c (KPJacquetStepFunction.value φ x) j = _
    rw [hc]

end WhittakerCoordinates

end DedekindZetaZeroFree.KPLocalTameValuationWhittakerBasis

end

end
