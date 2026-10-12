module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatedFiniteAnnulus
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CenterKernelSmallBlockBounds

@[expose] public section

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private theorem compact_level_right_invariant
    (I : IwasawaData A) (L : CompactOpenLevel (Cover F ζ hζ q))
    (hL : (L.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup)
    (ε : Sign) (z : ℂ) (ψ : centerCompactLevel F ζ hζ q T A I ε L)
    (g j : Cover F ζ hζ q) (hj : j ∈ L.toOpenSubgroup) :
    (centerCompactTrivialization F ζ hζ q T A I ε z ψ.val).val (g * j) =
      (centerCompactTrivialization F ζ hζ q T A I ε z ψ.val).val g := by
  let f := centerCompactTrivialization F ζ hζ q T A I ε z ψ.val
  let k := I.compactPart g
  let k' : I.compact.toOpenSubgroup := ⟨(k : Cover F ζ hζ q) * j,
    I.compact.toOpenSubgroup.mul_mem k.property (hL hj)⟩
  have hk : f.val (k : Cover F ζ hζ q) = ψ.val.val k := by
    change centerInducingAction F ζ hζ q T A ε z (I.borelPart (k : Cover F ζ hζ q))
      (ψ.val.val (I.compactPart (k : Cover F ζ hζ q))) = _
    rw [I.borelPart_compact, I.compactPart_compact, map_one]
    rfl
  have hk' : f.val (k' : Cover F ζ hζ q) = ψ.val.val k' := by
    change centerInducingAction F ζ hζ q T A ε z (I.borelPart (k' : Cover F ζ hζ q))
      (ψ.val.val (I.compactPart (k' : Cover F ζ hζ q))) = _
    rw [I.borelPart_compact, I.compactPart_compact, map_one]
    rfl
  have he : ψ.val.val k' = ψ.val.val k := ψ.property ⟨j, hj⟩ k k' rfl
  change f.val (g * j) = f.val g
  conv_lhs => rw [I.decomposition g, mul_assoc]
  change f.val ((I.borelPart g : Cover F ζ hζ q) * (k' : Cover F ζ hζ q)) = _
  rw [f.property.1, hk', he, ← hk, ← f.property.1, ← I.decomposition g]

private theorem small_region_subset_nhds (U : Set (LocalField F q))
    (hU : U ∈ nhds (0 : LocalField F q)) :
    ∃ N : ℕ, ∀ v ∈ smallRegion F q N, (v : LocalField F q) ∈ U := by
  obtain ⟨γ, hγ, hγU⟩ := (IsValuativeTopology.hasBasis_nhds_zero' (LocalField F q)).mem_iff.mp hU
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  let m : ℤ := WithZero.log (e γ)
  refine ⟨m.natAbs, ?_⟩
  intro v hv
  apply hγU
  change valuation (LocalField F q) (v : LocalField F q) < γ
  apply e.toOrderIso.lt_iff_lt.mp
  have hv0 : e (valuation (LocalField F q) (v : LocalField F q)) ≠ 0 :=
    (map_ne_zero e).2 (by simpa using v.ne_zero)
  have hγ0 : e γ ≠ 0 := (map_ne_zero e).2 hγ
  apply (WithZero.log_lt_log hv0 hγ0).mp
  change valuationIndex F q v < m
  have hm : -(m.natAbs : ℤ) ≤ m := by omega
  exact lt_of_lt_of_le hv hm

theorem uniform_forward_germ (I : IwasawaData A) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N₀ : ℕ, ∀ (r : ℂˣ), IsRegular F q r →
      ∀ v ∈ smallRegion F q N₀,
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q (v : LocalField F q)) =
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q 0) := by
  classical
  obtain ⟨L, hL, ψ, hψ⟩ := FiniteAnnulusSteps.compact_profile_uniform_laurent
    F ζ hζ q T A P I B rep hrep d φ hφ hcφ
  obtain ⟨χ, hχ⟩ := FiniteAnnulusSteps.forward_uniform_laurent_numerator
    F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ L hL ψ hψ
  have hn : Continuous (nLift F ζ hζ q) := by
    have he : nLift F ζ hζ q = fun s =>
        (A.upperRoot (Multiplicative.ofAdd s) : Cover F ζ hζ q) := by
      funext s
      exact (B.upper_eq s).symm
    rw [he]
    exact continuous_subtype_val.comp (A.upperRoot_continuous.comp continuous_ofAdd)
  have hn0 : nLift F ζ hζ q 0 = 1 := by
    rw [← B.upper_eq]
    change (A.upperRoot 1 : Cover F ζ hζ q) = 1
    simp
  have hU : {x : LocalField F q | nLift F ζ hζ q x ∈ L.toOpenSubgroup} ∈
      nhds (0 : LocalField F q) := by
    exact hn.continuousAt.preimage_mem_nhds
      (L.toOpenSubgroup.isOpen.mem_nhds (by rw [hn0]; exact L.toOpenSubgroup.one_mem))
  obtain ⟨N, hN⟩ := small_region_subset_nhds F q _ hU
  refine ⟨N, ?_⟩
  intro r hr v hv
  rw [hχ r hr]
  have he : openCoordinate F ζ hζ q (v : LocalField F q) =
      openCoordinate F ζ hζ q 0 * nLift F ζ hζ q (v : LocalField F q) := by
    simp [openCoordinate, hn0]
  rw [he]
  exact compact_level_right_invariant F ζ hζ q T A I L hL .minus
    (-additiveParameter F q r)
    ((1 - t F q (r : ℂ))⁻¹ • χ.sum (fun n f => (r : ℂ) ^ n • f))
    _ _ (hN v hv)

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail

end

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private theorem units_borel (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := by
  constructor
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K),
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

private theorem block_measurable (N n : ℕ) :
    MeasurableSet {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} := by
  letI : BorelSpace (LocalField F q)ˣ := units_borel (LocalField F q)
  have hc : IsLocallyConstant (valuationIndex F q) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hv : valuation (LocalField F q) (v : LocalField F q) ≠ 0 :=
      (valuation (LocalField F q)).ne_zero_iff.mpr v.ne_zero
    have he := (valuation (LocalField F q)).locally_const hv
    filter_upwards [Units.continuous_val.continuousAt.preimage_mem_nhds he] with w hw
    exact congrArg (fun a => WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) a)) hw
  exact (isClosed_le continuous_const hc.continuous).measurableSet.inter
    (isOpen_lt hc.continuous continuous_const).measurableSet

private lemma norm_mul (x y : (LocalField F q)ˣ) (z : ℂ) :
    normPower (LocalField F q) (x * y) z =
      normPower (LocalField F q) x z * normPower (LocalField F q) y z := by
  rw [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ x))
    (ne_of_gt (localAbs_pos _ y)), Complex.ofReal_add, mul_add, Complex.exp_add]
  rfl
private lemma norm_pow (x : (LocalField F q)ˣ) (n : ℕ) (z : ℂ) :
    normPower (LocalField F q) (x ^ n) z = normPower (LocalField F q) x (n * z) := by
  have ha : localAbs (LocalField F q) (x ^ n) = localAbs (LocalField F q) x ^ n := by
    induction n with
    | zero => simp [localAbs_one]
    | succ n ih => rw [pow_succ, localAbs_mul, ih, pow_succ]
  simp only [normPower, ha, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  ring
private lemma norm_inv (x : (LocalField F q)ˣ) (z : ℂ) :
    normPower (LocalField F q) x⁻¹ z = (normPower (LocalField F q) x z)⁻¹ := by
  have ha : localAbs (LocalField F q) x⁻¹ = (localAbs (LocalField F q) x)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
  simp [normPower, ha, Real.log_inv, Complex.exp_neg, mul_neg]
private lemma norm_add (x : (LocalField F q)ˣ) (z w : ℂ) :
    normPower (LocalField F q) x (z + w) = normPower (LocalField F q) x z * normPower (LocalField F q) x w := by
  simp [normPower, add_mul, Complex.exp_add]

theorem rootTorus_cube_translate (B : Binding F ζ hζ q A P)
    (v y : (LocalField F q)ˣ) :
    B.rootTorus (v * y ^ 3) = B.rootTorus v * (A.cubeLift (y ^ 2) : H₀) := by
  apply A.torus_injective
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul]
  rw [B.torus_eq, B.torus_eq, SignedBlockAlgebra.cube_sheet F ζ hζ q T A P B]
  rw [hLift, hLift, KPPGLLocalCover.A_mul]
  have hb : KPHilbert.B3 F ζ hζ (Sum.inr q) (v ^ 2) ((y ^ 2) ^ 3) = 1 := by
    rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1,
      SignedBlockAlgebra.BcubeL, inv_one]
  simp only [hb, one_pow, map_one, one_mul]
  congr 1
  rw [mul_pow]
  congr 1
  simp only [← pow_mul]

private theorem center_cube_scalar (y : (LocalField F q)ˣ) (V : CenterModule T) :
    centerTorus F ζ hζ q T A .minus (A.cubeLift y : H₀) V =
      normPower (LocalField F q) y⁻¹ (1 / 2) • V := by
  apply Subtype.ext
  funext h
  change V.val (h * A.weyl (A.cubeLift y : H₀)) = _
  rw [← A.weylCenter_coe, A.weyl_cube]
  rw [Subgroup.mem_center_iff.mp (T.central (A.cubeLift y⁻¹).property) h,
    V.property (A.cubeLift y⁻¹) h]
  change (T.ω (A.cubeLift y⁻¹) : ℂ) * V.val h = _
  rw [A.exceptional_cube, norm_pow]
  norm_num

set_option maxHeartbeats 800000 in

theorem constant_kernel_cube_translate (B : Binding F ζ hζ q A P)
    (V : CenterModule T) (r : ℂˣ) (lam : ℂ) (h : H₀)
    (v y : (LocalField F q)ˣ) :
    (B.eta (kappa F ζ hζ q (v * y ^ 3) 0) : ℂ) *
      (reverseRoot F ζ hζ q T A P B r (v * y ^ 3) V).val h *
      normPower (LocalField F q) (v * y ^ 3) lam =
    ((B.eta (kappa F ζ hζ q v 0) : ℂ) *
      (reverseRoot F ζ hζ q T A P B r v V).val h *
      normPower (LocalField F q) v lam) *
      normPower (LocalField F q) y (-1 - 6 * additiveParameter F q r + 3 * lam) := by
  rw [SignedBlockAlgebra.kappa_eq_one, SignedBlockAlgebra.kappa_eq_one]
  simp only [map_one, Units.val_one, one_mul]
  unfold reverseRoot
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [rootTorus_cube_translate, map_mul]
  change normPower (LocalField F q) ((v * y ^ 3) ^ 2) (-additiveParameter F q r) *
    (centerTorus F ζ hζ q T A .minus (B.rootTorus v)
      (centerTorus F ζ hζ q T A .minus (A.cubeLift (y ^ 2) : H₀) V)).val h *
    normPower (LocalField F q) (v * y ^ 3) lam = _
  rw [center_cube_scalar, map_smul]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp only [mul_pow, norm_mul, norm_pow, inv_pow, norm_inv]
  have hn (x : (LocalField F q)ˣ) (z : ℂ) :
      (normPower (LocalField F q) x z)⁻¹ = normPower (LocalField F q) x (-z) := by
    simp [normPower, neg_mul, Complex.exp_neg]
  rw [hn]
  norm_num only [Nat.cast_ofNat, mul_one] at *
  rw [show -1 - 6 * additiveParameter F q r + 3 * lam =
    (3 * (2 * -additiveParameter F q r) + -1) + 3 * lam by ring,
    norm_add, norm_add]
  ring

private theorem index_mul (u v : (LocalField F q)ˣ) :
    valuationIndex F q (u * v) = valuationIndex F q u + valuationIndex F q v := by
  simp only [valuationIndex, Units.val_mul, map_mul]
  rw [WithZero.log_mul]
  all_goals simp

private theorem index_pow (u : (LocalField F q)ˣ) (n : ℕ) :
    valuationIndex F q (u ^ n) = (n : ℤ) * valuationIndex F q u := by
  induction n with
  | zero => simp [valuationIndex]
  | succ n ih => rw [pow_succ, index_mul, ih]; push_cast; ring

theorem cube_step_scalar (r : ℂˣ) (lam : ℂ) (y : (LocalField F q)ˣ) (n : ℕ)
    (hy : valuationIndex F q y = -(n : ℤ)) :
    normPower (LocalField F q) y (-1 - 6 * additiveParameter F q r + 3 * lam) =
      ((t F q (r : ℂ))⁻¹ * Q F q lam ^ 3) ^ n := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    unfold residueCardinality
    exact_mod_cast Nat.card_pos
  have hlog : (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast (Finite.one_lt_card :
      1 < residueCardinality (LocalField F q)))).ne'
  have hl : (Real.log (localAbs (LocalField F q) y) : ℂ) =
      -(n : ℂ) * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) := by
    rw [localAbs, Real.log_rpow hq]
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    change (valuationIndex F q y : ℂ) * _ = _
    simp [hy]
  have he : Complex.exp ((1 + 6 * additiveParameter F q r - 3 * lam) *
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) =
      (t F q (r : ℂ))⁻¹ * Q F q lam ^ 3 := by
    unfold additiveParameter
    rw [show (1 + 6 * (-Complex.log (r : ℂ) /
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) - 3 * lam) *
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) =
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) -
        6 * Complex.log (r : ℂ) -
        3 * (lam * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) by
          field_simp; ring]
    rw [Complex.exp_sub, Complex.exp_sub]
    rw [show (6 : ℂ) = ((6 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul,
      Complex.exp_log r.ne_zero]
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul]
    have hqe : Complex.exp (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) =
        (residueCardinality (LocalField F q) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hq]
      norm_cast
    rw [hqe]
    unfold t Q
    rw [neg_mul, Complex.exp_neg]
    field_simp
  rw [normPower, hl]
  rw [show (-1 - 6 * additiveParameter F q r + 3 * lam) *
      (-(n : ℂ) * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) =
      (n : ℂ) * ((1 + 6 * additiveParameter F q r - 3 * lam) *
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) by ring,
    Complex.exp_nat_mul, he]

private theorem multiplicative_haar (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure] :
    (multiplicativeMeasure F q μ).IsHaarMeasure := by
  let K := LocalField F q
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have hc : IsCompact (KPCubicUnitIndices.Integers K : Set K) :=
    IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have ho : IsOpen (KPCubicUnitIndices.Integers K : Set K) := (valuation K).isOpen_integer
  have hp : 0 < μ (KPCubicUnitIndices.Integers K : Set K) :=
    ho.measure_pos (μ := μ) ⟨0, by simp⟩
  exact (kp_rankone_cubic_haar_power_measure K μ _
    (ENNReal.toReal_pos hp.ne' hc.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hc.measure_lt_top.ne).symm).1

theorem small_block_cube_translate (N n : ℕ) (y v : (LocalField F q)ˣ)
    (hy : valuationIndex F q y = -(n : ℤ)) :
    y ^ 3 * v ∈ {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} ↔
    v ∈ {v : (LocalField F q)ˣ | -((N + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -(N : ℤ)} := by
  simp only [Set.mem_setOf_eq, index_mul, index_pow, hy]
  push_cast
  omega

theorem constant_kernel_signed_blocks (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (B : Binding F ζ hζ q A P) (V : CenterModule T)
    (N : ℕ) (r : ℂˣ) (lam : ℂ) (h : H₀) (n : ℕ)
    (y : (LocalField F q)ˣ) (hy : valuationIndex F q y = -(n : ℤ)) :
    (∫ v in {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)},
      (B.eta (kappa F ζ hζ q v 0) : ℂ) *
        (reverseRoot F ζ hζ q T A P B r v V).val h *
        normPower (LocalField F q) v lam ∂multiplicativeMeasure F q μ) =
    (∫ v in {v : (LocalField F q)ˣ | -((N + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -(N : ℤ)},
      (B.eta (kappa F ζ hζ q v 0) : ℂ) *
        (reverseRoot F ζ hζ q T A P B r v V).val h *
        normPower (LocalField F q) v lam ∂multiplicativeMeasure F q μ) *
      ((t F q (r : ℂ))⁻¹ * Q F q lam ^ 3) ^ n := by
  letI : BorelSpace (LocalField F q)ˣ := units_borel (LocalField F q)
  letI := multiplicative_haar F q μ
  let ν := multiplicativeMeasure F q μ
  let f : (LocalField F q)ˣ → ℂ := fun v =>
    (B.eta (kappa F ζ hζ q v 0) : ℂ) *
      (reverseRoot F ζ hζ q T A P B r v V).val h * normPower (LocalField F q) v lam
  have he : (fun v : (LocalField F q)ˣ => y ^ 3 * v) ⁻¹'
      {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} =
      {v : (LocalField F q)ˣ | -((N + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -(N : ℤ)} := by
    ext v
    exact small_block_cube_translate F q N n y v hy
  have hi := (measurePreserving_mul_left ν (y ^ 3)).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft (y ^ 3)).measurableEmbedding f
    {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}
  rw [he] at hi
  change (∫ v in _, f v ∂ν) = (∫ v in _, f v ∂ν) * _
  rw [← hi]
  have hf : ∀ v, f (y ^ 3 * v) = f v * ((t F q (r : ℂ))⁻¹ * Q F q lam ^ 3) ^ n := by
    intro v
    dsimp [f]
    rw [mul_comm (y ^ 3), constant_kernel_cube_translate,
      cube_step_scalar F q r lam y n hy]
  simp_rw [hf]
  exact integral_mul_const _ _

private theorem exists_negative_index (n : ℕ) :
    ∃ y : (LocalField F q)ˣ, valuationIndex F q y = -(n : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-(n : ℤ))))
  have hx0 : x ≠ 0 := by
    intro h
    have he := congrArg e hx
    simp [h, e] at he
    exact WithZero.exp_ne_zero he.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  simp only [valuationIndex, Units.val_mk0, hx]
  change WithZero.log (e (e.symm (WithZero.exp (-(n : ℤ))))) = _
  simp

theorem initial_signed_block_numerator (I : IwasawaData A) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) :
    ∃ p : H₀ → ShellNumerator, ∀ r : ℂˣ, IsRegular F q r → ∀ lam : ℂ, ∀ h : H₀,
      (∫ v in {v : (LocalField F q)ˣ | -((N + 3 : ℕ) : ℤ) ≤
        valuationIndex F q v ∧ valuationIndex F q v < -(N : ℤ)},
        reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v
          ∂multiplicativeMeasure F q μ) =
        evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r) := by
  classical
  obtain ⟨L, hL, ψ, hψ⟩ := FiniteAnnulusSteps.compact_profile_uniform_laurent
    F ζ hζ q T A P I B rep hrep d φ hφ hcφ
  obtain ⟨χ, hχ⟩ := FiniteAnnulusSteps.forward_uniform_laurent_numerator
    F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ L hL ψ hψ
  obtain ⟨S, c, hc, hexp⟩ := FiniteAnnulusSteps.reverse_compact_laurent_annulus
    F ζ hζ q T A P I μ B L hL χ (N + 3)
  let E : Set (LocalField F q)ˣ := {v | -((N + 3 : ℕ) : ℤ) ≤
    valuationIndex F q v ∧ valuationIndex F q v < -(N : ℤ)}
  have hE : MeasurableSet E := by simpa [E] using block_measurable F q N 0
  have hsub : E ⊆ annulusRegion F q (N + 3) := by
    intro v hv
    change -((N + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
      valuationIndex F q v ≤ ((N + 3 : ℕ) : ℤ)
    dsimp [E] at hv
    push_cast at *
    exact ⟨hv.1, by omega⟩
  refine ⟨fun h => integratedShellNumerator ((multiplicativeMeasure F q μ).restrict E) S (c h), ?_⟩
  intro r hr lam h
  obtain ⟨_, he⟩ := setIntegral_finite_shell_expansion (multiplicativeMeasure F q μ)
    E hE S (c h) (fun ij hij => (hc h ij hij).mono_set hsub) r (Q F q lam)
      (1 - t F q r)
      (reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h) (by
        intro v hv
        unfold reverseIntegrand
        rw [hχ r hr]
        exact hexp r hr lam h v (hsub hv))
  exact he

theorem signed_block_formula (I : IwasawaData A) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) (hprofile : ∀ (r : ℂˣ), IsRegular F q r →
      ∀ v ∈ smallRegion F q N,
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q (v : LocalField F q)) =
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q 0)) :
    ∃ p : H₀ → ShellNumerator, ∀ (r : ℂˣ), IsRegular F q r →
      ∀ lam : ℂ, ConvergenceRegion F q r lam → ∀ h : H₀, ∀ n : ℕ,
        (∫ v in {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
          valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)},
          reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v ∂multiplicativeMeasure F q μ) =
        (evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r)) *
          ((t F q (r : ℂ))⁻¹ * Q F q lam ^ 3) ^ n := by
  classical
  obtain ⟨p, hp⟩ := initial_signed_block_numerator F ζ hζ q T A P I μ J B
    rep hrep d φ hφ hcφ N
  refine ⟨p, ?_⟩
  intro r hr lam hlam h n
  obtain ⟨y, hy⟩ := exists_negative_index F q n
  let V := (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
    (openCoordinate F ζ hζ q 0)
  let f : (LocalField F q)ˣ → ℂ := fun v =>
    (B.eta (kappa F ζ hζ q v 0) : ℂ) *
      (reverseRoot F ζ hζ q T A P B r v V).val h * normPower (LocalField F q) v lam
  have he (m : ℕ) :
      (∫ v in {v : (LocalField F q)ˣ | -((N + 3 * m + 3 : ℕ) : ℤ) ≤
        valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * m : ℕ) : ℤ)},
        reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v
          ∂multiplicativeMeasure F q μ) =
      ∫ v in {v : (LocalField F q)ˣ | -((N + 3 * m + 3 : ℕ) : ℤ) ≤
        valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * m : ℕ) : ℤ)},
        f v ∂multiplicativeMeasure F q μ := by
    apply setIntegral_congr_fun (block_measurable F q N m)
    intro v hv
    have hs : v ∈ smallRegion F q N := by
      change valuationIndex F q v < -(N : ℤ)
      have hu := hv.2
      push_cast at hu
      omega
    unfold reverseIntegrand
    rw [hprofile r hr v hs]
  have h0 : (∫ v in {v : (LocalField F q)ˣ | -((N + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -(N : ℤ)},
      f v ∂multiplicativeMeasure F q μ) =
      evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r) := by
    simpa using (he 0).symm.trans (hp r hr lam h)
  rw [he n]
  have hb := constant_kernel_signed_blocks F ζ hζ q T A P μ B V N r lam h n y hy
  change (∫ v in _, f v ∂multiplicativeMeasure F q μ) = _ at hb
  rw [hb, h0]

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail

end

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

theorem smallTail_valuationIndex_locallyConstant : IsLocallyConstant (valuationIndex F q) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn : valuation (LocalField F q) (x : LocalField F q) ≠ 0 :=
    (valuation (LocalField F q)).ne_zero_iff.mpr x.ne_zero
  have he : {y : LocalField F q | valuation (LocalField F q) y =
      valuation (LocalField F q) (x : LocalField F q)} ∈ nhds (x : LocalField F q) := by
    open scoped WithZeroTopology in
    have := (IsValuativeTopology.continuous_valuation (R := LocalField F q)).continuousAt
      (x := (x : LocalField F q))
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero hn] at this
    exact this
  have hp := Units.continuous_val.continuousAt.preimage_mem_nhds he
  filter_upwards [hp] with y hy
  change valuation (LocalField F q) (y : LocalField F q) =
    valuation (LocalField F q) (x : LocalField F q) at hy
  simp only [valuationIndex, hy]

private theorem smallTail_units_borel (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := by
  constructor
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K),
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

theorem smallTail_smallRegion_measurable (N : ℕ) : MeasurableSet (smallRegion F q N) := by
  letI : BorelSpace (LocalField F q)ˣ := smallTail_units_borel (LocalField F q)
  exact (isOpen_lt (smallTail_valuationIndex_locallyConstant F q).continuous
    continuous_const).measurableSet

theorem smallTail_ratio_norm_lt_one (r : ℂˣ) (lam : ℂ)
    (hlam : ConvergenceRegion F q r lam) :
    ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ < 1 := by
  have hqpos : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q)))))
  have htpos : 0 < ‖t F q (r : ℂ)‖ := by
    apply norm_pos_iff.mpr
    unfold t
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hqpos.ne'))
      (pow_ne_zero _ (Units.ne_zero r))
  have hnormQ : ‖Q F q lam‖ = Real.exp (-lam.re *
      Real.log (residueCardinality (LocalField F q) : ℝ)) := by
    simp only [Q, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, mul_zero, sub_zero]
  rw [norm_mul, norm_inv, norm_pow, hnormQ, ← Real.exp_nat_mul,
    inv_mul_lt_iff₀ htpos, mul_one]
  convert hlam.2 using 1
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hqpos]
  congr 1
  norm_num
  ring

theorem smallTail_factor_ne_zero (r : ℂˣ) (lam : ℂ)
    (hlam : ConvergenceRegion F q r lam) : smallFactor F q r (Q F q lam) ≠ 0 := by
  intro he
  have hz := (sub_eq_zero.mp he).symm
  have hn := smallTail_ratio_norm_lt_one F q r lam hlam
  rw [hz, norm_one] at hn
  exact lt_irrefl _ hn

theorem smallTail_region_blocks (N : ℕ) :
    smallRegion F q N = ⋃ n : ℕ, {v | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} := by
  ext v
  simp only [smallRegion, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hv
    let k : ℕ := (-valuationIndex F q v - (N : ℤ) - 1).toNat
    have hk : (k : ℤ) = -valuationIndex F q v - (N : ℤ) - 1 := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    refine ⟨k / 3, ?_⟩
    have hmod := Nat.mod_lt k (by decide : 0 < 3)
    have hdiv := Nat.mod_add_div k 3
    push_cast
    omega
  · rintro ⟨n, hn⟩
    push_cast at hn
    omega

theorem smallTail_block_measurable (N n : ℕ) :
    MeasurableSet {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} := by
  letI : BorelSpace (LocalField F q)ˣ := smallTail_units_borel (LocalField F q)
  exact (isClosed_le continuous_const
    (smallTail_valuationIndex_locallyConstant F q).continuous).measurableSet.inter
    (isOpen_lt (smallTail_valuationIndex_locallyConstant F q).continuous
      continuous_const).measurableSet

theorem smallTail_blocks_disjoint (N : ℕ) :
    Pairwise (fun n m : ℕ => Disjoint
      {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
        valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}
      {v : (LocalField F q)ˣ | -((N + 3 * m + 3 : ℕ) : ℤ) ≤
        valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * m : ℕ) : ℤ)}) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro v hv hw
  simp only [Set.mem_setOf_eq] at hv hw
  push_cast at hv hw
  omega

theorem smallTail_integral_of_block_data (N : ℕ) (μ : Measure (LocalField F q)ˣ)
    (f : (LocalField F q)ˣ → ℂ) (r : ℂˣ) (lam : ℂ)
    (hlam : ConvergenceRegion F q r lam) (c : ℂ) (M : ℝ)
    (hint : ∀ n : ℕ, IntegrableOn f
      {v | -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
        valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} μ)
    (hmajor : ∀ n : ℕ, (∫ v in
      {v | -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
        valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}, ‖f v‖ ∂μ) ≤
      M * ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n)
    (hshell : ∀ n : ℕ, (∫ v in
      {v | -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
        valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}, f v ∂μ) =
      c * ((t F q (r : ℂ))⁻¹ * Q F q lam ^ 3) ^ n) :
    IntegrableOn f (smallRegion F q N) μ ∧
      (∫ v in smallRegion F q N, f v ∂μ) = c / smallFactor F q r (Q F q lam) := by
  have hn := smallTail_ratio_norm_lt_one F q r lam hlam
  have hg : Summable (fun n : ℕ =>
      M * ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hn).mul_left M
  have hsum : Summable (fun n : ℕ => ∫ v in
      {v | -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
        valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}, ‖f v‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      hmajor hg
  have hi := integrableOn_iUnion_of_summable_integral_norm hint hsum
  rw [← smallTail_region_blocks F q N] at hi
  refine ⟨hi, ?_⟩
  rw [smallTail_region_blocks F q N, integral_iUnion
    (smallTail_block_measurable F q N) (smallTail_blocks_disjoint F q N)
    (by rwa [← smallTail_region_blocks F q N]), tsum_congr hshell,
    tsum_mul_left, tsum_geometric_of_norm_lt_one hn]
  rfl

theorem small_tail_shells    (I : IwasawaData A) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      MeasurableSet (smallRegion F q N) ∧
      ∃ p : H₀ → ShellNumerator, ∀ (r : ℂˣ), IsRegular F q r →
        ∀ lam : ℂ, ConvergenceRegion F q r lam → ∀ h : H₀,
          IntegrableOn
            (reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h)
            (smallRegion F q N) (multiplicativeMeasure F q μ) ∧
          (∫ v in smallRegion F q N,
            reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v
              ∂multiplicativeMeasure F q μ) =
            evaluateNumerator (p h) r (Q F q lam) / ((1 - t F q r) * smallFactor F q r (Q F q lam)) := by
  obtain ⟨N₀, hgerm⟩ := SmallTail.uniform_forward_germ
    F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ
  refine ⟨N₀, ?_⟩
  intro N hN
  have hprofile : ∀ (r : ℂˣ), IsRegular F q r →
      ∀ v ∈ smallRegion F q N,
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q (v : LocalField F q)) =
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q 0) := by
    intro r hr v hv
    apply hgerm r hr v
    change valuationIndex F q v < -(N : ℤ) at hv
    change valuationIndex F q v < -(N₀ : ℤ)
    exact lt_of_lt_of_le hv (neg_le_neg (by exact_mod_cast hN))
  obtain ⟨p, hp⟩ := SmallTail.signed_block_formula
    F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ N hprofile
  refine ⟨smallTail_smallRegion_measurable F q N, p, ?_⟩
  intro r hr lam hlam h
  obtain ⟨M, hint, hmajor⟩ := SmallTail.absolute_block_majorant
    F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ N hprofile r hr lam hlam h
  have htail := smallTail_integral_of_block_data F q N (multiplicativeMeasure F q μ)
    (reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h)
    r lam hlam (evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r)) M
    hint hmajor (hp r hr lam hlam h)
  refine ⟨htail.1, ?_⟩
  rw [htail.2, div_div]

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion

end
