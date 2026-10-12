module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.Integration.CubicShellSummation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ExceptionalParameterContinuation

@[expose] public section

section

open scoped Valued
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector.NegativeShell
open KPLocalPrincipalSeries
noncomputable section
set_option autoImplicit false

theorem integral_cubic_shell_of_sphere_values
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation K).integer : Set K) = 1)
    (H : K → ℂ) (A : ℂ)
    (hCubic : ∀ a v : Kˣ,
      ((v⁻¹ : Kˣ) : K) ∈ (valuation K).integer →
      valuation K (v : K) = valuation K (a ^ 3 : Kˣ) →
      H (v : K) = normPower K ((a ^ 3)⁻¹ ^ 2) (2 / 3) * A)
    (n : ℕ) (hn : 3 ∣ n + 1) :
    (∫ x in negativeValuationShell K n, H x ∂μ) =
      (1 - (residueCardinality K : ℂ)⁻¹) *
        ((residueCardinality K : ℂ)⁻¹) ^ ((n + 1) / 3) * A := by
  classical
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let q : ℝ := residueCardinality K
  have hq : 1 < q := by
    dsimp [q, residueCardinality]
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  let B (j : ℤ) : Set K := {x | valuation K x ≤ e.symm (WithZero.exp j)}
  have hB (j : ℤ) : B j = {x | KPCubicHaar.abs K x ≤ q ^ j} := by
    ext x
    change valuation K x ≤ e.symm (WithZero.exp j) ↔ _
    rw [← e.toOrderIso.le_iff_le]
    change e (valuation K x) ≤ e (e.symm (WithZero.exp j)) ↔ _
    rw [e.apply_symm_apply]
    by_cases hx : x = 0
    · subst x
      simp [KPCubicHaar.abs, le_of_lt (zpow_pos hq0 j)]
    have he0 : e (valuation K x) ≠ 0 := by simpa [e] using hx
    simp only [Set.mem_setOf_eq, KPCubicHaar.abs, if_neg hx]
    change e (valuation K x) ≤ WithZero.exp j ↔ q ^ WithZero.log (e (valuation K x)) ≤ q ^ j
    rw [zpow_le_zpow_iff_right₀ hq, ← WithZero.exp_log he0, WithZero.exp_le_exp]
    simp
  have hBm (j : ℤ) : MeasurableSet (B j) := by
    apply IsClosed.measurableSet
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hxl : e.symm (WithZero.exp j) < valuation K x := by
      simpa only [B, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hx
    have hx0 : valuation K x ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hxl)
    filter_upwards [(valuation K).locally_const hx0] with y hy
    change ¬ valuation K y ≤ e.symm (WithZero.exp j)
    rw [hy, not_le]
    exact hxl
  have hmass (j : ℤ) : μ (B j) = ENNReal.ofReal (q ^ j) := by
    rw [hB]
    simpa only [q, residueCardinality, hμ, mul_one] using
      NonarchimedeanHaarScaling.closedBall_measure K μ j
  have hs : negativeValuationShell K n = B (n + 1) \ B n := by
    ext x
    change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) ↔
      valuation K x ≤ e.symm (WithZero.exp ((n : ℤ) + 1)) ∧
        ¬ valuation K x ≤ e.symm (WithZero.exp (n : ℤ))
    rw [← e.toOrderIso.le_iff_le, ← e.toOrderIso.le_iff_le]
    change e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) ↔
      e (valuation K x) ≤ e (e.symm (WithZero.exp ((n : ℤ) + 1))) ∧
        ¬ e (valuation K x) ≤ e (e.symm (WithZero.exp (n : ℤ)))
    rw [e.apply_symm_apply, e.apply_symm_apply, not_le]
    constructor
    · intro hx
      rw [hx]
      simp only [Nat.cast_add, Nat.cast_one, le_refl, WithZero.exp_lt_exp, and_true,
        true_and]
      omega
    · rintro ⟨hx1, hx2⟩
      have he0 : e (valuation K x) ≠ 0 := ne_of_gt (lt_trans (WithZero.exp_pos) hx2)
      rw [← WithZero.exp_log he0, WithZero.exp_le_exp] at hx1
      rw [← WithZero.exp_log he0, WithZero.exp_lt_exp] at hx2
      have hl : WithZero.log (e (valuation K x)) = ((n + 1 : ℕ) : ℤ) := by omega
      rw [← WithZero.exp_log he0, hl]
  have hsm : MeasurableSet (negativeValuationShell K n) := by
    rw [hs]
    exact (hBm _).diff (hBm _)
  have hsub : B (n : ℤ) ⊆ B ((n : ℤ) + 1) := by
    intro x hx
    change valuation K x ≤ e.symm (WithZero.exp (n : ℤ)) at hx
    exact hx.trans (e.symm.toOrderIso.monotone (by rw [WithZero.exp_le_exp]; omega))
  have hreal : μ.real (negativeValuationShell K n) = q ^ ((n : ℤ) + 1) - q ^ (n : ℤ) := by
    rw [hs, measureReal_diff hsub (hBm _) (by rw [hmass]; exact ENNReal.ofReal_ne_top)]
    simp only [measureReal_def, hmass, ENNReal.toReal_ofReal (le_of_lt (zpow_pos hq0 _))]
  let k : ℕ := (n + 1) / 3
  have hk : n + 1 = 3 * k := by
    dsimp [k]
    exact (Nat.mul_div_cancel' hn).symm
  obtain ⟨a₀, ha₀⟩ := valuation_surjective (e.symm (WithZero.exp (k : ℤ)))
  have ha0 : a₀ ≠ 0 := by
    intro h
    subst a₀
    have hh := congrArg e ha₀
    exact (WithZero.exp_ne_zero (a := (k : ℤ))) (by simpa using hh.symm)
  let a : Kˣ := Units.mk0 a₀ ha0
  have hea : e (valuation K (a : K)) = WithZero.exp (k : ℤ) := by
    change e (valuation K a₀) = _
    rw [ha₀, e.apply_symm_apply]
  have hea3 : e (valuation K (a ^ 3 : Kˣ)) = WithZero.exp ((n + 1 : ℕ) : ℤ) := by
    simp only [Units.val_pow_eq_pow_val, map_pow, hea, ← WithZero.exp_nsmul]
    congr 1
    rw [hk]
    push_cast
    simp [nsmul_eq_mul, mul_comm]
  have hp : normPower K ((a ^ 3)⁻¹ ^ 2) (2 / 3) = (q : ℂ) ^ (-4 * (k : ℤ)) := by
    have hev : e (valuation K (((a ^ 3)⁻¹ ^ 2 : Kˣ) : K)) = WithZero.exp (-6 * (k : ℤ)) := by
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow, map_inv₀,
        hea, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    rw [normPower, localAbs, hev, WithZero.log_exp, Real.log_rpow hq0]
    change Complex.exp ((2 / 3) * (((-6 * (k : ℤ) : ℤ) : ℝ) * Real.log q : ℝ)) = _
    have heq : (2 / 3 : ℂ) * (((-6 * (k : ℤ) : ℤ) : ℝ) * Real.log q : ℝ) =
        ((-4 * (k : ℤ) : ℤ) : ℂ) * (Real.log q : ℂ) := by push_cast; ring
    rw [heq, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hq0]
  have hval : Set.EqOn H (fun _ => (q : ℂ) ^ (-4 * (k : ℤ)) * A)
      (negativeValuationShell K n) := by
    intro x hx
    have hex : e (valuation K x) = WithZero.exp ((n + 1 : ℕ) : ℤ) := hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simpa using hex
    let v : Kˣ := Units.mk0 x hx0
    have hvin : ((v⁻¹ : Kˣ) : K) ∈ (valuation K).integer := by
      change valuation K (x⁻¹) ≤ 1
      rw [← e.toOrderIso.le_iff_le]
      change e (valuation K (x⁻¹)) ≤ e 1
      rw [map_one, map_inv₀, map_inv₀, hex,
        ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hv : valuation K (v : K) = valuation K (a ^ 3 : Kˣ) := by
      apply e.injective
      exact hex.trans hea3.symm
    simpa only [hp, v, Units.val_mk0] using hCubic a v hvin hv
  rw [setIntegral_congr_fun hsm hval, setIntegral_const, hreal]
  change ((q ^ ((n : ℤ) + 1) - q ^ (n : ℤ) : ℝ) : ℂ) *
    ((q : ℂ) ^ (-4 * (k : ℤ)) * A) = _
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  push_cast
  rw [show (n : ℤ) + 1 = 3 * (k : ℤ) by exact_mod_cast hk]
  have hnz : (n : ℤ) = 3 * (k : ℤ) - 1 := by
    have hh : (n : ℤ) + 1 = 3 * (k : ℤ) := by exact_mod_cast hk
    omega
  rw [hnz]
  rw [zpow_sub₀ hqc, zpow_one]
  have hpowers : (q : ℂ) ^ (3 * (k : ℤ)) * (q : ℂ) ^ (-4 * (k : ℤ)) =
      (q : ℂ) ^ (-(k : ℤ)) := by
    rw [← zpow_add₀ hqc]
    congr 1
    ring
  change ((q : ℂ) ^ (3 * (k : ℤ)) - (q : ℂ) ^ (3 * (k : ℤ)) / (q : ℂ)) *
    ((q : ℂ) ^ (-4 * (k : ℤ)) * A) =
      (1 - (q : ℂ)⁻¹) * ((q : ℂ)⁻¹) ^ k * A
  rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  calc
    _ = (1 - (q : ℂ)⁻¹) *
        ((q : ℂ) ^ (3 * (k : ℤ)) * (q : ℂ) ^ (-4 * (k : ℤ))) * A := by ring
    _ = _ := by rw [hpowers]

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector.NegativeShell

end

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector.NegativeShell
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false

open LocalFieldTheory.IsNonarchimedeanLocalField

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (q : HeightOneSpectrum (𝓞 F)) (S : RawFiniteInducingData F ζ hζ q)
private theorem central (P : Polarization S.heisenberg)
    (e : rootsOfUnity 3 F) (V : InducedModule P) :
    tau P ((S.openCell P).centralTorus e) V = (ordinaryIota F ζ hζ e : ℂ) • V := by
  have hg := (S.openCell P).genuine .plus e V
  simpa [inducingAction, inducingScalar, deltaHalf, borelAction,
    S.borel.retract_torus, (S.openCell P).central_coordinate, normPower,
    localAbs_one, S.openCell_ordinary] using hg
private theorem rootmul (P : Polarization S.heisenberg)
    (a b : (LocalField F q)ˣ) :
    (S.openCell P).rootTorus a * (S.openCell P).rootTorus b =
      (S.openCell P).centralTorus
        (KPHilbert.B3 F ζ hζ (Sum.inr q) (a ^ 2) (b ^ 2) ^ 2) *
          (S.openCell P).rootTorus (a * b) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← S.torus_full, (S.openCell P).torus_eq,
    ← S.torus_full, (S.openCell P).torus_eq,
    ← S.torus_full, (S.openCell P).central_eq,
    ← S.torus_full, (S.openCell P).torus_eq]
  simp only [KPRankOneOpenCellKernel.hLift]
  rw [KPPGLLocalCover.A_mul, mul_pow]
private theorem tame (hgood : valuation (LocalField F q) (6 : LocalField F q) = 1) :
    ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3 := by
  have hunit : IsUnit (6 : KPTameCompact.O F q) :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (LocalField F q)))).mpr (by rw [map_ofNat]; exact hgood)
  letI : Nontrivial (KPTameCompact.O F q ⧸ KPTameCompact.p F q) := by
    change Nontrivial (IsLocalRing.ResidueField (valuation (LocalField F q)).integer)
    infer_instance
  intro hc
  have hz : (6 : KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 0 := by
    apply (ringChar.spec _ 6).mpr
    rw [hc]
    norm_num
  have hu := hunit.map (Ideal.Quotient.mk (KPTameCompact.p F q))
  rw [map_ofNat, hz] at hu
  exact not_isUnit_zero hu
private theorem invmask (P : Polarization S.heisenberg) (V : InducedModule P)
    (hu : ∀ u : (KPTameCompact.O F q)ˣ,
      tau P ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u)) V = V)
    (u : (KPTameCompact.O F q)ˣ) (v : (LocalField F q)ˣ) :
    tau P (((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u * v))⁻¹) V =
      (ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q)
        (KPTameCompact.unitInclusion F q u ^ 2) (v ^ 2) ^ 2) : ℂ) •
        tau P (((S.openCell P).rootTorus v)⁻¹) V := by
  let a := (S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u)
  let b := (S.openCell P).rootTorus v
  let r := (S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u * v)
  let z := (S.openCell P).centralTorus (KPHilbert.B3 F ζ hζ (Sum.inr q)
    (KPTameCompact.unitInclusion F q u ^ 2) (v ^ 2) ^ 2)
  have he : a * b = z * r := rootmul F ζ hζ q S P _ _
  have hr : r⁻¹ = b⁻¹ * a⁻¹ * z := by
    apply inv_eq_of_mul_eq_one_left
    rw [mul_assoc, ← he]
    simp [mul_assoc]
  have ha : tau P a⁻¹ V = V := by
    have hh := congrArg (tau P a⁻¹) (hu u)
    rw [← Module.End.mul_apply, ← map_mul] at hh
    simpa [a] using hh.symm
  change tau P r⁻¹ V = _
  rw [hr, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    central F ζ hζ q S, map_smul, ha, map_smul]
private theorem phase (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ) (hπ : valuationMap (LocalField F q) (Additive.ofMul π) = -1)
    (u : (KPTameCompact.O F q)ˣ) (v : (LocalField F q)ˣ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q)
      (KPTameCompact.unitInclusion F q u ^ 2) (v ^ 2) ^ 2 =
        KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^
          (8 * valuationMap (LocalField F q) (Additive.ofMul v)) := by
  have hp : valuationMap (LocalField F q) (Additive.ofMul π⁻¹) = 1 := by
    rw [valuationMap_ofMul_inv, hπ]; norm_num
  obtain ⟨w, hw⟩ := exists_integerUnit_mul_uniformizer_zpow (LocalField F q) π⁻¹ hp v
  have hwB := KPTameCompact.B3_units F q ζ hζ ht u w
  have ha := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1 π
    (KPTameCompact.unitInclusion F q u)
  simp only [KPHilbert.B3_canonical] at hwB ha ⊢
  simp only [map_pow, MonoidHom.pow_apply]
  conv_lhs => rw [← hw]
  simp only [map_mul, MonoidHom.mul_apply, map_zpow, MonoidHom.zpow_apply,
    map_inv, MonoidHom.inv_apply]
  change KPHilbert.finiteThreePairing F ζ hζ q
    (ClassFieldTheory.powerClass (LocalField F q) 3 (KPTameCompact.unitInclusion F q u))
    (ClassFieldTheory.powerClass (LocalField F q) 3 ((integerUnitsToFieldUnits (LocalField F q)) w)) = 1 at hwB
  rw [hwB, one_mul, ← ha]
  simp only [inv_zpow, inv_inv, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

private theorem valunit (u : (KPTameCompact.O F q)ˣ) :
    valuation (LocalField F q) (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 := by
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation (LocalField F q)))).mp u.isUnit

private theorem detecting
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (KPTameCompact.K F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (KPTameCompact.K F q)
      (valuation (KPTameCompact.K F q) (π : KPTameCompact.K F q)) =
        WithZero.exp (-1 : ℤ))
    (e : ℤ) (he : (e : ZMod 3) ≠ 0) :
    ∃ u : (KPTameCompact.O F q)ˣ,
      (((KPLocalCover.coefficientEmbedding F ζ hζ
        (KPLocalCover.threeToSix F
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π
            (KPTameCompact.unitInclusion F q u)))) : ℂ) ^ e) ≠ 1 := by
  let K := KPTameCompact.K F q
  let p := ClassFieldTheory.powerClass K (3 : ℕ+)
  let B := KPHilbert.finiteThreePairing F ζ hζ q
  have hvπ : valuationMap K (Additive.ofMul π) = -1 := by
    change Multiplicative.toAdd (WithZero.unzero _) = -1
    rw [WithZero.toAdd_unzero_eq_log]
    change WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (KPTameCompact.K F q))
      (valuation (KPTameCompact.K F q) (π : KPTameCompact.K F q))) = -1
    rw [hπ, WithZero.log_exp]
  have hvπinv : valuationMap K (Additive.ofMul π⁻¹) = 1 := by
    rw [valuationMap_ofMul_inv, hvπ]
    norm_num
  by_contra hn
  push Not at hn
  have hu : ∀ u : (KPTameCompact.O F q)ˣ,
      B (p (π ^ e)) (p (KPTameCompact.unitInclusion F q u)) = 1 := by
    intro u
    have hc : KPLocalCover.coefficientEmbedding F ζ hζ
        (KPLocalCover.threeToSix F
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π
            (KPTameCompact.unitInclusion F q u)) ^ e) = 1 := by
      apply Units.ext
      simpa only [map_zpow, Units.val_zpow_eq_zpow_val, Units.val_one] using hn u
    have h6 := KPLocalCover.coefficientEmbedding_injective F ζ hζ
      (hc.trans (map_one _).symm)
    have h3 : (KPHilbert.B3 F ζ hζ (Sum.inr q) π
        (KPTameCompact.unitInclusion F q u)) ^ e = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ))
        (by simpa only [← map_zpow, map_one] using h6)
    rw [KPHilbert.B3_canonical] at h3
    simpa only [p, B, map_zpow, MonoidHom.zpow_apply] using h3
  have hs : B (p π) (p π) = 1 := by
    simpa only [KPHilbert.B3_canonical] using
      ((KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 π).1
  have hall : ∀ x : Kˣ, B (p (π ^ e)) (p x) = 1 := by
    intro x
    obtain ⟨u, hx⟩ := exists_integerUnit_mul_uniformizer_zpow K π⁻¹ hvπinv x
    rw [← hx]
    simp only [map_mul, map_zpow, map_inv, MonoidHom.zpow_apply, MonoidHom.inv_apply]
    have huu := hu u
    simp only [map_zpow, MonoidHom.zpow_apply] at huu
    change B (p π) (p ((integerUnitsToFieldUnits K) u)) ^ e = 1 at huu
    rw [huu]
    simp [hs]
  have hclass : p (π ^ e) = 1 := by
    apply NormalizedSymbolTransport.inverseTransport_left_nondegenerate
      (KPHilbert.finiteRootsThree F ζ hζ q)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (KPHilbert.rootsThree F ζ hζ) q)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3
        (KPHilbert.rootsThree F ζ hζ) q).2.2.1.1
    intro b
    induction b using QuotientGroup.induction_on with
    | H x => exact hall x
  obtain ⟨t, ht⟩ := (ClassFieldTheory.powerClass_eq_one_iff K 3 (π ^ e)).mp hclass
  have hv := congrArg (fun x : Kˣ => valuationMap K (Additive.ofMul x)) ht
  change valuationMap K (Additive.ofMul (t ^ (3 : ℕ))) =
    valuationMap K (Additive.ofMul (π ^ e)) at hv
  rw [valuationMap_ofMul_pow, valuationMap_ofMul_zpow, hvπ] at hv
  apply he
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd e 3).mpr
  refine ⟨-valuationMap K (Additive.ofMul t), ?_⟩
  linarith

theorem actual_noncubic_shell_unit_eigenvalue
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    (S : RawFiniteInducingData F ζ hζ q)
    (hgood : valuation (LocalField F q) (6 : LocalField F q) = 1)
    (P : Polarization S.heisenberg)
    (V : InducedModule P) (H : LocalField F q → ℂ)
    (t : actualTorus F ζ hζ q)
    (hBruhat : ∀ v : (LocalField F q)ˣ,
      ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q →
      H (v : LocalField F q) =
        normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) *
          ((tau P) (((S.openCell P).rootTorus v)⁻¹) V).val t)
    (hUnit : ∀ u : (KPTameCompact.O F q)ˣ,
      tau P ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u)) V = V)
    (n : ℕ) (hn : ¬ 3 ∣ n + 1) :
    ∃ (u : (LocalField F q)ˣ) (c : ℂ),
      valuation (LocalField F q) (u : LocalField F q) = 1 ∧ c ≠ 1 ∧
      ∀ x ∈ negativeValuationShell (LocalField F q) n,
        H ((u : LocalField F q) * x) = c * H x := by
  have ht := tame F q hgood
  obtain ⟨πa, hπa⟩ := valuationMap_surjective (LocalField F q) (-1)
  let π := Additive.toMul πa
  have hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ) := by
    have hv : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q))) = -1 := by
      change Multiplicative.toAdd (WithZero.unzero _) = -1 at hπa
      rw [WithZero.toAdd_unzero_eq_log] at hπa
      exact hπa
    rw [← hv, WithZero.exp_log]
    simp
  have he : ((8 * ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod 3) ≠ 0 := by
    intro he
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp he
    have hn' : (3 : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by omega
    exact hn (by exact_mod_cast hn')
  obtain ⟨u, hu⟩ := detecting
    F ζ hζ q ht π hπ (8 * ((n + 1 : ℕ) : ℤ)) he
  let c : ℂ := (ordinaryIota F ζ hζ
    (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u)) : ℂ) ^
      (8 * ((n + 1 : ℕ) : ℤ))
  refine ⟨KPTameCompact.unitInclusion F q u, c, valunit F q u, hu, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hh
    simp [negativeValuationShell, hh] at hx
  let v : (LocalField F q)ˣ := Units.mk0 x hx0
  have hv : valuationMap (LocalField F q) (Additive.ofMul v) = ((n + 1 : ℕ) : ℤ) := by
    change Multiplicative.toAdd (WithZero.unzero _) = _
    rw [WithZero.toAdd_unzero_eq_log]
    change WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) x)) = _
    rw [hx, WithZero.log_exp]
  have hvint : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q := by
    change valuation (LocalField F q) (↑v⁻¹) ≤ 1
    apply (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q))).mp
    simp only [map_one, Units.val_inv_eq_inv_val, map_inv₀]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) x))⁻¹ ≤ 1
    rw [hx]
    rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have huvint : (((KPTameCompact.unitInclusion F q u * v)⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q := by
    change valuation (LocalField F q) (↑(KPTameCompact.unitInclusion F q u * v)⁻¹) ≤ 1
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, map_inv₀, map_mul, valunit F q u, one_mul]
    simpa only [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀] using hvint
  have hnrm : normPower (LocalField F q) ((KPTameCompact.unitInclusion F q u * v)⁻¹ ^ 2) (1 / 2) =
      normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) := by
    unfold normPower localAbs
    congr 4
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul,
      map_pow, map_inv₀, map_mul, valunit F q u, one_mul]
  change H (↑(KPTameCompact.unitInclusion F q u * v)) = c * H (↑v)
  rw [hBruhat _ huvint, hBruhat _ hvint, hnrm, invmask F ζ hζ q S P V hUnit,
    phase F ζ hζ q ht π hπa u v, hv, map_zpow, Units.val_zpow_eq_zpow_val]
  change _ * (c • tau P (((S.openCell P).rootTorus v)⁻¹) V).val t = _
  change _ * (c * _) = _
  ring

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector.NegativeShell

end

section

open scoped Valued
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector.NegativeShell
noncomputable section
set_option autoImplicit false

theorem integral_shell_eq_zero_of_unit_eigenfunction
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : K → ℂ) (n : ℕ) (u : Kˣ)
    (hu : valuation K (u : K) = 1)
    (c : ℂ) (hc : c ≠ 1)
    (hEigen : ∀ x ∈ negativeValuationShell K n,
      H ((u : K) * x) = c * H x) :
    (∫ x in negativeValuationShell K n, H x ∂μ) = 0 := by
  classical
  set s := negativeValuationShell K n with hs_def
  have hu0 : (u : K) ≠ 0 := u.ne_zero

  have habs : KPCubicHaar.abs K (u : K) = 1 := by
    rw [KPCubicHaar.abs, if_neg hu0, hu]
    simp
  have hmap : Measure.map (fun x : K => (u : K) * x) μ = μ := by
    rw [NonarchimedeanHaarScaling.map_mul K μ (u : K) hu0, habs]
    simp
  have hval (x : K) : valuation K ((u : K) * x) = valuation K x := by
    rw [map_mul, hu, one_mul]

  let φ : K ≃ᵐ K :=
    { toEquiv :=
        { toFun := fun x => (u : K) * x
          invFun := fun x => ((u⁻¹ : Kˣ) : K) * x
          left_inv := by intro x; simp [mul_assoc]
          right_inv := by intro x; simp [mul_assoc] }
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }
  have hmapφ : Measure.map φ μ = μ := hmap
  have hpre : φ ⁻¹' s = s := by
    show (fun x : K => (u : K) * x) ⁻¹' s = s
    rw [hs_def]
    ext x
    simp only [Set.mem_preimage, negativeValuationShell, Set.mem_setOf_eq, hval]
  have hs : MeasurableSet s := by
    rw [hs_def]
    apply IsOpen.measurableSet
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : valuation K x ≠ 0 := by
      intro h
      have hh := hx
      change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) =
        WithZero.exp ((n + 1 : ℕ) : ℤ) at hh
      simp [h] at hh
    filter_upwards [(valuation K).locally_const hx0] with y hy
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K y) =
      WithZero.exp ((n + 1 : ℕ) : ℤ)
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) =
      WithZero.exp ((n + 1 : ℕ) : ℤ) at hx
    simpa only [hy] using hx

  have h1 : (∫ x in s, H x ∂μ) = ∫ x in s, H (φ x) ∂μ := by
    conv_lhs => rw [← hmapφ]
    rw [MeasureTheory.setIntegral_map_equiv φ H s, hpre]

  have h2 : (∫ x in s, H (φ x) ∂μ) = c * ∫ x in s, H x ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_ae hs
    filter_upwards with x hx
    exact hEigen x hx
  have hfix : (∫ x in s, H x ∂μ) = c * ∫ x in s, H x ∂μ := h1.trans h2
  have hc1 : (1 - c) * (∫ x in s, H x ∂μ) = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hfix
  have hzero : (∫ x in s, H x ∂μ) = 0 := by
    rcases mul_eq_zero.mp hc1 with h | h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hc)
    · exact h
  simpa only [hs_def] using hzero

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector.NegativeShell

end

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (q : HeightOneSpectrum (𝓞 F)) (S : RawFiniteInducingData F ζ hζ q)

namespace BruhatPhase
open KPRankOneOpenCellKernel
private lemma winv (K : Type*) [Field K] : (KubotaRankTwo.w K)⁻¹ = KubotaRankTwo.d K (-1) (-1) * KubotaRankTwo.w K := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
private lemma Xwinv (K : Type*) [Field K] : KubotaRankTwo.X K (KubotaRankTwo.w K)⁻¹ = -1 := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply]
private lemma Xwnw (K : Type*) [Field K] (v : Kˣ) :
    KubotaRankTwo.X K ((KubotaRankTwo.w K)⁻¹ * KubotaRankTwo.n K (-((v⁻¹ : Kˣ) : K)) * (KubotaRankTwo.w K)⁻¹) = -v⁻¹ := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply, Units.ne_zero]

private lemma BoneL (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 a
private lemma BoneR (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 a
private lemma BnegR (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) a (-1) = 1 :=
  (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 a |>.2.1
private lemma sigmanR (g : KubotaRankTwo.GL2 (LocalField F q)) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q) g (KubotaRankTwo.n (LocalField F q) s) = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, BoneL, BoneR]
private lemma sigww : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    (KubotaRankTwo.w (LocalField F q)) (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xwinv, BoneL, BoneR]
private lemma sigwnw (v : (LocalField F q)ˣ) : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    ((KubotaRankTwo.w (LocalField F q))⁻¹ * KubotaRankTwo.n (LocalField F q) (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)))
    (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xwnw, KubotaRankTwo.X_mul_n,
    Xwinv, map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w, inv_one, one_mul,
    mul_one, one_pow]
  have hr : (-v⁻¹) / (-1) = v⁻¹ := by simp
  rw [hr, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 v⁻¹ |>.1, BoneL]
  simp
private lemma Xdnw (K : Type*) [Field K] (v : Kˣ) (s : K) :
    KubotaRankTwo.X K (KubotaRankTwo.d K (v ^ 2) 1 * KubotaRankTwo.n K s * (KubotaRankTwo.w K)⁻¹) = -1 := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply]
private lemma Bselfpow (a : (LocalField F q)ˣ) (m n : ℤ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (a ^ m) (a ^ n) = 1 := by
  let BL (b : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun x => KPHilbert.B3 F ζ hζ (Sum.inr q) x b
      map_one' := BoneL F ζ hζ q b
      map_mul' := fun x y => (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 x y b }
  let BR : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) a
      map_one' := BoneR F ζ hζ q a
      map_mul' := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 a }
  change BL (a ^ n) (a ^ m) = 1
  rw [map_zpow]
  change (BR (a ^ n)) ^ m = 1
  rw [map_zpow]
  change (KPHilbert.B3 F ζ hζ (Sum.inr q) a a ^ n) ^ m = 1
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 a |>.1]
  simp
private lemma BnegL (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) (-1) a = 1 := by
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1, BnegR]
  simp

private lemma sigdnw (v : (LocalField F q)ˣ) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (v ^ 2) 1 * KubotaRankTwo.n (LocalField F q) s)
      (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xdnw, KubotaRankTwo.X_mul_n,
    KubotaRankTwo.X_d, Xwinv, map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w,
    KubotaRankTwo.det_d, inv_one, mul_one, div_one, one_mul, one_pow]
  rw [BnegL, BoneR]
  simp
private lemma Xscalar (K : Type*) [Field K] (v : Kˣ) :
    KubotaRankTwo.X K (Matrix.GeneralLinearGroup.scalar (Fin 2) v) = v := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.scalar]
private lemma Xscalar_mul (K : Type*) [Field K] (v : Kˣ) (g : KubotaRankTwo.GL2 K) :
    KubotaRankTwo.X K (Matrix.GeneralLinearGroup.scalar (Fin 2) v * g) = v * KubotaRankTwo.X K g := by
  classical
  apply Units.ext
  simp only [KubotaRankTwo.X, Units.val_mk0, Units.val_mul]
  unfold KubotaRankTwo.x
  have he (i j : Fin 2) : (Matrix.GeneralLinearGroup.scalar (Fin 2) v * g) i j = (v : K) * g i j := by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.scalar]
  rw [he 1 0, he 1 1]
  simp only [mul_eq_zero, v.ne_zero, false_or]
  split_ifs <;> rfl
private lemma sigscalar (v : (LocalField F q)ˣ) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹)
      (KubotaRankTwo.d (LocalField F q) (v ^ 2) 1 * KubotaRankTwo.n (LocalField F q) ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        (KubotaRankTwo.w (LocalField F q))⁻¹ * KubotaRankTwo.n (LocalField F q) s) = 1 := by
  change KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    ((Matrix.GeneralLinearGroup.scalar (Fin 2)) v⁻¹) _ = 1
  unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
  simp only [Xscalar_mul, Xscalar,
    KubotaRankTwo.X_mul_n, Xdnw,
    KubotaRankTwo.det,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_one, mul_one]
  have h1 : v⁻¹ * (-1) / v⁻¹ = -1 := by simp
  rw [h1, BnegL]
  have hB : KPHilbert.B3 F ζ hζ (Sum.inr q) (v⁻¹ ^ 2) (v ^ 2) = 1 := by
    convert Bselfpow F ζ hζ q v (-2) 2 using 1 <;> simp
  simp only [map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w,
    KubotaRankTwo.det_d, inv_one, mul_one, ← inv_pow, hB, one_pow]

theorem actual_bruhat_kappa_eq_one (v : (LocalField F q)ˣ) (s : LocalField F q) : KPRankOneOpenCellKernel.kappa F ζ hζ q v s = 1 := by
  rw [KPRankOneOpenCellKernel.kappa, bruhatLeft, bruhatRight, signedWeyl_eq_prescribed_signed]
  have he : ∀ x : (LocalField F q)ˣ,
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) x).epsilon = 1 := fun _ => rfl
  have hg : ∀ x : (LocalField F q)ˣ,
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) x).g = Matrix.GeneralLinearGroup.scalar (Fin 2) x := fun _ => rfl
  simp only [KPLocalCover.mul_epsilon, KPLocalCover.inv_epsilon, KPLocalCover.mul_g,
    KPLocalCover.inv_g, KPStandardLocalRootLifts.signedW, KPStandardLocalRootLifts.N,
    KPStandardLocalRootLifts.A, he, hg,
    KPLocalCover.sectionMap_epsilon, KPLocalCover.sectionMap_g]
  simp only [sigww F ζ hζ q, sigmanR F ζ hζ q, sigwnw F ζ hζ q,
    sigdnw F ζ hζ q, sigscalar F ζ hζ q, one_mul, mul_one,
    inv_one, div_one]
end BruhatPhase

private theorem shell_weyl_mem
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    S.borel.liftedW ∈
      (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
        (KPGoodCompactSplitting.kStar F ζ hζ q ht))).range := by
  refine ⟨KPStandardLocalRootLifts.integralA F q (-1) *
    KPStandardLocalRootLifts.integralW F q, ?_⟩
  rw [map_mul, (S.openCell S.polarization).weyl_eq]
  change _ = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
    (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
      KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q))
  rw [map_mul, KPStandardLocalRootLifts.W_eq_compact F ζ hζ q ht]
  have hA := KPStandardLocalRootLifts.A_eq_compact F ζ hζ q ht (-1)
  have hu : KPTameCompact.unitInclusion F q (-1) = -1 := by
    apply Units.ext
    rfl
  rw [hu] at hA
  rw [hA]
  rfl

theorem actual_compact_spherical_bruhat_value
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (v : (LocalField F q)ˣ)
    (hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q) :
    f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) : ActualCover F ζ hζ q)) =
    inducingAction S.borel P .plus 0
      (S.borel.upperRoot (Multiplicative.ofAdd
          (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) *
        (S.borel.torus ((S.openCell P).rootTorus v))⁻¹ *
        (S.borel.torus ((S.openCell P).centralTorus
          (KPRankOneOpenCellKernel.kappa F ζ hζ q v 0)))⁻¹)
      (f.val 1) := by
  let B := S.openCell P
  let k := (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht)
  have hw : S.borel.liftedW⁻¹ ∈ k.range :=
    k.range.inv_mem (shell_weyl_mem F ζ hζ q S ht)
  have hn : (S.borel.upperRoot (Multiplicative.ofAdd
      (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) : ActualCover F ζ hζ q) ∈ k.range := by
    refine ⟨KPStandardLocalRootLifts.integralN F q
      ⟨-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q), ?_⟩, ?_⟩
    · exact (KPTameCompact.O F q).neg_mem hv
    · rw [B.upper_eq]
      change _ = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) _)
      rw [KPStandardLocalRootLifts.N_eq_compact F ζ hζ q ht
        ⟨-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q),
          (KPTameCompact.O F q).neg_mem hv⟩]
      rfl
  obtain ⟨a, ha⟩ := k.range.mul_mem (k.range.mul_mem hw hn) hw
  have hval : f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd
        (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) : ActualCover F ζ hζ q) *
      S.borel.liftedW⁻¹) = f.val 1 := by
    have hh := congrArg (fun z : sectionSpace S.borel P .plus 0 => z.val 1) (hfixed a)
    change f.val (1 * k a) = f.val 1 at hh
    simpa only [one_mul, ha] using hh
  have hb := KPRankOneOpenCellKernel.lifted_bruhat_identity F ζ hζ q v 0
  have hn0 : KPRankOneOpenCellKernel.nLift F ζ hζ q 0 = 1 := by
    simp only [KPRankOneOpenCellKernel.nLift, KPPGLLocalCover.N,
      KPStandardLocalRootLifts.N_zero, map_one]
  simp only [hn0, zero_add, mul_one] at hb
  rw [← B.weyl_eq, ← B.upper_eq, ← B.upper_eq,
    ← B.upper_eq, ← B.torus_eq, ← B.central_eq] at hb
  have he : S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) : ActualCover F ζ hζ q) =
      ((S.borel.upperRoot (Multiplicative.ofAdd
          (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) *
        (S.borel.torus (B.rootTorus v))⁻¹ *
        (S.borel.torus (B.centralTorus (KPRankOneOpenCellKernel.kappa F ζ hζ q v 0)))⁻¹ :
          S.borel.B) : ActualCover F ζ hζ q) *
      (S.borel.liftedW⁻¹ *
        (S.borel.upperRoot (Multiplicative.ofAdd
          (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) : ActualCover F ζ hζ q) *
        S.borel.liftedW⁻¹) := by
    rw [hb]
    have hi : (S.borel.upperRoot (Multiplicative.ofAdd
        (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) : ActualCover F ζ hζ q) =
        (S.borel.upperRoot (Multiplicative.ofAdd
          ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) : ActualCover F ζ hζ q)⁻¹ := by
      rw [← Subgroup.coe_inv, ← map_inv]
      rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hi]
    group
  rw [he, f.property.1, hval]

theorem actual_compact_spherical_bruhat_coordinate
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (v : (LocalField F q)ˣ)
    (hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q)
    (t : actualTorus F ζ hζ q) :
    (f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) : ActualCover F ζ hζ q))).val t =
    (ordinaryIota F ζ hζ (KPRankOneOpenCellKernel.kappa F ζ hζ q v 0) : ℂ)⁻¹ *
      normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) *
      ((tau P) (((S.openCell P).rootTorus v)⁻¹) (f.val 1)).val t := by
  rw [actual_compact_spherical_bruhat_value F ζ hζ q S ht P f hfixed v hv]
  let B := S.openCell P
  have hc (e : rootsOfUnity 3 F) (V : InducedModule P) :
      inducingAction S.borel P .plus 0 (S.borel.torus (B.centralTorus e)) V =
        (ordinaryIota F ζ hζ e : ℂ) • V := by
    change inducingScalar S.borel 0 _ • borelAction S.borel P .plus _ V = _
    rw [B.genuine, S.openCell_ordinary]
    simp [inducingScalar, deltaHalf, S.borel.retract_torus,
      B.central_coordinate, normPower, localAbs_one]
  have hci (e : rootsOfUnity 3 F) (V : InducedModule P) :
      inducingAction S.borel P .plus 0 (S.borel.torus (B.centralTorus e))⁻¹ V =
        (ordinaryIota F ζ hζ e : ℂ)⁻¹ • V := by
    have hh := hc e (inducingAction S.borel P .plus 0
      (S.borel.torus (B.centralTorus e))⁻¹ V)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at hh
    conv_rhs => rw [hh, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  have hr (V : InducedModule P) :
      inducingAction S.borel P .plus 0 (S.borel.torus (B.rootTorus v))⁻¹ V =
        normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) •
          (tau P) ((B.rootTorus v)⁻¹) V := by
    simp [inducingAction, inducingScalar, deltaHalf, borelAction,
      ← map_inv, S.borel.retract_torus, B.coordinate_eq,
      normPower, inv_pow]
    rw [map_inv, B.coordinate_eq]
  simp only [map_mul, Module.End.mul_apply]
  rw [upperRoot_trivial, hci, map_smul, hr]
  change _ = _
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem actual_compact_spherical_bruhat_coordinate_phase_free
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (v : (LocalField F q)ˣ)
    (hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q)
    (t : actualTorus F ζ hζ q) :
    (f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) :
        ActualCover F ζ hζ q))).val t =
      normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) *
        ((tau P) (((S.openCell P).rootTorus v)⁻¹) (f.val 1)).val t := by
  rw [actual_compact_spherical_bruhat_coordinate F ζ hζ q S ht P f hfixed v hv t,
    BruhatPhase.actual_bruhat_kappa_eq_one, map_one, Units.val_one, inv_one, one_mul]

theorem actual_compact_spherical_identity_unit_fixed
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (u : (KPTameCompact.O F q)ˣ)
    (a : actualTorus F ζ hζ q)
    (ha : (a : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)) :
    tau P a (f.val 1) = f.val 1 := by
  have hc : S.borel.coordinate a = KPTameCompact.unitInclusion F q u :=
    S.coordinate_lift a _ ha
  have hv : valuation (LocalField F q)
      ((KPTameCompact.unitInclusion F q u : (LocalField F q)ˣ) : LocalField F q) = 1 := by
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (LocalField F q)))).mp u.isUnit
  have hs : inducingScalar S.borel 0 (S.borel.torus a) = 1 := by
    simp [inducingScalar, deltaHalf, S.borel.retract_torus, hc, normPower,
      localAbs, hv]
  have hk : ((S.borel.torus a : S.borel.B) : ActualCover F ζ hζ q) =
      (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
        (KPGoodCompactSplitting.kStar F ζ hζ q ht))
          (KPStandardLocalRootLifts.integralA F q u)) := by
    rw [S.torus_full, ha]
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) _) = _
    rw [KPStandardLocalRootLifts.A_eq_compact F ζ hζ q ht]
    rfl
  have he := congrArg (fun g : sectionSpace S.borel P .plus 0 => g.val 1)
    (hfixed (KPStandardLocalRootLifts.integralA F q u))
  change f.val (1 * _) = f.val 1 at he
  rw [one_mul, ← hk] at he
  have hb := f.property.1 (S.borel.torus a) 1
  rw [mul_one] at hb
  rw [hb] at he
  simpa [inducingAction, hs, borelAction, S.borel.retract_torus] using he

theorem actual_rootTorus_cube_mul (P : Polarization S.heisenberg)
    (a u : (LocalField F q)ˣ) :
    (S.openCell P).rootTorus (a ^ 3 * u) =
      (S.borel.cubeLift (a ^ 2) : actualTorus F ζ hζ q) *
        (S.openCell P).rootTorus u := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [S.cube_actual, ← S.torus_full, (S.openCell P).torus_eq,
    KPRankOneOpenCellKernel.hLift, ← S.torus_full, (S.openCell P).torus_eq,
    KPRankOneOpenCellKernel.hLift, KPPGLLocalCover.A_mul]
  have hb : KPHilbert.B3 F ζ hζ (Sum.inr q) ((a ^ 2) ^ 3) (u ^ 2) = 1 :=
    ((KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 (a ^ 2) (u ^ 2)).1
  rw [hb, one_pow, map_one, one_mul]
  congr 1
  simp only [mul_pow, ← pow_mul]

theorem actual_compact_spherical_cube_unit_bruhat_coordinate
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (a : (LocalField F q)ˣ) (u : (KPTameCompact.O F q)ˣ)
    (ha : (((a ^ 3 * KPTameCompact.unitInclusion F q u)⁻¹ :
      (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q)
    (t : actualTorus F ζ hζ q) :
    (f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd
        (a ^ 3 * KPTameCompact.unitInclusion F q u : (LocalField F q)ˣ)) :
          ActualCover F ζ hζ q))).val t =
      normPower (LocalField F q) ((a ^ 3)⁻¹ ^ 2) (2 / 3) * (f.val 1).val t := by
  have hu : localAbs (LocalField F q) (KPTameCompact.unitInclusion F q u) = 1 := by
    have hv : valuation (LocalField F q)
        ((KPTameCompact.unitInclusion F q u : (LocalField F q)ˣ) : LocalField F q) = 1 :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation (LocalField F q)))).mp u.isUnit
    simp [localAbs, hv]
  have hui : localAbs (LocalField F q) ((KPTameCompact.unitInclusion F q u)⁻¹ ^ 2) = 1 := by
    have hv : valuation (LocalField F q)
        ((KPTameCompact.unitInclusion F q (u⁻¹ ^ 2) : (LocalField F q)ˣ) : LocalField F q) = 1 :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation (LocalField F q)))).mp (u⁻¹ ^ 2).isUnit
    simp only [map_pow, map_inv] at hv
    unfold localAbs
    rw [hv]
    simp
  have hm : normPower (LocalField F q)
      ((a ^ 3 * KPTameCompact.unitInclusion F q u)⁻¹ ^ 2) (1 / 2) =
      normPower (LocalField F q) ((a ^ 3)⁻¹ ^ 2) (1 / 2) := by
    simp only [normPower, mul_inv, mul_pow, localAbs_mul, hui, mul_one]
  rw [actual_compact_spherical_bruhat_coordinate F ζ hζ q S ht P f hfixed _ ha t,
    BruhatPhase.actual_bruhat_kappa_eq_one, map_one, Units.val_one, inv_one,
    one_mul, hm, actual_rootTorus_cube_mul, mul_inv_rev, map_mul,
    Module.End.mul_apply, ← Subgroup.coe_inv, tau_hasCentralCharacter]
  have hc : (S.heisenberg.ω.toMonoidHom ((S.borel.cubeLift (a ^ 2))⁻¹) : ℂ) =
      normPower (LocalField F q) ((a ^ 2)⁻¹ ^ 3) (1 / 6) := by
    change (S.heisenberg.ω ((S.borel.cubeLift (a ^ 2))⁻¹) : ℂ) = _
    rw [← S.borel.cubeLift.map_inv, S.borel.exceptional_cube]
  rw [hc, map_smul]
  have hf : tau P (((S.openCell P).rootTorus
      (KPTameCompact.unitInclusion F q u))⁻¹) (f.val 1) = f.val 1 := by
    have htau := actual_compact_spherical_identity_unit_fixed F ζ hζ q S ht P f
      hfixed (u ^ 2) ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u))
      (by rw [← S.torus_full, (S.openCell P).torus_eq,
        KPRankOneOpenCellKernel.hLift, map_pow])
    have h := congrArg (tau P (((S.openCell P).rootTorus
      (KPTameCompact.unitInclusion F q u))⁻¹)) htau
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h.symm
  rw [hf]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have he : (a ^ 2)⁻¹ ^ 3 = (a ^ 3)⁻¹ ^ 2 := by group
  rw [he, ← mul_assoc]
  congr 1
  unfold normPower
  rw [← Complex.exp_add]
  congr 1
  ring

theorem actual_centralTorus_action (P : Polarization S.heisenberg)
    (e : rootsOfUnity 3 F) (V : InducedModule P) :
    tau P ((S.openCell P).centralTorus e) V =
      (ordinaryIota F ζ hζ e : ℂ) • V := by
  have hg := (S.openCell P).genuine .plus e V
  simpa [inducingAction, inducingScalar, deltaHalf, borelAction,
    S.borel.retract_torus, (S.openCell P).central_coordinate, normPower,
    localAbs_one, S.openCell_ordinary] using hg

theorem actual_rootTorus_mul (P : Polarization S.heisenberg)
    (a b : (LocalField F q)ˣ) :
    (S.openCell P).rootTorus a * (S.openCell P).rootTorus b =
      (S.openCell P).centralTorus
        (KPHilbert.B3 F ζ hζ (Sum.inr q) (a ^ 2) (b ^ 2) ^ 2) *
          (S.openCell P).rootTorus (a * b) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← S.torus_full, (S.openCell P).torus_eq,
    ← S.torus_full, (S.openCell P).torus_eq,
    ← S.torus_full, (S.openCell P).central_eq,
    ← S.torus_full, (S.openCell P).torus_eq]
  simp only [KPRankOneOpenCellKernel.hLift]
  rw [KPPGLLocalCover.A_mul, mul_pow]

theorem actual_cubic_sphere_unit_decomposition
    (a v : (LocalField F q)ˣ)
    (hv : valuation (LocalField F q) (v : LocalField F q) =
      valuation (LocalField F q) (a ^ 3 : (LocalField F q)ˣ)) :
    ∃ u : (KPTameCompact.O F q)ˣ,
      v = a ^ 3 * KPTameCompact.unitInclusion F q u := by
  let w : (LocalField F q)ˣ := v / a ^ 3
  have hw : valuation (LocalField F q) (w : LocalField F q) = 1 := by
    change valuation (LocalField F q) (v / a ^ 3 : (LocalField F q)ˣ) = 1
    rw [Units.val_div_eq_div_val, map_div₀, hv, div_self]
    exact (map_ne_zero (valuation (LocalField F q))).mpr (Units.ne_zero _)
  let z : KPTameCompact.O F q := ⟨(w : LocalField F q), by
    change valuation (LocalField F q) (w : LocalField F q) ≤ 1
    rw [hw]⟩
  have hz : IsUnit z :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (LocalField F q)))).mpr hw
  obtain ⟨u, hu⟩ := hz
  refine ⟨u, ?_⟩
  have hwu : KPTameCompact.unitInclusion F q u = w := by
    apply Units.ext
    exact congrArg (fun c : KPTameCompact.O F q => (c : LocalField F q)) hu
  rw [hwu]
  simp [w, div_eq_mul_inv, mul_comm]

theorem actual_compact_spherical_cubic_sphere_coordinate
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (a v : (LocalField F q)ˣ)
    (ha : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q)
    (hv : valuation (LocalField F q) (v : LocalField F q) =
      valuation (LocalField F q) (a ^ 3 : (LocalField F q)ˣ))
    (t : actualTorus F ζ hζ q) :
    (f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) :
        ActualCover F ζ hζ q))).val t =
      normPower (LocalField F q) ((a ^ 3)⁻¹ ^ 2) (2 / 3) * (f.val 1).val t := by
  obtain ⟨u, hu⟩ := actual_cubic_sphere_unit_decomposition F q a v hv
  subst v
  exact actual_compact_spherical_cube_unit_bruhat_coordinate F ζ hζ q S ht P f
    hfixed a u ha t

theorem actual_compact_spherical_negative_shell_coordinate
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    (S : RawFiniteInducingData F ζ hζ q)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hgood : valuation (LocalField F q) (6 : LocalField F q) = 1)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (n : ℕ) (t : actualTorus F ζ hζ q) :
    (∫ x : LocalField F q in negativeValuationShell (LocalField F q) n,
      (f.val (S.borel.liftedW⁻¹ *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val t ∂μ) =
      if 3 ∣ n + 1 then
        (1 - (residueCardinality (LocalField F q) : ℂ)⁻¹) *
          ((residueCardinality (LocalField F q) : ℂ)⁻¹) ^ ((n + 1) / 3) *
          (f.val 1).val t
      else 0 := by
  classical
  let H : LocalField F q → ℂ := fun x =>
    (f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val t
  by_cases hn : 3 ∣ n + 1
  · rw [if_pos hn]
    exact NegativeShell.integral_cubic_shell_of_sphere_values
      (LocalField F q) μ hμ H ((f.val 1).val t)
      (fun a v ha hv => actual_compact_spherical_cubic_sphere_coordinate
        F ζ hζ q S ht P f hfixed a v ha hv t) n hn
  · rw [if_neg hn]
    have hBruhat := fun (v : (LocalField F q)ˣ)
        (hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q) =>
      actual_compact_spherical_bruhat_coordinate_phase_free
        F ζ hζ q S ht P f hfixed v hv t
    have hUnit : ∀ u : (KPTameCompact.O F q)ˣ,
        tau P ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u))
          (f.val 1) = f.val 1 := by
      intro u
      exact actual_compact_spherical_identity_unit_fixed F ζ hζ q S ht P f
        hfixed (u ^ 2) ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u))
        (by rw [← S.torus_full, (S.openCell P).torus_eq,
          KPRankOneOpenCellKernel.hLift, map_pow])
    obtain ⟨u, c, hu, hc, hEigen⟩ :=
      NegativeShell.actual_noncubic_shell_unit_eigenvalue
        F ζ hζ q S hgood P (f.val 1) H t hBruhat hUnit n hn
    exact NegativeShell.integral_shell_eq_zero_of_unit_eigenfunction
      (LocalField F q) μ H n u hu c hc hEigen

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector

end
