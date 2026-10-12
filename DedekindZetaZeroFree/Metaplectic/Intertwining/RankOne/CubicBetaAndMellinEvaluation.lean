module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.JointMellinBetaIntegrability
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicCharacterScalarSum
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBeta.RamifiedIntegralEvaluation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBeta.UnramifiedIntegralEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.RegulatedResidue
open MeasureTheory
open scoped ValuativeRel Topology

theorem residueCard_pos (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    0 < (KPCubicUnitIndices.residueCard K : ℝ) := by
  have h := KPCubicUnitIndices.two_le_residueCard K
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) h)

theorem cube_root_norm_bounds (q : ℝ) (hq : 0 < q)
    (t z : ℂˣ) (lam : ℂ) (hz : z ^ 3 = t)
    (hlower : q.rpow (-3 * lam.re) < ‖(t : ℂ)‖)
    (hupper : ‖(t : ℂ)‖ < 1) :
    q.rpow (-lam.re) < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1 := by
  have hn : ‖(t : ℂ)‖ = ‖(z : ℂ)‖ ^ 3 := by
    rw [← hz]
    simp
  have hp : q.rpow (-3 * lam.re) = (q.rpow (-lam.re)) ^ 3 := by
    calc
      q.rpow (-3 * lam.re) = q.rpow ((-lam.re) * (3 : ℝ)) := by congr 1; ring
      _ = (q.rpow (-lam.re)).rpow (3 : ℝ) := Real.rpow_mul hq.le _ _
      _ = (q.rpow (-lam.re)) ^ 3 := Real.rpow_natCast _ 3
  rw [hn, hp] at hlower
  rw [hn] at hupper
  constructor
  · exact (pow_lt_pow_iff_left₀ (Real.rpow_pos_of_pos hq (-lam.re)).le
      (norm_nonneg (z : ℂ)) (by decide : (3 : ℕ) ≠ 0)).mp hlower
  · exact (pow_lt_pow_iff_left₀ (norm_nonneg (z : ℂ))
      (by norm_num : (0 : ℝ) ≤ 1) (by decide : (3 : ℕ) ≠ 0)).mp
      (by simpa using hupper)

theorem beta_power_exp_coordinates
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : ℂ) (x : Kˣ) :
    (KPCubicHaar.abs K (x : K) : ℂ) ^ (-s) =
      (Complex.exp ((s - 1) *
        (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ))) ^
        KPCubicExpansion.valuationExponent K x /
      (KPCubicHaar.abs K (x : K) : ℂ) := by
  let q : ℝ := CubicUnitCharacters.residueCard K
  let j : ℤ := KPCubicExpansion.valuationExponent K x
  have hq : 0 < q := residueCard_pos K
  have habs : KPCubicHaar.abs K (x : K) = q ^ (-j) := by
    simp [KPCubicHaar.abs, x.ne_zero, KPCubicExpansion.valuationExponent, q, j]
    rfl
  have ha : 0 < KPCubicHaar.abs K (x : K) := KPCubicHaar.abs_pos K x.ne_zero
  have halog : (Real.log (KPCubicHaar.abs K (x : K)) : ℂ) =
      -(j : ℂ) * (Real.log q : ℂ) := by
    rw [habs, Real.log_zpow]
    push_cast
    ring
  have hae : (KPCubicHaar.abs K (x : K) : ℂ) =
      Complex.exp (-(j : ℂ) * (Real.log q : ℂ)) := by
    rw [← halog, ← Complex.ofReal_exp, Real.exp_log ha]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'),
    ← Complex.ofReal_log ha.le, halog, ← Complex.exp_int_mul, hae,
    ← Complex.exp_sub]
  congr 1
  dsimp [q, j]
  ring

theorem betaFunction_eq_ramified_integrand
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (χ : Kˣ →ₜ* ℂˣ) (s : ℂ) (y : Kˣ) :
    (χ y : ℂ) * KPCubicExpansion.betaFunction K s y =
      KPRankOneRamifiedBeta.betaIntegrand K χ
        (Units.mk0 (Complex.exp ((s - 1) *
          (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ)))
          (Complex.exp_ne_zero _)) y := by
  by_cases hy : y = 1
  · subst y
    simp [KPCubicExpansion.betaFunction, KPRankOneRamifiedBeta.betaIntegrand]
  · have hy' : (y : K) ≠ 1 := fun h => hy (Units.ext h)
    rw [KPCubicExpansion.betaFunction, if_neg hy,
      KPRankOneRamifiedBeta.betaIntegrand, dif_neg hy']
    have hp := beta_power_exp_coordinates K s
      (Units.mk0 (1 - (y : K)) (sub_ne_zero.mpr (Ne.symm hy')))
    simp only [Units.val_mk0] at hp
    rw [hp]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, div_eq_mul_inv]
    ring

theorem betaFunction_eq_unramified_integrand
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (b : ℂˣ) (s : ℂ) (y : Kˣ) :
    (KPRankOneCubicProjection.eta K b y : ℂ) * KPCubicExpansion.betaFunction K s y =
      KPRankOneUnramifiedBetaShells.integrand K b
        (Units.mk0 (Complex.exp ((s - 1) *
          (Real.log (CubicUnitCharacters.residueCard K : ℝ) : ℂ)))
          (Complex.exp_ne_zero _)) y := by
  by_cases hy : y = 1
  · subst y
    simp [KPCubicExpansion.betaFunction, KPRankOneUnramifiedBetaShells.integrand]
  · have hy' : 1 - (y : K) ≠ 0 := by
      intro h
      exact hy (Units.ext (sub_eq_zero.mp h).symm)
    rw [KPCubicExpansion.betaFunction, if_neg hy,
      KPRankOneUnramifiedBetaShells.integrand, dif_neg hy']
    have hp := beta_power_exp_coordinates K s (Units.mk0 (1 - (y : K)) hy')
    simp only [Units.val_mk0] at hp
    rw [hp]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, div_eq_mul_inv]
    ring

theorem uniformizer_unit_decomposition (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (π : Kˣ) (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K) (x : Kˣ) :
    ∃ (j : ℤ) (u : (𝒪[K])ˣ), x = π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u := by
  let j := KPCubicExpansion.valuationExponent K x
  let y := π ^ (-j) * x
  have he : KPCubicExpansion.valuationExponent K y = 0 := by
    dsimp [y]
    rw [KPCubicExpansion.valuationExponent_mul, KPCubicExpansion.valuationExponent_zpow,
      KPCubicExpansion.valuationExponent_uniformizer π hπ]
    dsimp [j]
    ring
  have hv : ValuativeRel.valuation K (y : K) = 1 := by
    have hn : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K (y : K)) ≠ 0 := by simp
    have hz : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K (y : K))) = 0 := by
      simpa [KPCubicExpansion.valuationExponent] using he
    have hh := congrArg WithZero.exp hz
    rw [WithZero.exp_log hn, WithZero.exp_zero] at hh
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective (hh.trans (map_one _).symm)
  let u : (𝒪[K])ˣ :=
    { val := ⟨(y : K), by change ValuativeRel.valuation K (y : K) ≤ 1; rw [hv]⟩
      inv := ⟨((y⁻¹ : Kˣ) : K), by change ValuativeRel.valuation K ((y⁻¹ : Kˣ) : K) ≤ 1; simp [hv]⟩
      val_inv := by apply Subtype.ext; exact y.val_inv
      inv_val := by apply Subtype.ext; exact y.inv_val }
  refine ⟨j, u, ?_⟩
  have hu : Units.map (𝒪[K]).subtype.toMonoidHom u = y := Units.ext rfl
  rw [hu]
  dsimp [y]
  rw [← mul_assoc, ← zpow_add]
  simp

theorem character_eq_eta_of_coordinates
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (π : Kˣ)
    (hπ : ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K)
    (b : ℂˣ) (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ (j : ℤ) (u : (𝒪[K])ˣ),
      χ (π ^ j * Units.map (𝒪[K]).subtype.toMonoidHom u) = b ^ j) :
    ∀ y : Kˣ, χ y = KPRankOneCubicProjection.eta K b y := by
  intro y
  obtain ⟨j, u, rfl⟩ := uniformizer_unit_decomposition K π hπ y
  rw [hχ]
  exact (KPRankOneCubicProjection.eta_uniformizer_coordinates K b π hπ j u).symm

theorem norm_beta_exp_parameter (q : ℝ) (hq : 0 < q) (s : ℂ) :
    ‖Complex.exp ((s - 1) * (Real.log q : ℂ))‖ = q.rpow (s.re - 1) := by
  change ‖Complex.exp ((s - 1) * (Real.log q : ℂ))‖ = q ^ (s.re - 1 : ℝ)
  rw [Complex.norm_exp, Real.rpow_def_of_pos hq]
  congr 1
  simp [Complex.mul_re]
  ring
theorem joint_strip_geometric_bounds (q : ℝ) (hq : 1 < q) (s : ℂ) (hs : s.re < 1)
    (b : ℂˣ) (hlo : q.rpow (-s.re) < ‖(b : ℂ)‖) (hhi : ‖(b : ℂ)‖ < 1) :
    q⁻¹ < ‖(b : ℂ)‖ ∧ ‖(b : ℂ)‖ < 1 ∧
      q⁻¹ / ‖(b : ℂ)‖ < q.rpow (s.re - 1) ∧ q.rpow (s.re - 1) < 1 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hb0 : 0 < ‖(b : ℂ)‖ := norm_pos_iff.mpr b.ne_zero
  have hpow : q.rpow (-1) < q.rpow (-s.re) :=
    Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
  have he : q.rpow (-s.re) * q.rpow (s.re - 1) = q⁻¹ := by
    change q ^ (-s.re) * q ^ (s.re - 1 : ℝ) = q⁻¹
    rw [← Real.rpow_add hq0]
    convert Real.rpow_neg_one q using 1 <;> ring
  change q ^ (-1 : ℝ) < q ^ (-s.re) at hpow
  rw [Real.rpow_neg_one] at hpow
  refine ⟨lt_trans hpow hlo, hhi, ?_,
    Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)⟩
  apply (div_lt_iff₀ hb0).mpr
  rw [← he]
  rw [mul_comm (q.rpow (s.re - 1))]
  exact mul_lt_mul_of_pos_right hlo (Real.rpow_pos_of_pos hq0 _)

end DedekindZetaZeroFree.RegulatedResidue

end
