module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicCharacterProjection
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBeta.RamifiedConductorFormula

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneRamifiedBeta

open scoped ValuativeRel Topology
open MeasureTheory ValuativeRel Topology

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def a : ℂ := (CubicUnitCharacters.residueCard K : ℂ)⁻¹

variable [MeasurableSpace K] [BorelSpace K]

def m (dx : Measure K) : ℝ := (dx (𝒪[K] : Set K)).toReal

def betaIntegrand (η : Kˣ →ₜ* ℂˣ) (u : ℂˣ) (y : Kˣ) : ℂ := by
  classical
  exact if h : (y : K) = 1 then 0 else
    (η y : ℂ) *
      ((u ^ KPCubicExpansion.valuationExponent K
        (Units.mk0 (1 - (y : K)) (sub_ne_zero.mpr (Ne.symm h))) : ℂˣ) : ℂ) *
      (KPCubicHaar.abs K (1 - (y : K)) : ℂ)⁻¹

def betaIntegral (dx : Measure K) (η : Kˣ →ₜ* ℂˣ) (u : ℂˣ) : ℂ :=
  ∫ y : Kˣ, betaIntegrand K η u y ∂KPCubicHaar.multiplicativeHaar K dx

def rationalBeta (dx : Measure K) (ξ : CubicUnitCharacters.Character K)
    (u : ℂ) : ℂ :=
  (m K dx : ℂ) * u ^ (CubicUnitCharacters.conductor K ξ - 1) *
    (u - a K) / (1 - u)

theorem conductor_exists (ξ : CubicUnitCharacters.Character K) :
    ∃ j, CubicUnitCharacters.unitFiltration K j ≤ ξ.toMonoidHom.ker := by
  haveI : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
  have ho : IsOpen (ξ.toMonoidHom.ker : Set (𝒪[K])ˣ) :=
    (isOpen_discrete {1}).preimage ξ.continuous
  have hi : (⋂ j, (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ)) ⊆ {1} := by
    intro u hu
    have hm : (u : 𝒪[K]) - 1 ∈ ⨅ j : ℕ, 𝓂[K] ^ j := by
      simp only [Submodule.mem_iInf]
      intro j
      exact (CubicUnitCharacters.unitFiltration_mem_iff K j u).mp (Set.mem_iInter.mp hu j)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hm
    apply Units.ext
    simpa only [Ideal.mem_bot, sub_eq_zero, Units.val_one] using hm
  exact exists_subset_nhds_of_compactSpace
    (CubicUnitCharacters.unitFiltration_antitone K).directed_ge
    (fun j => (CubicUnitCharacters.unitFiltration K j).isClosed_of_isOpen
      (CubicUnitCharacters.isOpen_unitFiltration K j)) (by
        apply mem_nhdsSet_iff_forall.mpr
        intro x hx
        have : x = 1 := Set.mem_singleton_iff.mp (hi hx)
        simpa [this] using ho.mem_nhds (by simp))

theorem conductor_exact (ξ : CubicUnitCharacters.Character K) (hξ : ξ ≠ 1) :
      1 ≤ CubicUnitCharacters.conductor K ξ ∧
      CubicUnitCharacters.unitFiltration K (CubicUnitCharacters.conductor K ξ) ≤
        ξ.toMonoidHom.ker ∧
      (∀ j < CubicUnitCharacters.conductor K ξ,
        ¬ CubicUnitCharacters.unitFiltration K j ≤ ξ.toMonoidHom.ker) := by
  have hmin : CubicUnitCharacters.unitFiltration K (CubicUnitCharacters.conductor K ξ) ≤
        ξ.toMonoidHom.ker := Nat.sInf_mem (conductor_exists K ξ)
  have hlower : ∀ j < CubicUnitCharacters.conductor K ξ,
      ¬ CubicUnitCharacters.unitFiltration K j ≤ ξ.toMonoidHom.ker := by
    intro j hj h
    exact (not_le_of_gt hj) (Nat.sInf_le h)
  refine ⟨?_, hmin, hlower⟩
  by_contra hp
  have hz : CubicUnitCharacters.conductor K ξ = 0 := by omega
  rw [hz] at hmin
  apply hξ
  apply ContinuousMonoidHom.ext
  intro u
  exact hmin (by simp [CubicUnitCharacters.unitFiltration])

open scoped Classical

local instance : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K

local instance : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [(Units.isEmbedding_val₀ (G₀ := K)).eq_induced, borel_comap]
  congr 1
  exact BorelSpace.measurable_eq⟩

local instance : BorelSpace (𝒪[K])ˣ := ⟨by
  have hc : Continuous (fun v : (𝒪[K])ˣ => ((v : 𝒪[K]) : K)) :=
    continuous_subtype_val.comp Units.continuous_val
  have hi : Function.Injective (fun v : (𝒪[K])ˣ => ((v : 𝒪[K]) : K)) := by
    intro v w h
    exact Units.ext (Subtype.ext h)
  change MeasurableSpace.comap Units.val
    (MeasurableSpace.comap Subtype.val ‹MeasurableSpace K›) = borel (𝒪[K])ˣ
  rw [MeasurableSpace.comap_comp, (hc.isClosedEmbedding hi).isEmbedding.eq_induced,
    borel_comap]
  congr 1
  exact BorelSpace.measurable_eq⟩

private lemma units_range : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact y.ne_zero
  · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
private lemma units_embedding : MeasurableEmbedding (Units.val : Kˣ → K) := by
  letI : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [@BorelSpace.measurable_eq K _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  apply (Units.isEmbedding_val₀ : Topology.IsEmbedding (Units.val : Kˣ → K)).measurableEmbedding
  rw [units_range]; exact (measurableSet_singleton (0 : K)).compl
private lemma units_map_comap (ν : Measure K) (hν : ν {0} = 0) :
    Measure.map Units.val (ν.comap (Units.val : Kˣ → K)) = ν := by
  rw [(units_embedding K).map_comap, units_range]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa using hν
private lemma power_identity (q : ℝ) (hq : 0 < q) (u : ℂˣ) (s : ℂ)
    (hs : (q : ℂ) ^ s = q * (u : ℂ)) (v : ℤ) :
    ((q ^ (-v) : ℝ) : ℂ) ^ (-s) = ((u ^ v : ℂˣ) : ℂ) * ((q ^ (-v) : ℝ) : ℂ)⁻¹ := by
  rw [Complex.ofReal_zpow]
  have ha : (q : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hq.le
  rw [← Complex.cpow_int_mul' (by simp [ha, Real.pi_pos]) (by simp [ha, Real.pi_pos.le])]
  rw [show ((-v : ℤ) : ℂ) * (-s) = (v : ℂ) * s by push_cast; ring]
  rw [Complex.cpow_int_mul, hs, mul_zpow]
  simp [map_zpow, zpow_neg, inv_zpow, mul_comm]
private lemma parameter_power (q : ℝ) (hq : 1 < q) (u : ℂˣ) :
    (q : ℂ) ^ (1 + Complex.log (u : ℂ) / (Real.log q : ℂ)) = q * (u : ℂ) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hl : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq0.ne')]
  rw [← Complex.ofReal_log hq0.le]
  rw [show (Real.log q : ℂ) * (1 + Complex.log (u : ℂ) / (Real.log q : ℂ)) =
    (Real.log q : ℂ) + Complex.log (u : ℂ) by field_simp]
  rw [Complex.exp_add, Complex.exp_log u.ne_zero, ← Complex.ofReal_exp, Real.exp_log hq0]
private lemma parameter_strip (q B U : ℝ) (hq : 1 < q)
    (hB : B < 1) (hBU : q⁻¹ / B < U) (hU : U < 1) (hB0 : 0 < B)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = U) :
    let s := 1 + Complex.log (u : ℂ) / (Real.log q : ℂ)
    0 < s.re ∧ s.re < 1 ∧ q ^ (-s.re) < B := by
  intro s
  have hq0 := lt_trans zero_lt_one hq
  have hp := parameter_power q hq u
  have hn : q ^ s.re = q * U := by
    have hh := congrArg norm hp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0, hu] at hh
    exact hh
  have hU0 : 0 < U := by rw [← hu]; exact norm_pos_iff.mpr u.ne_zero
  have hprod : 1 < q * U := by
    have : q⁻¹ < U := lt_trans (by
      rw [lt_div_iff₀ hB0]; nlinarith [inv_pos.mpr hq0]) hBU
    have : 1 / q < U := by simpa [one_div] using this
    exact (div_lt_iff₀ hq0).mp this |>.trans_eq (mul_comm U q)
  have hs0 : 0 < s.re := by
    by_contra h
    have hh := Real.rpow_le_rpow_of_exponent_le hq.le (le_of_not_gt h)
    rw [Real.rpow_zero, hn] at hh
    linarith
  have hs1 : s.re < 1 := by
    by_contra h
    have hh := Real.rpow_le_rpow_of_exponent_le hq.le (le_of_not_gt h)
    rw [Real.rpow_one, hn] at hh
    nlinarith
  refine ⟨hs0, hs1, ?_⟩
  rw [Real.rpow_neg hq0.le, hn]
  have hh := (div_lt_iff₀ hB0).mp hBU
  have : 1 < U * B * q := by
    have hh' := mul_lt_mul_of_pos_right hh hq0
    simpa [inv_mul_cancel₀ hq0.ne', mul_assoc] using hh'
  rw [← one_div, div_lt_iff₀ (mul_pos hq0 hU0)]
  nlinarith
private lemma integrands_agree (η : Kˣ →ₜ* ℂˣ) (u : ℂˣ) (s : ℂ) (hs0 : 0 < s.re)
    (hs : (CubicUnitCharacters.residueCard K : ℂ) ^ s = CubicUnitCharacters.residueCard K * (u : ℂ)) :
    KPRamifiedBeta.integrand K η s ∘ Units.val = betaIntegrand K η u := by
  funext y
  have hq : (0 : ℝ) < CubicUnitCharacters.residueCard K := by
    exact_mod_cast (Finite.card_pos (α := 𝓀[K]))
  by_cases hy : (y : K) = 1
  · simp [Function.comp_def, KPRamifiedBeta.integrand, y.ne_zero, betaIntegrand, hy,
      KPRamifiedBeta.normalizedAbs, show s ≠ 0 by
        intro hz; simp [hz] at hs0]
  · have hd : 1 - (y : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    let v := KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) hd)
    have ha : KPRamifiedBeta.normalizedAbs K (1 - (y : K)) =
        (CubicUnitCharacters.residueCard K : ℝ) ^ (-v) := by
      simp [KPRamifiedBeta.normalizedAbs, hd, v, KPCubicExpansion.valuationExponent]
    have ha' : KPCubicHaar.abs K (1 - (y : K)) =
        (CubicUnitCharacters.residueCard K : ℝ) ^ (-v) := ha
    have hu : Units.mk0 (y : K) y.ne_zero = y := by ext; rfl
    simp only [Function.comp_def, KPRamifiedBeta.integrand, dif_neg y.ne_zero, hu,
      betaIntegrand, dif_neg hy, ha, ha']
    rw [power_identity _ hq u s hs v]
    ring
private lemma density_zero (dx : Measure K) : KPRamifiedBeta.multiplicativeMeasure K dx {0} = 0 := by
  letI : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
  simp [KPRamifiedBeta.multiplicativeMeasure, withDensity_apply, KPRamifiedBeta.normalizedAbs]
private lemma rational_agree (dx : Measure K) (ξ : CubicUnitCharacters.Character K)
    (hf : 1 ≤ CubicUnitCharacters.conductor K ξ) (u : ℂ) :
    KPRamifiedBeta.rationalBeta (CubicUnitCharacters.residueCard K : ℝ) (m K dx)
        (CubicUnitCharacters.conductor K ξ) (CubicUnitCharacters.residueCard K * u) =
      rationalBeta K dx ξ u := by
  let q : ℂ := CubicUnitCharacters.residueCard K
  have hq : q ≠ 0 := by
    dsimp [q]; exact_mod_cast (Finite.card_pos (α := 𝓀[K])).ne'
  let f := CubicUnitCharacters.conductor K ξ
  have hp : q⁻¹ ^ f * q ^ (f - 1) = q⁻¹ := by
    rw [show f = (f - 1) + 1 by omega, pow_succ, inv_pow]
    have hh := mul_inv_cancel₀ (pow_ne_zero (f - 1) hq)
    calc
      (q ^ (f - 1))⁻¹ * q⁻¹ * q ^ (f - 1) =
        ((q ^ (f - 1))⁻¹ * q ^ (f - 1)) * q⁻¹ := by ring
      _ = q⁻¹ := by simp [pow_ne_zero _ hq]
  unfold KPRamifiedBeta.rationalBeta rationalBeta a
  simp only [Complex.ofReal_natCast]
  change (m K dx : ℂ) * q⁻¹ ^ f * (q * u) ^ (f - 1) * (q * u - 1) /
    (1 - q⁻¹ * (q * u)) = (m K dx : ℂ) * u ^ (f - 1) * (u - q⁻¹) / (1 - u)
  rw [mul_pow]
  have hd : q⁻¹ * (q * u) = u := by simp [← mul_assoc, hq]
  rw [hd]
  congr 1
  calc
    _ = (m K dx : ℂ) * (q⁻¹ ^ f * q ^ (f - 1)) * u ^ (f - 1) * (q * u - 1) := by ring
    _ = _ := by rw [hp]; field_simp

end
end DedekindZetaZeroFree.KPRankOneRamifiedBeta

namespace DedekindZetaZeroFree

open scoped ValuativeRel Topology
open MeasureTheory ValuativeRel KPRankOneRamifiedBeta

theorem exists_eta_uniformizer_extension
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (ξ : CubicUnitCharacters.Character K) (b : ℂˣ) :
    ∃ η : Kˣ →ₜ* ℂˣ, ∀ (k : ℤ) (v : (𝒪[K])ˣ),
      η (π ^ k * KPRankOneCubicProjection.unitInclusion K v) = b ^ k * (ξ v : ℂˣ) := by
  obtain ⟨χ, hχ, hb⟩ := KPRamifiedBetaConductorSeries.exists_character_extension K π hπ ξ b
  refine ⟨χ, fun k v => ?_⟩
  have hχ' : χ (KPRankOneCubicProjection.unitInclusion K v) = (ξ v : ℂˣ) := hχ v
  rw [map_mul, map_zpow, hb, hχ']

theorem betaIntegral_eq_rationalBeta
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (π : Kˣ) (hπ : valuation K (π : K) = uniformizer K)
    (ξ : CubicUnitCharacters.Character K) (hξ : ξ ≠ 1) (b : ℂˣ)
    (η : Kˣ →ₜ* ℂˣ)
    (hη : ∀ (k : ℤ) (v : (𝒪[K])ˣ),
      η (π ^ k * KPRankOneCubicProjection.unitInclusion K v) = b ^ k * (ξ v : ℂˣ)) :
    ∀ u : ℂˣ, ‖a K‖ < ‖(b : ℂ)‖ → ‖(b : ℂ)‖ < 1 →
      ‖a K‖ / ‖(b : ℂ)‖ < ‖(u : ℂ)‖ → ‖(u : ℂ)‖ < 1 →
        Integrable (betaIntegrand K η u) (KPCubicHaar.multiplicativeHaar K dx) ∧
        betaIntegral K dx η u = rationalBeta K dx ξ (u : ℂ) := by
  intro u hab hb1 hbu hu1
  let q : ℝ := CubicUnitCharacters.residueCard K
  have hq : 1 < q := by
    dsimp [q, CubicUnitCharacters.residueCard]
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  let s : ℂ := 1 + Complex.log (u : ℂ) / (Real.log q : ℂ)
  have ha : ‖a K‖ = q⁻¹ := by
    simp [a, q, norm_inv, ← Complex.ofReal_natCast, Complex.norm_of_nonneg (show 0 ≤ (CubicUnitCharacters.residueCard K : ℝ) by positivity)]
  have hs := parameter_strip q ‖(b : ℂ)‖ ‖(u : ℂ)‖ hq hb1 (by simpa [ha] using hbu)
    hu1 (norm_pos_iff.mpr b.ne_zero) u rfl
  obtain ⟨hs0, hs1, hsB⟩ := hs
  have hpower := parameter_power q hq u
  have hηunit : ∀ v : (𝒪[K])ˣ,
      η (Units.map (𝒪[K]).subtype.toMonoidHom v) = (ξ v : ℂˣ) := by
    intro v; simpa [KPRankOneCubicProjection.unitInclusion] using hη 0 v
  have hηπ : η π = b := by simpa using hη 1 1
  have hI : Integrable (KPRamifiedBeta.integrand K η s)
      (KPRamifiedBeta.multiplicativeMeasure K dx) :=
    KPRamifiedBetaConductorSeries.integrable_in_joint_strip K dx π hπ ξ η hηunit b hηπ s hs0 hs1 hsB hb1
  have hi := integrands_agree K η u s hs0 hpower
  have hmap : Measure.map Units.val (KPCubicHaar.multiplicativeHaar K dx) =
      KPRamifiedBeta.multiplicativeMeasure K dx :=
    units_map_comap K (KPRamifiedBeta.multiplicativeMeasure K dx) (density_zero K dx)
  have hint : Integrable (betaIntegrand K η u) (KPCubicHaar.multiplicativeHaar K dx) := by
    rw [← hi]
    apply (units_embedding K).integrable_map_iff.mp
    rw [hmap]
    exact hI
  refine ⟨hint, ?_⟩
  have heq : betaIntegral K dx η u = KPRamifiedBeta.betaIntegral K dx η s := by
    unfold betaIntegral KPRamifiedBeta.betaIntegral
    rw [← hi]
    simpa only [Function.comp_def, hmap] using
      ((units_embedding K).integral_map (μ := KPCubicHaar.multiplicativeHaar K dx)
        (KPRamifiedBeta.integrand K η s)).symm
  rw [heq]
  obtain ⟨hf, ht, he⟩ := conductor_exact K ξ hξ
  have hex := he (CubicUnitCharacters.conductor K ξ - 1) (by omega)
  have heval := KPRamifiedBetaConductorSeries.integral_eq_shell_series K dx ξ hξ
    (CubicUnitCharacters.conductor K ξ) hf ht hex η hηunit s hs1 hI
  change KPRamifiedBeta.betaIntegral K dx η s = _ at heval
  have hset : {x : K | x ∈ (valuation K).integer} = (𝒪[K] : Set K) := by ext; rfl
  rw [hset] at heval
  rw [heval]
  have hsum := KPRamifiedBeta.rationalBeta_shell_sum q (m K dx)
    (CubicUnitCharacters.conductor K ξ) hf ((q : ℂ) ^ s)
    (KPRamifiedBetaConductorSeries.beta_geometric_ratio_norm_lt_one q hq s hs1)
  simp only [q, m, Complex.ofReal_natCast] at hsum
  rw [hsum]
  have hpower' : (CubicUnitCharacters.residueCard K : ℂ) ^ s =
      CubicUnitCharacters.residueCard K * (u : ℂ) := hpower
  rw [hpower']
  exact rational_agree K dx ξ hf (u : ℂ)

end DedekindZetaZeroFree
