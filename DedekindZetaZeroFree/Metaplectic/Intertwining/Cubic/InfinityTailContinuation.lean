module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.InfinityIntegrandScalar
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseCompactLaurentAnnulus
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.InfinityValuationBlocks

@[expose] public section

namespace DedekindZetaZeroFree.KPActualResidueSources
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw KPActualScalarBinding KPActualResidueSources
open KPRankOneReverseLaurentShellExpansion.InfinityTailNumeratorSteps
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q)
local notation "H₀" => KPExceptionalRaw.actualTorus F ζ hζ q

variable (P : Polarization S.heisenberg) [DecidableEq S.D]

private theorem units_borel (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := by
  constructor
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K),
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

private theorem valuation_mul (u v : (LocalField F q)ˣ) :
    valuationIndex F q (u * v) = valuationIndex F q u + valuationIndex F q v := by
  simp only [valuationIndex, Units.val_mul, map_mul]
  rw [WithZero.log_mul]
  all_goals simp

private theorem exists_valuation (m : ℤ) : ∃ u : (LocalField F q)ˣ, valuationIndex F q u = m := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  obtain ⟨a, ha⟩ := valuation_surjective (e.symm (WithZero.exp m))
  have ha0 : a ≠ 0 := by
    intro hh
    simp only [hh, map_zero] at ha
    have hne : e.symm (WithZero.exp m) ≠ 0 := (map_ne_zero e.symm).2 (by simp)
    exact hne ha.symm
  refine ⟨Units.mk0 a ha0, ?_⟩
  change WithZero.log (e (valuation (LocalField F q) a)) = m
  rw [ha, e.apply_symm_apply]
  simp

private theorem block_measurable (N n : ℕ) : MeasurableSet (infinityBlock F q N n) := by
  letI := units_borel (LocalField F q)
  have hc : Continuous (valuationIndex F q) := by
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hv : valuation (LocalField F q) (v : LocalField F q) ≠ 0 := by simpa using v.ne_zero
    have hh := Units.continuous_val.continuousAt.preimage_mem_nhds
      ((valuation (LocalField F q)).locally_const hv)
    filter_upwards [hh] with w hw
    exact congrArg (fun a => WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) a)) hw
  exact (isOpen_lt continuous_const hc).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet

private theorem haar (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] : (KPCubicHaar.multiplicativeHaar K μ).IsHaarMeasure := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have hc : IsCompact (KPCubicUnitIndices.Integers K : Set K) :=
    IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have ho : IsOpen (KPCubicUnitIndices.Integers K : Set K) := Valued.isOpen_integer K
  have hp : 0 < μ (KPCubicUnitIndices.Integers K : Set K) :=
    ho.measure_pos (μ := μ) ⟨0, by simp⟩
  exact (kp_rankone_cubic_haar_power_measure K μ _
    (ENNReal.toReal_pos hp.ne' hc.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hc.measure_lt_top.ne).symm).1

private theorem weight_formula (v : (LocalField F q)ˣ) (lam : ℂ) :
    (localAbs (LocalField F q) v : ℂ)⁻¹ * normPower (LocalField F q) v lam =
    ((residueCardinality (LocalField F q) : ℂ) * Q F q lam) ^ (-valuationIndex F q v) := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
      (Valuation.integer (valuation (LocalField F q)))))
  have hn : normPower (LocalField F q) v lam = Q F q lam ^ (-valuationIndex F q v) := by
    rw [normPower, localAbs, Real.log_rpow hq, Q, ← Complex.exp_int_mul]
    congr 1
    simp only [valuationIndex]
    push_cast
    ring
  rw [hn, mul_zpow]
  congr 1
  simp only [localAbs, Real.rpow_intCast, Complex.ofReal_zpow,
    valuationIndex, zpow_neg, zpow_natCast]
  simp only [Complex.ofReal_natCast]

private theorem coefficient_expansion
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ (E₀ : Finset (ℤ × ℤ))
      (c : H₀ → ℕ → (ℤ × ℤ) → (LocalField F q)ˣ → ℂ),
      (∀ h n ij, ij ∈ E₀ → IntegrableOn (c h n ij) (infinityBlock F q N n)
        (multiplicativeMeasure F q μ)) ∧
      (∀ h n ij, ij ∈ E₀ →
        (∫ v in infinityBlock F q N n, c h n ij v ∂multiplicativeMeasure F q μ) =
          (∫ v in infinityBlock F q N 0, c h 0 ij v ∂multiplicativeMeasure F q μ) *
            ((residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ)) ^ n) ∧
      (∀ r : ℂˣ, IsRegular F q r → ∀ lam : ℂ,
        ∀ h n v, v ∈ infinityBlock F q N n →
        reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r lam h v =
          ((∑ ij ∈ E₀, c h n ij v * (r : ℂ) ^ ij.1 * Q F q lam ^ ij.2) /
            (1 - t F q (r : ℂ))) * (Q F q lam ^ (-3 : ℤ)) ^ n) := by
  classical
  letI := units_borel (LocalField F q)
  letI := haar (LocalField F q) μ
  obtain ⟨L, χ, N₀, hL, hχ, _⟩ := actual_forward_uniform_infinity_data
    F ζ hζ q S P I μ J rep hrep d φ hφ hcφ
  let a : H₀ → ℤ → ℂ := fun h i => ((χ i).val.val (1 : I.compact.toOpenSubgroup)).val h
  have hforward (r : ℂˣ) (hr : IsRegular F q r) (h : H₀) :
      ((forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r).val 1).val h =
        (∑ i ∈ χ.support, a h i * (r : ℂ) ^ i) / (1 - t F q (r : ℂ)) := by
    rw [hχ r hr]
    change (centerInducingAction F ζ hζ q S.heisenberg S.borel .minus (-additiveParameter F q r)
      (I.borelPart 1) (((1 - t F q (r : ℂ))⁻¹ •
        χ.sum (fun i f => (r : ℂ) ^ i • f)).val.val (I.compactPart 1))).val h = _
    have hb : I.borelPart 1 = 1 := by simpa using I.borelPart_compact 1
    have hk : I.compactPart 1 = 1 := by simpa using I.compactPart_compact 1
    rw [hb, hk, map_one]
    simp [Finsupp.sum, a, div_eq_mul_inv, Finset.sum_mul, mul_comm]
  obtain ⟨N₁, hscalar⟩ := actual_infinity_eventual_scalar F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ
  let cutoff := max N₀ N₁
  refine ⟨cutoff, ?_⟩
  intro N hN
  let E : Finset ℤ := Finset.Icc (-(N : ℤ) - 3) (-(N : ℤ) - 1)
  let qc : ℂ := residueCardinality (LocalField F q)
  have hq : qc ≠ 0 := by
    dsimp [qc]
    have hpos : 0 < residueCardinality (LocalField F q) := Nat.card_pos
    exact_mod_cast hpos.ne'
  let c : H₀ → ℕ → (ℤ × ℤ) → (LocalField F q)ˣ → ℂ := fun h n ij v =>
    if ij.2 = -valuationIndex F q v + 3 * (n : ℤ) then
      a h ij.1 * qc ^ (-valuationIndex F q v) else 0
  have hcscale (h : H₀) (n : ℕ) (ij : ℤ × ℤ)
      (u : (LocalField F q)ˣ) (hu : valuationIndex F q u = 3 * (n : ℤ))
      (v : (LocalField F q)ˣ) :
      c h n ij (u * v) = c h 0 ij v * (qc ^ (-3 : ℤ)) ^ n := by
    dsimp [c]
    rw [valuation_mul, hu]
    have hexp : -(3 * (n : ℤ) + valuationIndex F q v) =
        -valuationIndex F q v + (-3) * (n : ℤ) := by ring
    have htest : - (3 * (n : ℤ) + valuationIndex F q v) + 3 * (n : ℤ) =
        -valuationIndex F q v := by ring
    simp only [htest, Nat.cast_zero, mul_zero, add_zero]
    split_ifs
    · rw [hexp, zpow_add₀ hq, zpow_mul, zpow_natCast]
      ring
    · simp
  refine ⟨χ.support ×ˢ E, c, ?_, ?_, ?_⟩
  · intro h n ij _hij
    have hl : IsLocallyConstant (c h n ij) :=
      (KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps.reverse_compact_valuationIndex_locallyConstant F q).comp
        (fun k : ℤ => if ij.2 = -k + 3 * (n : ℤ) then a h ij.1 * qc ^ (-k) else 0)
    apply (hl.continuous.continuousOn.integrableOn_compact
      (KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps.reverse_compact_annulus_isCompact F q (N + 3 * (n + 1)))).mono_set
    intro v hv
    change -(↑(N + 3 * (n + 1)) : ℤ) ≤ valuationIndex F q v ∧
      valuationIndex F q v ≤ (↑(N + 3 * (n + 1)) : ℤ)
    change (N : ℤ) + 3 * (n : ℤ) < valuationIndex F q v ∧
      valuationIndex F q v ≤ (N : ℤ) + 3 * ((n : ℤ) + 1) at hv
    push_cast at *
    omega
  · intro h n ij _hij
    obtain ⟨u, hu⟩ := exists_valuation F q (3 * (n : ℤ))
    have htrans (v : (LocalField F q)ˣ) : u * v ∈ infinityBlock F q N n ↔
        v ∈ infinityBlock F q N 0 := by
      simp only [infinityBlock, Set.mem_setOf_eq, valuation_mul, hu]
      omega
    have hind (v : (LocalField F q)ˣ) :
        (infinityBlock F q N n).indicator (c h n ij) (u * v) =
          (infinityBlock F q N 0).indicator (c h 0 ij) v * (qc ^ (-3 : ℤ)) ^ n := by
      by_cases hv : v ∈ infinityBlock F q N 0
      · rw [Set.indicator_of_mem ((htrans v).mpr hv), Set.indicator_of_mem hv,
          hcscale h n ij u hu v]
      · rw [Set.indicator_of_notMem (fun hh => hv ((htrans v).mp hh)),
          Set.indicator_of_notMem hv, zero_mul]
    have hi := integral_mul_left_eq_self (μ := multiplicativeMeasure F q μ)
      ((infinityBlock F q N n).indicator (c h n ij)) u
    simp only [hind, integral_mul_const] at hi
    rw [integral_indicator (block_measurable F q N 0),
      integral_indicator (block_measurable F q N n)] at hi
    exact hi.symm
  · intro r hr lam h n v hv
    have hmin : N₁ ≤ N := le_trans (Nat.le_max_right _ _) hN
    have htail : (N₁ : ℤ) < valuationIndex F q v := by
      have hh : (N₁ : ℤ) ≤ N := by exact_mod_cast hmin
      have hv1 := hv.1
      change (N : ℤ) + 3 * (n : ℤ) < valuationIndex F q v at hv1
      omega
    rw [hscalar r hr lam h v htail, mul_assoc, weight_formula, hforward r hr h]
    have hk : -valuationIndex F q v + 3 * (n : ℤ) ∈ E := by
      change (N : ℤ) + 3 * (n : ℤ) < valuationIndex F q v ∧
        valuationIndex F q v ≤ (N : ℤ) + 3 * ((n : ℤ) + 1) at hv
      simp only [E, Finset.mem_Icc]
      omega
    have hsum : (∑ ij ∈ χ.support ×ˢ E,
        c h n ij v * (r : ℂ) ^ ij.1 * Q F q lam ^ ij.2) =
        (∑ i ∈ χ.support, a h i * (r : ℂ) ^ i) *
          qc ^ (-valuationIndex F q v) *
          Q F q lam ^ (-valuationIndex F q v + 3 * (n : ℤ)) := by
      rw [Finset.sum_product]
      simp only [c]
      have hs (i : ℤ) : (∑ j ∈ E,
          (if j = -valuationIndex F q v + 3 * (n : ℤ) then
            a h i * qc ^ (-valuationIndex F q v) else 0) *
              (r : ℂ) ^ i * Q F q lam ^ j) =
          a h i * qc ^ (-valuationIndex F q v) * (r : ℂ) ^ i *
            Q F q lam ^ (-valuationIndex F q v + 3 * (n : ℤ)) := by
        rw [Finset.sum_eq_single (-valuationIndex F q v + 3 * (n : ℤ))]
        · simp
        · intro j _hj hj
          simp [hj]
        · exact fun hh => (hh hk).elim
      simp only [hs, Finset.sum_mul]
      congr 2
      funext i
      ring
    rw [hsum, mul_zpow]
    have hQ : Q F q lam ≠ 0 := Complex.exp_ne_zero _
    rw [zpow_add₀ hQ, zpow_mul, zpow_natCast]
    have hcanc : (Q F q lam ^ (3 : ℤ)) ^ n * (Q F q lam ^ (-3 : ℤ)) ^ n = 1 := by
      rw [← mul_pow, ← zpow_add₀ hQ]
      norm_num
    dsimp [qc]
    simp only [div_eq_mul_inv]
    calc
      _ = ((∑ i ∈ χ.support, a h i * (r : ℂ) ^ i) *
          (1 - t F q (r : ℂ))⁻¹ *
          (residueCardinality (LocalField F q) : ℂ) ^ (-valuationIndex F q v) *
          Q F q lam ^ (-valuationIndex F q v)) *
            ((Q F q lam ^ (3 : ℤ)) ^ n * (Q F q lam ^ (-3 : ℤ)) ^ n) := by rw [hcanc]; ring
      _ = _ := by ring

variable {X : Type*} [MeasurableSpace X]

 def integratedShellNumerator (ν : Measure X) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) : ShellNumerator :=
  ∑ ij ∈ S, Finsupp.single ij (∫ x, c ij x ∂ν)

private theorem evaluate_integratedShellNumerator (ν : Measure X) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) (r Q : ℂ) :
    evaluateNumerator (integratedShellNumerator ν S c) r Q =
      ∑ ij ∈ S, (∫ x, c ij x ∂ν) * r ^ ij.1 * Q ^ ij.2 := by
  unfold integratedShellNumerator
  induction S using Finset.induction_on with
  | empty => simp [evaluateNumerator]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [evaluateNumerator, Finsupp.sum_add_index]
    · simp only [Finsupp.sum_single_index, mul_zero, zero_mul, add_zero]
      exact congrArg (_ + ·) ih
    · intro ij; simp
    · intro ij hij b d; ring

private theorem integral_finite_shell_expansion (ν : Measure X) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) (hc : ∀ ij ∈ S, Integrable (c ij) ν)
    (r Q den : ℂ) (f : X → ℂ)
    (hf : ∀ x, f x = (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den) :
    Integrable f ν ∧ (∫ x, f x ∂ν) =
      evaluateNumerator (integratedShellNumerator ν S c) r Q / den := by
  have hi : ∀ ij ∈ S, Integrable (fun x => c ij x * r ^ ij.1 * Q ^ ij.2) ν := by
    intro ij hij
    exact ((hc ij hij).mul_const _).mul_const _
  have hs := integrable_finsetSum S hi
  have hfun : f = fun x => (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den := funext hf
  rw [hfun]
  refine ⟨hs.div_const den, ?_⟩
  simp only [div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum S hi, evaluate_integratedShellNumerator]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  rw [integral_mul_const, integral_mul_const]

private theorem setIntegral_finite_shell_expansion (ν : Measure X) (E : Set X)
    (hE : MeasurableSet E) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) (hc : ∀ ij ∈ S, IntegrableOn (c ij) E ν)
    (r Q den : ℂ) (f : X → ℂ)
    (hf : ∀ x ∈ E, f x = (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den) :
    IntegrableOn f E ν ∧ (∫ x in E, f x ∂ν) =
      evaluateNumerator (integratedShellNumerator (ν.restrict E) S c) r Q / den := by
  let g : X → ℂ := fun x => (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den
  obtain ⟨hi, he⟩ := integral_finite_shell_expansion (ν.restrict E) S c hc r Q den g
    (fun _ => rfl)
  exact ⟨IntegrableOn.congr_fun hi (fun x hx => (hf x hx).symm) hE,
    (setIntegral_congr_fun hE hf).trans he⟩

private theorem block_numerators
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ p : H₀ → ShellNumerator,
      ∀ r : ℂˣ, IsRegular F q r → ∀ (lam : ℂ) (h : H₀) (n : ℕ),
        IntegrableOn
          (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h)
          (infinityBlock F q N n) (multiplicativeMeasure F q μ) ∧
        (∫ v in infinityBlock F q N n,
          reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h v ∂multiplicativeMeasure F q μ) =
          (evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r)) *
            ((residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) *
              Q F q lam ^ (-3 : ℤ)) ^ n := by
  obtain ⟨N₀, hN₀⟩ := coefficient_expansion F ζ hζ q S P I μ J rep hrep d φ hφ hcφ
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨E₀, c, hc, hscale, hexp⟩ := hN₀ N hN
  let ν := multiplicativeMeasure F q μ
  let p : H₀ → ShellNumerator := fun h =>
    integratedShellNumerator (ν.restrict (infinityBlock F q N 0)) E₀ (c h 0)
  refine ⟨p, ?_⟩
  intro r hr lam h n
  let g : (LocalField F q)ˣ → ℂ := fun v =>
    (∑ ij ∈ E₀, c h n ij v * (r : ℂ) ^ ij.1 * Q F q lam ^ ij.2) /
      (1 - t F q (r : ℂ))
  obtain ⟨hi, he⟩ := setIntegral_finite_shell_expansion ν
    (infinityBlock F q N n) (block_measurable F q N n) E₀
    (c h n) (hc h n) (r : ℂ) (Q F q lam) (1 - t F q (r : ℂ)) g
    (fun _ _ => rfl)
  have hfg := hexp r hr lam h n
  refine ⟨IntegrableOn.congr_fun (hi.mul_const ((Q F q lam ^ (-3 : ℤ)) ^ n))
    (fun v hv => (hfg v hv).symm) (block_measurable F q N n), ?_⟩
  rw [setIntegral_congr_fun (block_measurable F q N n) hfg,
    integral_mul_const, he]
  have hp : evaluateNumerator
      (integratedShellNumerator (ν.restrict (infinityBlock F q N n)) E₀ (c h n))
        r (Q F q lam) =
      evaluateNumerator (p h) r (Q F q lam) *
        ((residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ)) ^ n := by
    rw [evaluate_integratedShellNumerator]
    change _ = evaluateNumerator
      (integratedShellNumerator (ν.restrict (infinityBlock F q N 0)) E₀ (c h 0))
      r (Q F q lam) * _
    rw [evaluate_integratedShellNumerator, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [hscale h n ij hij]
    ring
  rw [hp, mul_pow]
  ring

private theorem norm_blocks_geometric
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℂˣ, IsRegular F q r →
      ∀ (lam : ℂ) (h : H₀) (n : ℕ),
        (∫ v in infinityBlock F q N n,
          ‖reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) =
        (∫ v in infinityBlock F q N 0,
          ‖reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) *
          ‖(residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) *
            Q F q lam ^ (-3 : ℤ)‖ ^ n := by
  obtain ⟨N₀, hscalar⟩ := actual_infinity_eventual_scalar F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ
  refine ⟨N₀, ?_⟩
  intro N hN r hr lam h n
  letI := units_borel (LocalField F q)
  letI := haar (LocalField F q) μ
  let b : ℂ := (residueCardinality (LocalField F q) : ℂ) * Q F q lam
  have hb : b ≠ 0 := mul_ne_zero (by
    have hq : 0 < residueCardinality (LocalField F q) := Nat.card_pos
    exact_mod_cast hq.ne') (Complex.exp_ne_zero _)
  let c : ℂ := ((forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r).val 1).val h
  let f : (LocalField F q)ˣ → ℂ := fun v => c * b ^ (-valuationIndex F q v)
  have he (k : ℕ) (v : (LocalField F q)ˣ) (hv : v ∈ infinityBlock F q N k) :
      reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r lam h v = f v := by
    rw [hscalar r hr lam h v (by
      have hv1 := hv.1
      change (N : ℤ) + 3 * (k : ℤ) < valuationIndex F q v at hv1
      have hh : (N₀ : ℤ) ≤ N := by exact_mod_cast hN
      omega), mul_assoc, weight_formula]
  rw [setIntegral_congr_fun (block_measurable F q N n) (fun v hv => congrArg norm (he n v hv)),
    setIntegral_congr_fun (block_measurable F q N 0) (fun v hv => congrArg norm (he 0 v hv))]
  obtain ⟨u, hu⟩ := exists_valuation F q (3 * (n : ℤ))
  have htrans (v : (LocalField F q)ˣ) : u * v ∈ infinityBlock F q N n ↔
      v ∈ infinityBlock F q N 0 := by
    simp only [infinityBlock, Set.mem_setOf_eq, valuation_mul, hu]
    omega
  have hscale (v : (LocalField F q)ˣ) : f (u * v) = f v * (b ^ (-3 : ℤ)) ^ n := by
    dsimp [f]
    rw [valuation_mul, hu, neg_add, zpow_add₀ hb]
    have hh : b ^ (-(3 * (n : ℤ))) = (b ^ (-3 : ℤ)) ^ n := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
    rw [hh]
    ring
  have hind (v : (LocalField F q)ˣ) :
      (infinityBlock F q N n).indicator (fun v => ‖f v‖) (u * v) =
      (infinityBlock F q N 0).indicator (fun v => ‖f v‖) v * ‖(b ^ (-3 : ℤ)) ^ n‖ := by
    by_cases hv : v ∈ infinityBlock F q N 0
    · rw [Set.indicator_of_mem ((htrans v).mpr hv), Set.indicator_of_mem hv, hscale, norm_mul]
    · rw [Set.indicator_of_notMem (fun hh => hv ((htrans v).mp hh)),
        Set.indicator_of_notMem hv, zero_mul]
  have hi := integral_mul_left_eq_self (μ := multiplicativeMeasure F q μ)
    ((infinityBlock F q N n).indicator (fun v => ‖f v‖)) u
  simp only [hind, integral_mul_const] at hi
  rw [integral_indicator (block_measurable F q N 0),
    integral_indicator (block_measurable F q N n)] at hi
  rw [← hi]
  congr 1
  dsimp [b]
  rw [mul_zpow, norm_pow]

private theorem infinityTail_norm_Q (lam : ℂ) :
    ‖Q F q lam‖ = (residueCardinality (LocalField F q) : ℝ).rpow (-lam.re) := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    have h : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
    exact_mod_cast (lt_trans Nat.zero_lt_one h)
  simp only [Q, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_eq_pow,
    Real.rpow_def_of_pos hq]
  congr 1
  ring

private theorem infinityTail_ratio_norm (lam : ℂ) :
    ‖(residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) * Q F q lam ^ (-3 : ℤ)‖ =
      (residueCardinality (LocalField F q) : ℝ).rpow (3 * lam.re - 3) := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    have h : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
    exact_mod_cast (lt_trans Nat.zero_lt_one h)
  rw [norm_mul, norm_zpow, norm_zpow, infinityTail_norm_Q F q]
  have hn : ‖(residueCardinality (LocalField F q) : ℂ)‖ =
      (residueCardinality (LocalField F q) : ℝ) := by simp
  rw [hn, Real.rpow_eq_pow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_add hq, Real.rpow_eq_pow]
  congr 1
  norm_num
  ring

private theorem infinityTail_ratio_norm_lt_one (lam : ℂ) (hlam : lam.re < 1) :
    ‖(residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) * Q F q lam ^ (-3 : ℤ)‖ < 1 := by
  rw [infinityTail_ratio_norm F q, Real.rpow_eq_pow]
  have hq : 1 < (residueCardinality (LocalField F q) : ℝ) := by
    have h : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
    exact_mod_cast h
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

private theorem infinityBlock_pairwise_disjoint (N : ℕ) :
    Pairwise (fun n m : ℕ => Disjoint (infinityBlock F q N n)
      (infinityBlock F q N m)) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro v hv hw
  simp only [infinityBlock, Set.mem_setOf_eq] at hv hw
  rcases lt_or_gt_of_ne hnm with h | h
  · have : (n : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast h
    omega
  · have : (m : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast h
    omega

private theorem infinityBlock_iUnion (N : ℕ) :
    (⋃ n : ℕ, infinityBlock F q N n) = infinityRegion F q N := by
  ext v
  simp only [infinityBlock, infinityRegion, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h1, h2⟩
    push_cast
    omega
  · intro hv
    push_cast at hv
    let k : ℕ := (valuationIndex F q v - (N : ℤ) - 1).toNat
    have hk : (k : ℤ) = valuationIndex F q v - (N : ℤ) - 1 := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    refine ⟨k / 3, ?_⟩
    have hmod := Nat.mod_lt k (by decide : 0 < 3)
    have hdiv := Nat.mod_add_div k 3
    push_cast
    omega

theorem actual_infinity_tail_specialization
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ p : H₀ → ShellNumerator,
      ∀ r : ℂˣ, IsRegular F q r → ∀ lam : ℂ, lam.re < 1 → ∀ h : H₀,
        IntegrableOn
          (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h)
          (infinityRegion F q N) (multiplicativeMeasure F q μ) ∧
        Summable (fun n : ℕ => ∫ v in infinityBlock F q N n,
          ‖reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) ∧
        (∀ n : ℕ,
          IntegrableOn
            (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
              rep hrep d φ hφ hcφ r lam h)
            (infinityBlock F q N n) (multiplicativeMeasure F q μ) ∧
          (∫ v in infinityBlock F q N n,
            reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
              rep hrep d φ hφ hcφ r lam h v ∂multiplicativeMeasure F q μ) =
            (evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r)) *
              ((residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) *
                Q F q lam ^ (-3 : ℤ)) ^ n) ∧
        (∫ v in infinityRegion F q N,
          reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h v ∂multiplicativeMeasure F q μ) =
          evaluateNumerator (p h) r (Q F q lam) /
            ((1 - t F q r) * infinityFactor F q (Q F q lam)) := by
  obtain ⟨N₁, h₁⟩ := block_numerators F ζ hζ q S P I μ J rep hrep d φ hφ hcφ
  obtain ⟨N₂, h₂⟩ := norm_blocks_geometric F ζ hζ q S P I μ J rep hrep d φ hφ hcφ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hn₁ : N₁ ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hn₂ : N₂ ≤ N := le_trans (Nat.le_max_right _ _) hN
  obtain ⟨p, hp⟩ := h₁ N hn₁
  refine ⟨p, ?_⟩
  intro r hr lam hlam h
  have hratio := infinityTail_ratio_norm_lt_one F q lam hlam
  have hs : Summable (fun n : ℕ => ∫ v in infinityBlock F q N n,
      ‖reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
        rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) := by
    have hefun : (fun n : ℕ => ∫ v in infinityBlock F q N n,
        ‖reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
          rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) =
        (fun n : ℕ => (∫ v in infinityBlock F q N 0,
          ‖reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
            rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) *
          ‖(residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) *
            Q F q lam ^ (-3 : ℤ)‖ ^ n) := funext (h₂ N hn₂ r hr lam h)
    rw [hefun]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hratio).mul_left _
  have hi : IntegrableOn
      (reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
        rep hrep d φ hφ hcφ r lam h)
      (⋃ n : ℕ, infinityBlock F q N n) (multiplicativeMeasure F q μ) :=
    integrableOn_iUnion_of_summable_integral_norm (fun n => (hp r hr lam h n).1) hs
  have hsum := hasSum_integral_iUnion (block_measurable F q N)
    (infinityBlock_pairwise_disjoint F q N) hi
  rw [infinityBlock_iUnion F q N] at hi hsum
  refine ⟨hi, hs, hp r hr lam h, ?_⟩
  simp_rw [(hp r hr lam h _).2] at hsum
  have hg := (hasSum_geometric_of_norm_lt_one hratio).mul_left
    (evaluateNumerator (p h) r (Q F q lam) / (1 - t F q r))
  have he := hsum.unique hg
  simpa only [infinityFactor, div_eq_mul_inv, mul_inv_rev, mul_assoc,
    mul_left_comm, mul_comm] using he

end
end DedekindZetaZeroFree.KPActualResidueSources
