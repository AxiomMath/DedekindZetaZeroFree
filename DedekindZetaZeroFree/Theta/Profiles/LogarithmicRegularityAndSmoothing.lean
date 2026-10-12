module

public import DedekindZetaZeroFree.Theta.Digits.WeightedDescentAndZeroDigits
public import DedekindZetaZeroFree.Theta.Profiles.WeylJetProductMajorants
public import DedekindZetaZeroFree.Theta.Profiles.SheetIntegralPowerBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def sheetLogProfile (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (v : R.A.UnitQuotient) (κ : R.A.V) (u : ℝ) : ℂ :=
  C.realization.sheet C.packet v κ ⟨Real.exp u, Real.exp_pos u⟩

theorem sheet_log_differentiation (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (C : JointDigitDescentSources R N) :
    (∀ v κ, ContDiff ℝ 2 (sheetLogProfile R C v κ)) ∧
    (∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ,
      letI : MeasurableSpace R.A.G1 := borel _;
      Integrable (fun y : R.A.G1 => iteratedDeriv j
        (fun t => radialSheetIntegrand R C v κ t y) u) R.probe.domain.measure ∧
      iteratedDeriv j (sheetLogProfile R C v κ) u =
        ∫ y : R.A.G1, iteratedDeriv j
          (fun t => radialSheetIntegrand R C v κ t y) u ∂ R.probe.domain.measure) := by
  letI : MeasurableSpace R.A.G1 := borel _
  obtain ⟨hreg, hmeas⟩ := radial_sheet_integrand_regular R C
  obtain ⟨M, D, hM, hD, hb⟩ := radial_sheet_jet_product_majorant R C 1 zero_lt_one
  have hp := (sheet_product_power_majorant_integrals R N C 0 (by norm_num) 1
    (by norm_num) M hM).2
  have hdata (v : R.A.UnitQuotient) (κ : R.A.V) :
      SourceSheet.Differentiation.TwoDerivativeData R.probe.domain.measure
        (fun j u y => iteratedDeriv j (fun t => radialSheetIntegrand R C v κ t y) u) := by
    refine ⟨hmeas v κ, ?_, ?_, ?_⟩
    · intro j hj y u
      simpa only [iteratedDeriv_succ] using
        ((hreg v κ y).differentiable_iteratedDeriv j (by exact_mod_cast hj) u).hasDerivAt
    · intro y
      exact (hreg v κ y).continuous_iteratedDeriv 2 le_rfl
    · intro u
      obtain ⟨s, hs, E, hE, he⟩ := hp u
      refine ⟨s, hs, fun y => D * E y, hE.const_mul D, ?_⟩
      filter_upwards [he] with y hy
      intro t ht j hj
      exact (hb v κ j hj t y).trans (mul_le_mul_of_nonneg_left (hy t ht) hD)
  have heq (v : R.A.UnitQuotient) (κ : R.A.V) :
      sheetLogProfile R C v κ = fun u => ∫ y : R.A.G1,
        iteratedDeriv 0 (fun t => radialSheetIntegrand R C v κ t y) u
          ∂ R.probe.domain.measure := by
    rfl
  refine ⟨fun v κ => ?_, fun v κ j hj u => ?_⟩
  · rw [heq]
    exact (hdata v κ).integral_calculus.1
  · refine ⟨(hdata v κ).integrable j hj u, ?_⟩
    rw [heq]
    exact (hdata v κ).integral_calculus.2 j hj u

theorem absolute_sheet_jet_power_bounds (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (C : JointDigitDescentSources R N) :
    ∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ v κ (j : ℕ), j ≤ 2 → ∀ u : ℝ,
        letI : MeasurableSpace R.A.G1 := borel _;
        (∫ y : R.A.G1, ‖iteratedDeriv j
          (fun t => radialSheetIntegrand R C v κ t y) u‖ ∂ R.probe.domain.measure) ≤
          K * Real.exp (-σ * u) := by
  letI : MeasurableSpace R.A.G1 := borel _
  intro σ hσ
  let A := max σ 0 + 1
  have hA : max σ 0 < A := by dsimp [A]; linarith
  obtain ⟨M, D, hM, hD, hb⟩ := radial_sheet_jet_product_majorant R C A
    (lt_of_le_of_lt (le_max_right _ _) hA)
  obtain ⟨K, hK, hk⟩ := (sheet_product_power_majorant_integrals R N C σ hσ A hA M hM).1
  refine ⟨D * K, mul_nonneg hD hK, ?_⟩
  intro v κ j hj u
  have hi := (sheet_log_differentiation R N C).2 v κ j hj u
  calc
    _ ≤ ∫ y : R.A.G1, D * sheetProductPowerMajorant R M A
        (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)) ∂ R.probe.domain.measure :=
      integral_mono hi.1.norm ((hk u).1.const_mul D) (hb v κ j hj u)
    _ = D * (∫ y : R.A.G1, sheetProductPowerMajorant R M A
        (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)) ∂ R.probe.domain.measure) :=
      integral_const_mul _ _
    _ ≤ D * (K * Real.exp (-σ * u)) := mul_le_mul_of_nonneg_left (hk u).2 hD
    _ = _ := by ring

theorem sheet_log_jet_power_bounds (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (C : JointDigitDescentSources R N) :
    ∃ K : ℝ → ℕ → ℝ,
      (∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ j : ℕ, j ≤ 2 → 0 ≤ K σ j) ∧
      (∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ j : ℕ, j ≤ 2 → ∀ v κ u,
        ‖iteratedDeriv j (sheetLogProfile R C v κ) u‖ ≤ K σ j * Real.exp (-σ * u)) := by
  let hp := absolute_sheet_jet_power_bounds R N C
  let K : ℝ → ℕ → ℝ := fun σ _ => if hσ : -(1 / 4 : ℝ) < σ then (hp σ hσ).choose else 0
  refine ⟨K, ?_, ?_⟩
  · intro σ hσ j hj
    simpa only [K, dif_pos hσ] using (hp σ hσ).choose_spec.1
  · intro σ hσ j hj v κ u
    letI : MeasurableSpace R.A.G1 := borel _
    rw [(sheet_log_differentiation R N C).2 v κ j hj u |>.2]
    exact (norm_integral_le_integral_norm _).trans (by
      simpa only [K, dif_pos hσ] using (hp σ hσ).choose_spec.2 v κ j hj u)

def sheetPositiveExtension (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (v : R.A.UnitQuotient) (κ : R.A.V) (x : ℝ) : ℂ :=
  if hx : 0 < x then C.realization.sheet C.packet v κ ⟨x, hx⟩ else 0

private theorem sheet_positive_extension_log_profile (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient) (κ : R.A.V) :
    logProfile (sheetPositiveExtension R C v κ) = sheetLogProfile R C v κ := by
  funext u
  simp [logProfile, sheetPositiveExtension, sheetLogProfile, Real.exp_pos]

private theorem log_convolution_measure_integrable_iff_positive_haar {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) : Integrable f logConvolutionMeasure ↔
      Integrable (fun T : ThetaProfileHaarSheets.PositiveAxis => f T.val)
        ThetaProfileHaarSheets.positiveHaar := by
  rw [logConvolutionMeasure, ← ThetaProfileHaarSheets.positiveHaar_map_val]
  exact (MeasurableEmbedding.subtype_coe measurableSet_Ioi).integrable_map_iff

private theorem log_convolution_measure_integral_eq_positive_haar (f : ℝ → ℂ) :
    (∫ T, f T ∂logConvolutionMeasure) =
      ∫ T : ThetaProfileHaarSheets.PositiveAxis, f T.val
        ∂ThetaProfileHaarSheets.positiveHaar := by
  rw [logConvolutionMeasure, ← ThetaProfileHaarSheets.positiveHaar_map_val]
  exact (MeasurableEmbedding.subtype_coe measurableSet_Ioi).integral_map f

theorem gaussian_kernel_measurable_and_absolute_moments (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    (Measurable (fun t : Set.Ioi (0 : ℝ) => C.packet.kernel t.val)) ∧
    (∀ σ : ℝ, Integrable (fun t : ℝ => ‖C.packet.kernel t‖ * t ^ σ)
      logConvolutionMeasure) := by
  have hr : 1 ≤ Fintype.card (InfinitePlace F) := Fintype.card_pos
  have hc := thetaProfileGaussianKernel_continuousOn C.packet.C₀ C.packet.A₀
    (Fintype.card (InfinitePlace F)) C.mellin.C₀_pos C.packet.A₀_pos hr
  refine ⟨hc.restrict.measurable, ?_⟩
  intro σ
  have hi := thetaProfileGaussianKernel_absolute_moment C.packet.C₀ C.packet.A₀
    (Fintype.card (InfinitePlace F)) C.mellin.C₀_pos C.packet.A₀_pos hr σ
  rw [logConvolutionMeasure, restrict_withDensity measurableSet_Ioi,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  simp [Packet.kernel, ENNReal.toReal_ofReal (inv_nonneg.mpr hT.le),
    smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]

private theorem smoothed_sheet_log_eq_log_convolution (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient) (κ : R.A.V) :
    logProfile (C.realization.H C.packet v κ) =
      logProfile (logConvolution C.packet.kernel (sheetPositiveExtension R C v κ)) := by
  funext u
  simp only [logProfile, Realization.H, dif_pos (Real.exp_pos u), logConvolution]
  rw [log_convolution_measure_integral_eq_positive_haar]
  apply integral_congr_ae
  filter_upwards with t
  simp only [sheetPositiveExtension, dif_pos (div_pos (Real.exp_pos u) t.property)]

theorem smoothed_sheet_log_calculus (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (C : JointDigitDescentSources R N) :
    (∀ v κ, ContDiff ℝ 2 (logProfile (C.realization.H C.packet v κ))) ∧
    (∃ K : ℝ → ℕ → ℝ,
      (∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ j : ℕ, j ≤ 2 → 0 ≤ K σ j) ∧
      (∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ j : ℕ, j ≤ 2 → ∀ v κ u,
        ‖iteratedDeriv j (logProfile (C.realization.H C.packet v κ)) u‖ ≤
          K σ j * Real.exp (-σ * u))) ∧
    (∀ v κ (j : ℕ), j ≤ 2 → ∀ x : ℝ, 0 < x →
      Integrable (fun t : ThetaProfileHaarSheets.PositiveAxis => C.packet.kernel t.val *
        iteratedDeriv j (fun z : ℝ => C.realization.sheet C.packet v κ
          ⟨Real.exp z / t.val, div_pos (Real.exp_pos z) t.property⟩) (Real.log x))
        ThetaProfileHaarSheets.positiveHaar) := by
  letI : Finite R.A.UnitQuotient := C.sources.finite_companions
  letI : Finite R.A.V := SArithmeticData.V_finite R.A
  letI : Fintype (R.A.UnitQuotient × R.A.V) := Fintype.ofFinite _
  obtain ⟨K, hK, hk⟩ := sheet_log_jet_power_bounds R N C
  obtain ⟨hkm, hm⟩ := gaussian_kernel_measurable_and_absolute_moments R C
  have hout := logConvolution_c2
    (fun i : R.A.UnitQuotient × R.A.V => sheetPositiveExtension R C i.1 i.2)
    C.packet.kernel K
    (fun i => by rw [sheet_positive_extension_log_profile]; exact (sheet_log_differentiation R N C).1 i.1 i.2)
    hK
    (fun σ hσ j hj i u => by rw [sheet_positive_extension_log_profile]; exact hk σ hσ j hj i.1 i.2 u)
    hkm hm
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro v κ
    rw [smoothed_sheet_log_eq_log_convolution]
    exact hout.2.1 (v, κ)
  · refine ⟨fun σ j => K σ j * logConvolutionMoment C.packet.kernel σ, ?_, ?_⟩
    · intro σ hσ j hj
      apply mul_nonneg (hK σ hσ j hj)
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg ht.le _)
    · intro σ hσ j hj v κ u
      rw [smoothed_sheet_log_eq_log_convolution]
      exact hout.2.2.2 σ hσ (v, κ) j hj u
  · intro v κ j hj x hx
    have hi := (log_convolution_measure_integrable_iff_positive_haar _).mp (hout.2.2.1 (v, κ) j hj (Real.log x)).1
    have heq (t : ThetaProfileHaarSheets.PositiveAxis) :
        (fun z : ℝ => C.realization.sheet C.packet v κ
          ⟨Real.exp z / t.val, div_pos (Real.exp_pos z) t.property⟩) =
        fun z => logProfile (sheetPositiveExtension R C v κ) (z - Real.log t.val) := by
      funext z
      simp [logProfile, sheetPositiveExtension, Real.exp_sub, Real.exp_log t.property,
        div_pos (Real.exp_pos z) t.property]
    apply hi.congr
    filter_upwards with t
    rw [heq, iteratedDeriv_comp_sub_const]

private theorem min_rpow_bound_of_exp_power_bounds
    {I : Type*} (E : I → ℝ → ℝ)
    (hp : ∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i u, E i u ≤ K * Real.exp (-σ * u)) :
    ∀ B : ℝ, 0 < B → ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, 0 < x →
      E i (Real.log x) ≤ K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B)) := by
  intro B hB
  obtain ⟨K₀, hK₀, hk₀⟩ := hp (-(1 / 8)) (by norm_num)
  obtain ⟨K₁, hK₁, hk₁⟩ := hp B (by linarith)
  let K := max K₀ K₁
  refine ⟨K, le_trans hK₀ (le_max_left _ _), ?_⟩
  intro i x hx
  have h₀ : E i (Real.log x) ≤ K * Real.rpow x (1 / 8) := by
    calc
      _ ≤ K₀ * Real.exp (-(-(1 / 8)) * Real.log x) := hk₀ i _
      _ = K₀ * Real.rpow x (1 / 8) := by
        change _ = K₀ * x ^ (1 / 8 : ℝ)
        rw [Real.rpow_def_of_pos hx]; congr 2 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _)
  have h₁ : E i (Real.log x) ≤ K * Real.rpow x (-B) := by
    calc
      _ ≤ K₁ * Real.exp (-B * Real.log x) := hk₁ i _
      _ = K₁ * Real.rpow x (-B) := by
        change _ = K₁ * x ^ (-B)
        rw [Real.rpow_def_of_pos hx]; congr 2 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx.le _)
  rcases le_total (Real.rpow x (1 / 8)) (Real.rpow x (-B)) with h | h
  · simpa only [min_eq_left h] using h₀
  · simpa only [min_eq_right h] using h₁

theorem same_residue_profiles_of_digits_descent (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (C : JointDigitDescentSources R N) :
    SameResidueProfiles R C.sources C.realization C.packet := by
  obtain ⟨hsmooth, ⟨K, hK, hk⟩, hsmoothing⟩ := smoothed_sheet_log_calculus R N C
  have hsheet := sheet_log_differentiation R N C
  have habs := absolute_sheet_jet_power_bounds R N C
  refine ⟨hsmooth, ?_, SArithmeticData.V_finite R.A, ?_, ?_, hsmoothing⟩
  · intro B hB j hj
    have hp : ∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∃ k : ℝ, 0 ≤ k ∧
        ∀ (i : R.A.UnitQuotient × R.A.V) u,
          ‖iteratedDeriv j (logProfile (C.realization.H C.packet i.1 i.2)) u‖ ≤
            k * Real.exp (-σ * u) := fun σ hσ =>
      ⟨K σ j, hK σ hσ j hj, fun i u => hk σ hσ j hj i.1 i.2 u⟩
    obtain ⟨k, hk0, hbound⟩ := min_rpow_bound_of_exp_power_bounds _ hp B hB
    exact ⟨k, hk0, fun v κ x hx => hbound (v, κ) x hx⟩
  · intro v κ j hj x hx
    exact (hsheet.2 v κ j hj (Real.log x)).1
  · intro B hB j hj
    letI : MeasurableSpace R.A.G1 := borel _
    have hp : ∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∃ k : ℝ, 0 ≤ k ∧
        ∀ (i : R.A.UnitQuotient × R.A.V) u,
          (∫ y : R.A.G1, ‖iteratedDeriv j
            (fun t => radialSheetIntegrand R C i.1 i.2 t y) u‖ ∂ R.probe.domain.measure) ≤
            k * Real.exp (-σ * u) := by
      intro σ hσ
      obtain ⟨k, hk0, hb⟩ := habs σ hσ
      exact ⟨k, hk0, fun i u => hb i.1 i.2 j hj u⟩
    obtain ⟨k, hk0, hbound⟩ := min_rpow_bound_of_exp_power_bounds _ hp B hB
    exact ⟨k, hk0, fun v κ x hx => hbound (v, κ) x hx⟩

theorem same_residue_profiles (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointDigitDescentSources R N)) : Nonempty (JointSameResidueProfileSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointDigitDescentSources := C, profiles := same_residue_profiles_of_digits_descent R N C }⟩

end DedekindZetaZeroFree.ThetaExpansion

end
