module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.CutoffAndLevelIndependence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
open KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

variable (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)

structure NativeMassFamily where
  full : Measure (FullOmega F ζ hζ (nativeDatum F ζ hζ))
  finite : IsFiniteMeasure full
  positive : 0 < full Set.univ
  open_positive : full.IsOpenPosMeasure
  from_source : ∀ V Y, OffsetAdmissible F ζ hζ R P S V Y →
    full = fullShell F ζ hζ R P S V Y
  weighted_mass : ∀ V, full Set.univ = weightedBeta F ζ hζ R P S V Set.univ

theorem cusp_density_measurable :
    Measurable (fun ω : KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) =>
      ENNReal.ofReal (cuspOffset F ζ hζ R P S V ω.1).val) :=
  KPMsActualNativeWeightedShapeMeasure.cuspDensity_measurable
    (nativeAtlas F ζ hζ R P S V)
    (fun j => ENNReal.ofReal (cuspOffset F ζ hζ R P S V j).val)

theorem weightedBeta_finite : IsFiniteMeasure (weightedBeta F ζ hζ R P S V) := by
  let A := nativeAtlas F ζ hζ R P S V
  let D := nativeDisintegration F ζ hζ R P S V
  letI := D.finite_beta
  let c : NativeCusp F ζ hζ R P S V → ℝ≥0∞ :=
    fun j => ENNReal.ofReal (cuspOffset F ζ hζ R P S V j).val
  let M : ℝ≥0∞ := ∑ j, c j
  have hM : M < ⊤ := by
    exact ENNReal.sum_lt_top.mpr (fun j _ => ENNReal.ofReal_lt_top)
  have hb : (∫⁻ ω : KPMsFixedHaarDisintegration.Omega A, c ω.1 ∂D.beta) ≤
      M * D.beta Set.univ := by
    rw [← lintegral_const]
    apply lintegral_mono
    intro ω
    exact Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ ω.1)
  apply isFiniteMeasure_withDensity
  exact (lt_of_le_of_lt hb (ENNReal.mul_lt_top hM (measure_lt_top D.beta Set.univ))).ne

theorem weightedBeta_positive : 0 < weightedBeta F ζ hζ R P S V Set.univ := by
  apply bot_lt_iff_ne_bot.mpr
  intro hz
  have hz' : (nativeDisintegration F ζ hζ R P S V).beta
      ({ω | ENNReal.ofReal (cuspOffset F ζ hζ R P S V ω.1).val ≠ 0} ∩ Set.univ) = 0 :=
    (withDensity_apply_eq_zero (cusp_density_measurable F ζ hζ R P S V)).mp hz
  have he : {ω : KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V) |
      ENNReal.ofReal (cuspOffset F ζ hζ R P S V ω.1).val ≠ 0} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (cuspOffset F ζ hζ R P S V ω.1).property).ne'
  rw [he, Set.univ_inter] at hz'
  exact (nativeDisintegration F ζ hζ R P S V).positive_beta hz'

theorem exists_offset_admissible : ∃ Y : ℝ, 0 < Y ∧ OffsetAdmissible F ζ hζ R P S V Y := by
  let T := (nativeAtlas F ζ hζ R P S V).threshold
  let c : NativeCusp F ζ hζ R P S V → ℝ := fun j => (cuspOffset F ζ hζ R P S V j).val
  let Y : ℝ := 1 + ∑ j, c j * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * T)
  have hY : 0 < Y := by
    apply add_pos_of_pos_of_nonneg zero_lt_one
    exact Finset.sum_nonneg (fun j _ => (mul_pos (cuspOffset F ζ hζ R P S V j).property
      (Real.exp_pos _)).le)
  refine ⟨Y, hY, ?_⟩
  intro j
  have hc : 0 < c j := (cuspOffset F ζ hζ R P S V j).property
  refine ⟨div_pos hY hc, ?_⟩
  have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F
      (nativeFamily F ζ hζ R P).totallyComplex))
  have hj : c j * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * T) ≤ Y := by
    apply le_trans (Finset.single_le_sum (fun k _ => (mul_pos
      (cuspOffset F ζ hζ R P S V k).property (Real.exp_pos _)).le) (Finset.mem_univ j))
    dsimp only [Y]
    linarith
  change T ≤ Real.log (Y / c j) / (2 * (KPCuspLogShape.dimension F : ℝ))
  rw [le_div_iff₀ hd]
  have he : Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * T) ≤ Y / c j := by
    rwa [le_div_iff₀ hc, mul_comm]
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  linarith

theorem exists_native_offset_mass_family : Nonempty (NativeMassFamily F ζ hζ R P S) := by
  let V₀ : Level F ζ hζ := KPShift81CoherentLevel.compactBaseLevel F ζ hζ
  obtain ⟨Y₀, _, hY₀⟩ := exists_offset_admissible F ζ hζ R P S V₀
  let μ := fullShell F ζ hζ R P S V₀ Y₀
  have hsource : ∀ V Y, OffsetAdmissible F ζ hζ R P S V Y →
      μ = fullShell F ζ hζ R P S V Y := by
    intro V Y hY
    exact fullShell_cutoff_and_cofinal_independent F ζ hζ R P S V₀ V Y₀ Y hY₀ hY
  have hfinite : IsFiniteMeasure μ := by
    letI := weightedBeta_finite F ζ hζ R P S V₀
    refine ⟨?_⟩
    change fullShell F ζ hζ R P S V₀ Y₀ Set.univ < ⊤
    rw [fullShell_mass F ζ hζ R P S V₀ Y₀ hY₀]
    exact measure_lt_top _ _
  have hpositive : 0 < μ Set.univ := by
    change 0 < fullShell F ζ hζ R P S V₀ Y₀ Set.univ
    rw [fullShell_mass F ζ hζ R P S V₀ Y₀ hY₀]
    exact weightedBeta_positive F ζ hζ R P S V₀
  refine ⟨{
    full := μ
    finite := hfinite
    positive := hpositive
    open_positive := fullShell_support F ζ hζ R P S V₀ Y₀ hY₀
    from_source := hsource
    weighted_mass := ?_ }⟩
  intro V
  obtain ⟨Y, _, hY⟩ := exists_offset_admissible F ζ hζ R P S V
  rw [hsource V Y hY]
  exact fullShell_mass F ζ hζ R P S V Y hY

def fullProbability (M : NativeMassFamily F ζ hζ R P S) :
    Measure (FullOmega F ζ hζ (nativeDatum F ζ hζ)) :=
  (M.full Set.univ)⁻¹ • M.full

def finiteMarginal (M : NativeMassFamily F ζ hζ R P S) :
    Measure (Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)) :=
  Measure.map (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)) M.full

def finiteProbability (M : NativeMassFamily F ζ hζ R P S) :
    Measure (Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)) :=
  Measure.map (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V))
    (fullProbability F ζ hζ R P S M)

theorem finiteMarginal_mass (M : NativeMassFamily F ζ hζ R P S) :
    finiteMarginal F ζ hζ R P S V M Set.univ = M.full Set.univ := by
  rw [finiteMarginal, Measure.map_apply
    (KPMsActualAngularShellSource.fullToLevel_measurable _ _) MeasurableSet.univ,
    Set.preimage_univ]

theorem finiteMarginal_finite (M : NativeMassFamily F ζ hζ R P S) :
    IsFiniteMeasure (finiteMarginal F ζ hζ R P S V M) := by
  letI := M.finite
  exact Measure.isFiniteMeasure_map _ _

theorem finiteMarginal_positive (M : NativeMassFamily F ζ hζ R P S) :
    0 < finiteMarginal F ζ hζ R P S V M Set.univ := by
  rw [finiteMarginal_mass]
  exact M.positive

theorem finiteProbability_eq_normalized (M : NativeMassFamily F ζ hζ R P S) :
    finiteProbability F ζ hζ R P S V M =
      (M.full Set.univ)⁻¹ • finiteMarginal F ζ hζ R P S V M := by
  exact Measure.map_smul _
    (KPMsActualAngularShellSource.fullToLevel_measurable _ _).aemeasurable

theorem finiteProbability_probability (M : NativeMassFamily F ζ hζ R P S) :
    IsProbabilityMeasure (finiteProbability F ζ hζ R P S V M) := by
  rw [finiteProbability_eq_normalized, ← finiteMarginal_mass F ζ hζ R P S V M]
  letI := finiteMarginal_finite F ζ hζ R P S V M
  letI : NeZero (finiteMarginal F ζ hζ R P S V M) :=
    ⟨Measure.measure_univ_pos.mp (finiteMarginal_positive F ζ hζ R P S V M)⟩
  exact isProbabilityMeasureSMul

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
