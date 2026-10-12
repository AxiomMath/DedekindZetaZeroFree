module

public import DedekindZetaZeroFree.Eisenstein.Continuation.MeanZero.JetSections
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnds.ExponentialMass
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Cubic.ZeroModeProjectionContraction
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspGrowth.UniformExponentialBound

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberMeanZeroAdapter

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

variable (a : Cusps F ζ hζ C R P H U)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def jetScalar (k : ℕ) (s : ℂ) (p : KPCuspCharts.Coordinates F) : ℂ :=
  parameterScalar F ζ hζ C R P H U a ι f k s (KPCuspCharts.toArch F p)

def gradientSq (k : ℕ) (s : ℂ) (p : KPCuspCharts.Coordinates F) : ℝ :=
  let w := HyperbolicChart.differential (d F)
    (parameterScalar F ζ hζ C R P H U a ι f k s ∘ KPMeanZeroWeightedEnergy.archCoordinates (d F))
    (KPMeanZeroWeightedEnergy.realCoordinates (d F) (KPCuspCharts.toArch F p))
  ∑ i, ∑ j, ‖w i j‖ ^ 2

def energyDensity (k : ℕ) (s : ℂ) (A : ℝ) (p : KPCuspCharts.Coordinates F) : ℝ :=
  Real.exp (2 * A * p.2) *
    (‖jetScalar F ζ hζ C R P H U a ι f k s p‖ ^ 2 +
      gradientSq F ζ hζ C R P H U a ι f k s p)

def energy (k : ℕ) (s : ℂ) (A T : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in tail F T, ENNReal.ofReal (energyDensity F ζ hζ C R P H U a ι f k s A p)
    ∂endMeasure F ζ hζ C R P H U a

variable {T₀ : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T₀)
variable (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T₀)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

def correctionMeanZeroSheet (s : ℂ) (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) : ℂ :=
  KPContActualChamberOutgoingAdapter.correctionSheet F ζ hζ C R P H U a ι buffer f χ source
    s t x b ε - (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (KPContActualChamberOutgoingAdapter.zeroMode F ζ hζ C R P H U a ι buffer f χ source
        s t b).val (QuotientAddGroup.mk x)

structure Properties : Prop where
  fiber_probability : ∀ a, @IsProbabilityMeasure
    (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a) _
    (fiberMeasure F ζ hζ C R P H U a)

  fiber_integrable : ∀ a k s, s ∈ V → ∀ t b ε,
    Integrable (fun z : KernelTorus F ζ hζ C R P H U a =>
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out z) b ε)
      (fiberMeasure F ζ hζ C R P H U a)

  representative_independent : ∀ a k s, s ∈ V → ∀ t b ε,
    ∀ x y : KPCuspCharts.Horizontal F,
      (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = QuotientAddGroup.mk y →
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε =
        meanZeroJetSheet F ζ hζ C R P H U a ι f k s t y b ε

  mean_zero : ∀ a k s, s ∈ V → ∀ t b,
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => ∫ z : KernelTorus F ζ hζ C R P H U a,
        meanZeroJetSheet F ζ hζ C R P H U a ι f k s t (Quotient.out z) b ε
        ∂fiberMeasure F ζ hζ C R P H U a) = 0

  smooth : ∀ a k s, s ∈ V →
    ContDiffOn ℝ (⊤ : ℕ∞) (parameterScalar F ζ hζ C R P H U a ι f k s)
      {z | buffer.τ < KPCuspLogShape.meanHeight (d F) z}

  jet_formula : ∀ a k s, s ∈ V → ∀ t x b ε,
    iteratedDerivWithin k
      (fun w => meanZeroJetSheet F ζ hζ C R P H U a ι f 0 w t x b ε) V s =
        meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε
  coordinate_jet : ∀ a k s, s ∈ V → ∀ p,
    jetScalar F ζ hζ C R P H U a ι f k s p =
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s p.2 p.1.1 p.1.2 1

  sheets : ∀ a k s, s ∈ V → ∀ t x b ε,
    meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b 1

  above_collars : ∀ a k s, s ∈ V → ∀ t x b ε,
    buffer.τ < t → T₀ + 1 ≤ t →
    meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε =
      iteratedDerivWithin k
        (fun w => correctionMeanZeroSheet F ζ hζ C R P H U a ι f buffer χ source w t x b ε) V s

  weighted_tails : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∀ k : ℕ,
    ∀ A : ℝ, 0 ≤ A → ∃ T B : ℝ,
      0 ≤ T ∧ (H.atlas (level F ζ hζ C R P H U)).threshold < T ∧
      buffer.τ < T ∧ T₀ + 1 < T ∧ 0 ≤ B ∧
      (∀ a s, s ∈ K →
        IntegrableOn (energyDensity F ζ hζ C R P H U a ι f k s A) (tail F T)
          (endMeasure F ζ hζ C R P H U a) ∧
        energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B ∧
        (∫ p in tail F T, energyDensity F ζ hζ C R P H U a ι f k s A p
          ∂endMeasure F ζ hζ C R P H U a) ≤ B) ∧
      ∀ R' : ℝ, T ≤ R' → ∀ a s, s ∈ K →
        IntegrableOn (energyDensity F ζ hζ C R P H U a ι f k s 0) (tail F R')
          (endMeasure F ζ hζ C R P H U a) ∧
        energy F ζ hζ C R P H U a ι f k s 0 R' ≤ ENNReal.ofReal (B * Real.exp (-2 * A * R')) ∧
        (∫ p in tail F R', energyDensity F ζ hζ C R P H U a ι f k s 0 p
          ∂endMeasure F ζ hζ C R P H U a) ≤ B * Real.exp (-2 * A * R')

section Growth
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem cauchy_bound (W : Set ℂ) (hW : IsOpen W)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g W)
    (k : ℕ) (s : ℂ) (r C : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall s r ⊆ W)
    (hb : ∀ z ∈ Metric.sphere s r, ‖g z‖ ≤ C) :
    ‖iteratedDerivWithin k g W s‖ ≤ (k.factorial : ℝ) * C / r ^ k := by
  have hs : s ∈ W := hball (Metric.mem_closedBall_self hr.le)
  rw [iteratedDerivWithin_eq_iteratedDeriv hW.uniqueDiffOn
    (((hg.contDiffOn hW) s hs).contDiffAt (hW.mem_nhds hs)) hs]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr _ hb
  exact hg.diffContOnCl_ball hball
private theorem cuspSheet_holomorphic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U) (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    DifferentiableOn ℂ
      (fun s => KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε) V := by
  let g := KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t x b ε
  let A : Set (KPContActualChamberNormalSeries.G F ζ hζ) := {g}
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_singleton
  have hh := KPContActualChamberNormalSeries.compactMixedJet_holomorphic
    F ζ hζ U ι f hι hf 0 [] A isCompact_singleton
  have hd := (ContinuousMap.evalCLM ℂ (⟨g,Set.mem_singleton g⟩ : A)).differentiable.comp_differentiableOn hh
  apply hd.congr
  intro s hs
  simp [KPContActualChamberNormalSeries.compactMixedJet, hs,
    KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord,
    KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet, g]

theorem cuspJet_exponential_bound (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) :
    ∃ C₀ M : ℝ, 0 ≤ C₀ ∧ 0 ≤ M ∧
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K,
        ∀ xb : KPCuspCharts.Cross F, ∀ ε : rootsOfUnity 3 F, ∀ t : ℝ, 0 ≤ t →
          ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s
            t xb.1 xb.2 ε‖ ≤ C₀ * Real.exp (M*t) := by
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open KPChamberL2Defect.chamber_isOpen hKV
  obtain ⟨C₀, M, hC₀, hM, hb⟩ := KPContinuation.ChamberModerateGrowth.actualCuspSheet_global_exponential_bound
    F ζ hζ C R P H U ι hι f hf (Metric.cthickening r K) hK.cthickening hrV
  refine ⟨(k.factorial : ℝ) * C₀ / r^k, M,
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₀) (pow_nonneg hr.le _), hM, ?_⟩
  intro a s hs xb ε t ht
  have hball := (Metric.closedBall_subset_cthickening hs r).trans hrV
  have hh := cauchy_bound V KPChamberL2Defect.chamber_isOpen
    (fun z => KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 z t xb.1 xb.2 ε)
    (cuspSheet_holomorphic F ζ hζ C R P H U ι f hι hf a t xb.1 xb.2 ε)
    k s r (C₀ * Real.exp (M*t)) hr hball (fun z hz =>
      hb a z (Metric.closedBall_subset_cthickening hs r (Metric.sphere_subset_closedBall hz)) xb ε t ht)
  rw [KPContActualChamberCasimirJets.cusp_restriction_commute
    F ζ hζ C R P H U ι f hι hf a k s (hKV hs)] at hh
  convert hh using 1 <;> ring

theorem meanZeroJet_exponential_bound (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) :
    ∃ C₀ M : ℝ, 0 ≤ C₀ ∧ 0 ≤ M ∧
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K,
        ∀ xb : KPCuspCharts.Cross F, ∀ ε : rootsOfUnity 3 F, ∀ t : ℝ, 0 ≤ t →
          ‖meanZeroJetSheet F ζ hζ C R P H U a ι f k s
            t xb.1 xb.2 ε‖ ≤ C₀ * Real.exp (M*t) := by
  obtain ⟨C₀, M, hC₀, hM, hb⟩ := cuspJet_exponential_bound
    F ζ hζ C R P H U ι f hι hf K hK hKV k
  refine ⟨2*C₀, M, mul_nonneg (by norm_num) hC₀, hM, ?_⟩
  intro a s hs xb ε t ht
  let μ := KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  have hi : ∀ η : rootsOfUnity 3 F, ‖∫ z : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t
        (Quotient.out z) xb.2 η ∂μ‖ ≤ C₀ * Real.exp (M*t) := by
    intro η
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun z : KernelTorus F ζ hζ C R P H U a =>
        hb a s hs ((Quotient.out z),xb.2) η t ht))
    letI : IsProbabilityMeasure μ := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
    simpa [Measure.real] using hh
  have hp := KPContinuation.ChamberModerateGrowth.zeroProjection_norm_le F ζ hζ C R P H U a _ (C₀ * Real.exp (M*t))
    (mul_nonneg hC₀ (Real.exp_nonneg _)) hi (QuotientAddGroup.mk xb.1)
  change ‖(KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a μ k s t xb.2).val
    (QuotientAddGroup.mk xb.1)‖ ≤ C₀ * Real.exp (M*t) at hp
  unfold KPContActualChamberMeanZeroAdapter.meanZeroJetSheet
  calc
    _ ≤ ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t xb.1 xb.2 ε‖ +
        ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
          (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a μ k s t xb.2).val
            (QuotientAddGroup.mk xb.1)‖ := norm_sub_le _ _
    _ ≤ (C₀ * Real.exp (M*t)) + (C₀ * Real.exp (M*t)) := by
      rw [norm_mul, KPContSectorCoveredQuotientVocabulary.chi_norm, one_mul]
      exact add_le_add (hb a s hs xb ε t ht) hp
    _ = _ := by ring

theorem meanZeroJet_negative_weighted_mass (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ) :
    ∃ b₀ B : ℝ, b₀ < 0 ∧ 0 ≤ B ∧
      ∀ a : Cusps F ζ hζ C R P H U, ∀ s ∈ K, ∀ ε : rootsOfUnity 3 F,
        (∫⁻ p in {p : KPCuspCharts.Coordinates F | 0 < p.2},
          ENNReal.ofReal (Real.exp (2*b₀*p.2) *
            ‖meanZeroJetSheet F ζ hζ C R P H U a ι f k s p.2 p.1.1 p.1.2 ε‖ ^ 2)
          ∂endMeasure F ζ hζ C R P H U a) ≤ ENNReal.ofReal B := by
  obtain ⟨C₀, M, hC₀, hM, hb⟩ := meanZeroJet_exponential_bound
    F ζ hζ C R P H U ι f hι hf K hK hKV k
  let b₀ := -M-1
  let I := fun a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U =>
    ∫⁻ p in {p : KPCuspCharts.Coordinates F | 0 < p.2}, ENNReal.ofReal (Real.exp (-2*p.2))
      ∂KPContActualChamberMeanZeroAdapter.endMeasure F ζ hζ C R P H U a
  have hI : ∀ a, I a < (∞ : ℝ≥0∞) := by
    intro a
    exact KPContinuation.ChamberModerateGrowth.end_exponential_mass_finite F ζ hζ C R P H U a (-2)
      (by have hd : 0 ≤ (KPCuspLogShape.dimension F : ℝ) := Nat.cast_nonneg _; linarith) 0
  let A : ℝ≥0∞ := ENNReal.ofReal (C₀^2) * ∑ a, I a
  have hA : A < (∞ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.sum_lt_top.mpr (fun a _ => hI a))
  refine ⟨b₀, A.toReal, by dsimp [b₀]; linarith, ENNReal.toReal_nonneg, ?_⟩
  intro a s hs ε
  rw [ENNReal.ofReal_toReal hA.ne]
  have hbound : ∀ p : KPCuspCharts.Coordinates F, 0 < p.2 →
      Real.exp (2*b₀*p.2) *
        ‖KPContActualChamberMeanZeroAdapter.meanZeroJetSheet F ζ hζ C R P H U a ι f k s
          p.2 p.1.1 p.1.2 ε‖ ^ 2 ≤ C₀^2 * Real.exp (-2*p.2) := by
    intro p hp
    have hh := hb a s hs p.1 ε p.2 hp.le
    have hsq := mul_self_le_mul_self (norm_nonneg _) hh
    have he : Real.exp (2*b₀*p.2) * (C₀ * Real.exp (M*p.2)) ^ 2 =
        C₀^2 * Real.exp (-2*p.2) := by
      rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp _) (C₀^2), mul_assoc,
        ← Real.exp_add]
      congr 2
      dsimp [b₀]
      ring
    exact (mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hsq) (Real.exp_nonneg _)).trans_eq he
  calc
    _ ≤ ∫⁻ p in {p : KPCuspCharts.Coordinates F | 0 < p.2},
        ENNReal.ofReal (C₀^2) * ENNReal.ofReal (Real.exp (-2*p.2))
        ∂KPContActualChamberMeanZeroAdapter.endMeasure F ζ hζ C R P H U a := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurable_snd measurableSet_Ioi)] with p hp
      rw [← ENNReal.ofReal_mul (sq_nonneg C₀)]
      exact ENNReal.ofReal_le_ofReal (hbound p hp)
    _ = ENNReal.ofReal (C₀^2) * I a := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ A := mul_le_mul_right (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)) _

end Growth

section Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
private theorem integral_extension {B T : Type*}
    [TopologicalSpace B] [CompactSpace B] [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ]
    (π : C(B,T)) (hπ : Function.Surjective π) :
    ∃ I : C(B,ℂ) →L[ℂ] ℂ, ∀ u : C(T,ℂ), I (u.comp π) = ∫ q, u q ∂μ := by
  let J : C(T,ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun u => ∫ q, u q ∂μ
      map_add' := fun u v => integral_add
        (u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (v.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c u => integral_smul c u }
    1 (by
      intro u
      simpa using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (u.norm_coe_le_norm)))
  let j : C(T,ℂ) →ₗᵢ[ℂ] C(B,ℂ) :=
    { toLinearMap := (ContinuousMap.compCLM ℂ ℂ π).toLinearMap
      norm_map' := by
        intro u
        apply le_antisymm
        · exact (ContinuousMap.norm_le _ (norm_nonneg u)).mpr (fun x => u.norm_coe_le_norm (π x))
        · exact (ContinuousMap.norm_le _ (norm_nonneg (u.comp π))).mpr (fun q => by
            obtain ⟨x, rfl⟩ := hπ q
            exact (u.comp π).norm_coe_le_norm x) }
  obtain ⟨I,hI,_⟩ := exists_extension_norm_eq j.toLinearMap.range
    (J.comp j.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨I, fun u => ?_⟩
  have h := hI (j.equivRange u)
  have hi : (j.equivRange u).val = u.comp π := by
    rw [LinearIsometry.equivRange_apply_coe]; rfl
  have hj : (J.comp j.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap) (j.equivRange u) = J u := by
    change J (j.equivRange.symm (j.equivRange u)) = J u
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hi, hj] at h
  exact h

private theorem kernel_integral_holomorphic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    DifferentiableOn ℂ (fun s => ∫ z : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out z) b ε)
      ∂fiberMeasure F ζ hζ C R P H U a) V := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  obtain ⟨B,hB,hrep⟩ := KPContinuation.ChamberModerateGrowth.compact_kernel_representatives F ζ hζ C R P H U a
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let π : C(B,KernelTorus F ζ hζ C R P H U a) :=
    ⟨fun x => QuotientAddGroup.mk x.val, QuotientAddGroup.continuous_mk.comp continuous_subtype_val⟩
  have hπ : Function.Surjective π := fun q => by
    obtain ⟨x,hx,he⟩ := hrep q
    exact ⟨⟨x,hx⟩,he⟩
  obtain ⟨I,hI⟩ := integral_extension (fiberMeasure F ζ hζ C R P H U a) π hπ
  let c : KPCuspCharts.Horizontal F → KPContActualChamberNormalSeries.G F ζ hζ :=
    fun x => KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t x b ε
  have hc : Continuous c := by
    have harch : Continuous (fun x : KPCuspCharts.Horizontal F => KPCuspCharts.toArch F ((x,b),t)) :=
      (KPCuspCharts.toArch_contDiff F).continuous.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    have hsec := (KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp harch
    have hins := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp hsec
    exact continuous_const.mul (hins.mul continuous_const)
  let A := c '' B
  have hA : IsCompact A := hB.image hc
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let cB : C(B,A) := ⟨fun x => ⟨c x.val, ⟨x.val,x.property,rfl⟩⟩,
    (hc.comp continuous_subtype_val).subtype_mk _⟩
  let g : ℂ → C(B,ℂ) := fun s =>
    (KPContActualChamberNormalSeries.compactMixedJet F ζ hζ U ι f hι hf 0 [] A s).comp cB
  have hg : DifferentiableOn ℂ g V :=
    (ContinuousMap.compCLM ℂ ℂ cB).differentiable.comp_differentiableOn
      (KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 [] A hA)
  apply (I.differentiable.comp_differentiableOn hg).congr
  intro s hs
  let u : C(KernelTorus F ζ hζ C R P H U a,ℂ) :=
    ⟨fun q => KPContActualChamberNormalSeries.E F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out q) b ε), by
      simpa only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
        iteratedDerivWithin_zero] using
        KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_continuous F ζ hζ C R P H U ι hι f hf a s hs t b ε⟩
  have he : g s = u.comp π := by
    ext x
    have hp := KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative F ζ hζ C R P H U
      ι hι f hf a s hs t x.val (Quotient.out (π x)) b ε (Quotient.out_eq (π x)).symm
    simpa [g, KPContActualChamberNormalSeries.compactMixedJet, hs, cB, c,
      KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord,
      KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet, u] using hp
  change (∫ z, u z ∂fiberMeasure F ζ hζ C R P H U a) = I (g s)
  rw [he]
  exact (hI u).symm

include hι hf in
private theorem projection_holomorphic (t : ℝ) (b : KPCuspCharts.Shape F)
    (q : KernelTorus F ζ hζ C R P H U a) :
    DifferentiableOn ℂ (fun z => (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U
      ι f a (fiberMeasure F ζ hζ C R P H U a) 0 z t b).val q) V := by
  letI := Fintype.ofFinite (rootsOfUnity 3 F)
  let J : (rootsOfUnity 3 F → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun e => (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a e).val q
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have he : DifferentiableOn ℂ (fun z ε => ∫ q : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberNormalSeries.E F ζ hζ U ι f z
        (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t (Quotient.out q) b ε)
      ∂fiberMeasure F ζ hζ C R P H U a) V :=
    differentiableOn_pi.mpr (fun ε => kernel_integral_holomorphic F ζ hζ C R P H U a ι f hι hf t b ε)
  exact J.toContinuousLinearMap.differentiable.comp_differentiableOn he

include hι hf in
private theorem sheet_holomorphic (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    DifferentiableOn ℂ (fun z => KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U
      ι f a 0 z t x b ε) V := by
  let g := KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t x b ε
  let A : Set (KPContActualChamberNormalSeries.G F ζ hζ) := {g}
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_singleton
  have hg := KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 [] A isCompact_singleton
  exact ((ContinuousMap.evalCLM ℂ (⟨g,Set.mem_singleton g⟩ : A)).differentiable.comp_differentiableOn hg).congr
    (fun z hz => by simp [KPContActualChamberNormalSeries.compactMixedJet,hz,
      KPContActualChamberNormalSeries.mixedJet,KPContActualChamberNormalSeries.rightWord,
      KPContActualChamberCasimirJets.cuspSheet,KPContActualChamberCasimirJets.jet,g])

include hι hf in
private theorem complement_jet (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    iteratedDerivWithin k (fun z => meanZeroJetSheet F ζ hζ C R P H U a ι f 0 z t x b ε) V s =
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε := by
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  unfold meanZeroJetSheet
  change iteratedDerivWithin k
    ((fun z => KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 z t x b ε) -
      (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
          (fiberMeasure F ζ hζ C R P H U a) 0 z t b).val (QuotientAddGroup.mk x))) V s = _
  rw [iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (((sheet_holomorphic F ζ hζ C R P H U a ι f hι hf t x b ε).contDiffOn KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)
    ((((projection_holomorphic F ζ hζ C R P H U a ι f hι hf t b (QuotientAddGroup.mk x)).const_mul _).contDiffOn
      KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs),iteratedDerivWithin_const_mul_field,
    KPContActualChamberCasimirJets.cusp_projection_commute F ζ hζ C R P H U ι f hι hf,
    KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf] <;> exact hs

include hι hf in
private theorem parameterScalar_coordinates (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (p : KPCuspCharts.Coordinates F) :
    parameterScalar F ζ hζ C R P H U a ι f k s (KPCuspCharts.toArch F p) =
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s p.2 p.1.1 p.1.2 1 := by
  unfold parameterScalar meanZero
  have he := (KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension).symm_apply_apply p
  change (KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension).symm
    (KPCuspCharts.toArch F p) = p at he
  rw [he]
  exact complement_jet F ζ hζ C R P H U a ι f hι hf k s hs p.2 p.1.1 p.1.2 1

include hι hf in
private theorem representative_law (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) (x y : KPCuspCharts.Horizontal F)
    (hxy : (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = QuotientAddGroup.mk y) :
    meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε =
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s t y b ε := by
  unfold meanZeroJetSheet
  rw [hxy]
  apply congrArg (fun c : ℂ => c - _)
  rw [← KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs,
    ← KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs]
  exact iteratedDerivWithin_congr (fun w hw =>
    KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative
      F ζ hζ C R P H U ι hι f hf a w hw t x y b ε hxy) hs

include hι hf in
private theorem sheet_law (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b ε =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s t x b 1 := by
  have he : KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t x b ε =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t x b 1 := by
    rw [← KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs,
      ← KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs,
      ← iteratedDerivWithin_const_mul_field]
    exact iteratedDerivWithin_congr (fun w hw =>
      KPGlobalResidualConstruction.ActualMeanZeroSection.actualCuspSheet_sheet_identity
        F ζ hζ C R P H U a ι hι f hf w hw t b x ε) hs
  unfold meanZeroJetSheet
  rw [he]
  simp only [map_one, Units.val_one, one_mul]
  exact (mul_sub _ _ _).symm

include hι hf in
private theorem projected_complement_zero (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (t : ℝ) (b : KPCuspCharts.Shape F) :
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => ∫ q : KernelTorus F ζ hζ C R P H U a,
        meanZeroJetSheet F ζ hζ C R P H U a ι f k s t (Quotient.out q) b ε
        ∂fiberMeasure F ζ hζ C R P H U a) = 0 := by
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  let v := KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
    (fiberMeasure F ζ hζ C R P H U a) k s t b
  have he : (fun ε => ∫ q : KernelTorus F ζ hζ C R P H U a,
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s t (Quotient.out q) b ε
      ∂fiberMeasure F ζ hζ C R P H U a) =
      (fun ε => ∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b ε
        ∂fiberMeasure F ζ hζ C R P H U a) -
      (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * v.val 0) := by
    funext ε
    unfold meanZeroJetSheet
    simp_rw [(KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
      (fiberMeasure F ζ hζ C R P H U a) k s t b).property.2]
    rw [integral_sub (KPContActualChamberCasimirJets.cusp_fiber_integrable
      F ζ hζ C R P H U ι f hι hf a (fiberMeasure F ζ hζ C R P H U a) k s hs t b ε)
      (integrable_const _), integral_const]
    simp only [Pi.sub_apply, probReal_univ, one_smul]
    rfl
  rw [he, map_sub, KPContActualChamberOutgoingAdapter.zeroProjection_reconstruct]
  exact sub_self v

include hι hf in
private theorem correction_complement_eq (s : ℂ) (hs : s ∈ V) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F)
    (ht : buffer.τ < t) :
    correctionMeanZeroSheet F ζ hζ C R P H U a ι f buffer χ source s t x b ε =
      meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s t x b ε := by
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < s.re
    change (1 : ℝ)/3 < s.re at hs
    linarith
  let W := ((χ a).toFun t : ℂ) •
    (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s (f s) t b)
  have hcut (y : KPCuspCharts.Horizontal F) (δ : rootsOfUnity 3 F) :
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff s)
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a δ ((y,b),t)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * W.val 0 := by
    rw [KPContActualCutoffSmoothDescent.scalar_coveredPoint,
      source.descent.cutoff_frame s hsΩ a ((y,b),t) ht]
    simp only [KPContActualCutoffSmoothDescent.incomingValue]
    change (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * (((χ a).toFun t : ℂ) * _) = _
    rw [(KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s (f s) t b).property.2 (QuotientAddGroup.mk y)]
    change _ = (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * (((χ a).toFun t : ℂ) * _)
    ring
  have hmode : KPContActualChamberOutgoingAdapter.zeroMode F ζ hζ C R P H U a ι buffer f χ source s t b =
      KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
        (fiberMeasure F ζ hζ C R P H U a) 0 s t b - W := by
    letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
    letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
    unfold KPContActualChamberOutgoingAdapter.zeroMode
    have he : (fun δ => ∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberOutgoingAdapter.correctionSheet F ζ hζ C R P H U a ι buffer f χ source
          s t (Quotient.out q) b δ ∂fiberMeasure F ζ hζ C R P H U a) =
      (fun δ => ∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out q) b δ
          ∂fiberMeasure F ζ hζ C R P H U a) -
      (fun δ => (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * W.val 0) := by
      funext δ
      unfold KPContActualChamberOutgoingAdapter.correctionSheet
      simp_rw [hcut]
      change (∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out q) b δ -
        (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * W.val 0 ∂fiberMeasure F ζ hζ C R P H U a) = _
      rw [integral_sub
        (KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_integrable F ζ hζ C R P H U ι hι f hf a s hs t b δ)
        (integrable_const _), integral_const]
      simp only [Pi.sub_apply, probReal_univ, one_smul]
    rw [he, map_sub, KPContActualChamberOutgoingAdapter.zeroProjection_reconstruct]
    rfl
  unfold correctionMeanZeroSheet KPContActualChamberOutgoingAdapter.correctionSheet meanZeroJetSheet
  rw [hcut, hmode]
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [W.property.2 (QuotientAddGroup.mk x)]
  change _ = _ - _
  simp only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet, iteratedDerivWithin_zero]
  ring

end Algebra
section Bootstrap
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
variable (E : KPMeanZeroWeightedEnergy.End F ζ hζ hF U)

 def restrictSection (v : KPMeanZeroWeightedEnergy.Section E 0) (T : ℝ) (hT : 0 ≤ T) :
    KPMeanZeroWeightedEnergy.Section E T where
  val := v.val
  smooth := v.smooth.mono (fun x hx => lt_of_le_of_lt hT hx)
  fiber := fun x hx => v.fiber x (lt_of_le_of_lt hT hx)
  equivariant := fun h x hx => v.equivariant h x (lt_of_le_of_lt hT hx)

 def forcingSection {T : ℝ} (v : ℕ → KPMeanZeroWeightedEnergy.Section E T)
    (c : ℕ → ℂ) (k : ℕ) : KPMeanZeroWeightedEnergy.Section E T where
  val := fun z => ∑ j ∈ Finset.Icc 1 (min k 2), c j * (v (k-j)).val z
  smooth := ContDiffOn.sum (fun j _ => contDiffOn_const.mul (v (k-j)).smooth)
  fiber := fun z hz => Submodule.sum_mem _ (fun j _ =>
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).smul_mem (c j) ((v (k-j)).fiber z hz))
  equivariant := by
    intro h z hz
    simp_rw [(v _).equivariant h z hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private theorem forcingMass_le_energy {T : ℝ} (v : KPMeanZeroWeightedEnergy.Section E T) (A R : ℝ) :
    KPMeanZeroWeightedEnergy.forcingMass E v A R ≤ KPMeanZeroWeightedEnergy.energy E v A R := by
  apply lintegral_mono
  intro p
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (v.gradientSq_nonneg E p)) (Real.exp_nonneg _)

private theorem forcing_bound {T : ℝ} (v : ℕ → KPMeanZeroWeightedEnergy.Section E T)
    (c : ℕ → ℂ) (k : ℕ) (C A R : ℝ) (hTR : T ≤ R) (hC : 0 ≤ C)
    (hc : ∀ j ∈ Finset.Icc 1 (min k 2), ‖c j‖ ≤ C) :
    KPMeanZeroWeightedEnergy.forcingMass E (forcingSection E v c k) A R ≤
      ENNReal.ofReal ((Finset.Icc 1 (min k 2)).card * C^2) *
        ∑ j ∈ Finset.Icc 1 (min k 2), KPMeanZeroWeightedEnergy.energy E (v (k-j)) A R := by
  let J := Finset.Icc 1 (min k 2)
  have hp (p : KPCuspCharts.Coordinates F) :
      ‖∑ j ∈ J, c j * (v (k-j)).scalar p‖^2 ≤
        (J.card : ℝ) * C^2 * ∑ j ∈ J, ‖(v (k-j)).scalar p‖^2 := by
    calc
      _ ≤ (∑ j ∈ J, ‖c j * (v (k-j)).scalar p‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      _ ≤ (J.card : ℝ) * ∑ j ∈ J, ‖c j * (v (k-j)).scalar p‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (J.card : ℝ) * ∑ j ∈ J, C^2 * ‖(v (k-j)).scalar p‖^2 := by
        gcongr with j hj
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j hj) _) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  calc
    _ ≤ ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
        ENNReal.ofReal ((J.card : ℝ) * C^2) *
          ∑ j ∈ J, ENNReal.ofReal (Real.exp (2*A*p.2) * ‖(v (k-j)).scalar p‖^2) ∂E.measure := by
      apply lintegral_mono
      intro p
      dsimp only
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      change Real.exp (2*A*p.2) * ‖∑ j ∈ J, c j * (v (k-j)).scalar p‖^2 ≤ _
      have hh := mul_le_mul_of_nonneg_left (hp p) (Real.exp_nonneg (2*A*p.2))
      convert hh using 1 <;> rw [← Finset.mul_sum] <;> ring
    _ ≤ ENNReal.ofReal ((J.card : ℝ) * C^2) *
        ∑ j ∈ J, KPMeanZeroWeightedEnergy.forcingMass E (v (k-j)) A R := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      apply le_of_eq
      apply lintegral_finsetSum'
      intro j hj
      apply AEMeasurable.ennreal_ofReal
      apply AEMeasurable.mul (by fun_prop)
      apply AEMeasurable.pow_const
      apply AEMeasurable.norm
      apply ContinuousOn.aemeasurable _ (measurableSet_Ioi.preimage measurable_snd)
      have ht : ∀ p : KPCuspCharts.Coordinates F, R < p.2 →
          KPCuspCharts.toArch F p ∈ {x | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x} := by
        intro p hp
        change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)
        rw [KPCuspCharts.toArch_meanHeight F E.geometry.positive_dimension]
        exact lt_of_le_of_lt hTR hp
      exact (v (k-j)).smooth.continuousOn.comp (KPCuspCharts.toArch_contDiff F).continuous.continuousOn ht
    _ ≤ _ := by gcongr with j hj; exact forcingMass_le_energy E (v (k-j)) A R

private theorem all_jets_energy {I : Type*}
    (D : KPMeanZeroWeightedEnergy.AnalyticAdapter E)
    (v : ℕ → I → KPMeanZeroWeightedEnergy.Section E 0)
    (z : I → ℂ) (c : ℕ → I → ℕ → ℂ)
    (Z : ℝ) (hZ : 0 ≤ Z) (hz : ∀ i, ‖z i‖ ≤ Z)
    (hv0 : ∀ k i, KPMeanZeroWeightedEnergy.MeanZero E D.fiberMeasure (v k i))
    (heq : ∀ k i p, 0 < p.2 → (v k i).laplacian p = z i * (v k i).scalar p +
      ∑ j ∈ Finset.Icc 1 (min k 2), c k i j * (v (k-j) i).scalar p)
    (hseed : ∀ k, ∃ b B : ℝ, 0 ≤ B ∧ ∀ i,
      KPMeanZeroWeightedEnergy.forcingMass E (v k i) b 0 ≤ ENNReal.ofReal B)
    (hc : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i j, j ∈ Finset.Icc 1 (min k 2) → ‖c k i j‖ ≤ C) :
    ∀ k : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ R : ℝ, 0 < R →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ i, KPMeanZeroWeightedEnergy.energy E (v k i) A R ≤ ENNReal.ofReal B := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA R hR
    let T := R/2
    have hT : 0 < T := half_pos hR
    have hTR : T < R := half_lt_self hR
    let w (n : ℕ) (i : I) := restrictSection E (v n i) T hT.le
    let g (i : I) := forcingSection E (fun n => w n i) (c k i) k
    obtain ⟨b,V,hV,hmass⟩ := hseed k
    have hseed' : ∀ S : ℝ, T < S → ∃ V : ℝ, 0 ≤ V ∧ ∀ i,
        KPMeanZeroWeightedEnergy.forcingMass E (w k i) b S ≤ ENNReal.ofReal V := by
      intro S hS
      refine ⟨V,hV,fun i => le_trans ?_ (hmass i)⟩
      apply lintegral_mono_set
      exact fun p hp => lt_trans hT (lt_trans hS hp)
    have hforcing : ∀ a : ℝ, 0 ≤ a → ∃ G : ℝ, 0 ≤ G ∧ ∀ i,
        KPMeanZeroWeightedEnergy.forcingMass E (g i) a T ≤ ENNReal.ofReal G := by
      intro a ha
      let J := Finset.Icc 1 (min k 2)
      have hex : ∀ j ∈ J, ∃ B : ℝ, 0 ≤ B ∧ ∀ i,
          KPMeanZeroWeightedEnergy.energy E (v (k-j) i) a T ≤ ENNReal.ofReal B := by
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjk : j ≤ k := le_trans (Finset.mem_Icc.mp hj).2 (min_le_left _ _)
        exact ih (k-j) (by omega) a ha T hT
      choose B hB hb using hex
      obtain ⟨C,hC,hc'⟩ := hc k
      let Bs := ∑ j : J, B j.val j.property
      have hBs : 0 ≤ Bs := Finset.sum_nonneg (fun j _ => hB j.val j.property)
      refine ⟨(J.card : ℝ)*C^2*Bs, by positivity, ?_⟩
      intro i
      have hf := forcing_bound E (fun n => w n i) (c k i) k C a T le_rfl hC (hc' i)
      apply hf.trans
      have hsum : (∑ j ∈ J, KPMeanZeroWeightedEnergy.energy E (w (k-j) i) a T) ≤ ENNReal.ofReal Bs := by
        rw [← Finset.sum_coe_sort J (fun j => KPMeanZeroWeightedEnergy.energy E (w (k-j) i) a T)]
        calc
          _ ≤ ∑ j : J, ENNReal.ofReal (B j.val j.property) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hb j.val j.property i
          _ = ENNReal.ofReal Bs := (ENNReal.ofReal_sum_of_nonneg (fun j _ => hB j.val j.property)).symm
      have hh := mul_le_mul_right hsum (ENNReal.ofReal ((J.card : ℝ)*C^2))
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (J.card : ℝ)*C^2)] using hh
    obtain ⟨B,hB,hbound,_⟩ := KPMeanZeroWeightedEnergy.weighted_energy_from_mass_seed E D
      (w k) g z Z b hZ hz (fun i b t => hv0 k i b ⟨t.val, lt_trans hT t.property⟩)
      (fun i p hp => by
        have hh := heq k i p (lt_trans hT hp)
        change (v k i).laplacian p - z i * (v k i).scalar p = _
        rw [hh, add_sub_cancel_left]
        rfl) hseed' hforcing A hA R hTR
    exact ⟨B,hB,hbound⟩

end Bootstrap

section Application
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)

include hι hf in
private theorem parameterScalar_global_smooth (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ContDiff ℝ (⊤ : ℕ∞) (parameterScalar F ζ hζ C R P H U a ι f k s) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨v,hv,_,_⟩ := actual_meanZero_jet_sections F ζ hζ C R P H U ι f hι hf a s hs
    (KPCuspLogShape.meanHeight (d F) z - 1)
  rw [← hv k]
  exact ((v k).smooth.contDiffAt (IsOpen.mem_nhds (isOpen_lt continuous_const (by unfold KPCuspLogShape.meanHeight; fun_prop)) (by dsimp; linarith)))

private theorem energyDensity_nonneg (k : ℕ) (s : ℂ) (A : ℝ) (p : KPCuspCharts.Coordinates F) :
    0 ≤ energyDensity F ζ hζ C R P H U a ι f k s A p := by
  unfold energyDensity gradientSq
  positivity

include hι hf in
private theorem energyDensity_continuous (k : ℕ) (s : ℂ) (hs : s ∈ V) (A : ℝ) :
    Continuous (energyDensity F ζ hζ C R P H U a ι f k s A) := by
  have hh := parameterScalar_global_smooth F ζ hζ C R P H U a ι f hι hf k s hs
  let L : HyperbolicChart.Space (d F) →L[ℝ] KPArch.Space (d F) :=
    LinearMap.toContinuousLinearMap {
      toFun := KPMeanZeroWeightedEnergy.archCoordinates (d F)
      map_add' := by intro x y; ext i <;> simp [KPMeanZeroWeightedEnergy.archCoordinates]; rfl
      map_smul' := by
        intro c x
        ext i : 1
        apply Prod.ext <;> simp [KPMeanZeroWeightedEnergy.archCoordinates, Complex.real_smul]
        apply Complex.ext <;> simp }
  have hac : ContDiff ℝ (⊤ : ℕ∞) (KPMeanZeroWeightedEnergy.archCoordinates (d F)) := L.contDiff
  have hreal : Continuous (KPMeanZeroWeightedEnergy.realCoordinates (d F)) := by
    unfold KPMeanZeroWeightedEnergy.realCoordinates
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (d F) × Fin 3 => ℝ)).comp
    apply continuous_pi
    intro j
    rcases j with ⟨i,j⟩
    fin_cases j <;> fun_prop
  let g := parameterScalar F ζ hζ C R P H U a ι f k s ∘ KPMeanZeroWeightedEnergy.archCoordinates (d F)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hh.comp hac
  have hfd : Continuous (fderiv ℝ g) := (hg.fderiv_right (m := 1) (by simp)).continuous
  have hcoord (i : Fin (d F)) (j : Fin 3) :
      Continuous (fun p => fderiv ℝ g p (HyperbolicChart.coordinateVector (d F) i j)) :=
    hfd.clm_apply continuous_const
  have hd : Continuous (HyperbolicChart.differential (d F) g) := by
    unfold HyperbolicChart.differential
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases j
    · simpa [HyperbolicChart.coordinateDerivative] using hcoord i 2
    · change Continuous (fun p : HyperbolicChart.Space (d F) => (Real.exp (p (i,2)) : ℂ) *
        fderiv ℝ g p (HyperbolicChart.coordinateVector (d F) i 0))
      exact
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop : Continuous (fun p : HyperbolicChart.Space (d F) => p (i,2))))).mul (hcoord i 0)
    · change Continuous (fun p : HyperbolicChart.Space (d F) => (Real.exp (p (i,2)) : ℂ) *
        fderiv ℝ g p (HyperbolicChart.coordinateVector (d F) i 1))
      exact
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop : Continuous (fun p : HyperbolicChart.Space (d F) => p (i,2))))).mul (hcoord i 1)
  unfold energyDensity jetScalar gradientSq
  apply Continuous.mul (by fun_prop)
  apply Continuous.add ((hh.continuous.comp (KPCuspCharts.toArch_contDiff F).continuous).norm.pow 2)
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  exact ((((continuous_apply j).comp ((continuous_apply i).comp hd)).comp
    (hreal.comp (KPCuspCharts.toArch_contDiff F).continuous)).norm.pow 2)

private theorem energy_integrable_of_bound (k : ℕ) (s : ℂ) (A T B : ℝ)
    (hB : 0 ≤ B) (hcont : Continuous (energyDensity F ζ hζ C R P H U a ι f k s A))
    (hb : energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B) :
    IntegrableOn (energyDensity F ζ hζ C R P H U a ι f k s A) (tail F T)
      (endMeasure F ζ hζ C R P H U a) ∧
      (∫ p in tail F T, energyDensity F ζ hζ C R P H U a ι f k s A p
        ∂endMeasure F ζ hζ C R P H U a) ≤ B := by
  have hn : 0 ≤ᵐ[(endMeasure F ζ hζ C R P H U a).restrict (tail F T)]
      energyDensity F ζ hζ C R P H U a ι f k s A := Filter.Eventually.of_forall
    (energyDensity_nonneg F ζ hζ C R P H U a ι f k s A)
  have hi : IntegrableOn (energyDensity F ζ hζ C R P H U a ι f k s A) (tail F T)
      (endMeasure F ζ hζ C R P H U a) :=
    ⟨hcont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hn).mpr (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp (he.symm ▸ hb)
include hι hf in
private theorem actual_energy_bound (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (k : ℕ) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ K,
      energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B := by
  let E := KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a
  have hv : ∀ s : K, ∃ v : ℕ → KPMeanZeroWeightedEnergy.Section E 0,
      (∀ n, (v n).val = parameterScalar F ζ hζ C R P H U a ι f n s.val) ∧
      (∀ n, KPMeanZeroWeightedEnergy.MeanZero E (fiberMeasure F ζ hζ C R P H U a) (v n)) ∧
      ∀ n p, 0 < p.2 → (v n).laplacian p = KPContActualChamberCasimirJets.lambda F s.val * (v n).scalar p +
        ∑ j ∈ Finset.Icc 1 (min n 2), (Nat.choose n j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s.val *
          (v (n-j)).scalar p := by
    intro s
    exact actual_meanZero_jet_sections F ζ hζ C R P H U ι f hι hf a s.val (hKV s.property) 0
  choose v hval hmean heq using hv
  let w := (H.disintegration (level F ζ hζ C R P H U)).componentWeight a.1
  have hw : w ≠ 0 := ne_of_gt ((H.disintegration _).positive_componentWeight a.1)
  have hwt : w ≠ (∞ : ℝ≥0∞) := (H.disintegration _).finite_componentWeight a.1 |>.ne
  have hem : endMeasure F ζ hζ C R P H U a = w • E.measure := rfl
  have hen (n : ℕ) (s : K) (A R₁ : ℝ) :
      energy F ζ hζ C R P H U a ι f n s.val A R₁ =
        w * KPMeanZeroWeightedEnergy.energy E (v s n) A R₁ := by
    unfold energy
    rw [hem, Measure.restrict_smul, lintegral_smul_measure]
    congr 1
    unfold KPMeanZeroWeightedEnergy.energy energyDensity jetScalar gradientSq
      KPMeanZeroWeightedEnergy.Section.scalar KPMeanZeroWeightedEnergy.Section.gradientSq
    rw [hval s n]
    rfl
  obtain ⟨D⟩ := kp_cont_mean_zero_weighted_energy_adapter E
  have hD : D.fiberMeasure = fiberMeasure F ζ hζ C R P H U a := by
    letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
    letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
    letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
    letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
    letI := D.fiberProbability
    letI := D.fiberHaar
    letI : BorelSpace E.KernelTorus :=
      KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
    exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  obtain ⟨Z,hZ⟩ := hK.exists_bound_of_continuousOn (f := KPContActualChamberCasimirJets.lambda F)
    ((by unfold KPContActualChamberCasimirJets.lambda KPContinuation.spectralCoordinate; fun_prop : Continuous (KPContActualChamberCasimirJets.lambda F)).continuousOn)
  have hcoef : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : K, ∀ j ∈ Finset.Icc 1 (min n 2),
      ‖(Nat.choose n j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s.val‖ ≤ C := by
    intro n
    obtain ⟨C1,h1⟩ := hK.exists_bound_of_continuousOn (f := fun s : ℂ => -4*(d F : ℂ)*(1/3+2*s)) (by fun_prop)
    let C := (n.choose 1 : ℝ) * max C1 0 + (n.choose 2 : ℝ) * ‖-8*(d F : ℂ)‖
    refine ⟨C, by dsimp [C]; positivity, ?_⟩
    intro s j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hj2 := le_trans (Finset.mem_Icc.mp hj).2 (min_le_right _ _)
    have hj : j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl
    · rw [norm_mul, Complex.norm_natCast, (KPContActualChamberCasimirJets.spectral_jets F s.val (hKV s.property)).2.2.1]
      have hh := mul_le_mul_of_nonneg_left ((h1 s.val s.property).trans (le_max_left C1 0)) (Nat.cast_nonneg (n.choose 1))
      dsimp [C]
      rw [show KPContActualChamberCasimirJets.d F = d F from
        (KPContFlatCuspCasimirSpecialization.dimension F ζ hζ).1.symm]
      exact hh.trans (le_add_of_nonneg_right (show 0 ≤ (n.choose 2 : ℝ) * ‖-8*(d F : ℂ)‖ by positivity))
    · rw [norm_mul, Complex.norm_natCast, (KPContActualChamberCasimirJets.spectral_jets F s.val (hKV s.property)).2.2.2.1]
      dsimp [C]
      rw [show KPContActualChamberCasimirJets.d F = d F from
        (KPContFlatCuspCasimirSpecialization.dimension F ζ hζ).1.symm]
      exact le_add_of_nonneg_left (show 0 ≤ (n.choose 1 : ℝ) * max C1 0 by positivity)
  have hseed : ∀ n, ∃ b B : ℝ, 0 ≤ B ∧ ∀ s : K,
      KPMeanZeroWeightedEnergy.forcingMass E (v s n) b 0 ≤ ENNReal.ofReal B := by
    intro n
    obtain ⟨b,B,hb,hB,hs⟩ := meanZeroJet_negative_weighted_mass F ζ hζ C R P H U ι f hι hf K hK hKV n
    let M := w⁻¹ * ENNReal.ofReal B
    have hMt : M < (∞ : ℝ≥0∞) := ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hw |>.lt_top) ENNReal.ofReal_lt_top
    refine ⟨b,M.toReal,ENNReal.toReal_nonneg,fun s => ?_⟩
    rw [ENNReal.ofReal_toReal hMt.ne]
    have hh := hs a s.val s.property 1
    have hm : w * KPMeanZeroWeightedEnergy.forcingMass E (v s n) b 0 ≤ ENNReal.ofReal B := by
      unfold KPMeanZeroWeightedEnergy.forcingMass
      change w • (∫⁻ p in {p : KPCuspCharts.Coordinates F | 0 < p.2},
        ENNReal.ofReal (Real.exp (2*b*p.2) * ‖(v s n).scalar p‖^2) ∂E.measure) ≤ _
      rw [← setLIntegral_smul_measure, ← hem]
      convert hh using 1
      congr 1
      funext p
      unfold KPMeanZeroWeightedEnergy.Section.scalar
      rw [hval s n, parameterScalar_coordinates F ζ hζ C R P H U a ι f hι hf n s.val (hKV s.property)]
    have hc := mul_le_mul_right hm w⁻¹
    rwa [← mul_assoc, ENNReal.inv_mul_cancel hw hwt, one_mul] at hc
  obtain ⟨B,hB,hbound⟩ := all_jets_energy E D (fun n s => v s n)
    (fun s => KPContActualChamberCasimirJets.lambda F s.val)
    (fun n s j => (n.choose j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s.val)
    (max Z 0) (le_max_right _ _) (fun s => (hZ s.val s.property).trans (le_max_left _ _))
    (fun n s => by rw [hD]; exact hmean s n) (fun n s => heq s n) hseed hcoef k A hA T hT
  let B' := w * ENNReal.ofReal B
  have hBt : B' < (∞ : ℝ≥0∞) := ENNReal.mul_lt_top hwt.lt_top ENNReal.ofReal_lt_top
  refine ⟨B'.toReal,ENNReal.toReal_nonneg,?_⟩
  intro s hs
  rw [hen k ⟨s,hs⟩, ENNReal.ofReal_toReal hBt.ne]
  exact mul_le_mul_right (hbound ⟨s,hs⟩) w

private theorem actual_energy_tail_bound (k : ℕ) (s : ℂ) (A T R' B : ℝ)
    (hA : 0 ≤ A) (hR : T ≤ R')
    (hb : energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B) :
    energy F ζ hζ C R P H U a ι f k s 0 R' ≤ ENNReal.ofReal (B*Real.exp (-2*A*R')) := by
  have hgrad (p : KPCuspCharts.Coordinates F) : 0 ≤ gradientSq F ζ hζ C R P H U a ι f k s p := by
    unfold gradientSq
    positivity
  have hp (p : KPCuspCharts.Coordinates F) (hp : R' < p.2) :
      ENNReal.ofReal (energyDensity F ζ hζ C R P H U a ι f k s 0 p) ≤
      ENNReal.ofReal (Real.exp (-2*A*R')) * ENNReal.ofReal (energyDensity F ζ hζ C R P H U a ι f k s A p) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    unfold energyDensity
    simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
    rw [← mul_assoc, ← Real.exp_add]
    apply le_mul_of_one_le_left (add_nonneg (sq_nonneg _) (hgrad p))
    apply Real.one_le_exp
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hp.le)]
  calc
    _ ≤ ∫⁻ p in tail F R', ENNReal.ofReal (Real.exp (-2*A*R')) *
        ENNReal.ofReal (energyDensity F ζ hζ C R P H U a ι f k s A p)
        ∂endMeasure F ζ hζ C R P H U a := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.preimage measurable_snd)] with p hp'
      exact hp p hp'
    _ = ENNReal.ofReal (Real.exp (-2*A*R')) * energy F ζ hζ C R P H U a ι f k s A R' :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (-2*A*R')) * energy F ζ hζ C R P H U a ι f k s A T := by
      gcongr
      exact lintegral_mono_set (fun p hp => lt_of_le_of_lt hR hp)
    _ ≤ ENNReal.ofReal (Real.exp (-2*A*R')) * ENNReal.ofReal B := mul_le_mul_right hb _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

include hι hf in
private theorem actual_weighted_tails (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V) (k : ℕ)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ T B : ℝ,
      0 ≤ T ∧ (H.atlas (level F ζ hζ C R P H U)).threshold < T ∧
      buffer.τ < T ∧ T₀ + 1 < T ∧ 0 ≤ B ∧
      (∀ a s, s ∈ K →
        IntegrableOn (energyDensity F ζ hζ C R P H U a ι f k s A) (tail F T)
          (endMeasure F ζ hζ C R P H U a) ∧
        energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B ∧
        (∫ p in tail F T, energyDensity F ζ hζ C R P H U a ι f k s A p
          ∂endMeasure F ζ hζ C R P H U a) ≤ B) ∧
      ∀ R' : ℝ, T ≤ R' → ∀ a s, s ∈ K →
        IntegrableOn (energyDensity F ζ hζ C R P H U a ι f k s 0) (tail F R')
          (endMeasure F ζ hζ C R P H U a) ∧
        energy F ζ hζ C R P H U a ι f k s 0 R' ≤ ENNReal.ofReal (B*Real.exp (-2*A*R')) ∧
        (∫ p in tail F R', energyDensity F ζ hζ C R P H U a ι f k s 0 p
          ∂endMeasure F ζ hζ C R P H U a) ≤ B*Real.exp (-2*A*R') := by
  let t₁ := (H.atlas (level F ζ hζ C R P H U)).threshold
  let m := max (max 0 t₁) (max buffer.τ (T₀+1))
  let T := m+1
  have hm0 : 0 ≤ m := (le_max_left 0 t₁).trans (le_max_left _ _)
  have hm1 : t₁ ≤ m := (le_max_right 0 t₁).trans (le_max_left _ _)
  have hm2 : buffer.τ ≤ m := (le_max_left buffer.τ (T₀+1)).trans (le_max_right _ _)
  have hm3 : T₀+1 ≤ m := (le_max_right buffer.τ (T₀+1)).trans (le_max_right _ _)
  have hT : 0 < T := by dsimp [T]; linarith
  have ht1 : (H.atlas (level F ζ hζ C R P H U)).threshold < T := by change t₁ < m+1; linarith
  have ht2 : buffer.τ < T := by dsimp [T]; linarith
  have ht3 : T₀+1 < T := by dsimp [T]; linarith
  have hex : ∀ a : Cusps F ζ hζ C R P H U, ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ K,
      energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B := by
    intro a
    exact actual_energy_bound F ζ hζ C R P H U a ι f hι hf K hK hKV k A T hA hT
  choose B hB hb using hex
  let B' := ∑ a : Cusps F ζ hζ C R P H U, B a
  have hB' : 0 ≤ B' := Finset.sum_nonneg (fun a _ => hB a)
  have hb' (a : Cusps F ζ hζ C R P H U) (s : ℂ) (hs : s ∈ K) :
      energy F ζ hζ C R P H U a ι f k s A T ≤ ENNReal.ofReal B' :=
    (hb a s hs).trans (ENNReal.ofReal_le_ofReal (Finset.single_le_sum (fun a _ => hB a) (Finset.mem_univ a)))
  refine ⟨T,B',hT.le,ht1,ht2,ht3,hB',?_,?_⟩
  · intro a s hs
    obtain ⟨hi,hint⟩ := energy_integrable_of_bound F ζ hζ C R P H U a ι f k s A T B' hB'
      (energyDensity_continuous F ζ hζ C R P H U a ι f hι hf k s (hKV hs) A) (hb' a s hs)
    exact ⟨hi,hb' a s hs,hint⟩
  · intro R' hR a s hs
    have htail := actual_energy_tail_bound F ζ hζ C R P H U a ι f k s A T R' B' hA hR (hb' a s hs)
    obtain ⟨hi,hint⟩ := energy_integrable_of_bound F ζ hζ C R P H U a ι f k s 0 R' (B'*Real.exp (-2*A*R'))
      (mul_nonneg hB' (Real.exp_nonneg _))
      (energyDensity_continuous F ζ hζ C R P H U a ι f hι hf k s (hKV hs) 0) htail
    exact ⟨hi,htail,hint⟩

end Application

end DedekindZetaZeroFree.KPContActualChamberMeanZeroAdapter

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_mean_zero_adapter
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι) (f : ℂ → S)
    (_hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {T₀ : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T₀)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T₀)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
      KPContinuation.spectralDomain f χ) :
    KPContActualChamberMeanZeroAdapter.Properties F ζ hζ C R P H U ι f buffer χ source := by
  classical
  letI := Fintype.ofFinite (rootsOfUnity 3 F)
  refine
    { fiber_probability := fun a => KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
      fiber_integrable := ?_
      representative_independent := ?_
      mean_zero := ?_
      smooth := ?_
      jet_formula := ?_
      coordinate_jet := ?_
      sheets := ?_
      above_collars := ?_
      weighted_tails := ?_ }
  · intro a k s hs t b ε
    letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
    letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
    exact KPContActualChamberCasimirJets.cusp_fiber_integrable F ζ hζ C R P H U ι f _hι _hf a
      (KPContActualChamberMeanZeroAdapter.fiberMeasure F ζ hζ C R P H U a) k s hs t b ε
  · exact fun a k s hs t b ε x y hxy =>
      KPContActualChamberMeanZeroAdapter.representative_law F ζ hζ C R P H U a ι f _hι _hf k s hs t b ε x y hxy
  · exact fun a k s hs t b =>
      KPContActualChamberMeanZeroAdapter.projected_complement_zero F ζ hζ C R P H U a ι f _hι _hf k s hs t b
  · intro a k s hs
    obtain ⟨v,hv,_,_⟩ := KPContActualChamberMeanZeroAdapter.actual_meanZero_jet_sections
      F ζ hζ C R P H U ι f _hι _hf a s hs buffer.τ
    rw [← hv k]
    exact (v k).smooth
  · exact fun a k s hs t x b ε =>
      KPContActualChamberMeanZeroAdapter.complement_jet F ζ hζ C R P H U a ι f _hι _hf k s hs t x b ε
  · intro a k s hs p
    exact KPContActualChamberMeanZeroAdapter.parameterScalar_coordinates F ζ hζ C R P H U a ι f _hι _hf k s hs p
  · exact fun a k s hs t x b ε =>
      KPContActualChamberMeanZeroAdapter.sheet_law F ζ hζ C R P H U a ι f _hι _hf k s hs t x b ε
  · intro a k s hs t x b ε ht _
    rw [← KPContActualChamberMeanZeroAdapter.complement_jet F ζ hζ C R P H U a ι f _hι _hf k s hs]
    apply iteratedDerivWithin_congr _ hs
    intro w hw
    exact (KPContActualChamberMeanZeroAdapter.correction_complement_eq F ζ hζ C R P H U a ι f
      buffer χ source _hι _hf w hw t x b ε ht).symm
  · exact KPContActualChamberMeanZeroAdapter.actual_weighted_tails F ζ hζ C R P H U ι f buffer _hι _hf

end DedekindZetaZeroFree

end
