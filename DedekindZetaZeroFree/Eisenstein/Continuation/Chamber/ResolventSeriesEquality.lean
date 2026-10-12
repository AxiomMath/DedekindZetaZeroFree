module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.FriedrichsDomainDefect
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.HolomorphicResolventInverse
public import DedekindZetaZeroFree.Eisenstein.Continuation.Resolvent.ClearedSmoothRepresentatives

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberFormulaEquality

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "HU" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Tests" => KPContActualAllCuspSource.Tests F ζ hζ C R P H U
local notation "μ" => KPContActualAllCuspSource.measure F ζ hζ C R P H U
local notation "Ω" => KPContinuation.spectralDomain
local notation "V" => KPContActualChamberDomainDefect.V
local notation "scalar" => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
local notation "testScalar" => KPContActualAllCuspSource.testScalar F ζ hζ C R P H U
local notation "Represents" => KPContActualSmoothLineGluing.Represents F ζ hζ level R P H
local notation "Charts" => KPContActualSmoothLineGluing.ChartBall F ζ hζ level R P H
local notation "coefficient" => KPContActualSmoothLineGluing.coefficient F ζ hζ level R P H
local notation "groupScalar" => KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ C R P H U
local notation "coveredPair" => KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
local notation "quotientPair" => KPContActualCutoffTestPairingHolomorphy.quotientPair F ζ hζ C R P H U

structure FormulaConclusions
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ level R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f Ω)
    (domain : KPContActualChamberDomainDefect.DomainConclusions F ζ hζ C R P H U
      ι f buffer χ source μG hμG hR realization hι hf)
    (W : ℂ → Smooth) where

  chamber_regular : V ⊆ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω)

  u_resolvent : ∀ s ∈ V,
    (domain.u 0 s : HU) = -(KPResolventPencil.shiftedResolvent (KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ
      level R P H μG hμG hR realization) (KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s)
      (source.h s))
  u_correction : ∀ s ∈ V, (domain.u 0 s : HU) = (KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR
    realization ι buffer Ω f χ source) s

  sections_equal : ∀ s ∈ V, (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
    (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s =
    domain.series s
  covered_equal : ∀ s ∈ V,
    scalar ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C
      R P H U μG hμG hR realization Ω) source.descent.cutoff) W s) = KPContActualChamberDomainDefect.seriesScalar F
      ζ hζ C R P H U ι f s
  charts_equal : ∀ s ∈ V, ∀ A : Charts,
    Set.EqOn (coefficient ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W
      s).val A)
      (coefficient (domain.series s).val A) A.ball.carrier

  group_equal : ∀ s ∈ V, ∀ g : KPContActualChamberNormalSeries.G F ζ hζ,
    groupScalar ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω (KPContActualHilbertSimpleGerms.Sigma F ζ
      hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s) g = KPContActualChamberNormalSeries.E F ζ
      hζ U ι f s g

  chamber_smooth_holomorphic : KPContActualCutoffPlusClearedGerm.SmoothTaylorData
    F ζ hζ C R P H U V ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W)
  series_smooth_holomorphic : KPContActualCutoffPlusClearedGerm.SmoothTaylorData
    F ζ hζ C R P H U V domain.series
  test_memLp : ∀ φ : Tests, MemLp (testScalar φ) 2 μ
  testClass : Tests →ₗ[ℂ] HU
  test_class_represents : ∀ φ : Tests,
    Represents (KPContActualAllCuspSource.testSection F ζ hζ C R P H U φ).val (testClass φ)

  covered_integrable : ∀ φ : Tests, ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
    realization Ω),
    Integrable (coveredPair ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s)
      (testScalar φ)) μ ∧
    Integrable (coveredPair (source.descent.cutoff s) (testScalar φ)) μ
  quotient_integrable : ∀ φ : Tests, ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
    realization Ω),
    Integrable (quotientPair ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s)
      (testScalar φ)) R.quotientHaar ∧
    Integrable (quotientPair (source.descent.cutoff s) (testScalar φ)) R.quotientHaar

  integral_identification : ∀ φ : Tests, ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
    realization Ω),
    (∫ x, quotientPair ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s)
      (testScalar φ) x ∂(R.quotientHaar)) =
      (∫ x, coveredPair ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
        (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s)
        (testScalar φ) x ∂μ) ∧
    (∫ x, quotientPair (source.descent.cutoff s) (testScalar φ) x ∂(R.quotientHaar)) =
      (∫ x, coveredPair (source.descent.cutoff s) (testScalar φ) x ∂μ)
  covered_formula : ∀ φ : Tests, ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
    realization Ω),
    (∫ x, coveredPair ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s)
      (testScalar φ) x ∂μ) =
      (∫ x, coveredPair (source.descent.cutoff s) (testScalar φ) x ∂μ) +
        inner ℂ (testClass φ) ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω
          f χ source) s)
  quotient_formula : ∀ φ : Tests, ∀ s ∈ Ω \ (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR
    realization Ω),
    (∫ x, quotientPair ((KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω
      (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω) source.descent.cutoff) W s)
      (testScalar φ) x ∂(R.quotientHaar)) =
      (∫ x, quotientPair (source.descent.cutoff s) (testScalar φ) x ∂(R.quotientHaar)) +
        inner ℂ (testClass φ) ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω
          f χ source) s)

  correction_pairing_meromorphic : ∀ φ : Tests,
    MeromorphicOn (fun s => inner ℂ (testClass φ) ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR
      realization ι buffer Ω f χ source) s)) Ω
  covered_pairing_meromorphic : ∀ φ : Tests,
    MeromorphicOn (fun s =>
      (∫ x, coveredPair (source.descent.cutoff s) (testScalar φ) x ∂μ) +
        inner ℂ (testClass φ) ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω
          f χ source) s)) Ω
  quotient_pairing_meromorphic : ∀ φ : Tests,
    MeromorphicOn (fun s =>
      (∫ x, quotientPair (source.descent.cutoff s) (testScalar φ) x ∂(R.quotientHaar)) +
        inner ℂ (testClass φ) ((KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω
          f χ source) s)) Ω

open KPContLocalNorm KPContRightJets

private theorem derivative_add {n : ℕ} (B : LocalBall n)
    {f g : Space n → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l (f + g))
      (coordinateDerivativeList l f + coordinateDerivativeList l g) B.carrier := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons i l ih =>
    intro x hx
    have he : coordinateDerivativeList l (f + g) =ᶠ[𝓝 x]
        coordinateDerivativeList l f + coordinateDerivativeList l g :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) ih
    change fderiv ℝ (coordinateDerivativeList l (f + g)) x (EuclideanSpace.single i 1) = _
    rw [he.fderiv_eq, fderiv_add]
    · rfl
    · exact ((KPContLocalHolomorphyUpgrade.CauchyAssembly.finite_coordinate_derivative_smooth B hf l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    · exact ((KPContLocalHolomorphyUpgrade.CauchyAssembly.finite_coordinate_derivative_smooth B hg l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)

private theorem chart_add {n : ℕ} (B : LocalBall n) {O : Set ℂ} {f g : ℂ → Space n → ℂ}
    (hf : KPCutoffSource.ChartSmoothHolomorphicOn B f O)
    (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B (fun s => f s + g s) O := by
  refine ⟨fun s hs => (hf.1 s hs).add (hg.1 s hs), ?_⟩
  intro K hK hKB m
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,hje⟩ := hf.2 K hK hKB m
  obtain ⟨k,hk,hke⟩ := hg.2 K hK hKB m
  refine ⟨fun s => j s + k s, hj.add hk, ?_⟩
  intro s hs α x
  change j s α x + k s α x = _
  rw [hje s hs α x, hke s hs α x]
  exact (derivative_add B (hf.1 s hs) (hg.1 s hs) α.directions (hKB x.property)).symm

private theorem series_add {n : ℕ} (B : LocalBall n) (c : ℂ) (ρ : ℝ)
    {b d : ℕ → Space n → ℂ} {f g : ℂ → Space n → ℂ}
    (hb : SmoothPowerSeriesOn B c ρ b f) (hd : SmoothPowerSeriesOn B c ρ d g) :
    SmoothPowerSeriesOn B c ρ (fun j => b j + d j) (fun s => f s + g s) := by
  refine ⟨fun j => (hb.1 j).add (hd.1 j), fun s hs => (hb.2.1 s hs).add (hd.2.1 s hs), ?_⟩
  intro K hK hKB m r hr hrρ ε hε
  obtain ⟨N,hN⟩ := hb.2.2 K hK hKB m r hr hrρ (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := hd.2.2 K hK hKB m r hr hrρ (ε/2) (by positivity)
  refine ⟨max N M,?_⟩
  intro L hL s hs α x
  have hsb : s ∈ Metric.ball c ρ := Metric.closedBall_subset_ball hrρ hs
  have he : (fun y => (∑ j ∈ Finset.range L, (s-c)^j * (b j + d j) y) - (f s + g s) y) =
      (fun y => (∑ j ∈ Finset.range L, (s-c)^j * b j y) - f s y) +
      (fun y => (∑ j ∈ Finset.range L, (s-c)^j * d j y) - g s y) := by
    funext y
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  rw [he]
  have hc1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (∑ j ∈ Finset.range L, (s-c)^j * b j y) - f s y) B.carrier :=
    (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hb.1 j)).sub (hb.2.1 s hsb)
  have hc2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (∑ j ∈ Finset.range L, (s-c)^j * d j y) - g s y) B.carrier :=
    (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hd.1 j)).sub (hd.2.1 s hsb)
  simp only [coordinateDerivative]
  rw [derivative_add B hc1 hc2 α.directions (hKB x.property)]
  exact (norm_add_le _ _).trans_lt (by
    have h1 := hN L (le_trans (le_max_left _ _) hL) s hs α x
    have h2 := hM L (le_trans (le_max_right _ _) hL) s hs α x
    simp only [coordinateDerivative] at h1 h2
    linarith)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer KPContinuation.spectralDomain f χ)
variable (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (domain : KPContActualChamberDomainDefect.DomainConclusions F ζ hζ C R P H U ι f buffer χ source μG hμG hR realization hι hf)
local notation "v" => KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source
local notation "poles" => KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω

include H in
theorem actual_spectralCoordinate : KPContActualChamberInverse.a_U F =
    KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) := by
  funext s
  unfold KPContActualChamberInverse.a_U KPContinuation.spectralCoordinate
  congr 1
  have ht : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp H.totallyComplex
  have hfin := @NumberField.IsTotallyComplex.finrank F _ _ ht
  have hnat : Module.finrank ℚ F / 2 = NumberField.InfinitePlace.nrComplexPlaces F := by rw [hfin]; omega
  rw [hnat, hfin]
  push_cast
  ring

include realization in
theorem chamber_regular_actual : V ⊆ Ω \ poles := by
  have hi := kp_cont_actual_chamber_inverse F ζ hζ μG hμG level R hR P H realization
  have ht : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp H.totallyComplex
  have hfin := @NumberField.IsTotallyComplex.finrank F _ _ ht
  have hd : ((Module.finrank ℚ F / 2 : ℕ) : ℝ) = (Module.finrank ℚ F : ℝ) / 2 := by
    rw [hfin, Nat.mul_div_right _ (by norm_num)]; push_cast; ring
  intro s hs
  have hr := (hi.chamber_regular s hs).1
  unfold KPContActualChamberInverse.Sigma_U at hr
  rw [actual_spectralCoordinate F ζ hζ R P H] at hr
  simpa only [KPContActualHilbertSimpleGerms.Sigma, hd, Nat.cast_ofNat, Nat.cast_mul,
    Int.natCast_div, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] using hr

include realization buffer in
theorem domain_class_correction : ∀ s ∈ V, (domain.u 0 s : HU) = v s := by
  have hi := kp_cont_actual_chamber_inverse F ζ hζ μG hμG level R hR P H realization
  intro s hs
  have hh := (hi.genuine_inverse s hs).choose_spec.2
  rw [actual_spectralCoordinate F ζ hζ R P H] at hh
  have ht := hh (domain.u 0 s)
  rw [domain.equation s hs, map_neg] at ht
  exact ht.symm

include realization buffer in
theorem domain_defect_represents (s : ℂ) (hs : s ∈ V) :
    Represents (domain.series s - source.descent.cutoff s).val (domain.u 0 s : HU) := by
  have hae := domain.defect_ae 0 s hs
  have hr : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
      (domain.series s - source.descent.cutoff s).val).val =
      KPContActualChamberDomainDefect.defectScalar F ζ hζ C R P H U ι f buffer χ source s := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    change ((KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm
      ((domain.series s).val - (source.descent.cutoff s).val)).val = _
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (source.descent.cutoff s).val,
      (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm.map_add,
      (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm.map_smul]
    change scalar (domain.series s) + (-1 : ℂ) • scalar (source.descent.cutoff s) = _
    rw [neg_one_smul, ← sub_eq_add_neg]
    rw [domain.series_formula s hs]
    rfl
  have hmem := domain.defect_memLp 0 s hs
  change MemLp (KPContActualChamberDomainDefect.defectScalar F ζ hζ C R P H U ι f buffer χ source s) 2 μ at hmem
  change ((domain.u 0 s : HU) : Lp ℂ 2 μ) =ᵐ[μ] KPContActualChamberDomainDefect.defectScalar F ζ hζ C R P H U ι f buffer χ source s at hae
  have hf' : MemLp (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
      (domain.series s - source.descent.cutoff s).val).val 2 μ := hr ▸ hmem
  refine ⟨hf', ?_⟩
  apply Lp.ext
  refine hf'.coeFn_toLp.trans ?_
  have ht : _ =ᵐ[μ] _ := Filter.Eventually.of_forall (congrFun hr)
  exact ht.trans hae.symm
variable (W : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
variable (hW : KPContActualClearedSmoothRepresentatives.Properties F ζ hζ C R P H U μG hμG hR realization ι buffer KPContinuation.spectralDomain f χ source W)

include hW in
theorem literal_sections_equal : ∀ s ∈ V,
    KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s = domain.series s := by
  intro s hs
  have hr := chamber_regular_actual F ζ hζ C R P H U μG hμG hR realization hs
  apply Eq.symm
  apply hW.continuation.off_pole_unique s hr
  rw [← domain_class_correction F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain s hs]
  exact domain_defect_represents F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain s hs

theorem actual_test_memLp (φ : Tests) : MemLp (testScalar φ) 2 μ := by
  let Z := KPContActualAllCuspSource.testSection F ζ hζ C R P H U φ
  let g := (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm Z.val
  have hc : Continuous g.val := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ level R P H Z.val).mp
    (fun i => (φ.property.1 i).continuous)
  have hk : HasCompactSupport g.val := by
    apply (KPContSectorSmoothFramesSupport.hasCompactSupport_iff F ζ hζ level R P H g).mpr
    rw [(KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).apply_symm_apply]
    obtain ⟨K,hK,hzero⟩ := φ.property.2
    let := KPContSectorQuotientRelationsComparison.instPolishSpaceRawXU F ζ hζ level
    apply HasCompactSupport.intro hK
    intro x hx
    obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas level).components.surjective x
    revert hx
    refine Quotient.inductionOn y ?_
    intro z hx
    rw [KPContSectorSmoothFramesSupport.sectionNorm_component]
    have hh := hzero i z
    have he : KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex level (H.atlas level) i z =
        (H.atlas level).components ⟨i, Quotient.mk _ z⟩ := by
      exact ((H.atlas level).components_formula i (Quotient.mk _ z)).symm
    rw [he] at hh
    change ‖(φ.val i).val z‖ = 0
    rw [hh hx]
    exact norm_zero
  exact KPContSectorFixedMeasureLocalFiniteness.compactSupport_memLp F ζ hζ R level g.val hc hk

def actualTestEmbedding : Tests →ₗ[ℂ]
    KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ level R where
  toFun φ := ⟨(KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm φ.val,
    ⟨((KPContSectorLineL2Isometry.continuous_iff F ζ hζ level R P H φ.val).mp
      (fun i => (φ.property.1 i).continuous)).measurable,
      actual_test_memLp F ζ hζ C R P H U φ⟩⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm.map_add φ.val ψ.val
  map_smul' a φ := by
    apply Subtype.ext
    exact (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm.map_smul a φ.val

def actualTestClass : Tests →ₗ[ℂ] HU :=
  (KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ level R P H).comp
    (actualTestEmbedding F ζ hζ C R P H U)

theorem actual_test_class_represents (φ : Tests) :
    Represents (KPContActualAllCuspSource.testSection F ζ hζ C R P H U φ).val
      (actualTestClass F ζ hζ C R P H U φ) := by
  have hr : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
      (KPContActualAllCuspSource.testSection F ζ hζ C R P H U φ).val).val = testScalar φ := rfl
  refine ⟨hr ▸ actual_test_memLp F ζ hζ C R P H U φ, ?_⟩
  exact (KPContSectorLineL2Isometry.scalarEmbedding_coe F ζ hζ level R P H
    (actualTestEmbedding F ζ hζ C R P H U φ)).symm

private theorem chart_parameter_congr {n : ℕ} (B : LocalBall n)
    {O : Set ℂ} {f g : ℂ → Space n → ℂ} (he : Set.EqOn f g O)
    (hf : KPCutoffSource.ChartSmoothHolomorphicOn B f O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B g O := by
  refine ⟨fun s hs => by rw [← he hs]; exact hf.1 s hs, ?_⟩
  intro K hK hKB m
  obtain ⟨j,hj,hje⟩ := hf.2 K hK hKB m
  refine ⟨j,hj,?_⟩
  intro s hs α x
  rw [← he hs]
  exact hje s hs α x

private theorem series_parameter_congr {n : ℕ} (B : LocalBall n)
    {c : ℂ} {ρ : ℝ} {b : ℕ → Space n → ℂ} {f g : ℂ → Space n → ℂ}
    (he : Set.EqOn f g (Metric.ball c ρ)) (hf : SmoothPowerSeriesOn B c ρ b f) :
    SmoothPowerSeriesOn B c ρ b g := by
  refine ⟨hf.1, fun s hs => by rw [← he hs]; exact hf.2.1 s hs, ?_⟩
  intro K hK hKB m r hr hrρ ε hε
  obtain ⟨N,hN⟩ := hf.2.2 K hK hKB m r hr hrρ ε hε
  refine ⟨N,?_⟩
  intro L hL s hs α x
  rw [← he (Metric.closedBall_subset_ball hrρ hs)]
  exact hN L hL s hs α x

private theorem chamber_isOpen : IsOpen V := by
  exact isOpen_lt continuous_const Complex.continuous_re

include hW in
theorem formula_smoothTaylorData :
    KPContActualCutoffPlusClearedGerm.SmoothTaylorData F ζ hζ C R P H U V
      (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W) := by
  have hreg := chamber_regular_actual F ζ hζ C R P H U μG hμG hR realization
  have hC : ∀ A : Charts, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient (source.descent.cutoff s).val A) Ω := by
    intro A
    have hh := (source.local_holomorphy A.component A.center A.chart A.phase A.ball A.contained).1
    have hcoef (w : Smooth) : KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w A.component A.phase = coefficient w.val A := by
      unfold KPContActualAllCuspSource.chartCoefficient KPContActualSmoothLineGluing.coefficient
      rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      rfl
    simpa only [hcoef] using hh
  have hholW := hW.continuation.correction_holomorphy
  have he : ∀ s ∈ V, ∀ A : Charts,
      coefficient (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s).val A =
        coefficient (source.descent.cutoff s).val A + coefficient (W s).val A := by
    intro s hs A
    rw [KPContActualCutoffPlusClearedGerm.E, if_pos (hreg hs),
      KPContActualCutoffPlusClearedGerm.coefficient_add]
  apply KPContActualCutoffPlusClearedGerm.smoothTaylorData_of_chart_series F ζ hζ C R P H U realization V chamber_isOpen
  · intro A
    apply chart_parameter_congr A.ball (fun s hs => (he s hs A).symm)
    apply chart_add A.ball
    · exact ⟨fun s hs => (hC A).1 s (hreg hs).1, fun K hK hKB m => by
        obtain ⟨j,hj,hje⟩ := (hC A).2 K hK hKB m
        exact ⟨j,hj.mono (fun s hs => (hreg hs).1),fun s hs => hje s (hreg hs).1⟩⟩
    · exact ⟨fun s hs => (hholW.holomorphic A).1 s (hreg hs), fun K hK hKB m => by
        obtain ⟨j,hj,hje⟩ := (hholW.holomorphic A).2 K hK hKB m
        exact ⟨j,hj.mono hreg,fun s hs => hje s (hreg hs)⟩⟩
  · intro c ρ hρ hclosed
    obtain ⟨b,hb⟩ := KPContActualCutoffPlusClearedGerm.actual_cutoff_common_disk_coefficients
      F ζ hζ C R P H U ι Ω f χ buffer source KPContinuation.spectralDomain_isOpen c ρ hρ
      (fun s hs => (hreg (hclosed hs)).1)
    obtain ⟨d,_,_,hd,_⟩ := hholW.disks c ρ hρ (hclosed.trans hreg)
    refine ⟨fun j => b j + d j, ?_⟩
    intro A
    have hsum := series_add A.ball c ρ (hb A) (hd A)
    have hbadd : (fun j => coefficient (b j + d j).val A) =
        (fun j => coefficient (b j).val A + coefficient (d j).val A) := by
      funext j
      exact KPContActualCutoffPlusClearedGerm.coefficient_add F ζ hζ C R P H U (b j) (d j) A
    rw [hbadd]
    apply series_parameter_congr A.ball _ hsum
    intro s hs
    exact (he s (hclosed (Metric.ball_subset_closedBall hs)) A).symm

include hW in
theorem literal_series_smoothTaylorData :
    KPContActualCutoffPlusClearedGerm.SmoothTaylorData F ζ hζ C R P H U V domain.series := by
  have hE := formula_smoothTaylorData F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source W hW
  have he := literal_sections_equal F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain W hW
  apply KPContActualCutoffPlusClearedGerm.smoothTaylorData_of_chart_series F ζ hζ C R P H U realization V chamber_isOpen
  · intro A
    apply chart_parameter_congr A.ball _ (hE.holomorphic A)
    intro s hs
    exact congrArg (fun Z : Smooth => coefficient Z.val A) (he s hs)
  · intro c ρ hρ hclosed
    obtain ⟨b,hb,_⟩ := hE.disks c ρ hρ hclosed
    refine ⟨b,fun A => series_parameter_congr A.ball ?_ (hb A)⟩
    intro s hs
    exact congrArg (fun Z : Smooth => coefficient Z.val A)
      (he s (hclosed (Metric.ball_subset_closedBall hs)))
open KPContActualSphericalFlatStage in
private theorem formula_stage
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (hι : Function.Injective ι) :
    KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι := by
  refine {
    source := sourceFlat_eq F ζ hζ C R P H U ι
    covariance := covariance F ζ hζ U ι
    smooth_holomorphy := smoothHolomorphy F ζ hζ U ι hι
    archimedean_parameter := ?_
    incoming := ?_
    «coefficient» := ?_
    frame_recipe := ?_
    transition := ?_
    metric_radial := ?_
    casimir := ?_
    rational_index := ?_ }
  · intro s vv u g
    have he : 1 + 2 * KPIncomingCasimir.nu s = 4 / 3 + 2 * s := by
      unfold KPIncomingCasimir.nu
      ring
    rw [he]
    exact KPContFlatArchDiagonalMultiplier.flatR_covariance F ζ hζ s u
      (coreInclusion F ζ hζ U ι vv) g
  · intro a s hs vv t b
    simpa [KPIncomingCasimir.heightFactor, KPIncomingCasimir.nu] using
      incoming_formula F ζ hζ C R P H U ι a s hs vv t b
  · intro a j
    exact ⟨fun s hs vv => KPContFlatCuspCoefficientTransition.locally_parallel
      F ζ hζ C R P H U a ι s hs vv j,
      fun b => KPContFlatCuspCoefficientTransition.frameCoefficient_holomorphic
        F ζ hζ C R P H U a ι j b⟩
  · intro a s hs vv b
    exact KPContFlatCuspCoefficientTransition.frameCoefficient_formula
      F ζ hζ C R P H U a ι s hs vv b
  · intro a s hs vv g b q
    exact ⟨(KPContFlatCuspCoefficientTransition.transport_formula F ζ hζ C R P H U a ι
      s hs vv g b).1,
      (KPContFlatCuspIncomingEvaluation.frequencies F ζ hζ C R P H U a).constantSystem.transition_formula
        g ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs vv).val b) q⟩
  · intro a s hs vv p q
    change KPContFlatCuspCasimirSpecialization.Δloc _ _ _ = _
    exact KPContFlatCuspCasimirSpecialization.metric_radial_scalar F ζ hζ C R P H U ι a s hs vv p q
  · intro a s hs vv q z
    change KPContFlatCuspCasimirSpecialization.Δloc _ _ _ = _
    exact KPContFlatCuspCasimirSpecialization.incoming_casimir_scalar F ζ hζ C R P H U ι a s hs vv q z
  · intro s vv g γ
    simpa only [KPContFlatRationalCosetCovariance.cosetEquiv_mk,
      KPContFlatRationalCosetCovariance.L, L,
      KPContFlatCommonLevelKernel.L, LinearMap.comp_apply, Submodule.coe_subtype] using
      KPContFlatRationalCosetCovariance.rationalTerm_transport_mk F ζ hζ s
        (coreInclusion F ζ hζ U ι vv) g γ

private theorem represented_pairing (Z Z' : Smooth) (u u' : HU)
    (hZ : Represents Z.val u) (hZ' : Represents Z'.val u') :
    Integrable (coveredPair Z' (scalar Z)) μ ∧
      (∫ x, coveredPair Z' (scalar Z) x ∂μ) = inner ℂ u u' := by
  obtain ⟨hf,he⟩ := hZ
  obtain ⟨hg,he'⟩ := hZ'
  have ha : ((u : Lp ℂ 2 μ) : _ → ℂ) =ᵐ[μ] scalar Z := by
    rw [← he]
    exact hf.coeFn_toLp
  have hb : ((u' : Lp ℂ 2 μ) : _ → ℂ) =ᵐ[μ] scalar Z' := by
    rw [← he']
    exact hg.coeFn_toLp
  have hab : (fun x => inner ℂ ((u : Lp ℂ 2 μ) x) ((u' : Lp ℂ 2 μ) x)) =ᵐ[μ]
      coveredPair Z' (scalar Z) := by
    filter_upwards [ha,hb] with x hx hy
    rw [hx,hy]
    simp only [KPContActualCutoffTestPairingHolomorphy.coveredPair, RCLike.inner_apply',
      RCLike.star_def]
    ring
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (u : Lp ℂ 2 μ) (u' : Lp ℂ 2 μ)).congr hab, ?_⟩
  change _ = inner ℂ (u : Lp ℂ 2 μ) (u' : Lp ℂ 2 μ)
  rw [L2.inner_def]
  exact integral_congr_ae hab.symm

private theorem quotient_transfer (Z : Smooth) (ψ : KPContActualAllCuspSource.Covered F ζ hζ C R P H U → ℂ)
    (hint : Integrable (coveredPair Z ψ) μ) :
    Integrable (quotientPair Z ψ) R.quotientHaar ∧
      (∫ x, quotientPair Z ψ x ∂(R.quotientHaar)) = ∫ x, coveredPair Z ψ x ∂μ := by
  have hp : AEMeasurable (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ level) R.quotientHaar :=
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ level).aemeasurable
  have hm : Integrable (coveredPair Z ψ)
      (Measure.map (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ level) R.quotientHaar) := hint
  exact ⟨(integrable_map_measure hm.aestronglyMeasurable hp).1 hm,
    (integral_map hp hm.aestronglyMeasurable).symm⟩

include hW hι hf in
theorem covered_formula_actual (φ : Tests) (s : ℂ) (hs : s ∈ Ω \ poles) :
    Integrable (coveredPair (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s) (testScalar φ)) μ ∧
    Integrable (coveredPair (source.descent.cutoff s) (testScalar φ)) μ ∧
    (∫ x, coveredPair (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s) (testScalar φ) x ∂μ) =
      (∫ x, coveredPair (source.descent.cutoff s) (testScalar φ) x ∂μ) +
        inner ℂ (actualTestClass F ζ hζ C R P H U φ) (v s) := by
  have hStage := formula_stage F ζ hζ C R P H U ι hι
  have hC := (kp_cont_actual_cutoff_test_pairing_holomorphy F ζ hζ C R P H U realization buffer
    ι hι hStage Ω Set.Subset.rfl KPContinuation.spectralDomain_isOpen f hf χ source.descent).cutoff_tests φ
  have hWpair := represented_pairing F ζ hζ C R P H U
    (KPContActualAllCuspSource.testSection F ζ hζ C R P H U φ) (W s)
    (actualTestClass F ζ hζ C R P H U φ) (v s)
    (actual_test_class_represents F ζ hζ C R P H U φ) (hW.continuation.correction_represents s hs)
  have he : coveredPair (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s) (testScalar φ) =
      coveredPair (source.descent.cutoff s) (testScalar φ) + coveredPair (W s) (testScalar φ) := by
    unfold KPContActualCutoffPlusClearedGerm.E
    rw [if_pos hs]
    unfold KPContActualCutoffTestPairingHolomorphy.coveredPair KPContActualCutoffSmoothDescent.scalar
    rw [map_add]
    funext x
    exact add_mul _ _ _
  rw [he]
  refine ⟨(hC.covered_integrable s hs.1).add hWpair.1, hC.covered_integrable s hs.1, ?_⟩
  change (∫ x, coveredPair (source.descent.cutoff s) (testScalar φ) x + coveredPair (W s) (testScalar φ) x ∂μ) = _
  exact (integral_add (hC.covered_integrable s hs.1) hWpair.1).trans
    (congrArg (fun z => (∫ x, coveredPair (source.descent.cutoff s) (testScalar φ) x ∂μ) + z) hWpair.2)

private theorem meromorphic_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℂ → E} {O : Set ℂ} (L : E →L[ℂ] ℂ) (hg : MeromorphicOn g O) :
    MeromorphicOn (fun s => L (g s)) O := by
  intro s hs
  obtain ⟨n,hn⟩ := hg s hs
  refine ⟨n, ?_⟩
  have h : AnalyticAt ℂ (fun z : ℂ => L ((z-s)^n • g z)) s :=
    AnalyticAt.comp (f := fun z : ℂ => (z-s)^n • g z) (L.analyticAt _) hn
  simpa only [Function.comp_def, map_smul] using h

include hW hι hf in
theorem correction_pairing_meromorphic_actual (φ : Tests) :
    MeromorphicOn (fun s => inner ℂ (actualTestClass F ζ hζ C R P H U φ) (v s)) Ω := by
  have hh := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U μG hμG hR realization
    ι hι (formula_stage F ζ hζ C R P H U ι hι) Ω KPContinuation.spectralDomain_isOpen Set.Subset.rfl f hf buffer χ source
  exact meromorphic_clm (InnerProductSpace.toDual ℂ HU (actualTestClass F ζ hζ C R P H U φ)) hh.hilbert_meromorphic

include hW in
theorem conclusions_same_domain : Nonempty (FormulaConclusions F ζ hζ C R P H U
    μG hμG hR realization ι f buffer χ source hι hf domain W) := by
  let testClass := actualTestClass F ζ hζ C R P H U
  have hr := chamber_regular_actual F ζ hζ C R P H U μG hμG hR realization
  have he := literal_sections_equal F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain W hW
  have hp := covered_formula_actual F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf W hW
  have hq (φ : Tests) (s : ℂ) (hs : s ∈ Ω \ poles) :=
    quotient_transfer F ζ hζ C R P H U
      (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s) (testScalar φ) (hp φ s hs).1
  have hqc (φ : Tests) (s : ℂ) (hs : s ∈ Ω \ poles) :=
    quotient_transfer F ζ hζ C R P H U (source.descent.cutoff s) (testScalar φ) (hp φ s hs).2.1
  have hpair := kp_cont_actual_cutoff_test_pairing_holomorphy F ζ hζ C R P H U realization buffer
    ι hι (formula_stage F ζ hζ C R P H U ι hι) Ω Set.Subset.rfl KPContinuation.spectralDomain_isOpen f hf χ source.descent
  have hm := correction_pairing_meromorphic_actual F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf W hW
  refine ⟨{
    chamber_regular := hr
    u_resolvent := domain_class_correction F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain
    u_correction := domain_class_correction F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain
    sections_equal := he
    covered_equal := ?_
    charts_equal := ?_
    group_equal := ?_
    chamber_smooth_holomorphic := formula_smoothTaylorData F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source W hW
    series_smooth_holomorphic := literal_series_smoothTaylorData F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain W hW
    test_memLp := actual_test_memLp F ζ hζ C R P H U
    testClass := testClass
    test_class_represents := actual_test_class_represents F ζ hζ C R P H U
    covered_integrable := fun φ s hs => ⟨(hp φ s hs).1,(hp φ s hs).2.1⟩
    quotient_integrable := fun φ s hs => ⟨(hq φ s hs).1,(hqc φ s hs).1⟩
    integral_identification := fun φ s hs => ⟨(hq φ s hs).2,(hqc φ s hs).2⟩
    covered_formula := fun φ s hs => (hp φ s hs).2.2
    quotient_formula := ?_
    correction_pairing_meromorphic := hm
    covered_pairing_meromorphic := ?_
    quotient_pairing_meromorphic := ?_ }⟩
  · intro s hs
    rw [he s hs]
    exact domain.series_formula s hs
  · intro s hs A
    rw [he s hs]
    exact fun _ _ => rfl
  · intro s hs g
    rw [he s hs]
    exact domain.series_lift s hs g
  · intro φ s hs
    rw [(hq φ s hs).2,(hqc φ s hs).2]
    exact (hp φ s hs).2.2
  · intro φ
    have hc := ((hpair.cutoff_tests φ).covered_holomorphic.analyticOnNhd KPContinuation.spectralDomain_isOpen).meromorphicOn
    exact hc.add (hm φ)
  · intro φ
    have hc := ((hpair.cutoff_tests φ).quotient_holomorphic.analyticOnNhd KPContinuation.spectralDomain_isOpen).meromorphicOn
    exact hc.add (hm φ)

end DedekindZetaZeroFree.KPContActualChamberFormulaEquality

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_formula_equality
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (T : ℝ)
    (hT : (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).threshold < T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) :
    ∃ buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T,
      ∃ source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
          KPContinuation.spectralDomain f χ,
        ∃ domain : KPContActualChamberDomainDefect.DomainConclusions F ζ hζ C R P H U
            ι f buffer χ source μG hμG hR realization hι hf,
          ∃ W : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U,
            KPContActualClearedSmoothRepresentatives.Properties
              F ζ hζ C R P H U μG hμG hR realization ι buffer
                KPContinuation.spectralDomain f χ source W ∧
            Nonempty (KPContActualChamberFormulaEquality.FormulaConclusions
              F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain W) := by
  obtain ⟨buffer,source,⟨domain⟩⟩ := kp_cont_actual_chamber_domain_defect
    F ζ hζ C μG hμG R hR P H U realization ι hι f hf T hT χ
  have hStage := KPContActualChamberFormulaEquality.formula_stage F ζ _ C R P H U ι hι
  obtain ⟨W,hW⟩ := kp_cont_actual_cleared_smooth_representatives F ζ _ C R P H U μG hμG hR realization
    ι hι hStage KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen Set.Subset.rfl
    f hf buffer χ source
  refine ⟨buffer,source,domain,W,hW,?_⟩
  exact KPContActualChamberFormulaEquality.conclusions_same_domain
    F ζ _ C R P H U μG hμG hR realization ι f buffer χ source hι hf domain W hW

end DedekindZetaZeroFree

end
