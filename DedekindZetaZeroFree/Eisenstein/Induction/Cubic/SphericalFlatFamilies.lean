module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingCasimirEquation

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPContActualSphericalFlatStage

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Stage (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) :=
  KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
variable [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] Stage F ζ hζ U)

abbrev coreInclusion := (Stage F ζ hζ U).subtype.comp ι

abbrev L := KPContFlatCommonLevelKernel.L F ζ hζ U ι

theorem stage_smooth (v : S) :
    (coreInclusion F ζ hζ U ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
  have h := (coreInclusion F ζ hζ U ι v).property
  change (coreInclusion F ζ hζ U ι v).val ∈ KPGlobalEisensteinData.hcHeckeCore _ _ _ at h
  apply (show KPGlobalEisensteinData.hcHeckeCore _ _ _ ≤
    KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) from ?_) h
  unfold KPGlobalEisensteinData.hcHeckeCore
  exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left

theorem sourceFlat_eq (s : ℂ) (v : S) :
    let _ := C; let _ := R; let _ := P; let _ := H
    L F ζ hζ U ι s v =
      (KPContFlatSourceRecipe.flatR F ζ hζ s (coreInclusion F ζ hζ U ι v)).val := by
  rfl

def Covariance : Prop :=
  ∀ (s : ℂ), s ∈ KPContinuation.spectralDomain →
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      L F ζ hζ U ι s v (g * u.val) = L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (k : KPContSectorArchSphericalFibers.KInfinity F),
      L F ζ hζ U ι s v
        (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
          L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) (ε : rootsOfUnity 3 F),
      L F ζ hζ U ι s v (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (a : KPGlobalResidualKernel.rationalBorel F ζ hζ),
      L F ζ hζ U ι s v (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ a.val * g) =
        L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H)
      (x : KPGlobalTorusFunctionData.Adeles F),
      L F ζ hζ U ι s v ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
          ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂ) *
            L F ζ hζ U ι s v g)

theorem covariance : Covariance F ζ hζ U ι := by
  intro s hs
  obtain ⟨hU, hK, hχ, _, hB⟩ := KPContFlatCommonLevelKernel.stage_properties F ζ hζ U ι s hs
  refine ⟨hU, hK, fun v g ε => hχ v ε g, ?_, fun v g h x => hB v h x g⟩
  intro v g a
  exact KPContFlatRationalCosetCovariance.L_rationalBorel F ζ hζ s
    (coreInclusion F ζ hζ U ι v) a g

def SmoothHolomorphy : Prop :=
  (∀ (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ),
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => L F ζ hζ U ι s v
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) ∧
  (∀ (f : ℂ → S), DifferentiableOn ℂ f KPContinuation.spectralDomain →
    ∀ (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
      (Q : KPGlobalTorusFunctionData.JetCompact
        (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)),
    letI : CompactSpace Q.set := isCompact_iff_compactSpace.mp Q.compact
    DifferentiableOn ℂ
      (fun s => KPContFlatStageJetHolomorphy.compactJet F ζ hζ
        (coreInclusion F ζ hζ U ι) (stage_smooth F ζ hζ U ι) g n Q s (f s))
      KPContinuation.spectralDomain)

theorem smoothHolomorphy (hι : Function.Injective ι) :
    SmoothHolomorphy F ζ hζ U ι := by
  refine ⟨?_, ?_⟩
  · intro s v g
    exact KPContFlatStageJetHolomorphy.L_contDiffOn F ζ hζ
      (coreInclusion F ζ hζ U ι) (stage_smooth F ζ hζ U ι) (fun _ => v) s g
  · intro f hf g n Q
    exact KPContFlatStageJetHolomorphy.compactJet_holomorphic F ζ hζ
      (coreInclusion F ζ hζ U ι) (stage_smooth F ζ hζ U ι)
      ((Stage F ζ hζ U).injective_subtype.comp hι) f hf g n Q

abbrev Cusps := KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U

variable (a : Cusps F ζ hζ C R P H U)

theorem incoming_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (t : ℝ) (b : KPCuspCharts.Shape F) :
    KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s v t b =
      Complex.exp (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * ((4 : ℂ) / 3 + 2 * s) * (t : ℂ)) •
        (KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b := by
  exact KPContFlatCuspIncomingEvaluation.incoming_formula F ζ hζ C R P H U a ι s hs v t b

end DedekindZetaZeroFree.KPContActualSphericalFlatStage

namespace DedekindZetaZeroFree.KPContActualSphericalFlatStage

def coordinateDirection (d : ℕ) (i : Fin d) (j : Fin 3) : KPArch.Space d :=
  Pi.single i (if j = 0 then (1, 0) else if j = 1 then (Complex.I, 0) else (0, 1))

def inverseMetricWeight (d : ℕ) (z : KPArch.Space d) (i : Fin d) (j : Fin 3) : ℝ :=
  if j = 2 then 1 else KPArch.height (z i) ^ 2

def localLaplacian (d : ℕ) (f : KPArch.Space d → ℂ) (z : KPArch.Space d) : ℂ :=
  -((KPArch.volumeDensity d z : ℂ)⁻¹ *
    ∑ i : Fin d, ∑ j : Fin 3,
      fderiv ℝ (fun y =>
        ((KPArch.volumeDensity d y * inverseMetricWeight d y i j : ℝ) : ℂ) *
          fderiv ℝ f y (coordinateDirection d i j)) z (coordinateDirection d i j))

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] Stage F ζ hζ U)
variable (a : Cusps F ζ hζ C R P H U)

def incomingOnArch (s : ℂ) (v : S)
    (q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) : ℂ :=
  let p := (KPCuspCharts.toArchHomeomorph F
    (KPCuspLogShape.dimension_pos F H.totallyComplex)).symm z
  (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s v p.2 p.1.2).val q

structure StageConclusions : Prop where
  source : ∀ (s : ℂ) (v : S), L F ζ hζ U ι s v =
    (KPContFlatSourceRecipe.flatR F ζ hζ s (coreInclusion F ζ hζ U ι v)).val
  covariance : Covariance F ζ hζ U ι
  smooth_holomorphy : SmoothHolomorphy F ζ hζ U ι
  archimedean_parameter : ∀ (s : ℂ) (v : S)
    (u : NumberField.InfinitePlace F → ℝ) (g : KPGlobalTorusFunctionData.G F ζ hζ),
    L F ζ hζ U ι s v ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val * g) =
      Complex.exp ((1 + 2 * KPIncomingCasimir.nu s) * ((∑ v, u v : ℝ) : ℂ)) *
        L F ζ hζ U ι s v g
  incoming : ∀ (a : Cusps F ζ hζ C R P H U) (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S) (t : ℝ) (b : KPCuspCharts.Shape F),
    KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s v t b =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t •
        (KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b
  coefficient : ∀ (a : Cusps F ζ hζ C R P H U)
    (j : Fin (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).atlas.chartCount),
    (∀ (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S),
      IsLocallyConstant (fun b :
        (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).atlas.shapeLift j =>
          (KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b.val)) ∧
    (∀ b : (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).atlas.shapeLift j,
      DifferentiableOn ℂ
        (KPContFlatCuspCoefficientTransition.frameCoefficient F ζ hζ C R P H U a ι b.val)
        KPContinuation.spectralDomain)
  frame_recipe : ∀ (a : Cusps F ζ hζ C R P H U) (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S) (b : KPCuspCharts.Shape F),
    KPContFlatCuspCoefficientTransition.frameCoefficient F ζ hζ C R P H U a ι b s v =
      (KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b
  transition : ∀ (a : Cusps F ζ hζ C R P H U) (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (g : KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
    (b : KPCuspCharts.Shape F)
    (q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a),
    let B := KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v
    let Dₐ := KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a
    let T := (KPContFlatCuspIncomingEvaluation.frequencies F ζ hζ C R P H U a).constantSystem
    B.val (b + KPCuspLogShape.logarithm F H.totallyComplex Dₐ.E Dₐ.integralUnits
      (Additive.ofMul (Dₐ.ratio g))) = T.transport (Dₐ.ratio g) (B.val b) ∧
    (T.transport (Dₐ.ratio g) (B.val b)).val q =
      (KPCuspGenuineMonodromy.chi F ζ hζ
        (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a g) : ℂ) *
          (B.val b).val
            ((KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).monodromy g⁻¹ q)
  metric_radial : ∀ (a : Cusps F ζ hζ C R P H U) (s : ℂ),
    s ∈ KPContinuation.spectralDomain → ∀ (v : S) (p : KPCuspCharts.Coordinates F)
      (q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a),
    localLaplacian (KPCuspLogShape.dimension F)
      (incomingOnArch F ζ hζ C R P H U ι a s v q) (KPCuspCharts.toArch F p) =
        KPIncomingCasimir.radialLaplacian (Module.finrank ℚ F / 2)
          (fun t => (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s v t p.1.2).val q) p.2
  casimir : ∀ (a : Cusps F ζ hζ C R P H U) (s : ℂ),
    s ∈ KPContinuation.spectralDomain → ∀ (v : S)
      (q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a)
      (z : KPArch.Space (KPCuspLogShape.dimension F)),
    localLaplacian (KPCuspLogShape.dimension F)
      (incomingOnArch F ζ hζ C R P H U ι a s v q) z =
        KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
          incomingOnArch F ζ hζ C R P H U ι a s v q z
  rational_index : ∀ (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F),
    KPContFlatRationalCosetCovariance.rationalTerm F ζ hζ s (coreInclusion F ζ hζ U ι v) g
      (KPContFlatRationalCosetCovariance.cosetEquiv F ζ hζ
        (KPChamberBruhatTwoCells.rationalCoset F γ)) =
      L F ζ hζ U ι s v (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ γ * g)

private theorem lap_eq (d : ℕ) (f : KPArch.Space d → ℂ) (z : KPArch.Space d) :
    localLaplacian d f z = KPContFlatCuspCasimirSpecialization.Δloc d f z := by
  rfl
 theorem stageConclusions (hι : Function.Injective ι) : StageConclusions F ζ hζ C R P H U ι := by
  refine {
    source := sourceFlat_eq F ζ hζ C R P H U ι
    covariance := covariance F ζ hζ U ι
    smooth_holomorphy := smoothHolomorphy F ζ hζ U ι hι
    archimedean_parameter := ?_
    incoming := ?_
    coefficient := ?_
    frame_recipe := ?_
    transition := ?_
    metric_radial := ?_
    casimir := ?_
    rational_index := ?_ }
  · intro s v u g
    have he : 1 + 2 * KPIncomingCasimir.nu s = 4 / 3 + 2 * s := by
      unfold KPIncomingCasimir.nu
      ring
    rw [he]
    exact KPContFlatArchDiagonalMultiplier.flatR_covariance F ζ hζ s u
      (coreInclusion F ζ hζ U ι v) g
  · intro a s hs v t b
    simpa [KPIncomingCasimir.heightFactor, KPIncomingCasimir.nu] using
      incoming_formula F ζ hζ C R P H U ι a s hs v t b
  · intro a j
    exact ⟨fun s hs v => KPContFlatCuspCoefficientTransition.locally_parallel
      F ζ hζ C R P H U a ι s hs v j,
      fun b => KPContFlatCuspCoefficientTransition.frameCoefficient_holomorphic
        F ζ hζ C R P H U a ι j b⟩
  · intro a s hs v b
    exact KPContFlatCuspCoefficientTransition.frameCoefficient_formula
      F ζ hζ C R P H U a ι s hs v b
  · intro a s hs v g b q
    exact ⟨(KPContFlatCuspCoefficientTransition.transport_formula F ζ hζ C R P H U a ι
      s hs v g b).1,
      (KPContFlatCuspIncomingEvaluation.frequencies F ζ hζ C R P H U a).constantSystem.transition_formula
        g ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b) q⟩
  · intro a s hs v p q
    rw [lap_eq]
    exact KPContFlatCuspCasimirSpecialization.metric_radial_scalar F ζ hζ C R P H U ι a s hs v p q
  · intro a s hs v q z
    rw [lap_eq]
    exact KPContFlatCuspCasimirSpecialization.incoming_casimir_scalar F ζ hζ C R P H U ι a s hs v q z
  · intro s v g γ
    simpa only [KPContFlatRationalCosetCovariance.cosetEquiv_mk,
      KPContFlatRationalCosetCovariance.L, L,
      KPContFlatCommonLevelKernel.L, LinearMap.comp_apply, Submodule.coe_subtype] using
      KPContFlatRationalCosetCovariance.rationalTerm_transport_mk F ζ hζ s
        (coreInclusion F ζ hζ U ι v) g γ

end DedekindZetaZeroFree.KPContActualSphericalFlatStage

namespace DedekindZetaZeroFree

open KPContActualSphericalFlatStage

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

end DedekindZetaZeroFree

end
