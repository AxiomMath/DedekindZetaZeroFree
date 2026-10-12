module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.MeanZero.CuspSectionCasimirEquation

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPContActualChamberMeanZeroAdapter

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)

open MeasureTheory Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
section CompactIntegration
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem partialJets_smooth (f : E → X → ℂ)
 (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) (n : ℕ) :
 ContDiff ℝ (⊤ : ℕ∞) (fun p : E × X => iteratedFDeriv ℝ n (fun g => f g p.2) p.1) := by
 induction n with
 | zero =>
   simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
   exact (continuousMultilinearCurryFin0 ℝ E ℂ).symm.contDiff.comp hf
 | succ n ih =>
   letI : TopologicalSpace (E [×(n+1)]→L[ℝ] ℂ) :=
     (inferInstance : NormedAddCommGroup (E [×(n+1)]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
   letI : TopologicalSpace (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
     (inferInstance : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
   simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def]
   let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) ℂ).symm
   let Lc : (E →L[ℝ] E [×n]→L[ℝ] ℂ) →L[ℝ] E [×(n+1)]→L[ℝ] ℂ :=
     { toLinearMap := L.toLinearEquiv.toLinearMap
       cont := by convert L.continuous using 1 }
   apply ContDiff.continuousLinearMap_comp (𝕜 := ℝ) (E := E × X)
     (F := E →L[ℝ] E [×n]→L[ℝ] ℂ) (G := E [×(n+1)]→L[ℝ] ℂ) (g := Lc)
   apply ContDiff.fderiv (f := fun p : E × X => fun g => iteratedFDeriv ℝ n (fun g => f g p.2) g)
   · exact ih.comp (contDiff_snd.prodMk (contDiff_fst.snd))
   · exact contDiff_fst
   · simp

private theorem periodic_integral_smooth [FiniteDimensional ℝ E]
    (L : AddSubgroup X) [CompactSpace (X ⧸ L)] [MeasurableSpace (X ⧸ L)] [BorelSpace (X ⧸ L)]
    (μ : Measure (X ⧸ L)) [IsProbabilityMeasure μ]
    (f : E → X → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f))
    (hrep : ∀ g x y, (QuotientAddGroup.mk x : X ⧸ L) = QuotientAddGroup.mk y → f g x = f g y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g => ∫ q, f g (Quotient.out q) ∂μ) ∧
      ∀ n g, iteratedFDeriv ℝ n (fun g => ∫ q, f g (Quotient.out q) ∂μ) g =
        ∫ q, iteratedFDeriv ℝ n (fun g => f g (Quotient.out q)) g ∂μ := by
  apply DedekindZetaZeroFree.KPCompactPeriod.compact_integral_smooth
  · intro q
    exact hf.comp (contDiff_id.prodMk contDiff_const)
  · intro n
    have hm := (IsOpenQuotientMap.id (X := E)).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := L))
    apply hm.continuous_comp_iff.mp
    have he (x : X) : (fun g => f g (Quotient.out (QuotientAddGroup.mk x : X ⧸ L))) =
        (fun g => f g x) := by
      funext g
      exact hrep g _ _ (Quotient.out_eq _)
    change Continuous (fun p : E × X =>
      iteratedFDeriv ℝ n (fun g => f g (Quotient.out (QuotientAddGroup.mk p.2 : X ⧸ L))) p.1)
    simp_rw [he]
    exact (partialJets_smooth f hf n).continuous

private theorem periodic_jet_integrable [FiniteDimensional ℝ E]
    (L : AddSubgroup X) [CompactSpace (X ⧸ L)] [MeasurableSpace (X ⧸ L)] [BorelSpace (X ⧸ L)]
    (μ : Measure (X ⧸ L)) [IsProbabilityMeasure μ]
    (f : E → X → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f))
    (hrep : ∀ g x y, (QuotientAddGroup.mk x : X ⧸ L) = QuotientAddGroup.mk y → f g x = f g y)
    (n : ℕ) (g : E) :
    Integrable (fun q => iteratedFDeriv ℝ n (fun w => f w (Quotient.out q)) g) μ := by
  have hm := (IsOpenQuotientMap.id (X := E)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := L))
  have he (x : X) : (fun g => f g (Quotient.out (QuotientAddGroup.mk x : X ⧸ L))) =
      (fun g => f g x) := by
    funext g
    exact hrep g _ _ (Quotient.out_eq _)
  have hc : Continuous (fun p : E × (X ⧸ L) =>
      iteratedFDeriv ℝ n (fun w => f w (Quotient.out p.2)) p.1) := by
    apply hm.continuous_comp_iff.mp
    change Continuous (fun p : E × X =>
      iteratedFDeriv ℝ n (fun g => f g (Quotient.out (QuotientAddGroup.mk p.2 : X ⧸ L))) p.1)
    simp_rw [he]
    exact (partialJets_smooth f hf n).continuous
  exact (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end CompactIntegration

open KPContFlatCuspCasimirSpecialization
private theorem second_eq_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f : E → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z v : E) :
 fderiv ℝ (fun y => fderiv ℝ f y v) z v = iteratedFDeriv ℝ 2 f z (fun _ => v) := by
 rw [iteratedFDeriv_two_apply]
 have hd := (hf.fderiv_right (m := 1) (by simp)).differentiable (by norm_num) z
 rw [fderiv_clm_apply hd (differentiableAt_const v)]
 simp
private theorem laplacian_jets (d : ℕ) (f : KPArch.Space d → ℂ)
 (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : KPArch.Space d) :
 KPContActualSphericalFlatStage.localLaplacian d f z =
 ∑ i : Fin d,
   (-(iteratedFDeriv ℝ 2 f z (fun _ => coordinateDirection d i 2)) +
   2 * iteratedFDeriv ℝ 1 f z (fun _ => coordinateDirection d i 2) -
   (KPArch.height (z i) ^ 2 : ℂ) *
     (iteratedFDeriv ℝ 2 f z (fun _ => coordinateDirection d i 0) +
      iteratedFDeriv ℝ 2 f z (fun _ => coordinateDirection d i 1))) := by
 change Δloc d f z = _
 rw [Δloc_coordinate_expression d f (hf.of_le (by norm_num))]
 simp_rw [second_eq_jet f hf, iteratedFDeriv_one_apply]
 simp only [smul_eq_mul, Complex.ofReal_pow]

private theorem localLaplacian_sub (d : ℕ) (f g : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : KPArch.Space d) :
    KPContActualSphericalFlatStage.localLaplacian d (fun y => f y - g y) z =
      KPContActualSphericalFlatStage.localLaplacian d f z -
        KPContActualSphericalFlatStage.localLaplacian d g z := by
  have hd (y) := hf.differentiable (by simp) y
  have he (y) := hg.differentiable (by simp) y
  have hj (i : Fin d) (j : Fin 3) :
      (fun y => fderiv ℝ (fun x => f x - g x) y (coordinateDirection d i j)) =
        (fun y => fderiv ℝ f y (coordinateDirection d i j) -
          fderiv ℝ g y (coordinateDirection d i j)) := by
    funext y
    have hh := congrArg (fun L : KPArch.Space d →L[ℝ] ℂ => L (coordinateDirection d i j))
      (fderiv_sub (hd y) (he y))
    exact hh
  have hdf (i : Fin d) (j : Fin 3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ f y (coordinateDirection d i j)) z := by
    exact ((hf.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by norm_num) z
  have hdg (i : Fin d) (j : Fin 3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ g y (coordinateDirection d i j)) z := by
    exact ((hg.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by norm_num) z
  change Δloc d (fun y => f y - g y) z = Δloc d f z - Δloc d g z
  rw [Δloc_coordinate_expression d _ ((hf.sub hg).of_le (by norm_num)),
    Δloc_coordinate_expression d f (hf.of_le (by norm_num)),
    Δloc_coordinate_expression d g (hg.of_le (by norm_num)), ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [hj]
  have hs (j : Fin 3) : fderiv ℝ
      (fun y => fderiv ℝ f y (coordinateDirection d i j) - fderiv ℝ g y (coordinateDirection d i j)) z =
      fderiv ℝ (fun y => fderiv ℝ f y (coordinateDirection d i j)) z -
        fderiv ℝ (fun y => fderiv ℝ g y (coordinateDirection d i j)) z := fderiv_sub (hdf i j) (hdg i j)
  have hfirst : fderiv ℝ (fun y => f y - g y) z = fderiv ℝ f z - fderiv ℝ g z :=
    fderiv_sub (hd z) (he z)
  rw [hs 2, hs 0, hs 1, hfirst]
  simp only [ContinuousLinearMap.sub_apply, smul_eq_mul]
  ring

section Helpers
variable (a : Cusps F ζ hζ C R P H U)
variable (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
 def wholeJet (k : ℕ) (s : ℂ) (z : KPArch.Space (d F)) : ℂ :=
  (KPContSectorScalarLineAlgebra.J F ζ hζ (level F ζ hζ C R P H U)
    (KPContActualChamberCasimirJets.coveredJet F ζ hζ C R P H U ι f hι hf k s)).val
      (z, KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1)

private theorem wholeJet_coordinates (k : ℕ) (s : ℂ) (hs : s ∈ V) (p : KPCuspCharts.Coordinates F) :
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (KPCuspCharts.toArch F p) =
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s p.2 p.1.1 p.1.2 1 := by
  unfold wholeJet
  rw [← KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection F ζ hζ (KPCuspCharts.toArch F p)]
  rw [← KPContSectorScalarLineAlgebra.group_lift_formula]
  rw [KPContActualChamberCasimirJets.coveredJet_projection F ζ hζ C R P H U ι f hι hf k s hs]
  change KPContActualChamberCasimirJets.jet F ζ hζ U ι f k s
    (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a p.2 p.1.1 p.1.2 1) =
    KPContActualChamberCasimirJets.jet F ζ hζ U ι f k s
    (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a p.2 p.1.1 p.1.2 1)
  unfold KPContActualChamberCasimirJets.jet
  apply iteratedDerivWithin_congr _ hs
  intro z hz
  exact ((KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf z hz).1
    (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) _).symm

private theorem wholeJet_smooth (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ContDiff ℝ (⊤ : ℕ∞) (wholeJet F ζ hζ C R P H U ι f a hι hf k s) := by
  exact ((KPContSectorSmoothFramesSupport.smooth_iff F ζ hζ (level F ζ hζ C R P H U)
    R P H (KPContActualChamberCasimirJets.coveredJet F ζ hζ C R P H U ι f hι hf k s)).mpr
      (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs))
        (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1)

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
    differentiableOn_pi.mpr (fun ε => kernel_integral_holomorphic F ζ hζ C R P H U ι f a hι hf t b ε)
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
  unfold meanZeroJetSheet
  change iteratedDerivWithin k
    ((fun z => KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 z t x b ε) -
      (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
          (fiberMeasure F ζ hζ C R P H U a) 0 z t b).val (QuotientAddGroup.mk x))) V s = _
  rw [iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (((sheet_holomorphic F ζ hζ C R P H U ι f a hι hf t x b ε).contDiffOn KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)
    ((((projection_holomorphic F ζ hζ C R P H U ι f a hι hf t b (QuotientAddGroup.mk x)).const_mul _).contDiffOn
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
  exact complement_jet F ζ hζ C R P H U ι f a hι hf k s hs p.2 p.1.1 p.1.2 1

include hι hf in
private theorem projection_rawMean (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ) (b : KPCuspCharts.Shape F) :
    (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
      (fiberMeasure F ζ hζ C R P H U a) k s t b).val 0 =
    ∫ q : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b 1
      ∂fiberMeasure F ζ hζ C R P H U a := by
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  rw [← KPContActualChamberCasimirJets.cusp_projection_commute F ζ hζ C R P H U ι f hι hf a
    (fiberMeasure F ζ hζ C R P H U a) k s hs,
    ← KPContActualChamberCasimirJets.cusp_integral_commute F ζ hζ C R P H U ι f hι hf a
    (fiberMeasure F ζ hζ C R P H U a) k s hs]
  exact iteratedDerivWithin_congr (fun z hz =>
    KPGlobalResidualConstruction.ActualMeanZeroSection.actualCuspSheet_projection_eq_rawMean
      F ζ hζ C R P H U a ι hι f hf z hz t b) hs

private theorem wholeJet_horizontal_representative (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (z : KPArch.Space (d F)) (x y : KPCuspCharts.Horizontal F)
    (hxy : (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = QuotientAddGroup.mk y) :
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (fun i => (x i, (z i).2)) =
      wholeJet F ζ hζ C R P H U ι f a hι hf k s (fun i => (y i, (z i).2)) := by
  let e := KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension
  obtain ⟨p, rfl⟩ := e.surjective z
  change wholeJet F ζ hζ C R P H U ι f a hι hf k s (KPCuspCharts.toArch F ((x,p.1.2),p.2)) =
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (KPCuspCharts.toArch F ((y,p.1.2),p.2))
  rw [wholeJet_coordinates F ζ hζ C R P H U ι f a hι hf k s hs,
    wholeJet_coordinates F ζ hζ C R P H U ι f a hι hf k s hs,
    ← KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs,
    ← KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs]
  exact iteratedDerivWithin_congr (fun z hz =>
    KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative
      F ζ hζ C R P H U ι hι f hf a z hz p.2 x y p.1.2 1 hxy) hs

private theorem parameterScalar_eq_whole_sub_rawMean (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    parameterScalar F ζ hζ C R P H U a ι f k s z =
      wholeJet F ζ hζ C R P H U ι f a hι hf k s z -
        ∫ q : KernelTorus F ζ hζ C R P H U a,
          wholeJet F ζ hζ C R P H U ι f a hι hf k s
            (fun i => (Quotient.out q i, (z i).2))
          ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  let e := KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension
  obtain ⟨p, rfl⟩ := e.surjective z
  change parameterScalar F ζ hζ C R P H U a ι f k s
    (KPCuspCharts.toArch F p) =
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (KPCuspCharts.toArch F p) -
      ∫ q : KernelTorus F ζ hζ C R P H U a,
        wholeJet F ζ hζ C R P H U ι f a hι hf k s
          (fun i => (Quotient.out q i, (KPCuspCharts.toArch F p i).2))
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a
  rw [parameterScalar_coordinates F ζ hζ C R P H U ι f a hι hf k s hs]
  unfold meanZeroJetSheet
  simp only [map_one, Units.val_one, one_mul]
  rw [(KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
    (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a)
    k s p.2 p.1.2).property.2 (QuotientAddGroup.mk p.1.1)]
  rw [projection_rawMean F ζ hζ C R P H U ι f a hι hf k s hs p.2 p.1.2]
  rw [wholeJet_coordinates F ζ hζ C R P H U ι f a hι hf k s hs]
  apply congrArg (fun c : ℂ =>
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s p.2 p.1.1 p.1.2 1 - c)
  apply integral_congr_ae
  filter_upwards [] with q
  change KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s
      p.2 (Quotient.out q) p.1.2 1 =
    wholeJet F ζ hζ C R P H U ι f a hι hf k s
      (KPCuspCharts.toArch F ((Quotient.out q,p.1.2),p.2))
  exact (wholeJet_coordinates F ζ hζ C R P H U ι f a hι hf k s hs
    ((Quotient.out q,p.1.2),p.2)).symm

section JetSpatial
variable (k : ℕ) (s : ℂ) (hs : s ∈ V)
include hι hf hs
private theorem componentJet_casimir
 (i : Fin (H.atlas (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U)).componentCount)
 (z : KPArch.Space (KPCuspLogShape.dimension F)) :
 KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s i).val z =
 KPContActualChamberCasimirJets.lambda F s *
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s i).val z +
   ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s *
     (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf (k-j) s i).val z := by
 obtain ⟨O⟩ := KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
   (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U) R P H i z
 let p := KPContCotangentActualOverlap.placeEquiv F ζ hζ
 let a : KPContActualChamberCasimirJets.Frame F ζ hζ C R P H U i :=
   { kind := .orbifold z O
     places := p
     splitting := fun _ => 1
     splitting_locallyConstant := IsLocallyConstant.const 1 }
 let x := KPContCotangentActualOverlap.labeledAInv p z
 have hxz : KPContCotangentActualOverlap.labeledA p x = z := by
   funext k
   simp only [x, KPContCotangentActualOverlap.labeledAInv, KPContCotangentActualOverlap.labeledA]
   rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
 have hx : x ∈ a.omega := by
   change KPContCotangentActualOverlap.labeledA p x ∈ O.neighborhood
   rw [hxz]
   exact O.center_mem
 have hh := KPContActualChamberCasimirJets.casimir_jets F ζ hζ C R P H U ι f hι hf k s hs a x hx
 have he (n : ℕ) : KPContActualChamberCasimirJets.frameJet F ζ hζ C R P H U ι f hι hf n s a =
   fun y => (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf n s i).val
     (KPContCotangentActualOverlap.labeledA p y) := by
   funext y
   simp [KPContActualChamberCasimirJets.frameJet, KPContCotangentActualOverlap.LiftedChart.coefficient,
     a, KPContCotangentActualOverlap.ChartKind.representative]
 simp_rw [he] at hh
 have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv _ _ p
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s i).val
   (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs i) x
 change _ = HyperbolicChart.laplacian _ (fun y =>
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s i).val
     (KPContCotangentActualOverlap.labeledA p y)) x at hb
 rw [←hb] at hh
 change KPContActualSphericalFlatStage.localLaplacian _ _
   (KPContCotangentActualOverlap.labeledA p x) = _ at hh
 simpa only [hxz] using hh

private theorem wholeJet_component (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    wholeJet F ζ hζ C R P H U ι f a hι hf k s z =
      (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s a.1).val
        (KPCuspSiegel.action F (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) z) := by
  let e := KPContActualChamberCasimirJets.coveredJet F ζ hζ C R P H U ι f hι hf k s
  let j := KPContSectorScalarLineAlgebra.J F ζ hζ (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U) e
  have hr := j.property.1 z (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1)
    (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a)
  have hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) * KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1 =
      (KPContFlatCuspIncomingEvaluation.atlas F ζ hζ C R P H U).representative a.1 := by
    simp [KPContFlatCuspIncomingEvaluation.finiteRepresentative, mul_assoc]
  rw [hc] at hr
  rw [wholeJet, KPContActualChamberCasimirJets.lineJet,
    KPContSectorScalarLineAlgebra.S_apply]
  exact hr.symm

include hs in

private theorem wholeJet_casimir (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (wholeJet F ζ hζ C R P H U ι f a hι hf k s) z =
    KPContActualChamberCasimirJets.lambda F s *
      wholeJet F ζ hζ C R P H U ι f a hι hf k s z +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s *
        wholeJet F ζ hζ C R P H U ι f a hι hf (k-j) s z := by
  have he (n : ℕ) := funext (wholeJet_component F ζ hζ C R P H U ι f a hι hf n s hs)
  simp_rw [he]
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a)
  have hact : (fun y : KPArch.Space (KPCuspLogShape.dimension F) =>
      KPCuspSiegel.action F (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) y) =
    KPArch.productAction (KPCuspLogShape.dimension F)
      (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) := by
    funext y
    rw [←hB]
    exact KPCuspSiegel.action_mk F B y
  simp only [show ∀ y, KPCuspSiegel.action F (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) y =
    KPArch.productAction (KPCuspLogShape.dimension F)
      (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) y
      from fun y => congrFun hact y]
  rw [KPContArchLaplacianNaturality.pullback _ _ _
    (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs a.1)]
  exact componentJet_casimir F ζ hζ C R P H U ι f hι hf k s hs a.1 _

 def horizontalInsertion (x : KPCuspCharts.Horizontal F) :
    KPArch.Space (KPCuspLogShape.dimension F) := fun i => (x i, 0)
 def shiftedMean (z : KPArch.Space (KPCuspLogShape.dimension F)) : ℂ :=
  ∫ q : KernelTorus F ζ hζ C R P H U a,
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (z + horizontalInsertion F (Quotient.out q))
      ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a

include hs in
private theorem shiftedMean_eq_rawMean (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    shiftedMean F ζ hζ C R P H U ι f a hι hf k s z =
      ∫ q : KernelTorus F ζ hζ C R P H U a,
        wholeJet F ζ hζ C R P H U ι f a hι hf k s
          (fun i => (Quotient.out q i, (z i).2))
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  let φ : KernelTorus F ζ hζ C R P H U a → ℂ := fun q =>
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (fun i => (Quotient.out q i, (z i).2))
  let x : KPCuspCharts.Horizontal F := fun i => (z i).1
  have he (q : KernelTorus F ζ hζ C R P H U a) :
      φ (q + QuotientAddGroup.mk x) =
        wholeJet F ζ hζ C R P H U ι f a hι hf k s (z + horizontalInsertion F (Quotient.out q)) := by
    dsimp only [φ]
    have hh := wholeJet_horizontal_representative F ζ hζ C R P H U ι f a hι hf k s hs z
      (Quotient.out (q + QuotientAddGroup.mk x)) (Quotient.out q + x)
      (by
        rw [QuotientAddGroup.mk_add]
        exact (Quotient.out_eq (q + QuotientAddGroup.mk x)).trans
          (congrArg (fun r : KernelTorus F ζ hζ C R P H U a => r + QuotientAddGroup.mk x)
            (Quotient.out_eq q).symm))
    apply hh.trans
    apply congrArg (wholeJet F ζ hζ C R P H U ι f a hι hf k s)
    funext i
    apply Prod.ext <;> simp [horizontalInsertion, x, add_comm]
  unfold shiftedMean
  rw [show (fun q : KernelTorus F ζ hζ C R P H U a =>
    wholeJet F ζ hζ C R P H U ι f a hι hf k s (z + horizontalInsertion F (Quotient.out q))) =
      (fun q => φ (q + QuotientAddGroup.mk x)) from funext (fun q => (he q).symm)]
  exact integral_add_right_eq_self φ (QuotientAddGroup.mk x)

include hs in
private theorem shiftedMean_spatial_jets :
    ContDiff ℝ (⊤ : ℕ∞) (shiftedMean F ζ hζ C R P H U ι f a hι hf k s) ∧
      ∀ n : ℕ, ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        iteratedFDeriv ℝ n (shiftedMean F ζ hζ C R P H U ι f a hι hf k s) z =
          ∫ q : KernelTorus F ζ hζ C R P H U a,
            iteratedFDeriv ℝ n
              (fun w => wholeJet F ζ hζ C R P H U ι f a hι hf k s
                (w + horizontalInsertion F (Quotient.out q))) z
            ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  apply periodic_integral_smooth
    (E := KPArch.Space (KPCuspLogShape.dimension F)) (X := KPCuspCharts.Horizontal F)
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice
      (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a) (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
      (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a)))
    (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a)
    (fun z x => wholeJet F ζ hζ C R P H U ι f a hι hf k s (z + horizontalInsertion F x))
  · apply (wholeJet_smooth F ζ hζ C R P H U ι f a hι hf k s hs).comp
    apply contDiff_fst.add
    apply contDiff_pi.mpr
    intro i
    exact (((contDiff_apply ℝ ℂ i).comp contDiff_snd).prodMk contDiff_const)
  · intro z x y hxy
    have hh := wholeJet_horizontal_representative F ζ hζ C R P H U ι f a hι hf k s hs z
      (x := (fun i => (z i).1) + x) (y := (fun i => (z i).1) + y)
      (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, hxy])
    have hz (u : KPCuspCharts.Horizontal F) :
        z + horizontalInsertion F u = (fun i => ((z i).1 + u i, (z i).2)) := by
      funext i
      apply Prod.ext <;> simp [horizontalInsertion]
    rw [hz x, hz y]
    exact hh

include hs in
private theorem shiftedMean_jet_integrable (n : ℕ) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    Integrable (fun q : KernelTorus F ζ hζ C R P H U a =>
      iteratedFDeriv ℝ n
        (fun w => wholeJet F ζ hζ C R P H U ι f a hι hf k s
          (w + horizontalInsertion F (Quotient.out q))) z)
      (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  apply periodic_jet_integrable
    (E := KPArch.Space (KPCuspLogShape.dimension F)) (X := KPCuspCharts.Horizontal F)
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice
      (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a) (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
      (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a)))
    (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a)
    (fun z x => wholeJet F ζ hζ C R P H U ι f a hι hf k s (z + horizontalInsertion F x))
    (n := n) (g := z)
  · apply (wholeJet_smooth F ζ hζ C R P H U ι f a hι hf k s hs).comp
    apply contDiff_fst.add
    apply contDiff_pi.mpr
    intro i
    exact (((contDiff_apply ℝ ℂ i).comp contDiff_snd).prodMk contDiff_const)
  · intro z x y hxy
    have hh := wholeJet_horizontal_representative F ζ hζ C R P H U ι f a hι hf k s hs z
      (x := (fun i => (z i).1) + x) (y := (fun i => (z i).1) + y)
      (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, hxy])
    have hz (u : KPCuspCharts.Horizontal F) :
        z + horizontalInsertion F u = (fun i => ((z i).1 + u i, (z i).2)) := by
      funext i
      apply Prod.ext <;> simp [horizontalInsertion]
    rw [hz x, hz y]
    exact hh

include hs in
private theorem shiftedMean_evaluated_jet (n : ℕ)
    (z : KPArch.Space (KPCuspLogShape.dimension F))
    (m : Fin n → KPArch.Space (KPCuspLogShape.dimension F)) :
    iteratedFDeriv ℝ n (shiftedMean F ζ hζ C R P H U ι f a hι hf k s) z m =
      ∫ q : KernelTorus F ζ hζ C R P H U a,
        iteratedFDeriv ℝ n (wholeJet F ζ hζ C R P H U ι f a hι hf k s)
          (z + horizontalInsertion F (Quotient.out q)) m
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  rw [(shiftedMean_spatial_jets F ζ hζ C R P H U ι f a hι hf k s hs).2 n z,
    ContinuousMultilinearMap.integral_apply
      (shiftedMean_jet_integrable F ζ hζ C R P H U ι f a hι hf k s hs n z)]
  simp only [iteratedFDeriv_comp_add_right]

include hs in
private theorem shiftedMean_laplacian_commute (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (shiftedMean F ζ hζ C R P H U ι f a hι hf k s) z =
      ∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
          (wholeJet F ζ hζ C R P H U ι f a hι hf k s)
          (z + horizontalInsertion F (Quotient.out q))
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  let μ := KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a
  let w := wholeJet F ζ hζ C R P H U ι f a hι hf k s
  let D := KPCuspLogShape.dimension F
  let A (n : ℕ) (i : Fin D) (j : Fin 3) (q : KernelTorus F ζ hζ C R P H U a) : ℂ :=
    iteratedFDeriv ℝ n w (z + horizontalInsertion F (Quotient.out q))
      (fun _ => coordinateDirection D i j)
  have hAi (n : ℕ) (i : Fin D) (j : Fin 3) : Integrable (A n i j) μ := by
    have hi := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => KPArch.Space D) ℂ
      (fun _ => coordinateDirection D i j)).integrable_comp
      (shiftedMean_jet_integrable F ζ hζ C R P H U ι f a hι hf k s hs n z)
    simpa only [iteratedFDeriv_comp_add_right, ContinuousMultilinearMap.apply_apply] using hi
  have hheight (q : KernelTorus F ζ hζ C R P H U a) (i : Fin D) :
      KPArch.height ((z + horizontalInsertion F (Quotient.out q)) i) = KPArch.height (z i) := by
    simp [KPArch.height, horizontalInsertion]
  rw [laplacian_jets _ _ (shiftedMean_spatial_jets F ζ hζ C R P H U ι f a hι hf k s hs).1]
  simp_rw [shiftedMean_evaluated_jet F ζ hζ C R P H U ι f a hι hf k s hs]
  simp_rw [laplacian_jets _ _ (wholeJet_smooth F ζ hζ C R P H U ι f a hι hf k s hs), hheight]
  change (∑ i : Fin D, (-(∫ q, A 2 i 2 q ∂μ) + 2 * (∫ q, A 1 i 2 q ∂μ) -
      (KPArch.height (z i) : ℂ)^2 * ((∫ q, A 2 i 0 q ∂μ) + (∫ q, A 2 i 1 q ∂μ)))) =
    ∫ q, ∑ i : Fin D, (-A 2 i 2 q + 2 * A 1 i 2 q -
      (KPArch.height (z i) : ℂ)^2 * (A 2 i 0 q + A 2 i 1 q)) ∂μ
  have hi (i : Fin D) : Integrable (fun q => -A 2 i 2 q + 2 * A 1 i 2 q -
      (KPArch.height (z i) : ℂ)^2 * (A 2 i 0 q + A 2 i 1 q)) μ :=
    ((hAi 2 i 2).neg.add ((hAi 1 i 2).const_mul 2)).sub
      (((hAi 2 i 0).add (hAi 2 i 1)).const_mul _)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hsub : Integrable (fun q => -A 2 i 2 q + 2 * A 1 i 2 q) μ :=
    (hAi 2 i 2).neg.add ((hAi 1 i 2).const_mul 2)
  have hmul : Integrable (fun q => (KPArch.height (z i) : ℂ)^2 * (A 2 i 0 q + A 2 i 1 q)) μ :=
    ((hAi 2 i 0).add (hAi 2 i 1)).const_mul _
  rw [integral_sub hsub hmul]
  have hn : Integrable (fun q => -A 2 i 2 q) μ := (hAi 2 i 2).neg
  have hc : Integrable (fun q => (2 : ℂ) * A 1 i 2 q) μ := (hAi 1 i 2).const_mul 2
  rw [integral_add hn hc, integral_neg, integral_const_mul, integral_const_mul,
    integral_add (hAi 2 i 0) (hAi 2 i 1)]

private theorem shiftedMean_integrable (z : KPArch.Space (d F)) :
    Integrable (fun q : KernelTorus F ζ hζ C R P H U a =>
      wholeJet F ζ hζ C R P H U ι f a hι hf k s (z + horizontalInsertion F (Quotient.out q)))
      (fiberMeasure F ζ hζ C R P H U a) := by
  have hi := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => KPArch.Space (d F)) ℂ
    (fun _ => 0)).integrable_comp
    (shiftedMean_jet_integrable F ζ hζ C R P H U ι f a hι hf k s hs 0 z)
  simpa only [ContinuousMultilinearMap.apply_apply, iteratedFDeriv_zero_apply] using hi

private theorem shiftedMean_casimir (z : KPArch.Space (d F)) :
    KPContActualSphericalFlatStage.localLaplacian (d F)
      (shiftedMean F ζ hζ C R P H U ι f a hι hf k s) z =
      KPContActualChamberCasimirJets.lambda F s * shiftedMean F ζ hζ C R P H U ι f a hι hf k s z +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s *
        shiftedMean F ζ hζ C R P H U ι f a hι hf (k-j) s z := by
  rw [shiftedMean_laplacian_commute F ζ hζ C R P H U ι f a hι hf k s hs]
  simp_rw [wholeJet_casimir F ζ hζ C R P H U ι f a hι hf k s hs]
  rw [integral_add ((shiftedMean_integrable F ζ hζ C R P H U ι f a hι hf k s hs z).const_mul _)
    (integrable_finsetSum _ (fun j _ =>
      (shiftedMean_integrable F ζ hζ C R P H U ι f a hι hf (k-j) s hs z).const_mul _)),
    integral_finsetSum _ (fun j _ =>
      (shiftedMean_integrable F ζ hζ C R P H U ι f a hι hf (k-j) s hs z).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

private theorem parameterScalar_eq_sub_shifted :
    parameterScalar F ζ hζ C R P H U a ι f k s =
      fun z => wholeJet F ζ hζ C R P H U ι f a hι hf k s z -
        shiftedMean F ζ hζ C R P H U ι f a hι hf k s z := by
  funext z
  rw [parameterScalar_eq_whole_sub_rawMean F ζ hζ C R P H U ι f a hι hf k s hs,
    shiftedMean_eq_rawMean F ζ hζ C R P H U ι f a hι hf k s hs]

private theorem parameterScalar_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (parameterScalar F ζ hζ C R P H U a ι f k s) := by
  rw [parameterScalar_eq_sub_shifted F ζ hζ C R P H U ι f a hι hf k s hs]
  exact (wholeJet_smooth F ζ hζ C R P H U ι f a hι hf k s hs).sub
    (shiftedMean_spatial_jets F ζ hζ C R P H U ι f a hι hf k s hs).1

private theorem parameterScalar_casimir (z : KPArch.Space (d F)) :
    KPContActualSphericalFlatStage.localLaplacian (d F)
      (parameterScalar F ζ hζ C R P H U a ι f k s) z =
      KPContActualChamberCasimirJets.lambda F s * parameterScalar F ζ hζ C R P H U a ι f k s z +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s *
        parameterScalar F ζ hζ C R P H U a ι f (k-j) s z := by
  have he (n : ℕ) := parameterScalar_eq_sub_shifted F ζ hζ C R P H U ι f a hι hf n s hs
  rw [he k, localLaplacian_sub _ _ _
    (wholeJet_smooth F ζ hζ C R P H U ι f a hι hf k s hs)
    (shiftedMean_spatial_jets F ζ hζ C R P H U ι f a hι hf k s hs).1,
    wholeJet_casimir F ζ hζ C R P H U ι f a hι hf k s hs,
    shiftedMean_casimir F ζ hζ C R P H U ι f a hι hf k s hs]
  simp_rw [he, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

private theorem parameterScalar_jet (z : KPArch.Space (d F)) :
    iteratedDerivWithin k (fun w => parameterScalar F ζ hζ C R P H U a ι f 0 w z) V s =
      parameterScalar F ζ hζ C R P H U a ι f k s z := by
  simp only [parameterScalar, iteratedDerivWithin_zero]

private theorem parameterScalar_fiber (z : KPArch.Space (d F)) :
    parameterScalar F ζ hζ C R P H U a ι f k s z ∈
      KPCuspGenuineMonodromy.scalarFiber F ζ hζ (level F ζ hζ C R P H U) := by
  intro ε hε
  rw [← parameterScalar_jet F ζ hζ C R P H U ι f a hι hf k s hs,
    ← iteratedDerivWithin_const_mul_field]
  exact iteratedDerivWithin_congr (fun w hw =>
    KPGlobalResidualConstruction.ActualMeanZeroSection.actual_parameterScalar_zero_fiber
      F ζ hζ C R P H U a ι hι f hf w hw z ε hε) hs

set_option backward.isDefEq.respectTransparency true in
private theorem parameterScalar_equivariant
    (h : (KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a).parabolicGroup)
    (z : KPArch.Space (d F)) :
    parameterScalar F ζ hζ C R P H U a ι f k s
      (KPCuspSiegel.action F h.val z) =
      (KPCuspGenuineMonodromy.chi F ζ hζ
        ((KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a).rho h) : ℂ) *
      parameterScalar F ζ hζ C R P H U a ι f k s z := by
  have he : Set.EqOn
      (fun w => parameterScalar F ζ hζ C R P H U a ι f 0 w
        (KPCuspSiegel.action F h.val z))
      (fun w => (KPCuspGenuineMonodromy.chi F ζ hζ
        ((KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a).rho h) : ℂ) *
        parameterScalar F ζ hζ C R P H U a ι f 0 w z) V := by
    intro w hw
    exact KPGlobalResidualConstruction.ActualMeanZeroSection.actual_parameterScalar_zero_equivariant
      F ζ hζ C R P H U a ι hι f hf w hw h z
  have hd := iteratedDerivWithin_congr (n := k) he hs
  rw [iteratedDerivWithin_const_mul_field,
    parameterScalar_jet F ζ hζ C R P H U ι f a hι hf k s hs,
    parameterScalar_jet F ζ hζ C R P H U ι f a hι hf k s hs] at hd
  exact hd

private theorem wholeJet_raw_integrable (z : KPArch.Space (d F)) :
    Integrable (fun q : KernelTorus F ζ hζ C R P H U a =>
      wholeJet F ζ hζ C R P H U ι f a hι hf k s (fun i => (Quotient.out q i, (z i).2)))
      (fiberMeasure F ζ hζ C R P H U a) := by
  have hi := shiftedMean_integrable F ζ hζ C R P H U ι f a hι hf k s hs (fun i => (0,(z i).2))
  have he (q : KernelTorus F ζ hζ C R P H U a) :
      (fun i => (0, (z i).2)) + horizontalInsertion F (Quotient.out q) =
        (fun i => (Quotient.out q i, (z i).2)) := by
    funext i
    apply Prod.ext <;> simp [horizontalInsertion]
  simp_rw [he] at hi
  exact hi

private theorem sheet_raw_integrable (t : ℝ) (b : KPCuspCharts.Shape F) :
    Integrable (fun q : KernelTorus F ζ hζ C R P H U a =>
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b 1)
      (fiberMeasure F ζ hζ C R P H U a) := by
  have hi := wholeJet_raw_integrable F ζ hζ C R P H U ι f a hι hf k s hs
    (KPCuspCharts.toArch F ((0,b),t))
  have he (q : KernelTorus F ζ hζ C R P H U a) :
      wholeJet F ζ hζ C R P H U ι f a hι hf k s
        (fun i => (Quotient.out q i, (KPCuspCharts.toArch F ((0,b),t) i).2)) =
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b 1 :=
    wholeJet_coordinates F ζ hζ C R P H U ι f a hι hf k s hs ((Quotient.out q,b),t)
  simp_rw [he] at hi
  exact hi

private theorem meanZeroJet_rawMean_zero (t : ℝ) (b : KPCuspCharts.Shape F) :
    (∫ q : KernelTorus F ζ hζ C R P H U a,
      meanZeroJetSheet F ζ hζ C R P H U a ι f k s t (Quotient.out q) b 1
      ∂fiberMeasure F ζ hζ C R P H U a) = 0 := by
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  unfold meanZeroJetSheet
  simp only [map_one, Units.val_one, one_mul]
  simp_rw [(KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
    (fiberMeasure F ζ hζ C R P H U a) k s t b).property.2]
  rw [integral_sub (sheet_raw_integrable F ζ hζ C R P H U ι f a hι hf k s hs t b)
    (integrable_const _), integral_const,
    projection_rawMean F ζ hζ C R P H U ι f a hι hf k s hs t b]
  simp only [probReal_univ, one_smul, sub_self]

private theorem section_torusSlice {T : ℝ}
    (v : KPMeanZeroWeightedEnergy.Section
      (KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a) T)
    (hv : v.val = parameterScalar F ζ hζ C R P H U a ι f k s)
    (b : KPCuspCharts.Shape F) (t : Set.Ioi T)
    (q : (KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a).KernelTorus) :
    v.torusSlice b t q = meanZeroJetSheet F ζ hζ C R P H U a ι f k s t.val (Quotient.out q) b 1 := by
  have hr := (KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a).monodromy.realization_formula
    ((KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a).monodromy.realization.symm (v.horizontalSlice b t))
    (Quotient.out q)
  simp only [LinearEquiv.apply_symm_apply, Quotient.out_eq] at hr
  change v.scalar (((Quotient.out q), b), t.val) = v.torusSlice b t q at hr
  rw [← hr]
  unfold KPMeanZeroWeightedEnergy.Section.scalar
  rw [hv, parameterScalar_coordinates F ζ hζ C R P H U ι f a hι hf k s hs]

private theorem section_rawMeanZero {T : ℝ}
    (v : KPMeanZeroWeightedEnergy.Section
      (KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a) T)
    (hv : v.val = parameterScalar F ζ hζ C R P H U a ι f k s) :
    KPMeanZeroWeightedEnergy.MeanZero
      (KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a)
      (fiberMeasure F ζ hζ C R P H U a) v := by
  intro b t
  unfold KPMeanZeroWeightedEnergy.average
  simp_rw [section_torusSlice F ζ hζ C R P H U ι f a hι hf k s hs v hv]
  exact meanZeroJet_rawMean_zero F ζ hζ C R P H U ι f a hι hf k s hs t.val b

end JetSpatial

end Helpers

theorem actual_meanZero_jet_sections
    (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U) (s : ℂ) (hs : s ∈ V) (T : ℝ) :
    let E : KPMeanZeroWeightedEnergy.End F ζ hζ H.totallyComplex
        (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U) :=
      { atlas := KPContFlatCuspIncomingEvaluation.atlas F ζ hζ C R P H U
        component := a.1
        cusp := a.2 }
    ∃ v : ℕ → KPMeanZeroWeightedEnergy.Section E T,
      (∀ k, (v k).val = parameterScalar F ζ hζ C R P H U a ι f k s) ∧
      (∀ k, KPMeanZeroWeightedEnergy.MeanZero E
        (fiberMeasure F ζ hζ C R P H U a) (v k)) ∧
      ∀ k (p : KPCuspCharts.Coordinates F), T < p.2 →
        (v k).laplacian p = KPContActualChamberCasimirJets.lambda F s * (v k).scalar p +
          ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
            KPContActualChamberCasimirJets.lambdaJet F j s * (v (k-j)).scalar p := by
  let E := KPGlobalResidualConstruction.ActualMeanZeroSection.actualEnd F ζ hζ C R P H U a
  let v (k : ℕ) : KPMeanZeroWeightedEnergy.Section E T :=
    { val := parameterScalar F ζ hζ C R P H U a ι f k s
      smooth := (parameterScalar_smooth F ζ hζ C R P H U ι f a hι hf k s hs).contDiffOn
      fiber := fun z _ => parameterScalar_fiber F ζ hζ C R P H U ι f a hι hf k s hs z
      equivariant := fun h z _ =>
        parameterScalar_equivariant F ζ hζ C R P H U ι f a hι hf k s hs h z }
  refine ⟨v, fun _ => rfl, ?_, ?_⟩
  · intro k
    exact section_rawMeanZero F ζ hζ C R P H U ι f a hι hf k s hs (v k) rfl
  · intro k p _
    unfold KPMeanZeroWeightedEnergy.Section.laplacian KPMeanZeroWeightedEnergy.Section.scalar
    change HyperbolicChart.laplacian (d F)
      (parameterScalar F ζ hζ C R P H U a ι f k s ∘ KPMeanZeroWeightedEnergy.archCoordinates (d F))
      (KPMeanZeroWeightedEnergy.realCoordinates (d F) (KPCuspCharts.toArch F p)) = _
    have hb := KPContArchLaplacianCoordinateBridge.bridge F
      (parameterScalar F ζ hζ C R P H U a ι f k s)
      (parameterScalar_smooth F ζ hζ C R P H U ι f a hι hf k s hs)
      (KPCuspCharts.toArch F p)
    change KPContActualSphericalFlatStage.localLaplacian (d F)
        (parameterScalar F ζ hζ C R P H U a ι f k s) (KPCuspCharts.toArch F p) =
      HyperbolicChart.laplacian (d F)
        (parameterScalar F ζ hζ C R P H U a ι f k s ∘ KPMeanZeroWeightedEnergy.archCoordinates (d F))
        (KPMeanZeroWeightedEnergy.realCoordinates (d F) (KPCuspCharts.toArch F p)) at hb
    rw [← hb]
    exact parameterScalar_casimir F ζ hζ C R P H U ι f a hι hf k s hs (KPCuspCharts.toArch F p)

end DedekindZetaZeroFree.KPContActualChamberMeanZeroAdapter

end
