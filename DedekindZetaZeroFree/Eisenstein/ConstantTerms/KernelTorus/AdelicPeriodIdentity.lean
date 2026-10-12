module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.UnipotentOrbit.FiniteRootInvariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicTraceQuotientCompatibility

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open KPContFlatCuspIncomingEvaluation
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S) (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
variable (a : Cusps F ζ hζ C R P H U) (t : ℝ) (b : KPCuspCharts.Shape F)
include hι hf hs in
private theorem kernel_period_sheet_eq (ε : rootsOfUnity 3 F) :
 (∫ z : KernelTorus F ζ hζ C R P H U a,
   KPContActualChamberNormalSeries.E F ζ hζ U ι f s (cuspGroup F ζ hζ C R P H U a t (Quotient.out z) b ε)
   ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
 (∫ q : KPCompactFourier.AdditiveQuotient F,
   KPContActualChamberNormalSeries.E F ζ hζ U ι f s
     (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * localGroup F ζ hζ C R P H U a t 0 b ε)
   ∂KPWildKernelUpperBound.quotientHaar F) := by
 obtain ⟨K,hc,ho,hroot,hkernel⟩ := actual_cusp_finite_kernel_level F ζ hζ C R P H U a
 let g := localGroup F ζ hζ C R P H U a t 0 b ε
 let G : KPCompactFourier.AdditiveQuotient F → ℂ := fun q =>
   KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
 have hG : Continuous G := actual_upper_orbit_continuous F ζ hζ U ι f hι hf s hs g
 have hinv : ∀q h, h ∈ finiteLevelImage K → G (q + h) = G q := by
   intro q h hh
   obtain ⟨z,hz,rfl⟩ := hh
   induction q using Quotient.inductionOn with | h x =>
     change G (QuotientAddGroup.mk x + QuotientAddGroup.mk (finiteParameter F z)) = G (QuotientAddGroup.mk x)
     rw [← QuotientAddGroup.mk_add]
     dsimp only [G]
     rw [actual_upper_orbit_mk F ζ hζ U ι f hι hf s hs g,
       actual_upper_orbit_mk F ζ hζ U ι f hι hf s hs g]
     exact actual_upper_orbit_finite_root_invariant F ζ hζ C R P H U ι f hι hf s hs a t b ε z (hroot z hz) x
 letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
 obtain ⟨D,hD,hfd⟩ := additiveProductHaar_exists_fundamentalDomain F (KPAdditiveHaar.finiteMeasure F)
 have hnorm : KPAdditiveHaar.finiteMeasure F (integralFiniteAdeles F : Set _) =
   ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|) :=
   (KPAdditiveHaar.finiteMeasure_integral_mass F).trans (KPAdditiveHaar.finiteMass_eq_discriminant F).1
 obtain ⟨GK,hGK,hformula,hint⟩ := finiteLevel_quotient_integral_torus_probability F
   (KPAdditiveHaar.finiteMeasure F) hnorm D hD hfd K hc ho G hG hinv
 obtain ⟨ν,hν,hprob⟩ := finiteLevel_torus_exists_haar_probability K hc ho
 letI := hν
 letI := hprob
 have hQ : additiveQuotientMeasureFromDomain F (KPAdditiveHaar.finiteMeasure F) D =
   KPWildKernelUpperBound.quotientHaar F := by
   obtain ⟨hhaar,hp,-⟩ := additiveQuotientMeasureFromDomain_haar_probability F (KPAdditiveHaar.finiteMeasure F) hnorm D hD hfd
   letI := hhaar
   letI := hp
   exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
 have hGI : (∫q, G q ∂KPWildKernelUpperBound.quotientHaar F) = ∫x,GK x ∂ν := by
   rw [← hQ]
   exact hint ν hν hprob
 let L := KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
   (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a)
 have hle := finiteLevelLattice_le_horizontal_of_rational_kernel F K L hkernel
 let p := mixedHorizontalQuotientMap F K L hle
 let φ : KernelTorus F ζ hζ C R P H U a → ℂ := fun z =>
   KPContActualChamberNormalSeries.E F ζ hζ U ι f s (cuspGroup F ζ hζ C R P H U a t (Quotient.out z) b ε)
 have hφ : Continuous φ := by
   simpa only [φ, KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
     iteratedDerivWithin_zero] using
     KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_continuous F ζ hζ C R P H U ι hι f hf a s hs t b ε
 have heq : GK = φ ∘ p := by
   funext q
   induction q using Quotient.inductionOn with | h x =>
     rw [hformula]
     dsimp only [Function.comp_def,p]
     rw [mixedHorizontalQuotientMap_mk]
     dsimp only [G,φ,g]
     change KPContActualChamberNormalSeries.E F ζ hζ U ι f s
       (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk
         (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x,0) : KPGlobalTorusFunctionData.Adeles F) : KPCompactFourier.AdditiveQuotient F)) *
         localGroup F ζ hζ C R P H U a t 0 b ε) = _
     rw [actual_upper_orbit_mk F ζ hζ U ι f hι hf s hs,
       actual_arch_root_orbit_coordinate F ζ hζ C R P H U ι f hι hf s hs]
     rw [RingEquiv.apply_symm_apply]
     rw [cuspGroup, (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1]
     have hrep := KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative F ζ hζ C R P H U ι hι f hf a s hs t
       (Quotient.out (QuotientAddGroup.mk (mixedToHorizontal F x) : KernelTorus F ζ hζ C R P H U a))
       (mixedToHorizontal F x) b ε (Quotient.out_eq _)
     simpa only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
       iteratedDerivWithin_zero, cuspGroup,
       (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1] using hrep.symm
 rw [hGI,heq]
 have hm := actual_kernelTorus_probabilityHaar_transport F ζ hζ C R P H U a K hc ho hle ν
 letI := finiteLevelLattice_discrete K hc ho
 letI : DiscreteTopology (finiteLevelLattice K).toAddSubgroup := inferInstanceAs (DiscreteTopology (finiteLevelLattice K))
 letI : IsClosed ((finiteLevelLattice K).toAddSubgroup : Set (mixedEmbedding.mixedSpace F)) := AddSubgroup.isClosed_of_discrete
 letI : BorelSpace (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup) := AddCosetSpace.borelSpace
 letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
 change (∫ z, φ z ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) = ∫x, φ (p x) ∂ν
 rw [← hm]
 exact integral_map (mixedHorizontalQuotientMap_continuous F K L hle).measurable.aemeasurable hφ.measurable.aestronglyMeasurable

theorem actual_projected_kernel_period_eq
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (t : ℝ) (b : KPCuspCharts.Shape F) :
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => ∫ z : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s
          (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a
            t (Quotient.out z) b ε)
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
    KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
      (fun ε => ∫ q : KPCompactFourier.AdditiveQuotient F,
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
            KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a
              t 0 b ε)
        ∂KPWildKernelUpperBound.quotientHaar F) := by
  have heq := funext (kernel_period_sheet_eq F ζ hζ C R P H U ι f hι hf s hs a t b)
  rw [heq]

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
