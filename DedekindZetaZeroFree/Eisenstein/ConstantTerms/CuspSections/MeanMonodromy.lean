module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspSections.MeanZeroProjection

@[expose] public section

section
noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (cusp : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
open KPContFlatCuspIncomingEvaluation

theorem actual_monodromy_preserves_fiberMeasure (s : stabilizer F ζ hζ C R P H U cusp) :
 MeasurePreserving ((monodromy F ζ hζ C R P H U cusp).monodromy s)
 (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U cusp)
 (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U cusp) := by
 let D := parabolic F ζ hζ C R P H U cusp
 let M0 := monodromy F ζ hζ C R P H U cusp
 let μ := KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U cusp
 letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U cusp
 letI := M0.compact
 letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U cusp
 letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U cusp
 let M := M0.monodromy s
 let e : KernelTorus F ζ hζ C R P H U cusp ≃ₜ KernelTorus F ζ hζ C R P H U cusp :=
   M.trans (Homeomorph.addRight (-M 0))
 have hadd : ∀x y,e (x+y)=e x+e y := by
   intro x y
   induction x using Quotient.inductionOn with | h x =>
     induction y using Quotient.inductionOn with | h y =>
       obtain ⟨A,hA,hc⟩ := D.upper s.val s.property
       change M (QuotientAddGroup.mk x + QuotientAddGroup.mk y) + -M 0 =
         (M (QuotientAddGroup.mk x)+ -M 0)+(M (QuotientAddGroup.mk y)+ -M 0)
       simp only [←sub_eq_add_neg]
       rw [←QuotientAddGroup.mk_add]
       have hz : (0:KernelTorus F ζ hζ C R P H U cusp) = QuotientAddGroup.mk (0:KPCuspCharts.Horizontal F) := rfl
       simp only [M,hz,M0.monodromy_formula s A _ hA hc]
       simp only [Pi.zero_apply,mul_zero,zero_add]
       rw [←QuotientAddGroup.mk_sub,←QuotientAddGroup.mk_sub,←QuotientAddGroup.mk_sub,←QuotientAddGroup.mk_add]
       congr 1
       ext i
       simp only [Pi.sub_apply,Pi.add_apply]
       ring
 let a : KernelTorus F ζ hζ C R P H U cusp ≃ₜ+ KernelTorus F ζ hζ C R P H U cusp :=
   ⟨{e.toEquiv with map_add':=hadd},e.continuous,e.symm.continuous⟩
 letI : (μ.map a).IsAddHaarMeasure := a.isAddHaarMeasure_map μ
 letI : IsProbabilityMeasure (μ.map a) := (Measure.isProbabilityMeasure_map_iff a.continuous.measurable.aemeasurable).mpr inferInstance
 have ha : MeasurePreserving a μ μ := ⟨a.continuous.measurable,Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
 have hp := (measurePreserving_add_right μ (M 0)).comp ha
 convert hp using 1
 ext z
 change M z = (M z + -M 0)+M 0
 abel
end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection

end

end

section
noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : Cusps F ζ hζ C R P H U)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s:ℂ) (hs:s∈KPContActualChamberNormalSeries.V) (t:ℝ) (b:KPCuspCharts.Shape F)
include hι hf hs in
theorem actualCuspSheet_rawMean_unit_covariance (h:stabilizer F ζ hζ C R P H U a) :
 let D := parabolic F ζ hζ C R P H U a
 let b' := b + KPCuspLogShape.logarithm F H.totallyComplex D.E D.integralUnits (Additive.ofMul (D.ratio h))
 (∫z:KernelTorus F ζ hζ C R P H U a,
   KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b' 1
   ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
 (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a h):ℂ)*
 (∫z:KernelTorus F ζ hζ C R P H U a,
   KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
   ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) := by
 dsimp only
 let D := parabolic F ζ hζ C R P H U a
 let b' := b + KPCuspLogShape.logarithm F H.totallyComplex D.E D.integralUnits (Additive.ofMul (D.ratio h))
 let M := (monodromy F ζ hζ C R P H U a).monodromy h
 let φ : KPCuspCharts.Shape F → KernelTorus F ζ hζ C R P H U a → ℂ := fun b z =>
   KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
 have hm (z:KernelTorus F ζ hζ C R P H U a) : φ b' (M z) =
   (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a h):ℂ)*φ b z := by
   obtain ⟨A,hA,hc⟩ := D.upper h h.property
   let x := Quotient.out z
   let x' : KPCuspCharts.Horizontal F := fun i => KPCuspCharts.embedding F ((D.ratio h:Fˣ):F) i*x i + KPCuspCharts.embedding F (A 0 1/A 1 1) i
   have hx : (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = z := Quotient.out_eq _
   have hmx : M z = QuotientAddGroup.mk x' := by
     rw [←hx]
     exact (monodromy F ζ hζ C R P H U a).monodromy_formula h A x hA hc
   have hp : (geometry F ζ hζ C R P H U a).crossAction h (x,b) = (x',b') := by
     rw [(geometry F ζ hζ C R P H U a).crossAction_formula h A hA hc]
     rfl
   have hcov := KPContinuation.ChamberModerateGrowth.actualCuspSheet_crossAction F ζ hζ C R P H U ι hι f hf a s hs h t (x,b) 1
   rw [hp] at hcov
   dsimp only [φ]
   have hrep := KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative F ζ hζ C R P H U ι hι f hf a s hs t
     (Quotient.out (M z)) x' b' 1 ((Quotient.out_eq (M z)).trans hmx)
   exact hrep.trans hcov
 have hmp := actual_monodromy_preserves_fiberMeasure F ζ hζ C R P H U a h
 letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
 change (∫z,φ b' z ∂_) = _
 rw [← hmp.integral_comp M.toMeasurableEquiv.measurableEmbedding (φ b')]
 change (∫z,φ b' (M z) ∂_) = _
 simp_rw [hm]
 exact integral_const_mul _ _
include hι hf hs in

theorem actualMeanZeroSheet_crossAction
    (h : stabilizer F ζ hζ C R P H U a) (x : KPCuspCharts.Horizontal F) :
    KPContActualChamberMeanZeroAdapter.meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s t
      ((geometry F ζ hζ C R P H U a).crossAction h (x,b)).1
      ((geometry F ζ hζ C R P H U a).crossAction h (x,b)).2 1 =
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a h) : ℂ) *
      KPContActualChamberMeanZeroAdapter.meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s t x b 1 := by
  obtain ⟨A, hA, hc⟩ := (parabolic F ζ hζ C R P H U a).upper h h.property
  have hp := (geometry F ζ hζ C R P H U a).crossAction_formula h A hA hc (x,b)
  unfold KPContActualChamberMeanZeroAdapter.meanZeroJetSheet
  simp only [map_one, Units.val_one, one_mul]
  rw [KPContinuation.ChamberModerateGrowth.actualCuspSheet_crossAction F ζ hζ C R P H U ι hι f hf a s hs]
  have hcst (z : KernelTorus F ζ hζ C R P H U a) (b : KPCuspCharts.Shape F) :
      (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
        (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) 0 s t b).val z =
      (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
        (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) 0 s t b).val 0 :=
    (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
      (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) 0 s t b).property.2 z
  dsimp only [KPContActualChamberMeanZeroAdapter.fiberMeasure]
  simp_rw [hcst]
  rw [actualCuspSheet_projection_eq_rawMean F ζ hζ C R P H U a ι hι f hf s hs t,
    actualCuspSheet_projection_eq_rawMean F ζ hζ C R P H U a ι hι f hf s hs t]
  rw [hp]
  change _ - (∫ z, KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
    (Quotient.out z) (b + KPCuspLogShape.logarithm F H.totallyComplex
      (parabolic F ζ hζ C R P H U a).E (parabolic F ζ hζ C R P H U a).integralUnits
      (Additive.ofMul ((parabolic F ζ hζ C R P H U a).ratio h))) 1 ∂_) = _
  have hv := actualCuspSheet_rawMean_unit_covariance F ζ hζ C R P H U a ι hι f hf s hs t b h
  change _ - (∫ z : KernelTorus F ζ hζ C R P H U a,
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      (Quotient.out z) (b + KPCuspLogShape.logarithm F H.totallyComplex
        (parabolic F ζ hζ C R P H U a).E (parabolic F ζ hζ C R P H U a).integralUnits
        (Additive.ofMul ((parabolic F ζ hζ C R P H U a).ratio h))) 1
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) = _
  rw [hv]
  ring

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection

end

end
