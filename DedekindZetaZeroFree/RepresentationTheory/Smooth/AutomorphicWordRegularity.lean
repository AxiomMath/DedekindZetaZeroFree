module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteLevelChartRegularity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.QuotientDescentAndHolomorphicJets

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalWordRegularity
open KPMsClearedTruncationL2
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalFiniteLevelSmooth renaming upstairs_smooth_finiteLevel_rawSmooth → upstairs_smooth_finiteLevel_rawSmooth

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : Level F ζ hζ}

private theorem finitePart_eq : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    ActualQuotient.finiteSubgroup F ζ hζ := by
  unfold KPGlobalTorusFunctionData.finitePart ActualQuotient.finiteSubgroup
  congr 1
  ext x
  simp [ActualQuotient.finiteTuples, Subgroup.mem_iInf, MonoidHom.mem_ker]

private theorem word_smoothAutomorphic (v : smoothSpace F ζ hζ U)
    (w : List (KPSmoothActualFlowData.B F)) :
    KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ
      (KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val) := by
  exact ⟨ActualWordSpatial.word_continuous F ζ hζ U v.val v.property.1
    v.property.2.1 w,
    ActualWordLinearity.word_orbit_contDiff F ζ hζ v.val v.property.1 w⟩

private theorem word_centre_covariant
    (v : smoothSpace F ζ hζ U) (w : List (KPSmoothActualFlowData.B F))
    (g : G F ζ hζ) (ε : rootsOfUnity 3 F) :
    KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε)) =
      (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) *
        KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  induction w generalizing g with
  | nil => exact v.property.2.2 g ε
  | cons b w ih =>
    change deriv _ 0 = _ * deriv _ 0
    have he : (fun t : ℝ => KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          ((g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (KPSmoothActualFlowData.flow F b t)))) =
        (fun t : ℝ => (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) *
          KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val
            (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
                (KPSmoothActualFlowData.flow F b t)))) := by
      funext t
      rw [mul_assoc, SmoothDescent.centreMap_mul, ← mul_assoc]
      exact ih _
    simp only [SmoothDescent.rightTranslate_quotientMap]
    rw [he, deriv_const_mul_field]

 theorem word_mem_smoothSpace (v : smoothSpace F ζ hζ U)
    (w : List (KPSmoothActualFlowData.B F)) :
    KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val ∈ smoothSpace F ζ hζ U := by
  refine ⟨word_smoothAutomorphic v w, ?_, word_centre_covariant v w⟩
  intro g u
  exact ActualWordSpatial.word_right_invariant F ζ hζ v.val u.val
    (fun a => RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a
      ⟨u.val, by
        obtain ⟨a, ha, he⟩ := u.property
        rw [← he]
        rw [← finitePart_eq]
        exact a.property⟩)
    (fun g => v.property.2.1 g u) w g

end DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalWordRegularity

end
