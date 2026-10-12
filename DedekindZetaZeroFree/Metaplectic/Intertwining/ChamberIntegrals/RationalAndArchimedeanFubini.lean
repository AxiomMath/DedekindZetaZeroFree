module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.ArchimedeanTraceCofactor
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicCharts.TraceBoxFubini

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ChamberReferenceInsertion
open KPGlobalTorusFiniteStages ActualCofactor
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
set_option backward.isDefEq.respectTransparency false

open MeasureTheory KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann

theorem rational_chamber_chart_integral
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (s : ℂ)
    (hs : KPRankOneShellContinuation.convergenceHalfPlane .plus s) :
    (∫ z : KPAdditiveHaar.Chart F E,
      rationalChamberIntegrand F ζ hζ P C E hE φ t s z.1 ∂(KPAdditiveHaar.chartMeasure F E)) =
    rationalStageEval F ζ hζ P C E hE t
      (fun q => (localHalfDifferentFactor F q.val : ℂ) •
        (KPRankOneShellRepair.actualCanonicalContinued F q.val ζ hζ (C.canonical q.val)
          (C.polarization q.val)
          (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val))
          (ActualCofactor.unit_mass F q.val) .plus s (φ q)).val 1) := by
  let : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // q ∉ E},
    IsProbabilityMeasure (KPAdditiveHaar.integerProbabilityMeasure F q.val) :=
      fun q => KPAdditiveHaar.integerProbabilityMeasure_isProbabilityMeasure F q.val
  have h := integral_fun_fst
    (μ := Measure.pi (fun q : E => localNormalizedHaar F q.val))
    (ν := Measure.infinitePi (fun q : {q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // q ∉ E} =>
      KPAdditiveHaar.integerProbabilityMeasure F q.val))
    (rationalChamberIntegrand F ζ hζ P C E hE φ t s)
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
  exact h.trans (rational_finite_chamber_integral F ζ hζ P C E hE φ t s hs).2

include ζ hζ in

theorem arch_chamber_integral (s : ℂ) :
    (∫ a, TraceBox.archCylinder F s a ∂(KPAdditiveHaar.archMeasure F)) =
      ∏ _w : NumberField.InfinitePlace F, ∫ x : ℂ,
        TraceBox.complexIntegrand s x ∂((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea) := by
  let := primitive12_totallyComplex F ζ hζ
  have h := TraceBox.arch_cylinder_integral F ζ hζ s
  let e : NumberField.InfinitePlace F ≃ {w : NumberField.InfinitePlace F // w.IsComplex} :=
    { toFun := fun w => ⟨w, NumberField.IsTotallyComplex.isComplex w⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact h.trans (e.prod_comp (fun _ => ∫ x : ℂ, TraceBox.complexIntegrand s x
    ∂((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea))).symm

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ChamberReferenceInsertion

end
