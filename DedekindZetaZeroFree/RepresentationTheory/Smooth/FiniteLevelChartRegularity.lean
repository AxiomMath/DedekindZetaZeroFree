module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ArchimedeanMatrixParametrization
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalFiniteLevelSmooth
open KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge renaming matrixClass → matrixClass
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge renaming smooth_matrix_parametrization → smooth_matrix_parametrization
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge renaming rightPolynomial → rightPolynomial
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge renaming rightPolynomial_smooth → rightPolynomial_smooth
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge renaming rightPolynomial_det → rightPolynomial_det

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

private theorem native_chart_contDiffOn
    (u : Cover F ζ hζ → ℂ) (hu : Smooth F ζ hζ u) (g : Cover F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  intro x hx
  have hdet : ∀ w, (rightPolynomial x w).det ≠ 0 := by
    intro w
    rw [rightPolynomial_det]
    exact hx w
  have hd := smooth_matrix_parametrization u hu g rightPolynomial x
    rightPolynomial_smooth.contDiffAt hdet
  apply hd.contDiffWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin] with y hy
    congr 2
    rw [KPLiteralChamber.right_insertion F ζ hζ y]
    congr 1
    funext w
    have hyw : (rightPolynomial y w).det ≠ 0 := by
      rw [rightPolynomial_det]
      exact hy w
    simp only [matrixClass, dite_eq_left hyw]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (KPLiteralChamber.rightMatrix (y w)).val i j = rightPolynomial y w i j
    rw [KPLiteralChamber.rightMatrix_val _ (hy w)]
    rfl
  · exact hx

 theorem upstairs_smooth_finiteLevel_rawSmooth
    (u : Cover F ζ hζ → ℂ) (hu : Smooth F ζ hζ u)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : ∀ g a, a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U → u (g * a) = u g) :
    KPLiteralRaw.Smooth F ζ hζ u := by
  exact ⟨hu.1, native_chart_contDiffOn u hu, U, hU⟩

end DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalFiniteLevelSmooth

end
