module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RootIntegrals.QuotientKernelDetection
public import DedekindZetaZeroFree.Theta.Periods.FiniteHaarTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct NNReal
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (M : ∀ q, LocalImageData R q)

theorem traceHaar_eq_characterOne :
    ArchSelfDual.complexMeasure =
      ENNReal.ofReal (4 * Real.pi) • KPCplxCharacterHaar.characterHaar (1 : ℂˣ) := by
  unfold ArchSelfDual.complexMeasure KPCplxCharacterHaar.characterHaar
    KPCplxCharacterHaar.characterScale KPCplxCharacterHaar.euclideanArea
  simp only [Units.val_one, norm_one, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h : 4 * Real.pi * (1 / (2 * Real.pi)) = (2 : ℝ) := by field_simp; ring
  rw [h]
  norm_num

def arithmeticRootMeasure : ∀ p, Measure (RootPoint R p)
  | Sum.inl _ => ArchSelfDual.complexMeasure
  | Sum.inr q => N.finiteHaar q

def arithmeticRootScale (_R : PrincipalMellin.ActualRecipe S η) : KPHilbert.Place F → ℝ
  | Sum.inl _ => 4 * Real.pi
  | Sum.inr q => PoissonS.integerVolume F q

theorem arithmeticRootScale_pos (p : KPHilbert.Place F) :
    0 < arithmeticRootScale R p := by
  cases p with
  | inl w => exact mul_pos (by norm_num) Real.pi_pos
  | inr q => exact PoissonS.integerVolume_pos F q

theorem arithmeticRootMeasure_eq (p : KPHilbert.Place F) :
    arithmeticRootMeasure R N p =
      ENNReal.ofReal (arithmeticRootScale R p) • rootMeasure R M p := by
  cases p with
  | inl w => exact traceHaar_eq_characterOne
  | inr q => exact FourierContinuation.finiteHaar_transport N q (M q)

omit M in
instance arithmeticRootMeasureSigmaFinite (p : KPHilbert.Place F) :
    SigmaFinite (arithmeticRootMeasure R N p) := by
  cases p with
  | inl w =>
    change SigmaFinite ArchSelfDual.complexMeasure
    change SigmaFinite ((2 : ℝ≥0) • (volume : Measure ℂ))
    infer_instance
  | inr q =>
    letI := N.finiteHaar_add q
    exact inferInstanceAs (SigmaFinite (N.finiteHaar q))

def arithmeticStageScale (s : Finset (KPHilbert.Place F)) : ℝ :=
  ∏ p : s, arithmeticRootScale R p

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource

end
