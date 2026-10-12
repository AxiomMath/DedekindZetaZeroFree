module

public import DedekindZetaZeroFree.LFunctions.Tate.ComplexTraceFourierMellinNormalization
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceCharacter

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree
namespace ArchSelfDual

open MeasureTheory NumberField
open scoped Classical ENNReal NNReal FourierTransform SchwartzMap

def realMeasure : Measure ℝ := volume

def complexMeasure : Measure ℂ := (2 : ℝ≥0∞) • volume

def realFourier (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (((-2 * Real.pi * (x * y) : ℝ) : ℂ) * Complex.I)
    ∂realMeasure

theorem complexTraceFourier_eq_integral (f : ℂ → ℂ) (y : ℂ) :
    complexTraceFourier f y =
      ∫ z : ℂ, f z * Complex.exp (((-4 * Real.pi * (z * y).re : ℝ) : ℂ) * Complex.I)
        ∂complexMeasure := by
  simp [complexTraceFourier, complexMeasure, integral_smul_measure, smul_eq_mul]

private theorem realFourier_eq_fourier (f : ℝ → ℂ) :
    realFourier f = FourierTransform.fourier f := by
  funext y
  rw [Real.fourier_eq']
  simp [realFourier, realMeasure, real_inner_comm, mul_comm]

theorem realFourier_schwartz (f : SchwartzMap ℝ ℂ) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = realFourier f y := by
  refine ⟨FourierTransform.fourier f, ?_⟩
  intro y
  rw [realFourier_eq_fourier]
  rfl

def complexJ : ℂ ≃L[ℝ] ℂ :=
  Complex.conjLIE.toContinuousLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ ℂ 2 (by norm_num)).toContinuousLinearEquiv

private theorem complexJ_apply (z : ℂ) : complexJ z = 2 * (starRingEnd ℂ) z := by
  simp [complexJ, Complex.conjLIE_apply, Complex.real_smul]

theorem complexTraceFourier_schwartz (f : SchwartzMap ℂ ℂ) :
    ∃ g : SchwartzMap ℂ ℂ, ∀ y : ℂ, g y = complexTraceFourier f y := by
  refine ⟨(2 : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ complexJ
    (FourierTransform.fourier f), ?_⟩
  intro y
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, complexJ_apply, SchwartzMap.fourier_coe, smul_eq_mul,
    complexTraceFourier_eq_fourier]

instance completionMeasurableSpace {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _

instance completionBorelSpace {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩

instance infiniteMeasurableSpace (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((v : InfinitePlace F) → v.Completion))

instance instSigmaFiniteTraceInversionRealMeasure : SigmaFinite realMeasure := inferInstanceAs (SigmaFinite (volume : Measure ℝ))

instance instSigmaFiniteTraceInversionComplexMeasure : SigmaFinite complexMeasure := by
  change SigmaFinite ((2 : ℝ≥0) • (volume : Measure ℂ))
  infer_instance

public theorem pi_complexMeasure_eq_smul_volume (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => complexMeasure) =
      (2 : ℝ≥0∞) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, volume_pi, Measure.pi_pi,
    complexMeasure]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

end ArchSelfDual
end DedekindZetaZeroFree

end
