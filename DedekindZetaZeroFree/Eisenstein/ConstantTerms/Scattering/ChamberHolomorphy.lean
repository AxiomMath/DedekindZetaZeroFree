module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberIntegrability
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScatteringChamberAnalyticity
public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.FinitePlaceActions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming standard_integrable → standard_integrable
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming literal_two_cells → literal_two_cells
open _root_.DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation renaming exponential_integral_differentiable → exponential_integral_differentiable
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)

def coreScattering (x : V) (s : ℂ) (g : G F ζ hζ) : ℂ :=
  ∫ y : KPAdeles F, (coreFlatInsertion R P C x).val s
    (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y * g)
      ∂KPAdditiveHaar.adelicMeasure F

theorem coreScattering_integrable (x : V) (s : ℂ) (hs : (1 / 3 : ℝ) < s.re)
    (g : G F ζ hζ) :
    Integrable (fun y : KPAdeles F => (coreFlatInsertion R P C x).val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y * g))
      (KPAdditiveHaar.adelicMeasure F) :=
  standard_integrable F ζ hζ (fullProductCompact R) (full_product_compact_iwasawa R)
    (coreFlatInsertion R P C x) s hs g

theorem coreChamber_constantTerm (x : V)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : G F ζ hζ) :
    (∫ q : KPAdditiveQuotient F,
      eisenstein F ζ hζ (fullProductCompact R) (coreFlatInsertion R P C x) s
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ) =
      (μ.real Set.univ : ℂ) * ((coreFlatInsertion R P C x).val s g + coreScattering R P C x s g) :=
  literal_two_cells F ζ hζ (fullProductCompact R) (full_product_compact_iwasawa R) μ hμ
    (coreFlatInsertion R P C x) s hs g

theorem coreScattering_analytic (x : V) (g : G F ζ hζ) :
    AnalyticOnNhd ℂ (fun s => coreScattering R P C x s g)
      {s : ℂ | (1 / 3 : ℝ) < s.re} := by
  let f := coreFlatInsertion R P C x
  let arg : KPAdeles F → G F ζ hζ := fun y =>
    KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y * g
  let p := fun y => KPLiteralChamber.iwasawaTriple F ζ hζ
    (fullProductCompact R) (full_product_compact_iwasawa R) (arg y)
  let l : KPAdeles F → ℝ := fun y => Real.log
    (((KPGlobalTorusFunctionData.delta F ζ hζ (p y).1 : NNReal) : ℝ))
  let c : KPAdeles F → ℂ := fun y => f.val 0 ((p y).1.val * (p y).2.2.val)
  have hf (s : ℂ) (y : KPAdeles F) :
      f.val s (arg y) = Complex.exp (s * (l y : ℂ)) * c y := by
    rw [← KPLiteralChamber.compactExtension_eq_flat F ζ hζ
      (fullProductCompact R) (full_product_compact_iwasawa R) f s (arg y)]
    rfl
  have hint (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) :
      Integrable (fun y => Complex.exp (s * (l y : ℂ)) * c y)
        (KPAdditiveHaar.adelicMeasure F) := by
    simpa only [← hf] using coreScattering_integrable R P C x s hs g
  have hd := exponential_integral_differentiable (KPAdditiveHaar.adelicMeasure F)
    l c ((1 : ℝ) / 3) hint
  have heq : (fun s => coreScattering R P C x s g) =
      (fun s => ∫ y, Complex.exp (s * (l y : ℂ)) * c y
        ∂KPAdditiveHaar.adelicMeasure F) := by
    funext s
    unfold coreScattering
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => hf s y))
  rw [heq]
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
