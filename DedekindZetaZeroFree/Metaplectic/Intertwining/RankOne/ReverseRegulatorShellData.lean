module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CenterInducedDiagonalComparison

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseRegulatorShellsRaw

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

def additiveParameter (r : ℂˣ) : ℂ :=
  -Complex.log (r : ℂ) / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)

def t (r : ℂ) : ℂ := (residueCardinality (LocalField F q) : ℂ)⁻¹ * r ^ 6

def IsRegular (r : ℂˣ) : Prop := 1 - t F q (r : ℂ) ≠ 0

def Q (lam : ℂ) : ℂ :=
  Complex.exp (-lam * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ))

def ConvergenceRegion (r : ℂˣ) (lam : ℂ) : Prop :=
  lam.re < 1 ∧
    (residueCardinality (LocalField F q) : ℝ).rpow (-3 * lam.re) < ‖t F q (r : ℂ)‖

variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def actualSection (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) : centerSectionSpace F ζ hζ q T A .plus (additiveParameter F q r) :=
  Classical.choose (center_pure_coordinate_section F ζ hζ q T A P B rep hrep d
    (additiveParameter F q r) φ hφ hcφ)

def forwardSection (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) : centerSectionSpace F ζ hζ q T A .minus (-additiveParameter F q r) :=
  J.op .plus (additiveParameter F q r)
    (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r)

run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``DedekindZetaZeroFree.KPRankOneReverseRegulatorShellsRaw.forwardSection
  let info ← Lean.getConstInfo name
  let _ ← Lean.Meta.mkCongrSimpForConst? name
    (info.levelParams.map Lean.Level.param)
  pure ()

def reverseRoot (B : Binding F ζ hζ q A P) (r : ℂˣ)
    (v : (LocalField F q)ˣ) : CenterModule T →ₗ[ℂ] CenterModule T :=
  normPower (LocalField F q) (v ^ 2) (-additiveParameter F q r) •
    centerTorus F ζ hζ q T A .minus (B.rootTorus v)

def reverseIntegrand (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (lam : ℂ) (h : H₀) (v : (LocalField F q)ˣ) : ℂ :=
  (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (reverseRoot F ζ hζ q T A P B r v
      ((forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
        (openCoordinate F ζ hζ q (v : LocalField F q)))).val h *
    normPower (LocalField F q) v lam

def H (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (lam : ℂ) (h : H₀) : ℂ :=
  ∫ v : (LocalField F q)ˣ,
    reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v
      ∂multiplicativeMeasure F q μ

abbrev ShellNumerator := (ℤ × ℤ) →₀ ℂ

def evaluateNumerator (p : ShellNumerator) (r Q : ℂ) : ℂ :=
  p.sum (fun ij c => c * r ^ ij.1 * Q ^ ij.2)

def shellDenominator (r Q : ℂ) : ℂ :=
  (1 - t F q r) * (1 - (t F q r)⁻¹ * Q ^ 3) *
    (1 - (residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) * Q ^ (-3 : ℤ))

def valuationIndex (v : (LocalField F q)ˣ) : ℤ :=
  WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
    (LocalField F q) (valuation (LocalField F q) (v : LocalField F q)))

def smallRegion (N : ℕ) : Set (LocalField F q)ˣ :=
  {v | valuationIndex F q v < -(N : ℤ)}

def annulusRegion (N : ℕ) : Set (LocalField F q)ˣ :=
  {v | -(N : ℤ) ≤ valuationIndex F q v ∧ valuationIndex F q v ≤ (N : ℤ)}

def infinityRegion (N : ℕ) : Set (LocalField F q)ˣ :=
  {v | (N : ℤ) < valuationIndex F q v}

def smallFactor (r Q : ℂ) : ℂ := 1 - (t F q r)⁻¹ * Q ^ 3

def infinityFactor (Q : ℂ) : ℂ :=
  1 - (residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ) * Q ^ (-3 : ℤ)

end
end DedekindZetaZeroFree.KPRankOneReverseRegulatorShellsRaw
