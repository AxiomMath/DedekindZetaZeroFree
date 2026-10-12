module

public import DedekindZetaZeroFree.LFunctions.Dedekind.PrincipalHeckeData
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.InverseMellinRepresentation

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open Filter
namespace DedekindZetaZeroFree.LargeSieve.SquarePoisson

def weight (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  fieldTransform D r h (x ^ 2)

def spectrum (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  B D r h (s / 2) / 2

def reflectedSpectrum (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
    (Complex.Gammaℂ (1 - s))⁻¹ ^ r * spectrum D r h (1 - s)

def reflectedTransform (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then mellinInv (3 / 2) (reflectedSpectrum D r h) x else 0
variable {F : Type} [Field F] [NumberField F]

def kappa (data : PrincipalHeckeData F) : ℂ :=
  data.E 1 / ((Real.sqrt (principalDiscriminant F) : ℂ) *
    Complex.Gammaℂ 1 ^ principalComplexPlaces F)

end DedekindZetaZeroFree.LargeSieve.SquarePoisson

end
