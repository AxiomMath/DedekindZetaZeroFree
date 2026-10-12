module

public import DedekindZetaZeroFree.Moments.Probes.AnnularWeightsAndCancellingProfiles
public import DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

def localUnitsRaw (A : SArithmeticData F) : A.G ≃* (SLocalProduct F A.Sf)ˣ :=
  ((MulEquiv.piUnits).symm.prodCongr (MulEquiv.piUnits).symm).trans
    (MulEquiv.prodUnits).symm

def ellRaw (A : SArithmeticData F) (T : ℝ) : (SLocalProduct F A.Sf)ˣ :=
  if hT : 0 < T then localUnitsRaw A (A.radialSection T hT) else 1

def sheetPointRaw (A : SArithmeticData F) (T : ℝ) (t : A.G1) :
    (SLocalProduct F A.Sf)ˣ := localUnitsRaw A t.val * ellRaw A T

def complexNormFlowRaw (A : SArithmeticData F) (w : InfinitePlace F)
    (u : ℝ) (x : SLocalProduct F A.Sf) : SLocalProduct F A.Sf :=
  (Function.update x.1 w
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
      (Real.exp (u / 2) : ℂ) * x.1 w), x.2)

def logDerivativeRaw (A : SArithmeticData F) (w : InfinitePlace F) (k : ℕ)
    (f : SLocalProduct F A.Sf → ℂ) (x : SLocalProduct F A.Sf) : ℂ :=
  iteratedDeriv k (fun u : ℝ => f (complexNormFlowRaw A w u x)) 0

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
