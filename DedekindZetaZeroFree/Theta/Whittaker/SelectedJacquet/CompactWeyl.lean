module

public import DedekindZetaZeroFree.Theta.Profiles.LocalTensorActions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction

def compactWeyl : ComplexSU2 :=
  ⟨!![0, Complex.I; Complex.I, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

end DedekindZetaZeroFree.SheetRescaling

end
