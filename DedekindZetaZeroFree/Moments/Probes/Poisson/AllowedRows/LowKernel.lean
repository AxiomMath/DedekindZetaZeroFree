module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions

noncomputable section

open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Iz (u : D.Row) (ξ w : ℂ) (v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral v (fun z => PoissonKernel.K D u ξ w z Z)

def Iwz (u : D.Row) (ξ : ℂ) (y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u ξ w v Z)

def triple (u : D.Row) (x y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral x (fun ξ => Iwz D u ξ y v Z)

def explicitFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

theorem explicitFactor_eq_rowFactor (u : D.Row) (ξ w z : ℂ) :
    explicitFactor D u ξ w z = PoissonKernel.rowFactor D u ξ w z := by
  unfold explicitFactor PoissonKernel.rowFactor
  ring

theorem explicitFactor_funext : explicitFactor D = PoissonKernel.rowFactor D := by
  funext u ξ w z
  exact explicitFactor_eq_rowFactor D u ξ w z

theorem K_eq_kernelWith (u : D.Row) (ξ w z : ℂ) (Z : ℝ) :
    PoissonKernel.K D u ξ w z Z = PoissonKernel.kernelWith D (explicitFactor D) u ξ w z Z := by
  rw [explicitFactor_funext]
  rfl

theorem Iz_eq_kernelWith (u : D.Row) (ξ w : ℂ) (v Z : ℝ) :
    Iz D u ξ w v Z = comparisonVerticalIntegral v
      (fun z => PoissonKernel.kernelWith D (explicitFactor D) u ξ w z Z) := by
  unfold Iz
  simp only [K_eq_kernelWith]

theorem Iwz_eq_wzIntegral (u : D.Row) (ξ : ℂ) (y v Z : ℝ) :
    Iwz D u ξ y v Z = PoissonKernel.wzIntegral D u ξ y v Z := rfl

theorem triple_eq_J (u : D.Row) (x y v Z : ℝ) :
    triple D u x y v Z = comparisonVerticalIntegral x
      (fun ξ => PoissonKernel.wzIntegral D u ξ y v Z) := rfl

end

end DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions
