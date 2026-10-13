module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowContLocal (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

def wResidueLocal (u : D.Row) (ξ z : ℂ) (Z : ℝ) : ℂ :=
  Filter.limUnder (nhdsWithin (1 : ℂ) {1}ᶜ)
    (fun w : ℂ => (w - 1) * kernelWith D (rowContLocal D) u ξ w z Z)

def zResidueLocal (u : D.Row) (ξ : ℂ) (Z : ℝ) : ℂ :=
  Filter.limUnder (nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ)
    (fun z : ℂ => (z - 1 / 6) * wResidueLocal D u ξ z Z)

end

end DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions
