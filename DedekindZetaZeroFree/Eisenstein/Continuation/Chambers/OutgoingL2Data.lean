module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPChamberOutgoingL2

open MeasureTheory Filter Topology
open scoped ENNReal

def compactDecayRate (d : ℕ) (L : Set ℂ) : ℝ :=
  (d : ℝ) * sInf ((fun s : ℂ => (1 / 3 : ℝ) + 2 * s.re) '' L)

def outgoingFactor (d : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((d : ℂ) * ((2 / 3 : ℂ) - 2 * s) * (t : ℂ))

section Charts
variable (F : Type*) [Field F] [NumberField F]
variable {G Q N A H : Type*} [Group G] [MeasurableSpace N] [Finite A]
    [AddCommGroup H] [Module ℂ H]

end Charts

end DedekindZetaZeroFree.KPChamberOutgoingL2

end
