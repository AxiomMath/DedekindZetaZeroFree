module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage

@[expose] public section

namespace DedekindZetaZeroFree.KPGlobalGoodEulerFactor

open KPLocalStoneVonNeumann KPLocalPrincipalSeries MeasureTheory
open scoped Valued

noncomputable section

def convergenceChamber : Set ℂ := {s | -(1 / 6 : ℝ) < s.re}

def sphericalCoefficient (q m : ℝ) (s : ℂ) : ℂ :=
  (m : ℂ) *
    (1 - Complex.exp ((-2 - 6 * s) * (Real.log q : ℂ))) /
    (1 - Complex.exp ((-1 - 6 * s) * (Real.log q : ℂ)))

def traceSelfDualIntegerMass (q : ℝ) (differentExponent : ℕ) : ℝ :=
  q ^ (-(differentExponent : ℝ) / 2)

@[simp] theorem traceSelfDualIntegerMass_unramified (q : ℝ) :
    traceSelfDualIntegerMass q 0 = 1 := by
  simp [traceSelfDualIntegerMass]

variable {K : Type*} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

end

end DedekindZetaZeroFree.KPGlobalGoodEulerFactor
