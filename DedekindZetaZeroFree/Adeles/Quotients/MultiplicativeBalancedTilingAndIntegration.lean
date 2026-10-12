module

public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators
public import DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection
public import DedekindZetaZeroFree.Adeles.Quotients.SixthPowerCompactCover
public import DedekindZetaZeroFree.MeasureTheory.BorelCocompactTransversals
public import DedekindZetaZeroFree.Adeles.Lattices.SixthPowerUnitDiscreteness

@[expose] public section

open MeasureTheory
open scoped nonZeroDivisors ENNReal

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

local instance : MeasurableSpace A.G1 := borel _
local instance : BorelSpace A.G1 := ⟨rfl⟩

theorem exists_multiplicative_quotient_balanced_tiling :
    ∃ (K_bal D : Set A.G1), IsCompact K_bal ∧
      (∀ y : A.G1, ∃ γ : A.Gamma1, (γ : A.G1) * y ∈ K_bal) ∧
      MeasurableSet D ∧ IsCompact (closure D) ∧ D ⊆ K_bal ∧
      (∀ y : A.G1, ∃! γ : A.Gamma1, (γ : A.G1) * y ∈ D) := by
  obtain ⟨n, V, hV, hcover⟩ :=
    exists_finite_relativelyCompact_quotient_slices (G := A.G1) A.Gamma1
  obtain ⟨D, hDmeas, hDcomp, htiling⟩ :=
    exists_measurable_relativelyCompact_exact_transversal_of_finite_slices
      A.G1 A.Gamma1 n V (fun i => (hV i).1) (fun i => (hV i).2.1)
      (fun i => (hV i).2.2) hcover
  refine ⟨closure D, D, hDcomp, ?_, hDmeas, hDcomp, subset_closure, htiling⟩
  intro y
  obtain ⟨γ, hγ, _⟩ := htiling y
  exact ⟨γ, subset_closure hγ⟩

end
end SArithmeticData
end DedekindZetaZeroFree
