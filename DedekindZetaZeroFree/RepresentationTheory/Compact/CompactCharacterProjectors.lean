module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace DedekindZetaZeroFree.CompactProjectors

open MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {K H E F : Type*}

def IsStable [Monoid K] [AddCommGroup H] [Module ℂ H]
    (ρ : Representation ℂ K H) (C : Submodule ℂ H) : Prop :=
  ∀ (k : K) (x : H), x ∈ C → ρ k x ∈ C

end DedekindZetaZeroFree.CompactProjectors
