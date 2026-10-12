module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.IrreducibleClassification
public import DedekindZetaZeroFree.RepresentationTheory.Compact.IntegratedOperators
public import DedekindZetaZeroFree.RepresentationTheory.Compact.CompactCharacterProjectors
public import Mathlib

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation

open MeasureTheory
open scoped Matrix.Norms.L2Operator InnerProductSpace

abbrev RawU2 := Matrix.unitaryGroup (Fin 2) ℂ

abbrev RawHarmonicType (d : ℕ) := Fin d → ℕ

noncomputable def rawSymmetricPowerTrace (n : ℕ) (g : RawU2) : ℂ :=
  match n with
  | 0 => 1
  | 1 => Matrix.trace g.val
  | n + 2 => Matrix.trace g.val * rawSymmetricPowerTrace (n + 1) g -
      Matrix.det g.val * rawSymmetricPowerTrace n g

noncomputable def rawRankOneCharacter (ℓ : ℕ) (g : RawU2) : ℂ :=
  rawSymmetricPowerTrace (2 * ℓ) g / Matrix.det g.val ^ ℓ

noncomputable def rawCharacter {d : ℕ} (ℓ : RawHarmonicType d)
    (g : Fin d → RawU2) : ℂ :=
  ∏ j, rawRankOneCharacter (ℓ j) (g j)

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation

end
