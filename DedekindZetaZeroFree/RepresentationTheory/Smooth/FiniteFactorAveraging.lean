module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

open scoped Classical NumberField Topology

open MeasureTheory

namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarFiniteAverage

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

abbrev Level (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) := KPGlobalTorusFunctionData.FiniteLevel F ζ hζ

abbrev CompactGroup (U : Level F ζ hζ) := U.toOpenSubgroup.toSubgroup

instance (U : Level F ζ hζ) : CompactSpace (CompactGroup U) :=
  isCompact_iff_compactSpace.mp U.isCompact

instance (U : Level F ζ hζ) : MeasurableSpace (CompactGroup U) := borel _

instance (U : Level F ζ hζ) : BorelSpace (CompactGroup U) := ⟨rfl⟩

def haar (U : Level F ζ hζ) : Measure (CompactGroup U) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : TopologicalSpace.PositiveCompacts _)

instance (U : Level F ζ hζ) : (haar U).IsHaarMeasure := by unfold haar; infer_instance

instance (U : Level F ζ hζ) : IsProbabilityMeasure (haar U) := by
  constructor
  exact Measure.haarMeasure_self

end DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarFiniteAverage

end
