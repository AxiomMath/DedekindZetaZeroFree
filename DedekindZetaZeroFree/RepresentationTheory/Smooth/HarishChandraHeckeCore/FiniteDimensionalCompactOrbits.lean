module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue.SourceCoreCompactOrbit
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}

private theorem source_raw_compact_orbit_finiteDimensional
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun k : D.K => fun g => f.val.val (g * k.val)))) := by
  let i := (KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).subtype
  let orbit := fun v : KPMsRationalCompactCrossPairing.Source F ζ hζ 0 =>
    Submodule.span ℂ (Set.range (fun k : D.K => fun g => v.val (g * k.val)))
  change FiniteDimensional ℂ (orbit f.val)
  apply Submodule.iSup_induction _ (motive := fun v => FiniteDimensional ℂ (orbit v)) f.property
  · intro U v hv
    apply Submodule.iSup_induction _ (motive := fun v => FiniteDimensional ℂ (orbit v)) hv
    · intro τ v hv
      letI := τ.finiteDimensional
      have hle : orbit v ≤ τ.space.map i := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        refine Submodule.mem_map.mpr ⟨_, τ.invariant k _ (show v ∈ τ.space from hv.2), rfl⟩
      exact Submodule.finiteDimensional_of_le hle
    · have hle : orbit 0 ≤ (⊥ : Submodule ℂ (KPMsRationalCompactCrossPairing.G F ζ hζ → ℂ)) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact Submodule.zero_mem _
      exact Submodule.finiteDimensional_of_le hle
    · intro v w hv hw
      letI := hv
      letI := hw
      have hle : orbit (v + w) ≤ orbit v ⊔ orbit w := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact Submodule.add_mem _
          (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
          (Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩))
      exact Submodule.finiteDimensional_of_le hle
  · have hle : orbit 0 ≤ (⊥ : Submodule ℂ (KPMsRationalCompactCrossPairing.G F ζ hζ → ℂ)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.zero_mem _
    exact Submodule.finiteDimensional_of_le hle
  · intro v w hv hw
    letI := hv
    letI := hw
    have hle : orbit (v + w) ≤ orbit v ⊔ orbit w := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩))
    exact Submodule.finiteDimensional_of_le hle

theorem source_finiteDimensional
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun k : D.K => fun g => f.val.val (g * k.val)))) :=
  source_raw_compact_orbit_finiteDimensional f

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue.SourceCoreCompactOrbit

end
