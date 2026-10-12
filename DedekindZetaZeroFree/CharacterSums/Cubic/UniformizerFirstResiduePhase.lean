module

public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalResidueUnitHaarIntegral
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ConductorShellSubstitution

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPTameTransposeLiteralShell
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPTameTransposeLiteral
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

theorem residueShellIntegrand_eq_tame_phase
    (π : (LocalField F q)ˣ)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (κ : MulChar (RawResidue F q) ℂ)
    (hκ : RawPiFirstOrientation F ζ hζ q π κ)
    (p : KPTameCompact.O F q) (hp : (p : LocalField F q) = π)
    (j : ZMod 3) (u : (KPTameCompact.O F q)ˣ) :
    KPTameGauss.residueShellIntegrand κ
      (AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp ψ)) p j
      ((KPTameCompact.unitInclusion F q) u) =
    (ordinaryIota F ζ hζ
      (KPHilbert.B3 F ζ hζ (Sum.inr q) π
        ((KPTameCompact.unitInclusion F q) u)) : ℂ) ^ j.val *
      (ψ (Multiplicative.ofAdd
        (((KPTameCompact.unitInclusion F q) u : LocalField F q) /
          (π : LocalField F q))) : ℂ) := by
  have hu : ((KPTameCompact.unitInclusion F q) u : LocalField F q) ∈
      ((valuation (LocalField F q)).integer : Subring (LocalField F q)) :=
    (u : KPTameCompact.O F q).property
  simp only [KPTameGauss.residueShellIntegrand, dif_pos hu]
  rw [hp]
  change κ (IsLocalRing.residue (KPTameCompact.O F q) (u : KPTameCompact.O F q)) ^ j.val * _ = _
  rw [hκ u]
  rfl

theorem isClosed_integerUnitShell :
    IsClosed (KPTameGauss.integerUnitShell (LocalField F q)) := by
  have he : KPTameGauss.integerUnitShell (LocalField F q) =
      {u | valuation (LocalField F q) u = 1} := by
    ext u
    constructor
    · rintro ⟨u, rfl, hu⟩
      exact (Valuation.integer.integers (valuation (LocalField F q))).isUnit_iff_valuation_eq_one.mp hu
    · intro hu
      exact ⟨⟨u, hu.le⟩, rfl,
        (Valuation.integer.integers (valuation (LocalField F q))).isUnit_iff_valuation_eq_one.mpr hu⟩
  rw [he]
  letI : TopologicalSpace (ValueGroupWithZero (LocalField F q)) := WithZeroTopology.topologicalSpace
  letI : T5Space (ValueGroupWithZero (LocalField F q)) := WithZeroTopology.t5Space
  exact (isClosed_singleton (x := (1 : ValueGroupWithZero (LocalField F q)))).preimage
    (IsValuativeTopology.continuous_valuation (R := LocalField F q))

theorem measurable_integerUnitShell :
    MeasurableSet (KPTameGauss.integerUnitShell (LocalField F q)) :=
  (isClosed_integerUnitShell F q).measurableSet

end DedekindZetaZeroFree.KPTameTransposeLiteralShell

end
