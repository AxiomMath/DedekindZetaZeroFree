module

public import DedekindZetaZeroFree.Theta.Whittaker.SphericalJacquetNormalization

@[expose] public section

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.ResidualExteriorWhittaker
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open DedekindZetaZeroFree.ExteriorWhittakerValues
open ActualSpherical ActualJacquet ActualShellOutput ActualShellNormalization
open KPExteriorUnitShellIntegrals
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization inducingData.heisenberg)
variable (μ : MeasureTheory.Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (hμ : μ ((valuation (LocalField F v)).integer : Set (LocalField F v)) = 1)
variable [Fintype (IsLocalRing.ResidueField (valuation (LocalField F v)).integer)]
variable (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
variable (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
variable (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
variable (ψ : AddChar (LocalField F v) ℂ)
variable (hψcont : Continuous ψ) (hψunitary : ∀ x, ‖ψ x‖ = 1)
variable (hcond : ConductorZero ψ π)

variable (φ : Image F ζ hζ v inducingData P μ hμ)
variable (hφ : φ ∈ ImageFixed F ζ hζ v inducingData P μ hμ ht) (hne : φ ≠ 0)
include ht hgood hπ hψcont hψunitary hcond hφ hne in
theorem exists_normalized_whittaker :
    ∃ L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ,
      IsWhittaker F ζ hζ v inducingData P μ hμ ψ L ∧ L φ = 1 := by
  classical
  have hπval : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (uniformizerUnit F v π hπ : LocalField F v)) =
        WithZero.exp (-1 : ℤ) := by
    simpa only [uniformizerUnit, Units.val_mk0, WithZero.exp] using
      LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible (LocalField F v) π hπ
  obtain ⟨Eφ, hEφ, _⟩ := exists_unique_coordinateEquiv F ζ hζ v inducingData P ht hgood
    (uniformizerUnit F v π hπ) hπval φ.val
    (fun k ↦ congrArg Subtype.val (hφ k)) (by simpa using hne)
  letI : Module.Finite ℂ (VMinus F ζ hζ v inducingData P) := Module.Finite.equiv Eφ
  obtain ⟨N, hN⟩ := CompatibleFiniteNorm.exists_compatible (VMinus F ζ hζ v inducingData P)
  obtain ⟨J, hJ, _⟩ := exists_unique_stableJacquet F ζ hζ v inducingData P μ N hN
    hgood π hπ ψ hψcont hψunitary hcond
  exact ⟨sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ,
    sphericalFunctional_whittaker F ζ hζ v inducingData P μ hμ N hN hgood π hπ ψ
      hψcont hψunitary hcond J hJ Eφ,
    sphericalFunctional_at_spherical F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ
      hψcont hψunitary hcond J hJ φ hφ hne Eφ hEφ⟩
end
end DedekindZetaZeroFree.FourierContinuation.ResidualExteriorWhittaker
