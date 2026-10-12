module

public import DedekindZetaZeroFree.Theta.Whittaker.SphericalJacquetNormalization

@[expose] public section

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellValues
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open ActualSpherical ActualJacquet ActualShellOutput ActualShellNormalization
open KPExteriorUnitShellIntegrals
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
def radialValue (g₂ : ℂ) (e : ℤ) : ℂ :=
  if e < 0 then 0 else if e % 3 = 0 then QPower F v (-((e / 3 : ℤ) : ℝ))
  else if e % 3 = 1 then QPower F v (-((e / 3 : ℤ) : ℝ) - (1 / 2 : ℝ)) * g₂ else 0
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
variable (χκ : MulChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
variable (hactual : ∀ u, unitCharacter χκ u = arithmeticUnitCharacter F ζ hζ v hgood u)
variable (ψbar : AddChar (IsLocalRing.ResidueField (valuation (LocalField F v)).integer) ℂ)
variable (hbar : ∀ u : (valuation (LocalField F v)).integer,
  ψbar (IsLocalRing.residue _ u) = ψ ((π : LocalField F v)⁻¹ * (u : LocalField F v)))
variable (φ : Image F ζ hζ v inducingData P μ hμ)
variable (hφ : φ ∈ ImageFixed F ζ hζ v inducingData P μ hμ ht) (hne : φ ≠ 0)
include ht hgood hπ hψcont hψunitary hcond hactual hbar hφ hne in
 theorem nonnegative_values
    (L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ)
    (hL : IsWhittaker F ζ hζ v inducingData P μ hμ ψ L) (hLφ : L φ = 1) (e : ℕ) :
    L (ImageAction F ζ hζ v inducingData P μ hμ
      (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (uniformizerUnit F v π hπ ^ (e : ℤ))) φ) =
      radialValue F v (g χκ ψbar 2) (e : ℤ) := by
  classical
  have hπval : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) (uniformizerUnit F v π hπ : LocalField F v)) =
        WithZero.exp (-1 : ℤ) := by
    simpa only [uniformizerUnit, Units.val_mk0, WithZero.exp] using
      LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible (LocalField F v) π hπ
  obtain ⟨Eφ, hEφ, _⟩ := exists_unique_coordinateEquiv F ζ hζ v inducingData P ht hgood
    (uniformizerUnit F v π hπ) hπval φ.val (fun k => congrArg Subtype.val (hφ k)) (by simpa using hne)
  letI : Module.Finite ℂ (VMinus F ζ hζ v inducingData P) := Module.Finite.equiv Eφ
  obtain ⟨N, hN⟩ := CompatibleFiniteNorm.exists_compatible (VMinus F ζ hζ v inducingData P)
  obtain ⟨J, hJ, _⟩ := exists_unique_stableJacquet F ζ hζ v inducingData P μ N hN hgood π hπ ψ
    hψcont hψunitary hcond
  have hLne : L ≠ 0 := by
    intro h
    have : L φ = 0 := by rw [h]; rfl
    exact one_ne_zero (hLφ.symm.trans this)
  have hn := normalizedWhittaker_eq_jacquet F ζ hζ v inducingData P μ hμ N hN ht hgood
    π hπ ψ hψcont hψunitary hcond J hJ φ hφ hne Eφ hEφ L hL hLne
    (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (uniformizerUnit F v π hπ ^ (e : ℤ)))
  simp only [normalizedWhittaker, hLφ, div_one] at hn
  rw [hn]
  have hcoords := stableJacquet_spherical_coordinates F ζ hζ v inducingData P μ hμ N hN ht hgood
    π hπ ψ hψcont hψunitary hcond χκ hactual ψbar hbar J hJ φ.val
    (fun k => congrArg Subtype.val (hφ k)) (by simpa using hne) Eφ hEφ e
  change (Eφ.symm (J (sphericalTranslate F ζ hζ v inducingData P π hπ φ.val e))) 0 = _
  rw [hcoords]
  have hQ : 1 < (KPLocalPrincipalSeries.residueCardinality (LocalField F v) : ℝ) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField
      (valuation (LocalField F v)).integer))
  obtain ⟨hχ, ψ₀, hψ₀ne, _, hψ₀, _, hg, _⟩ :=
    arithmetic_unit_shell_integrals F ζ hζ v hgood μ hμ π hπ ψ
      hψcont hψunitary hcond χκ hactual
  have hψeq : ψ₀ = ψbar := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective
      (R := (valuation (LocalField F v)).integer) x
    exact (hψ₀ a).trans (hbar a).symm
  rw [hψeq] at hg
  have hzero : KPThreeShell.shell
      (KPLocalPrincipalSeries.residueCardinality (LocalField F v) : ℝ)
      (g χκ ψbar 2) (g χκ ψbar 4) 0 (0 : Fin 3) = 1 := by
    rw [KPThreeShell.shell_zero _ hQ]
    norm_num [KPThreeShell.basis, Pi.add_apply, Pi.smul_apply]
  have hrem : e % 3 < 3 := Nat.mod_lt _ (by decide)
  have hdecomp : e = 3 * (e / 3) + e % 3 := by omega
  have hdiv : ((e : ℤ) / 3 : ℤ) = (e / 3 : ℕ) := by omega
  have hmod : ((e : ℤ) % 3 : ℤ) = (e % 3 : ℕ) := by omega
  rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 by omega) with hr | hr | hr
  · have hd : e = 3 * (e / 3) := by omega
    conv_lhs => rw [hd, KPThreeShell.shell_three_mul _ hQ _ _ hg]
    simp only [Pi.smul_apply, smul_eq_mul, hzero, mul_one, radialValue,
      Int.natCast_nonneg, not_lt_of_ge, ↓reduceIte, hdiv, hmod, hr,
      Nat.cast_zero, QPower, Int.cast_natCast]
  · have hd : e = 3 * (e / 3) + 1 := by omega
    conv_lhs => rw [hd, KPThreeShell.shell_three_mul_add_one _ hQ _ _ hg]
    simp only [Pi.smul_apply, smul_eq_mul, hzero, mul_one, radialValue,
      Int.natCast_nonneg, not_lt_of_ge, ↓reduceIte, hdiv, hmod, hr,
      Nat.cast_one, one_ne_zero, QPower,
      Int.cast_natCast]
  · have hd : e = 3 * (e / 3) + 2 := by omega
    rw [hd, KPThreeShell.shell_three_mul_add_two _ hQ _ _ hg]
    simp [radialValue, hmod, hr]

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellValues
