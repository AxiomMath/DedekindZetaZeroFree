module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.InverseRootEndpointValues
public import DedekindZetaZeroFree.Metaplectic.Torus.CubicHeisenbergInducingData
public import DedekindZetaZeroFree.Theta.Whittaker.TameTransposeResidueNormalization
public import DedekindZetaZeroFree.CharacterSums.Cubic.UniformizerFirstResiduePhase

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.TameInverseRootValueAudit
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameTransposeLiteralCoefficients KPTameTransposeUnitNumeratorSteps
open _root_.DedekindZetaZeroFree.TameInverseRootValueAudit renaming eventual_actual_inverse_root_endpoint → eventual_actual_inverse_root_endpoint

open _root_.DedekindZetaZeroFree.KPTameTransposeLiteralShell renaming measurable_integerUnitShell → measurable_integerUnitShell

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem ordinary_plus_phase_power
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (e : rootsOfUnity 3 F) (i : Fin 3) :
    (ordinaryIota F ζ hζ (e ^ ((i.val : ℤ) + 1)) : ℂ) =
      (ordinaryIota F ζ hζ e : ℂ) ^ (((i.val : ZMod 3) + 1).val) := by
  have h3 : e ^ 3 = 1 := by
    apply Subtype.ext
    exact e.property
  have he : e ^ ((i.val : ℤ) + 1) = e ^ (((i.val : ZMod 3) + 1).val) := by
    rw [zpow_eq_zpow_emod' _ h3]
    fin_cases i <;> norm_num [ZMod.val]
  rw [he, map_pow, Units.val_pow_eq_pow_val]

theorem eventual_actual_inverse_root_outer_gauss
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : KPTameTransposeLiteral.RawNormalizedExtension F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ) (hbar : HasConductorOneResidue F q π ψ ψbar) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : Fin 3,
      ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m f →
      (∫ u in KPTameGauss.integerUnitShell (LocalField F q),
        ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
            (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-u / π))).val 1 *
                (ψ (Multiplicative.ofAdd (u / π)) : ℂ) ∂μ) =
        (rootMass F ζ hζ q μ m : ℂ) *
          (residueCardinality (LocalField F q) : ℂ) ^ (-(i.val : ℤ) - 3) *
            g κ ψbar ((i.val : ZMod 3) + 1) := by
  obtain ⟨M, hM⟩ := eventual_actual_inverse_root_endpoint F ζ hζ q S P μ hμ
    hP htame hnormalized π hπ
  obtain ⟨p, hpirr, hp⟩ := KPTameTransposeLiteral.uniformizer_integer_irreducible F q π hπ
  refine ⟨M, ?_⟩
  intro m hm i f hf
  let c : ℂ := (rootMass F ζ hζ q μ m : ℂ) *
    (residueCardinality (LocalField F q) : ℂ) ^ (-(i.val : ℤ) - 2)
  have hpoint : ∀ u ∈ KPTameGauss.integerUnitShell (LocalField F q),
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
            (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-u / π))).val 1 *
                (ψ (Multiplicative.ofAdd (u / π)) : ℂ) =
      c * KPTameGauss.residueShellIntegrand κ
        (AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp ψ)) p
          ((i.val : ZMod 3) + 1) u := by
    rintro x ⟨u, hu, hunit⟩
    obtain ⟨U, hU⟩ := hunit
    have hx : x = (KPTameCompact.unitInclusion F q U : LocalField F q) := by
      exact hu.symm.trans (congrArg (fun z : KPTameCompact.O F q => (z : LocalField F q)) hU.symm)
    rw [hx, (hM m hm i f hf U).2]
    rw [KPTameTransposeLiteralShell.residueShellIntegrand_eq_tame_phase
      F ζ hζ q π ψ κ hκ p hp ((i.val : ZMod 3) + 1) U,
      ordinary_plus_phase_power F ζ hζ _ i]
    dsimp [c]
    ring
  rw [setIntegral_congr_fun (measurable_integerUnitShell F q) hpoint, integral_const_mul]
  rw [KPTameTransposeLiteral.actual_residue_unit_haar_integral F q μ hμ p hpirr ψ hψ
    κ ψbar (by simpa only [hp] using hbar.2) ((i.val : ZMod 3) + 1)]
  have hQ : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Residue F q)).ne'
  have hexp : -(i.val : ℤ) - 3 = (-(i.val : ℤ) - 2) + (-1) := by omega
  rw [hexp, zpow_add₀ hQ, zpow_neg_one]
  dsimp [c, g]
  ring

end DedekindZetaZeroFree.TameInverseRootValueAudit

end
