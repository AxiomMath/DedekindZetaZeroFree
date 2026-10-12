module

public import DedekindZetaZeroFree.Theta.Whittaker.SphericalJacquetShellDecomposition
public import DedekindZetaZeroFree.Theta.Whittaker.ImageRepresentationUniqueness

@[expose] public section

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain ValuativeRel

namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellNormalization

open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open ActualSpherical ActualJacquet ActualShellOutput KPRankOneShellRepair
open KPExteriorUnitShellIntegrals

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (inducingData : CanonicalFiniteInducingData F ζ hζ v)
variable (P : Polarization inducingData.heisenberg)
variable (μ : MeasureTheory.Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (hμ : μ ((valuation (LocalField F v)).integer : Set (LocalField F v)) = 1)
abbrev Image := actualCanonicalImageModule F ζ hζ v inducingData P μ hμ
abbrev ImageAction := actualCanonicalImageRepresentation F ζ hζ v inducingData P μ hμ
abbrev imageInclusion := (actualCanonicalImage F ζ hζ v inducingData P μ hμ).toSubmodule.subtype
abbrev ImageFixed (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3) :=
  fixedSubmodule (ImageAction F ζ hζ v inducingData P μ hμ) (Compact F ζ hζ v ht)
variable (N : AddGroupNorm (VMinus F ζ hζ v inducingData P))
variable (hN : ∀ (c : ℂ) (b : VMinus F ζ hζ v inducingData P), N (c • b) = ‖c‖ * N b)

def sphericalFunctional
    (J : IMinusActual F ζ hζ v inducingData P →ₗ[ℂ] VMinus F ζ hζ v inducingData P)
    (Eφ : (Fin 3 → ℂ) ≃ₗ[ℂ] VMinus F ζ hζ v inducingData P) :
    Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ :=
  (LinearMap.proj (0 : Fin 3)).comp
    (Eφ.symm.toLinearMap.comp (J.comp (imageInclusion F ζ hζ v inducingData P μ hμ)))

def IsWhittaker (ψ : AddChar (LocalField F v) ℂ)
    (L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (t : LocalField F v) (f : Image F ζ hζ v inducingData P μ hμ),
    L (ImageAction F ζ hζ v inducingData P μ hμ
      (inducingData.borel.upperRoot (Multiplicative.ofAdd t) : ActualCover F ζ hζ v) f) =
      ψ t * L f

def normalizedWhittaker
    (φ : Image F ζ hζ v inducingData P μ hμ)
    (L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ)
    (g : ActualCover F ζ hζ v) : ℂ :=
  L (ImageAction F ζ hζ v inducingData P μ hμ g φ) / L φ

variable (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
variable (hgood : valuation (LocalField F v) (6 : LocalField F v) = 1)
variable (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
variable (ψ : AddChar (LocalField F v) ℂ)
variable (hψcont : Continuous ψ) (hψunitary : ∀ x, ‖ψ x‖ = 1)
variable (hcond : ConductorZero ψ π)
variable (J : IMinusActual F ζ hζ v inducingData P →ₗ[ℂ] VMinus F ζ hζ v inducingData P)
variable (hJ : IsStableJacquet F ζ hζ v inducingData P μ N hN ψ π J)
variable (φ : Image F ζ hζ v inducingData P μ hμ)
variable (hφ : φ ∈ ImageFixed F ζ hζ v inducingData P μ hμ ht) (hne : φ ≠ 0)
variable (Eφ : (Fin 3 → ℂ) ≃ₗ[ℂ] VMinus F ζ hζ v inducingData P)
variable (hEφ : ∀ j : ℤ, Eφ (KPThreeShell.basis j) =
  bCoordinate F ζ hζ v inducingData P (uniformizerUnit F v π hπ) φ.val j)

include hgood hπ hψcont hψunitary hcond hJ in

theorem sphericalFunctional_whittaker :
    IsWhittaker F ζ hζ v inducingData P μ hμ ψ (sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ) := by
  intro t f
  change (Eφ.symm (J (IMinus inducingData.borel P _
    (imageInclusion F ζ hζ v inducingData P μ hμ f)))) 0 = _
  rw [stableJacquet_unipotent F ζ hζ v inducingData P μ N hN π hπ ψ hψunitary J hJ]
  simp [sphericalFunctional]

include ht hgood hπ hψcont hψunitary hcond hJ hφ hne hEφ in

theorem sphericalFunctional_at_spherical :
    sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ φ = 1 := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (valuation (LocalField F v)).integer)
  obtain ⟨χκ, hχκ, _⟩ := exists_unique_arithmetic_residue_character F ζ hζ v hgood
  obtain ⟨ψbar, hbar, _⟩ := exists_unique_residue_addChar π hπ ψ hψcont hψunitary hcond
  have hc := stableJacquet_spherical_coordinates F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ
    hψcont hψunitary hcond χκ hχκ.2 ψbar hbar.2.2 J hJ φ.val (fun k => congrArg Subtype.val (hφ k)) (by simpa using hne) Eφ hEφ 0
  have hf : sphericalTranslate F ζ hζ v inducingData P π hπ φ.val 0 =
      imageInclusion F ζ hζ v inducingData P μ hμ φ := by
    simp [sphericalTranslate, KPPGLLocalCover.A, KPStandardLocalRootLifts.A_one]
  rw [hf] at hc
  change (Eφ.symm (J (imageInclusion F ζ hζ v inducingData P μ hμ φ))) 0 = 1
  rw [hc]
  simp [KPThreeShell.shell, KPThreeShell.basis, Finset.sum_filter]

include ht hgood hπ hψcont hψunitary hcond hJ hφ hne hEφ in

theorem whittaker_scalar_multiple
    (L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ)
    (hL : IsWhittaker F ζ hζ v inducingData P μ hμ ψ L) :
    L = (L φ) • sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ := by
  classical
  let χ : Multiplicative (LocalField F v) →ₜ* ℂˣ := {
    toFun := fun t => (ψ.val_isUnit (Multiplicative.toAdd t)).unit
    map_one' := by apply Units.ext; simp
    map_mul' := by
      intro x y
      apply Units.ext
      simp [ψ.map_add_eq_mul]
    continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
      (by
        have he : (Units.val ∘ fun t => (ψ.val_isUnit (Multiplicative.toAdd t)).unit) =
            (fun t => ψ (Multiplicative.toAdd t)) := by
          funext t
          exact (ψ.val_isUnit _).unit_spec
        rw [he]
        exact hψcont.comp continuous_toAdd) }
  have hχ (t : Multiplicative (LocalField F v)) : (χ t : ℂ) = ψ (Multiplicative.toAdd t) :=
    (ψ.val_isUnit _).unit_spec
  have hχne : χ.toMonoidHom ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := hcond.2
    apply hu
    have hh := congrArg (fun c : Multiplicative (LocalField F v) →* ℂˣ =>
      (c (Multiplicative.ofAdd ((π : LocalField F v)⁻¹ * (u : LocalField F v))) : ℂ)) h
    simpa [hχ] using hh
  have h6 : IsUnit (6 : (valuation (LocalField F v)).integer) :=
    (Valuation.integer.integers (valuation (LocalField F v))).isUnit_iff_valuation_eq_one.mpr
      (by simpa only [map_ofNat] using hgood)
  have h3 : IsUnit (3 : (valuation (LocalField F v)).integer) := by
    apply isUnit_of_mul_isUnit_right (x := (2 : (valuation (LocalField F v)).integer))
    convert h6 using 1 <;> norm_num
  have ht3 : (3 : (valuation (LocalField F v)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F v)).integer := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h3
  let S := RootEquivariantMaps (ImageAction F ζ hζ v inducingData P μ hμ)
    (KPLocalJacquetImage.root inducingData.borel) χ.toMonoidHom ℂ
  have hrank : Module.rank ℂ S ≤ 1 :=
    ActualWhittaker.rank_le_one F ζ hζ v inducingData P μ hμ ht3 χ hχne
  letI : Module.Finite ℂ S := Module.rank_lt_aleph0_iff.mp
    (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hle : Module.finrank ℂ S ≤ 1 := Module.finrank_le_of_rank_le
    (by simpa using hrank : Module.rank ℂ S ≤ (1 : ℕ))
  have hmem (l : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ)
      (hl : IsWhittaker F ζ hζ v inducingData P μ hμ ψ l) : l ∈ S := by
    intro t f
    simpa [KPLocalJacquetImage.root, hχ, smul_eq_mul] using hl (Multiplicative.toAdd t) f
  let l₀ : S := ⟨sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ,
    hmem _ (sphericalFunctional_whittaker F ζ hζ v inducingData P μ hμ N hN hgood π hπ ψ
      hψcont hψunitary hcond J hJ Eφ)⟩
  have hval := sphericalFunctional_at_spherical F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ
    hψcont hψunitary hcond J hJ φ hφ hne Eφ hEφ
  have hl₀ : l₀ ≠ 0 := by
    intro h
    have hz := congrArg (fun l : S => l.val φ) h
    change sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ φ = 0 at hz
    rw [hval] at hz
    exact one_ne_zero hz
  letI : Nontrivial S := ⟨⟨l₀, 0, hl₀⟩⟩
  have hdim : Module.finrank ℂ S = 1 := le_antisymm hle (Module.finrank_pos (R := ℂ) (M := S))
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hl₀ (⟨L, hmem L hL⟩ : S)
  have hc' : c • sphericalFunctional F ζ hζ v inducingData P μ hμ J Eφ = L := congrArg Subtype.val hc
  have hcval := congrArg (fun l : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ => l φ) hc'
  simp only [LinearMap.smul_apply, smul_eq_mul, hval, mul_one] at hcval
  rw [← hcval]
  exact hc'.symm

include ht hgood hπ hψcont hψunitary hcond hJ hφ hne hEφ in

theorem whittaker_spherical_ne_zero
    (L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ)
    (hL : IsWhittaker F ζ hζ v inducingData P μ hμ ψ L) (hLne : L ≠ 0) :
    L φ ≠ 0 := by
  intro hz
  apply hLne
  rw [whittaker_scalar_multiple F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ hψcont
    hψunitary hcond J hJ φ hφ hne Eφ hEφ L hL, hz, zero_smul]

include ht hgood hπ hψcont hψunitary hcond hJ hφ hne hEφ in

theorem normalizedWhittaker_eq_jacquet
    (L : Image F ζ hζ v inducingData P μ hμ →ₗ[ℂ] ℂ)
    (hL : IsWhittaker F ζ hζ v inducingData P μ hμ ψ L) (hLne : L ≠ 0)
    (g : ActualCover F ζ hζ v) :
    normalizedWhittaker F ζ hζ v inducingData P μ hμ φ L g =
      (Eφ.symm (J (imageInclusion F ζ hζ v inducingData P μ hμ
        (ImageAction F ζ hζ v inducingData P μ hμ g φ)))) (0 : Fin 3) := by
  have hn := whittaker_spherical_ne_zero F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ
    hψcont hψunitary hcond J hJ φ hφ hne Eφ hEφ L hL hLne
  have hs := whittaker_scalar_multiple F ζ hζ v inducingData P μ hμ N hN ht hgood π hπ ψ
    hψcont hψunitary hcond J hJ φ hφ hne Eφ hEφ L hL
  unfold normalizedWhittaker
  conv_lhs => arg 1; rw [hs]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [mul_div_cancel_left₀ _ hn]
  rfl

end
end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualShellNormalization
