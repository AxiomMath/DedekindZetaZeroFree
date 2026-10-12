module

public import DedekindZetaZeroFree.Theta.Whittaker.TameTransposeShellCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPTameJacquetTestDuality KPLocalPrincipalSeries
open KPTameTransposeLiteralCoefficients

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

theorem actual_conductor_one_residue
    [Fintype (Residue F q)]
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    (hconductor : HasConductorIntegers F q ψ) :
    ∃! ψbar : AddChar (Residue F q) ℂ,
      HasConductorOneResidue F q π ψ ψbar := by
  obtain ⟨p, hp, he⟩ := KPTameTransposeLiteral.uniformizer_integer_irreducible F q π hπ
  let Ψ : AddChar (LocalField F q) ℂ :=
    { toFun := fun x => (ψ (Multiplicative.ofAdd x) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intro x y; exact congrArg Units.val (ψ.map_mul _ _) }
  have hΨ : Continuous Ψ := Units.continuous_val.comp hψ
  have hO : ∀ u : 𝒪[LocalField F q], Ψ (u : LocalField F q) = 1 := by
    intro u
    have h := (hconductor 1).mpr (by simp)
    simpa [Ψ] using congrArg Units.val (h u)
  have hexact : ∃ u : 𝒪[LocalField F q], Ψ ((u : LocalField F q) / (p : LocalField F q)) ≠ 1 := by
    have hnot : (π : LocalField F q)⁻¹ ∉ (valuation (LocalField F q)).integer := by
      intro H
      change valuation (LocalField F q) ((π : LocalField F q)⁻¹) ≤ 1 at H
      have hh := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
        (LocalField F q)).toOrderIso.monotone H
      change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
        (valuation (LocalField F q) ((π : LocalField F q)⁻¹)) ≤
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1 at hh
      rw [map_inv₀, map_inv₀, hπ, map_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hh
      omega
    have hn := (hconductor (π : LocalField F q)⁻¹).not.mpr hnot
    push Not at hn
    obtain ⟨u, hu⟩ := hn
    refine ⟨u, ?_⟩
    intro H
    apply hu
    apply Units.ext
    simpa [Ψ, he, div_eq_mul_inv] using H
  obtain ⟨ψbar, hbar, huniq⟩ := KPTameGauss.exists_residue_addChar p hp Ψ hΨ hO hexact
  refine ⟨ψbar, ?_, ?_⟩
  · exact ⟨hbar.1, fun u => by simpa [Ψ, he] using hbar.2 u⟩
  · intro ψbar' hbar'
    apply huniq ψbar'
    exact ⟨hbar'.1, fun u => by simpa [Ψ, he] using hbar'.2 u⟩

theorem actual_pi_first_residue
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ) :
    ∃! κ : MulChar (Residue F q) ℂ, HasPiFirstOrientation F ζ hζ q π κ := by
  let r := Units.map (IsLocalRing.residue (KPTameCompact.O F q)).toMonoidHom
  have hr : Function.Surjective r :=
    IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance
  let c : (KPTameCompact.O F q)ˣ → ℂˣ := fun u =>
    ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u))
  have hfiber : ∀ u v, r u = r v → c u = c v := by
    intro u v huv
    apply congrArg (ordinaryIota F ζ hζ)
    apply KPTameCompact.B3_congruent_right F q ζ hζ htame π u v
    exact congrArg Units.val huv
  let s : (Residue F q)ˣ → (KPTameCompact.O F q)ˣ := fun x => (hr x).choose
  have hs : ∀ x, r (s x) = x := fun x => (hr x).choose_spec
  have hc : ∀ u v, c (u * v) = c u * c v := by
    intro u v
    simp only [c, map_mul]
    rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1, map_mul]
  have hc1 : c 1 = 1 := by
    simp only [c, map_one]
    have H := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 π 1 1
    simp only [one_mul] at H
    have H1 : KPHilbert.B3 F ζ hζ (Sum.inr q) π 1 = 1 := by
      exact (mul_left_cancel (H.symm.trans (mul_one _).symm))
    rw [H1, map_one]
  let d : (Residue F q)ˣ →* ℂˣ :=
    { toFun := fun x => c (s x)
      map_one' := by rw [hfiber (s 1) 1 (by simpa using hs 1), hc1]
      map_mul' := by
        intro x y
        rw [hfiber (s (x * y)) (s x * s y) (by simp [hs]), hc] }
  have hd : ∀ u, d (r u) = c u := fun u => hfiber _ _ (hs _)
  refine ⟨MulChar.ofUnitHom d, ?_, ?_⟩
  · intro u
    change MulChar.ofUnitHom d ((r u : (Residue F q)ˣ) : Residue F q) = _
    rw [MulChar.ofUnitHom_coe, hd]
  · intro κ hκ
    apply MulChar.ext
    intro x
    obtain ⟨u, rfl⟩ := hr x
    rw [MulChar.ofUnitHom_coe, hd]
    exact hκ u

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end
