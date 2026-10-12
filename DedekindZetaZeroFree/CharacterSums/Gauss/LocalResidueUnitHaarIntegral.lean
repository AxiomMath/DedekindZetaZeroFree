module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedResidueCharacterExtensions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteral
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
variable [Fintype (RawResidue F q)]

theorem uniformizer_integer_irreducible (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ p : KPTameCompact.O F q, Irreducible p ∧ (p : LocalField F q) = π := by
  let K := LocalField F q
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hxle : valuation K (π : K) ≤ 1 := by
    apply e.toOrderIso.le_iff_le.mp
    change e (valuation K (π : K)) ≤ e 1
    rw [hπ, map_one, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by decide)
  let p : KPTameCompact.O F q := ⟨(π : K), hxle⟩
  have hspan : IsLocalRing.maximalIdeal (KPTameCompact.O F q) = Ideal.span {p} := by
    ext y
    change y ∈ IsLocalRing.maximalIdeal (KPTameCompact.O F q) ↔
      y ∈ (Ideal.span {p} : Set (KPTameCompact.O F q))
    rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
    change ¬IsUnit y ↔ valuation K (y : K) ≤ valuation K (π : K)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rw [← e.toOrderIso.lt_iff_lt, ← e.toOrderIso.le_iff_le]
    change e (valuation K (y : K)) < e 1 ↔
      e (valuation K (y : K)) ≤ e (valuation K (π : K))
    rw [map_one, hπ]
    by_cases hy : e (valuation K (y : K)) = 0
    · rw [hy]; simp
    · rw [← WithZero.exp_log hy, ← WithZero.exp_zero, WithZero.exp_lt_exp,
        WithZero.exp_le_exp]
      omega
  refine ⟨p, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal p ?_ hspan, rfl⟩
  intro H
  exact π.ne_zero (congrArg Subtype.val H)

include hμ in

theorem actual_residue_unit_haar_integral
    (π : KPTameCompact.O F q) (hπ : Irreducible π)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    (κ : MulChar (RawResidue F q) ℂ)
    (ψbar : AddChar (RawResidue F q) ℂ)
    (hbar : ∀ u : KPTameCompact.O F q,
      ψbar (IsLocalRing.residue (KPTameCompact.O F q) u) =
        (ψ (Multiplicative.ofAdd ((u : LocalField F q) / (π : LocalField F q))) : ℂ))
    (j : ZMod 3) :
    (∫ x in KPTameGauss.integerUnitShell (LocalField F q),
      KPTameGauss.residueShellIntegrand κ
        (AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp ψ)) π j x ∂μ) =
      KPTameGauss.cubicGaussSum κ ψbar j /
        (residueCardinality (LocalField F q) : ℂ) := by
  have hcont : Continuous
      (AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp ψ)) := by
    change Continuous (fun x : LocalField F q => (ψ (Multiplicative.ofAdd x) : ℂ))
    exact Units.continuous_val.comp hψ
  simpa only [residueCardinality, Nat.card_eq_fintype_card] using
    KPTameGauss.additive_haar_shell_integral μ hμ π hπ κ
      (AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp ψ)) hcont ψbar hbar j

end DedekindZetaZeroFree.KPTameTransposeLiteral

end
