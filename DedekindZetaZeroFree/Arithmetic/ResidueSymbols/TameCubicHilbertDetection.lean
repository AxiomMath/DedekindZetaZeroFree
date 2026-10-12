module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLowShellSupport

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
open LocalFieldTheory.IsNonarchimedeanLocalField

theorem exists_tame_cubic_unit_detecting_exponent
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (KPTameCompact.K F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (KPTameCompact.K F q)
      (valuation (KPTameCompact.K F q) (π : KPTameCompact.K F q)) =
        WithZero.exp (-1 : ℤ))
    (e : ℤ) (he : (e : ZMod 3) ≠ 0) :
    ∃ u : (KPTameCompact.O F q)ˣ,
      (((KPLocalCover.coefficientEmbedding F ζ hζ
        (KPLocalCover.threeToSix F
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π
            (KPTameCompact.unitInclusion F q u)))) : ℂ) ^ e) ≠ 1 := by
  let K := KPTameCompact.K F q
  let p := ClassFieldTheory.powerClass K (3 : ℕ+)
  let B := KPHilbert.finiteThreePairing F ζ hζ q
  have hvπ : valuationMap K (Additive.ofMul π) = -1 := by
    change Multiplicative.toAdd (WithZero.unzero _) = -1
    rw [WithZero.toAdd_unzero_eq_log]
    change WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (KPTameCompact.K F q))
      (valuation (KPTameCompact.K F q) (π : KPTameCompact.K F q))) = -1
    rw [hπ, WithZero.log_exp]
  have hvπinv : valuationMap K (Additive.ofMul π⁻¹) = 1 := by
    rw [valuationMap_ofMul_inv, hvπ]
    norm_num
  by_contra hn
  push Not at hn
  have hu : ∀ u : (KPTameCompact.O F q)ˣ,
      B (p (π ^ e)) (p (KPTameCompact.unitInclusion F q u)) = 1 := by
    intro u
    have hc : KPLocalCover.coefficientEmbedding F ζ hζ
        (KPLocalCover.threeToSix F
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π
            (KPTameCompact.unitInclusion F q u)) ^ e) = 1 := by
      apply Units.ext
      simpa only [map_zpow, Units.val_zpow_eq_zpow_val, Units.val_one] using hn u
    have h6 := KPLocalCover.coefficientEmbedding_injective F ζ hζ
      (hc.trans (map_one _).symm)
    have h3 : (KPHilbert.B3 F ζ hζ (Sum.inr q) π
        (KPTameCompact.unitInclusion F q u)) ^ e = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ))
        (by simpa only [← map_zpow, map_one] using h6)
    rw [KPHilbert.B3_canonical] at h3
    simpa only [p, B, map_zpow, MonoidHom.zpow_apply] using h3
  have hs : B (p π) (p π) = 1 := by
    simpa only [KPHilbert.B3_canonical] using
      ((KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 π).1
  have hall : ∀ x : Kˣ, B (p (π ^ e)) (p x) = 1 := by
    intro x
    obtain ⟨u, hx⟩ := exists_integerUnit_mul_uniformizer_zpow K π⁻¹ hvπinv x
    rw [← hx]
    simp only [map_mul, map_zpow, map_inv, MonoidHom.zpow_apply, MonoidHom.inv_apply]
    have huu := hu u
    simp only [map_zpow, MonoidHom.zpow_apply] at huu
    change B (p π) (p ((integerUnitsToFieldUnits K) u)) ^ e = 1 at huu
    rw [huu]
    simp [hs]
  have hclass : p (π ^ e) = 1 := by
    apply NormalizedSymbolTransport.inverseTransport_left_nondegenerate
      (KPHilbert.finiteRootsThree F ζ hζ q)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (KPHilbert.rootsThree F ζ hζ) q)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3
        (KPHilbert.rootsThree F ζ hζ) q).2.2.1.1
    intro b
    induction b using QuotientGroup.induction_on with
    | H x => exact hall x
  obtain ⟨t, ht⟩ := (ClassFieldTheory.powerClass_eq_one_iff K 3 (π ^ e)).mp hclass
  have hv := congrArg (fun x : Kˣ => valuationMap K (Additive.ofMul x)) ht
  change valuationMap K (Additive.ofMul (t ^ (3 : ℕ))) =
    valuationMap K (Additive.ofMul (π ^ e)) at hv
  rw [valuationMap_ofMul_pow, valuationMap_ofMul_zpow, hvπ] at hv
  apply he
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd e 3).mpr
  refine ⟨-valuationMap K (Additive.ofMul t), ?_⟩
  linarith

end DedekindZetaZeroFree.KPTameTransposeLowShellSupport

end
