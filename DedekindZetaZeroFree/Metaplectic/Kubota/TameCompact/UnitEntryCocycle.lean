module

public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.CorrectionAndDeterminantTwist

@[expose] public section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPTameCompact

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (hv : ringChar (O F v ⧸ p F v) ≠ 3)

private lemma norm_unit (x : K F v) (hx : ‖x‖ = 1) :
    ∃ u : (O F v)ˣ, (unitInclusion F v u : K F v) = x := by
  letI : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have hnorm : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
    apply le_antisymm
    · simpa using (Valued.toNormedField.norm_le_iff (x := x) (x' := 1)).mp (by simp [hx])
    · simpa using (Valued.toNormedField.norm_le_iff (x := 1) (x' := x)).mp (by simp [hx])
  have mem (y : K F v) (hy : (Valued.v y : WithZero (Multiplicative ℤ)) ≤ 1) : y ∈ O F v := by
    change ValuativeRel.valuation (K F v) y ≤ 1
    rw [← Valuation.vle_one_iff, Valuation.vle_one_iff (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ)))]
    exact hy
  have hn : x ≠ 0 := by intro h; simp [h] at hx
  let u : (O F v)ˣ := ⟨⟨x, mem x hnorm.le⟩, ⟨x⁻¹, mem _ (by simp [map_inv₀, hnorm])⟩,
    by apply Subtype.ext; simp [hn], by apply Subtype.ext; simp [hn]⟩
  exact ⟨u, rfl⟩

private lemma norm_integer_le_one (x : O F v) : ‖(x : K F v)‖ ≤ 1 := by
  letI : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← norm_one (α := K F v)]
  apply (Valued.toNormedField.norm_le_iff (x := (x : K F v)) (x' := 1)).mpr
  simp only [map_one]
  exact (Valuation.vle_one_iff (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ)))).mp
    ((Valuation.vle_one_iff (ValuativeRel.valuation (K F v))).mpr x.property)

private lemma norm_of_integer_unit (x : (O F v)ˣ) :
    ‖(unitInclusion F v x : K F v)‖ = 1 := by
  have h1 := norm_integer_le_one F v (x : O F v)
  have h2 := norm_integer_le_one F v (x⁻¹ : (O F v)ˣ)
  change ‖(unitInclusion F v x : K F v)‖ ≤ 1 at h1
  change ‖(unitInclusion F v (x⁻¹) : K F v)‖ ≤ 1 at h2
  have hi : ‖(unitInclusion F v x : K F v)⁻¹‖ ≤ 1 := by simpa using h2
  have hpos : 0 < ‖(unitInclusion F v x : K F v)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have heq : ‖(unitInclusion F v x : K F v)‖ *
      ‖(unitInclusion F v x : K F v)⁻¹‖ = 1 := by
    rw [← norm_mul, mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  nlinarith [norm_nonneg ((unitInclusion F v x : K F v)⁻¹)]

include hv

private lemma B3_norm_units (x y : (K F v)ˣ)
    (hx : ‖(x : K F v)‖ = 1) (hy : ‖(y : K F v)‖ = 1) :
    KPHilbert.B3 F ζ hζ (Sum.inr v) x y = 1 := by
  obtain ⟨u, hu⟩ := norm_unit F v _ hx
  obtain ⟨w, hw⟩ := norm_unit F v _ hy
  have eu : unitInclusion F v u = x := Units.ext hu
  have ew : unitInclusion F v w = y := Units.ext hw
  rw [← eu, ← ew]
  exact B3_units F v ζ hζ hv u w

private lemma B3_norm_congruent (x y y' : (K F v)ˣ)
    (hy : ‖(y : K F v)‖ = 1) (hy' : ‖(y' : K F v)‖ = 1)
    (hdiff : ‖(y : K F v) - (y' : K F v)‖ < 1) :
    KPHilbert.B3 F ζ hζ (Sum.inr v) x y =
      KPHilbert.B3 F ζ hζ (Sum.inr v) x y' := by
  obtain ⟨u, hu⟩ := norm_unit F v _ hy
  obtain ⟨w, hw⟩ := norm_unit F v _ hy'
  have eu : unitInclusion F v u = y := Units.ext hu
  have ew : unitInclusion F v w = y' := Units.ext hw
  rw [← eu, ← ew]
  apply B3_congruent_right F v ζ hζ hv
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  letI : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  change (u : O F v) - w ∈ IsLocalRing.maximalIdeal (O F v)
  apply (Valuation.mem_maximalIdeal_iff (K F v) (ValuativeRel.valuation (K F v))).mpr
  rw [← Valuation.vlt_one_iff, Valuation.vlt_one_iff
    (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ)))]
  have hd : ‖((u : O F v) : K F v) - ((w : O F v) : K F v)‖ < ‖(1 : K F v)‖ := by
    change ‖(unitInclusion F v u : K F v) - (unitInclusion F v w : K F v)‖ < _
    simpa [hu, hw] using hdiff
  exact (lt_iff_not_ge).mpr (fun hn => (not_le_of_gt hd)
    ((Valued.toNormedField.norm_le_iff).mpr (by simpa using hn)))

private lemma X_inclusion (g : K0 F v) (hc : c F v g ≠ 0) :
    KubotaRankTwo.X (K F v) (inclusion F v g) = Units.mk0 (c F v g) hc := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, inclusion,
    KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hc]

include hv

theorem unit_unit (g h : K0 F v)
    (hc : ‖c F v g‖ = 1) (he : ‖c F v h‖ = 1) :
    kappa F v ζ hζ (g * h) =
      kappa F v ζ hζ g * kappa F v ζ hζ h *
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
          (inclusion F v g) (inclusion F v h) := by
  have hc0 : c F v g ≠ 0 := by intro h0; simp [h0] at hc
  have he0 : c F v h ≠ 0 := by intro h0; simp [h0] at he
  rw [kappa_norm_one F v ζ hζ g hc, kappa_norm_one F v ζ hζ h he,
    one_mul, one_mul]
  let C : (K F v)ˣ := Units.mk0 (c F v g) hc0
  let E : (K F v)ˣ := Units.mk0 (c F v h) he0
  let D : (K F v)ˣ := Matrix.GeneralLinearGroup.det (inclusion F v g)
  let H : (K F v)ˣ := Matrix.GeneralLinearGroup.det (inclusion F v h)
  let Z := KubotaRankTwo.X (K F v) (inclusion F v (g * h))
  let B := KPHilbert.B3 F ζ hζ (Sum.inr v)
  have hD : ‖(D : K F v)‖ = 1 := (det_norm_and_entries F v g).1
  have hH : ‖(H : K F v)‖ = 1 := (det_norm_and_entries F v h).1
  have hC : ‖(C : K F v)‖ = 1 := hc
  have hE : ‖(E : K F v)‖ = 1 := he
  have hED : ‖((E * D : (K F v)ˣ) : K F v)‖ = 1 := by
    change ‖(E : K F v) * (D : K F v)‖ = 1
    simp [norm_mul, hE, hD]
  have hratio : ‖((C / (E * D) : (K F v)ˣ) : K F v)‖ = 1 := by
    simp only [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, hC, hE, hD, one_mul, div_self one_ne_zero]
  obtain ⟨hL, hR, hskew, _, _, halt⟩ := KPHilbert.B3_laws F ζ hζ (Sum.inr v)
  have hsigma : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
      (inclusion F v g) (inclusion F v h) = B Z (C / (E * D)) := by
    unfold KPLocalCover.sigmaTwo
    rw [det_twist_trivial F v ζ hζ hv g h, mul_one]
    unfold KubotaElementaryLastArgument.tau
    rw [← map_mul, X_inclusion F v hv g hc0, X_inclusion F v hv h he0]
    change B (Z / C) (Z / (E * D)) = B Z (C / (E * D))
    rw [KubotaDefectSymbolAlgebra.div_left _ _ B hL,
      KubotaDefectSymbolAlgebra.div_right _ _ B hR,
      KubotaDefectSymbolAlgebra.div_right _ _ B hR,
      KubotaDefectSymbolAlgebra.div_right _ _ B hR]
    dsimp only [B]
    rw [(halt Z).1, B3_norm_units F ζ hζ v hv C (E * D) hC hED,
      hskew C Z]
    simp only [one_div, div_one]
    change (B Z (E * D))⁻¹ / (B Z C)⁻¹ = B Z C / B Z (E * D)
    exact inv_div_inv _ _
  rw [hsigma]
  by_cases hsmall : ‖c F v (g * h)‖ < 1
  · have htunit := (diagonal_units F v (g * h) hsmall).2.1
    obtain ⟨T, hT⟩ := htunit
    have ht : ‖d F v (g * h)‖ = 1 := by
      have hn := norm_of_integer_unit F v T
      change ‖((T : O F v) : K F v)‖ = 1 at hn
      simpa only [hT] using hn
    have ht0 := (diagonal_units F v (g * h) hsmall).2.2.2
    by_cases hz : c F v (g * h) = 0
    · rw [kappa_zero F v ζ hζ (g * h) hz]
      symm
      apply B3_norm_units F ζ hζ v hv Z (C / (E * D)) _ hratio
      change ‖KubotaRankTwo.x (K F v) (inclusion F v (g * h))‖ = 1
      unfold KubotaRankTwo.x
      have hzmap : ((inclusion F v (g * h) : Matrix (Fin 2) (Fin 2) (K F v))) 1 0 = 0 := hz
      rw [if_pos hzmap]
      exact ht
    · have hzX : Z = Units.mk0 (c F v (g * h)) hz := X_inclusion F v hv (g * h) hz
      have hdet : Δ F v (g * h) = (D : K F v) * (H : K F v) := by
        simp [Δ, D, H]
      let Y : (K F v)ˣ := Units.mk0 (d F v (g * h) / Δ F v (g * h))
        (div_ne_zero ht0 (Matrix.GeneralLinearGroup.det_ne_zero (inclusion F v (g * h))))
      have hy : ‖(Y : K F v)‖ = 1 := by
        change ‖d F v (g * h) / Δ F v (g * h)‖ = 1
        rw [norm_div, ht, (det_norm_and_entries F v (g * h)).1, div_self one_ne_zero]
      have hyr : ‖((-(C / (E * D)) : (K F v)ˣ) : K F v)‖ = 1 := by
        change ‖-((C / (E * D) : (K F v)ˣ) : K F v)‖ = 1
        simpa using hratio
      have hid : c F v h * d F v (g * h) =
          d F v h * c F v (g * h) - c F v g * Δ F v h := by
        simp only [d, c, Δ, inclusion, KPLocalCube.integerInclusion,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          map_add, map_mul, Matrix.GeneralLinearGroup.val_det_apply,
          Matrix.det_fin_two, Matrix.GeneralLinearGroup.map_apply]
        simp only [Subring.coe_add, Subring.coe_mul, Subring.subtype_apply]
        ring
      have hdiff : (Y : K F v) - (-(C / (E * D)) : (K F v)ˣ) =
          d F v h * c F v (g * h) / ((E : K F v) * (D : K F v) * (H : K F v)) := by
        simp only [Units.val_neg, Units.val_div_eq_div_val, Units.val_mul]
        change d F v (g * h) / Δ F v (g * h) -
          -(c F v g / (c F v h * (D : K F v))) = _
        rw [hdet]
        have hnE := E.ne_zero
        have hnD := D.ne_zero
        have hnH := H.ne_zero
        change c F v h * d F v (g * h) = d F v h * c F v (g * h) - c F v g * (H : K F v) at hid
        change (E : K F v) * d F v (g * h) = d F v h * c F v (g * h) - c F v g * (H : K F v) at hid
        change d F v (g * h) / ((D : K F v) * H) -
          -(c F v g / ((E : K F v) * D)) = _
        field_simp
        linear_combination hid
      have hdsmall : ‖(Y : K F v) - (-(C / (E * D)) : (K F v)ˣ)‖ < 1 := by
        rw [hdiff]
        simp only [norm_div, norm_mul, hE, hD, hH, one_mul, div_one]
        have hdle := (det_norm_and_entries F v h).2 1 1
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hdle) hsmall
      have hk : kappa F v ζ hζ (g * h) = B Z Y := by
        simp only [kappa, dif_pos hz, dif_pos ht0, dif_pos hsmall]
        rw [hzX]
      rw [hk]
      dsimp only [B]
      rw [B3_norm_congruent F ζ hζ v hv Z Y (-(C / (E * D))) hy hyr hdsmall]
      have hn : -(C / (E * D)) = (-1 : (K F v)ˣ) * (C / (E * D)) := by simp
      rw [hn, hR, (halt Z).2.1, one_mul]
  · have hn : ‖c F v (g * h)‖ = 1 := le_antisymm
        ((det_norm_and_entries F v (g * h)).2 1 0) (le_of_not_gt hsmall)
    have hz : c F v (g * h) ≠ 0 := by intro hz; simp [hz] at hn
    rw [kappa_norm_one F v ζ hζ (g * h) hn]
    symm
    apply B3_norm_units F ζ hζ v hv Z (C / (E * D)) _ hratio
    rw [show Z = Units.mk0 (c F v (g * h)) hz from X_inclusion F v hv (g * h) hz]
    exact hn

end
end DedekindZetaZeroFree.KPTameCompact
