module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubeNeighborhoodsAndMatrixCongruences
public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalCoverAlgebra
public import DedekindZetaZeroFree.Arithmetic.Kummer.CubicSexticArtinNormalization

@[expose] public section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPTameCompact

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

abbrev K := KPLocalCube.LocalField F v

abbrev O := KPLocalCube.LocalIntegers F v

abbrev p := KPLocalCube.maximalIdeal F v

abbrev K0 := KPLocalCube.IntegerGL2 F v

abbrev inclusion : K0 F v →* Matrix.GeneralLinearGroup (Fin 2) (K F v) :=
  KPLocalCube.integerInclusion F v

theorem inclusion_injective : Function.Injective (inclusion F v) := by
  intro x y h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Subtype.ext
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (K F v) => g i j) h

abbrev a (g : K0 F v) : K F v := (g 0 0 : K F v)
abbrev b (g : K0 F v) : K F v := (g 0 1 : K F v)
abbrev c (g : K0 F v) : K F v := (g 1 0 : K F v)
abbrev d (g : K0 F v) : K F v := (g 1 1 : K F v)

abbrev Δ (g : K0 F v) : K F v :=
  (Matrix.GeneralLinearGroup.det (inclusion F v g) : K F v)

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hv : ringChar (O F v ⧸ p F v) ≠ 3)

abbrev unitInclusion : (O F v)ˣ →* (K F v)ˣ :=
  KPHilbert.integerUnitInclusion F v

omit hv

def active (g : K0 F v) : Prop :=
  c F v g ≠ 0 ∧ d F v g ≠ 0 ∧ ‖c F v g‖ < 1

def kappa (g : K0 F v) : rootsOfUnity 3 F :=
  if hc : c F v g ≠ 0 then
    if hd : d F v g ≠ 0 then
      if _hn : ‖c F v g‖ < 1 then
        KPHilbert.B3 F ζ hζ (Sum.inr v)
          (Units.mk0 (c F v g) hc)
          (Units.mk0 (d F v g / Δ F v g)
            (div_ne_zero hd (Matrix.GeneralLinearGroup.det_ne_zero (inclusion F v g))))
      else 1
    else 1
  else 1

local instance preludeValuativeRel : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance preludeLocalField : IsNonarchimedeanLocalField (K F v) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

section TameSymbolCalculus

 local instance tamePreludeKValuativeRel : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
 local instance tamePreludeKLocalField : IsNonarchimedeanLocalField (K F v) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
 local instance tamePreludeSourceValuativeRel : ValuativeRel (KPHilbert.CFTSource F v) := GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
 local instance tamePreludeSourceLocalField : IsNonarchimedeanLocalField (KPHilbert.CFTSource F v) := GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
private lemma three_unit (hv : ringChar (O F v ⧸ p F v) ≠ 3) : IsUnit (3 : O F v) := by
  letI : Nontrivial (O F v ⧸ p F v) := Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (O F v)).ne_top
  letI : (p F v).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (O F v)
  let q := Ideal.Quotient.mk (p F v)
  letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  apply isUnit_of_map_unit q
  letI : Field (O F v ⧸ p F v) := Ideal.Quotient.field (p F v)
  apply isUnit_iff_ne_zero.mpr
  simpa only [q, map_ofNat, Nat.cast_ofNat] using CharP.cast_ne_zero_of_ne_of_prime (O F v ⧸ p F v) Nat.prime_three hv

 lemma source_order (x y : KPHilbert.CFTSource F v) :
    ValuativeRel.valuation (KPHilbert.CFTSource F v) x ≤ ValuativeRel.valuation (KPHilbert.CFTSource F v) y ↔ ‖x‖ ≤ ‖y‖ := by
  change ValuativeRel.ValueGroupWithZero.mk x 1 ≤ ValuativeRel.ValueGroupWithZero.mk y 1 ↔ _
  rw [ValuativeRel.ValueGroupWithZero.mk_le_mk]
  simp only [Submonoid.coe_one, mul_one]
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  simp only [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]

 def sourceIntegerMap : O F v →+* (ValuativeRel.valuation (KPHilbert.CFTSource F v)).integer :=
  ((relativeFinitePlaceCompletionAlgEquiv v).symm.toRingHom.comp (O F v).subtype).codRestrict _ (by
    intro x
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation (KPHilbert.CFTSource F v)), source_order, norm_one]
    change ‖(relativeFinitePlaceCompletionAlgEquiv v).symm (x : K F v)‖ ≤ 1
    rw [relativeFinitePlaceCompletionAlgEquiv_symm_norm]
    letI : (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have hn : ‖(x : K F v)‖ ≤ ‖(1 : K F v)‖ := by
      rw [Valued.toNormedField.norm_le_iff]
      rw [← Valuation.Compatible.vle_iff_le, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (K F v))]
      simpa only [map_one, Valuation.mem_integer_iff] using x.property
    simpa only [norm_one] using hn)

private lemma source_three (hv : ringChar (O F v ⧸ p F v) ≠ 3) :
    ValuativeRel.valuation (KPHilbert.CFTSource F v) (3 : KPHilbert.CFTSource F v) = 1 := by
  have hu := (three_unit F v hv).map (sourceIntegerMap F v)
  have h := (Valuation.integer.integers (ValuativeRel.valuation (KPHilbert.CFTSource F v))).isUnit_iff_valuation_eq_one.mp hu
  change ValuativeRel.valuation (KPHilbert.CFTSource F v) (((sourceIntegerMap F v) 3 : (ValuativeRel.valuation (KPHilbert.CFTSource F v)).integer) : KPHilbert.CFTSource F v) = 1 at h
  norm_num only [map_ofNat, Nat.cast_ofNat, Subring.coe_natCast] at h
  exact h

private lemma source_unit (u : (O F v)ˣ) :
  KPHilbert.cftSourceUnit F v (unitInclusion F v u) =
    LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits (KPHilbert.CFTSource F v) (Units.map (sourceIntegerMap F v).toMonoidHom u) := by
  apply Units.ext
  rfl

open Polynomial in
private lemma congruent_cube (hv : ringChar (O F v ⧸ p F v) ≠ 3)
    (u u' : (O F v)ˣ)
    (heq : Ideal.Quotient.mk (p F v) (u : O F v) = Ideal.Quotient.mk (p F v) (u' : O F v)) :
    ∃ t : (K F v)ˣ, t ^ 3 = unitInclusion F v u / unitInclusion F v u' := by
  letI : HenselianRing (O F v) (p F v) := (LocalFieldTheory.localCompleteDVF (K F v)).henselianRing
  let q := Ideal.Quotient.mk (p F v)
  let z := u / u'
  have hr : q (z : O F v) = 1 := by
    have hu : Units.map q.toMonoidHom u = Units.map q.toMonoidHom u' := Units.ext heq
    have hz : Units.map q.toMonoidHom z = 1 := by rw [show z = u / u' from rfl, _root_.map_div, hu, div_self']
    exact congrArg Units.val hz
  let P : (O F v)[X] := X ^ 3 - C (z : O F v)
  have hm : P.Monic := by
    apply monic_X_pow_sub
    simp
  have he : P.eval 1 ∈ p F v := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (P.eval 1) = 0
    simp only [P, eval_sub, eval_pow, eval_X, one_pow, eval_C, map_sub, map_one, hr, sub_self]
  have hd : IsUnit (q (P.derivative.eval 1)) := by
    have h : P.derivative.eval 1 = (3 : O F v) := by simp [P, derivative_sub, derivative_pow]
    rw [h]
    exact (three_unit F v hv).map q
  obtain ⟨w, hw, hwp⟩ := HenselianRing.is_henselian P hm 1 he hd
  have hw3 : w ^ 3 = (z : O F v) := by simpa only [IsRoot, P, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hw
  have hwn : (w : K F v) ≠ 0 := by
    intro hw0
    have wz : w = 0 := Subtype.val_injective hw0
    have hz : (z : O F v) = 0 := by simpa only [wz, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hw3.symm
    exact z.ne_zero hz
  refine ⟨Units.mk0 (w : K F v) hwn, ?_⟩
  apply Units.ext
  change (w : K F v) ^ 3 = _
  have hf := congrArg (fun x : O F v => (x : K F v)) hw3
  rw [← _root_.map_div]
  exact hf

include hv

theorem B3_units (u u' : (O F v)ˣ) :
    KPHilbert.B3 F ζ hζ (Sum.inr v)
      (unitInclusion F v u) (unitInclusion F v u') = 1 := by
  apply (KPHilbert.finiteRootsThree F ζ hζ v).injective
  rw [KPHilbert.B3_localSameCFT, map_one]
  apply (KPHilbert.cftSourceCoefficients F v 3 (KPHilbert.rootsThree F ζ hζ)).symm.injective
  erw [KPHilbert.finiteFamily_source]
  erw [map_one, ClassFieldTheory.localHilbertPairing_powerClass]
  unfold ClassFieldTheory.localHilbertSymbol
  erw [source_unit, source_unit]
  have h := LocalClassFieldTheory.Kummer.localHilbertSymbol_integerUnit_integerUnit_eq_one
    (KPHilbert.CFTSource F v) 3 (source_three F v hv) (KPHilbert.cftSourceRoots F v 3 (KPHilbert.rootsThree F ζ hζ))
    (Units.map (sourceIntegerMap F v).toMonoidHom u') (Units.map (sourceIntegerMap F v).toMonoidHom u)
  erw [h]
  exact map_one _

theorem B3_congruent_right (x : (K F v)ˣ) (u u' : (O F v)ˣ)
    (heq : (Ideal.Quotient.mk (p F v)) (u : O F v) =
      (Ideal.Quotient.mk (p F v)) (u' : O F v)) :
    KPHilbert.B3 F ζ hζ (Sum.inr v) x (unitInclusion F v u) =
      KPHilbert.B3 F ζ hζ (Sum.inr v) x (unitInclusion F v u') := by
  obtain ⟨t, ht⟩ := congruent_cube F v hv u u' heq
  have hu : unitInclusion F v u = t ^ 3 * unitInclusion F v u' := by rw [ht]; simp
  rw [hu, (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1,
    ((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.1 x t).2, one_mul]

end TameSymbolCalculus

private lemma val_norm_le (x y : K F v) :
    ValuativeRel.valuation (K F v) x ≤ ValuativeRel.valuation (K F v) y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v y ↔ _
  exact (Valued.toNormedField.norm_le_iff).symm
private lemma unit_norm (u : (O F v)ˣ) : ‖((u : O F v) : K F v)‖ = 1 := by
  have h := (Valuation.integer.integers (ValuativeRel.valuation (K F v))).valuation_unit u
  change ValuativeRel.valuation (K F v) ((u : O F v) : K F v) = 1 at h
  apply le_antisymm
  · simpa only [norm_one] using (val_norm_le F v _ 1).mp (by simpa only [map_one] using h.le)
  · simpa only [norm_one] using (val_norm_le F v 1 _).mp (by simpa only [map_one] using h.ge)
private lemma unit_iff_norm (x : O F v) : IsUnit x ↔ ‖(x : K F v)‖ = 1 := by
  have heq := (Valuation.integer.integers (ValuativeRel.valuation (K F v))).isUnit_iff_valuation_eq_one (x := x)
  change IsUnit x ↔ ValuativeRel.valuation (K F v) (x : K F v) = 1 at heq
  rw [heq, le_antisymm_iff]
  simp only [← map_one (ValuativeRel.valuation (K F v)), val_norm_le, norm_one]
  exact le_antisymm_iff.symm
private lemma small_mem (x : O F v) (h : ‖(x : K F v)‖ < 1) : x ∈ p F v := by
  change x ∈ IsLocalRing.maximalIdeal (O F v)
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit x
  rw [unit_iff_norm]
  exact ne_of_lt h

theorem det_norm_and_entries (g : K0 F v) :
    ‖Δ F v g‖ = 1 ∧ ∀ i j : Fin 2, ‖(g i j : K F v)‖ ≤ 1 := by
  constructor
  · change ‖(Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (O F v).subtype g) : K F v)‖ = 1
    rw [Matrix.GeneralLinearGroup.map_det]
    exact unit_norm F v _
  · intro i j
    simpa only [norm_one] using (val_norm_le F v (g i j : K F v) 1).mp (by simpa only [map_one, Valuation.mem_integer_iff] using (g i j).property)

theorem diagonal_units (g : K0 F v) (hc : ‖c F v g‖ < 1) :
    IsUnit (g 0 0 : O F v) ∧ IsUnit (g 1 1 : O F v) ∧
      a F v g ≠ 0 ∧ d F v g ≠ 0 := by
  let q := Ideal.Quotient.mk (p F v)
  letI : Nontrivial (O F v ⧸ p F v) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (O F v)).ne_top
  letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hcz : q (g 1 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by
    change g 1 0 ∈ IsLocalRing.maximalIdeal (O F v)
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬IsUnit (g 1 0)
    rw [unit_iff_norm]
    exact ne_of_lt hc)
  have hdet : q (g 0 0) * q (g 1 1) = q (Matrix.GeneralLinearGroup.det g : O F v) := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hcz]
  have hu : IsUnit (q (g 0 0) * q (g 1 1)) := by
    rw [hdet]
    exact (Matrix.GeneralLinearGroup.det g).isUnit.map q
  have hau := isUnit_of_map_unit q (g 0 0) (IsUnit.mul_iff.mp hu).1
  have hdu := isUnit_of_map_unit q (g 1 1) (IsUnit.mul_iff.mp hu).2
  refine ⟨hau, hdu, ?_, ?_⟩
  · exact (hau.map (O F v).subtype).ne_zero
  · exact (hdu.map (O F v).subtype).ne_zero

theorem diagonal_reduction (g : K0 F v) (hc : ‖c F v g‖ < 1) :
    ∃ u u' : (O F v)ˣ,
      (unitInclusion F v u : K F v) = d F v g / Δ F v g ∧
      (unitInclusion F v u' : K F v) = (a F v g)⁻¹ ∧
      (Ideal.Quotient.mk (p F v)) (u : O F v) =
        (Ideal.Quotient.mk (p F v)) (u' : O F v) := by
  let au := (diagonal_units F v g hc).1.unit
  let du := (diagonal_units F v g hc).2.1.unit
  let D := Matrix.GeneralLinearGroup.det g
  refine ⟨du / D, au⁻¹, ?_, ?_, ?_⟩
  · rw [map_div, Units.val_div_eq_div_val]
    change ((du : O F v) : K F v) / ((D : O F v) : K F v) = _
    have hd : ((du : O F v) : K F v) = d F v g := congrArg Subtype.val (IsUnit.unit_spec _)
    have hD : ((D : O F v) : K F v) = Δ F v g := by
      change _ = (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (O F v).subtype g) : K F v)
      rw [Matrix.GeneralLinearGroup.map_det]
      rfl
    rw [hd, hD]
  · change (((Units.map (O F v).subtype.toMonoidHom au)⁻¹ : (K F v)ˣ) : K F v) = _
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe]
    congr 1
  · let q := Ideal.Quotient.mk (p F v)
    have hcz : q (g 1 0) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact small_mem F v (g 1 0) hc
    have hdet : q (D : O F v) = q (au : O F v) * q (du : O F v) := by
      simp [D, au, du, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hcz]
    have he : Units.map q.toMonoidHom D = Units.map q.toMonoidHom au * Units.map q.toMonoidHom du := by
      apply Units.ext
      exact hdet
    have hu : Units.map q.toMonoidHom (du / D) = Units.map q.toMonoidHom (au⁻¹) := by
      rw [map_div, map_inv, he]
      simp [div_eq_mul_inv, mul_comm]
    exact congrArg Units.val hu

include hv

theorem kappa_active (g : K0 F v)
    (hc : c F v g ≠ 0) (hsmall : ‖c F v g‖ < 1) :
    kappa F v ζ hζ g =
      KPHilbert.B3 F ζ hζ (Sum.inr v)
        (Units.mk0 (c F v g) hc)
        (Units.mk0 (a F v g)⁻¹
          (inv_ne_zero (diagonal_units F v g hsmall).2.2.1)) := by
  have hd := (diagonal_units F v g hsmall).2.2.2
  obtain ⟨u, u', hu, hu', heq⟩ := diagonal_reduction F v g hsmall
  simp only [kappa, dif_pos hc, dif_pos hd, dif_pos hsmall]
  have huU : unitInclusion F v u = Units.mk0 (d F v g / Δ F v g)
      (div_ne_zero hd (Matrix.GeneralLinearGroup.det_ne_zero (inclusion F v g))) :=
    Units.ext hu
  have huU' : unitInclusion F v u' = Units.mk0 (a F v g)⁻¹
      (inv_ne_zero (diagonal_units F v g hsmall).2.2.1) := Units.ext hu'
  rw [← huU, ← huU']
  exact B3_congruent_right F v ζ hζ hv _ u u' heq

omit hv

theorem kappa_zero (g : K0 F v) (hc : c F v g = 0) :
    kappa F v ζ hζ g = 1 := by
  simp [kappa, hc]

theorem kappa_norm_one (g : K0 F v) (hc : ‖c F v g‖ = 1) :
    kappa F v ζ hζ g = 1 := by
  simp [kappa, hc.not_lt]

include hv

theorem det_twist_trivial (g h : K0 F v) :
    KPHilbert.B3 F ζ hζ (Sum.inr v)
      (Matrix.GeneralLinearGroup.det (inclusion F v g))
      (Matrix.GeneralLinearGroup.det (inclusion F v h)) ^ 2 = 1 := by
  have hg : Matrix.GeneralLinearGroup.det (inclusion F v g) =
      unitInclusion F v (Matrix.GeneralLinearGroup.det g) := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (O F v).subtype g) = _
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  have hh : Matrix.GeneralLinearGroup.det (inclusion F v h) =
      unitInclusion F v (Matrix.GeneralLinearGroup.det h) := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (O F v).subtype h) = _
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  rw [hg, hh, B3_units F v ζ hζ hv]
  simp

end
end DedekindZetaZeroFree.KPTameCompact
