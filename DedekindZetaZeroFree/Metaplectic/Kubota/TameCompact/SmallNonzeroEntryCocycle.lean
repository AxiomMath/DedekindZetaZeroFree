module

public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.CorrectionAndDeterminantTwist

@[expose] public section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPTameCompact

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hv : ringChar (O F v ⧸ p F v) ≠ 3)

omit hv

local instance smallNonzeroValuativeRel : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance smallNonzeroCompatible : (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
private lemma small_mem (x : O F v) (hx : ‖(x : K F v)‖ < 1) : x ∈ p F v := by
  change x ∈ IsLocalRing.maximalIdeal (O F v)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rw [← Valuation.vlt_one_iff, Valuation.vlt_one_iff (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ)))]
  exact Valued.toNormedField.norm_lt_one_iff.mp hx
private lemma product_small (g h : K0 F v) (hc : ‖c F v g‖ < 1) (he : ‖c F v h‖ < 1) : ‖c F v (g*h)‖ < 1 := by
  have hz : c F v (g*h) = c F v g * a F v h + d F v g * c F v h := by
    simp [c, a, d, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hz]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
  rw [max_lt_iff, norm_mul, norm_mul]
  constructor
  · exact (mul_le_of_le_one_right (norm_nonneg _) ((det_norm_and_entries F v h).2 0 0)).trans_lt hc
  · exact (mul_le_of_le_one_left (norm_nonneg _) ((det_norm_and_entries F v g).2 1 1)).trans_lt he
include hv
private lemma unit_symbol (x y : O F v) (hx : IsUnit x) (hy : IsUnit y)
    (X Y : (K F v)ˣ) (hX : (X : K F v) = x) (hY : (Y : K F v) = y) :
    KPHilbert.B3 F ζ hζ (Sum.inr v) X Y = 1 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨w, hw⟩ := hy
  have hXu : X = unitInclusion F v u := Units.ext (by simpa [unitInclusion, KPHilbert.integerUnitInclusion, Units.map, hu] using hX)
  have hYw : Y = unitInclusion F v w := Units.ext (by simpa [unitInclusion, KPHilbert.integerUnitInclusion, Units.map, hw] using hY)
  rw [hXu, hYw]
  exact B3_units F v ζ hζ hv u w
private lemma reduction_symbol (x y : O F v) (hx : IsUnit x) (hy : IsUnit y)
    (X Y T : (K F v)ˣ) (hX : (X : K F v) = x) (hY : (Y : K F v) = y)
    (hred : Ideal.Quotient.mk (p F v) x = Ideal.Quotient.mk (p F v) y) :
    KPHilbert.B3 F ζ hζ (Sum.inr v) T X = KPHilbert.B3 F ζ hζ (Sum.inr v) T Y := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨w, hw⟩ := hy
  have hXu : X = unitInclusion F v u := Units.ext (by simpa [unitInclusion, KPHilbert.integerUnitInclusion, Units.map, hu] using hX)
  have hYw : Y = unitInclusion F v w := Units.ext (by simpa [unitInclusion, KPHilbert.integerUnitInclusion, Units.map, hw] using hY)
  rw [hXu, hYw]
  exact B3_congruent_right F v ζ hζ hv T u w (by simpa [hu, hw] using hred)
private lemma det_symbol (g : K0 F v) (hc : ‖c F v g‖ < 1) (T A D : (K F v)ˣ)
    (hA : (A : K F v) = a F v g) (hD : (D : K F v) = d F v g) :
    KPHilbert.B3 F ζ hζ (Sum.inr v) T (Matrix.GeneralLinearGroup.det (inclusion F v g)) =
      KPHilbert.B3 F ζ hζ (Sum.inr v) T (A*D) := by
  let B := KPHilbert.B3 F ζ hζ (Sum.inr v)
  have hL := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1
  have hR := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1
  obtain ⟨u, w, hu, hw, hr⟩ := diagonal_reduction F v g hc
  have hu' : unitInclusion F v u = D / Matrix.GeneralLinearGroup.det (inclusion F v g) :=
    Units.ext (by simpa [hD] using hu)
  have hw' : unitInclusion F v w = A⁻¹ := Units.ext (by simpa [hA] using hw)
  have hh := B3_congruent_right F v ζ hζ hv T u w hr
  rw [hu', hw', KubotaDefectSymbolAlgebra.div_right _ _ _ hR,
    KubotaDefectSymbolAlgebra.inv_right _ _ _ hR] at hh
  rw [hR]
  apply eq_of_div_eq_one
  have hh' : B T D / B T (Matrix.GeneralLinearGroup.det (inclusion F v g)) * B T A = 1 := by
    change KPHilbert.B3 F ζ hζ (Sum.inr v) T D / _ * _ = 1
    rw [hh]; exact inv_mul_cancel _
  change B T (Matrix.GeneralLinearGroup.det (inclusion F v g)) / (B T A * B T D) = 1
  apply (inv_eq_one).mp
  convert hh' using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ac_rfl
omit hv in
private lemma product_a_reduction (g h : K0 F v) (he : ‖c F v h‖ < 1) :
    Ideal.Quotient.mk (p F v) ((g*h) 0 0) =
      Ideal.Quotient.mk (p F v) (g 0 0 * h 0 0) := by
  have hm := small_mem F v (h 1 0) he
  have hz : Ideal.Quotient.mk (p F v) (g 0 1 * h 1 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ((p F v).mul_mem_left _ hm)
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, hz, add_zero]

omit hv in
private lemma factor_nonzero {L M : Type*} [Field L] [CommGroup M]
    (B : Lˣ → Lˣ → M)
    (hL : ∀ a b c, B (a*b) c = B a c * B b c)
    (hR : ∀ a b c, B a (b*c) = B a b * B a c)
    (hAlt : ∀ a, B a a = 1)
    (C E Z A D H : Lˣ) (hAD : B A D = 1) (hAH : B A H = 1) (hDH : B D H = 1) :
    B C A⁻¹ * B E H⁻¹ * B (Z/C) (Z/(E*(A*D))) =
      B Z (A*H)⁻¹ * B (Z/(C*H)) (Z/(D*E)) := by
  have sk := KubotaDefectSymbolAlgebra.skew_symmetry L M B hL hR hAlt
  simp only [div_eq_mul_inv, mul_inv_rev, hL, hR,
    KubotaDefectSymbolAlgebra.inv_left L M B hL,
    KubotaDefectSymbolAlgebra.inv_right L M B hR, hAlt,
    sk E C, sk Z C, sk A C, sk D C, sk H C,
    sk Z E, sk A E, sk D E, sk H E,
    sk A Z, sk D Z, sk H Z, sk D A, sk H A, sk H D,
    hAD, hAH, hDH, inv_one, one_mul, mul_one, inv_inv]
  apply Additive.ofMul.injective
  change _ = _
  have omul : ∀ p q : M, Additive.ofMul (p*q) = Additive.ofMul p + Additive.ofMul q := fun _ _ => rfl
  have oinv : ∀ p : M, Additive.ofMul p⁻¹ = -Additive.ofMul p := fun _ => rfl
  simp only [omul, oinv]
  abel
omit hv in
private lemma factor_zero {L M : Type*} [Field L] [CommGroup M]
    (B : Lˣ → Lˣ → M)
    (hL : ∀ a b c, B (a*b) c = B a c * B b c)
    (hR : ∀ a b c, B a (b*c) = B a b * B a c)
    (hAlt : ∀ a, B a a = 1)
    (C E W A D H : Lˣ) (hAD : B A D = 1) (hAH : B A H = 1) (hDH : B D H = 1)
    (hWA : B W A = 1) (hWD : B W D = 1)
    (hCW : B C W = (B W E)⁻¹) :
    B C A⁻¹ * B E H⁻¹ * B (W/C) (W/(E*(A*D))) = B (C*H) (D*E) := by
  have sk := KubotaDefectSymbolAlgebra.skew_symmetry L M B hL hR hAlt
  simp only [div_eq_mul_inv, mul_inv_rev, hL, hR,
    KubotaDefectSymbolAlgebra.inv_left L M B hL,
    KubotaDefectSymbolAlgebra.inv_right L M B hR, hAlt,
    sk E C, sk W C, sk A C, sk D C, sk H C,
    sk A E, sk D E, sk H E, sk D A, sk H A, sk H D,
    hCW, hWA, hWD, hAD, hAH, hDH, inv_one, one_mul, mul_one, inv_inv]
  apply Additive.ofMul.injective
  have omul : ∀ p q : M, Additive.ofMul (p*q) = Additive.ofMul p + Additive.ofMul q := fun _ _ => rfl
  have oinv : ∀ p : M, Additive.ofMul p⁻¹ = -Additive.ofMul p := fun _ => rfl
  simp only [omul, oinv]
  abel

omit hv in
private lemma mk_inv {L : Type*} [Field L] (x : L) (hx : x ≠ 0) :
    Units.mk0 x⁻¹ (inv_ne_zero hx) = (Units.mk0 x hx)⁻¹ := Units.ext rfl
omit hv in
private lemma sum_symbol {L M : Type*} [Field L] [CommGroup M]
    (B : Lˣ → Lˣ → M)
    (hL : ∀ a b c, B (a*b) c = B a c * B b c)
    (hR : ∀ a b c, B a (b*c) = B a b * B a c)
    (hSt : ∀ a b : Lˣ, (a:L)+(b:L)=1 → B a b = 1)
    (U V Z : Lˣ) (hz : (Z:L)=(U:L)+(V:L)) : B (Z/U) (Z/V) = 1 := by
  have hs' : ((U/Z:Lˣ):L) + ((V/Z:Lˣ):L) = 1 := by
    simp only [Units.val_div_eq_div_val]
    rw [← add_div, ← hz, div_self Z.ne_zero]
  have hh := hSt (U/Z) (V/Z) hs'
  simpa only [inv_div] using (KubotaDefectSymbolAlgebra.inv_inv L M B hL hR (U/Z) (V/Z)).trans hh
omit hv in
private lemma sigma_formula (g h : K0 F v) (C E W : (K F v)ˣ)
    (hC : KubotaRankTwo.X (K F v) (inclusion F v g) = C)
    (hE : KubotaRankTwo.X (K F v) (inclusion F v h) = E)
    (hW : KubotaRankTwo.X (K F v) (inclusion F v (g*h)) = W)
    (ht : KPHilbert.B3 F ζ hζ (Sum.inr v)
      (Matrix.GeneralLinearGroup.det (inclusion F v g))
      (Matrix.GeneralLinearGroup.det (inclusion F v h)) ^ 2 = 1) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (inclusion F v g) (inclusion F v h) =
      KPHilbert.B3 F ζ hζ (Sum.inr v) (W/C)
        (W/(E*Matrix.GeneralLinearGroup.det (inclusion F v g))) := by
  unfold KPLocalCover.sigmaTwo
  rw [ht, mul_one]
  unfold KubotaElementaryLastArgument.tau
  rw [← map_mul, hC, hE, hW]
omit hv in
private lemma X_small (g : K0 F v) (hc : c F v g ≠ 0) :
    KubotaRankTwo.X (K F v) (inclusion F v g) = Units.mk0 (c F v g) hc := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, inclusion, KPLocalCube.integerInclusion,
    Matrix.GeneralLinearGroup.map_apply, hc]
omit hv in
private lemma X_zero (g : K0 F v) (hc : c F v g = 0) (hd : d F v g ≠ 0) :
    KubotaRankTwo.X (K F v) (inclusion F v g) = Units.mk0 (d F v g) hd := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, inclusion, KPLocalCube.integerInclusion,
    Matrix.GeneralLinearGroup.map_apply, hc]

include hv

theorem kappa_mul_small_nonzero_of_product_entry_ne_zero
    (g h : K0 F v) (hc : c F v g ≠ 0) (he : c F v h ≠ 0)
    (hcg : ‖c F v g‖ < 1) (hch : ‖c F v h‖ < 1)
    (hz : c F v (g * h) ≠ 0) :
    kappa F v ζ hζ (g * h) =
      kappa F v ζ hζ g * kappa F v ζ hζ h *
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
          (inclusion F v g) (inclusion F v h) := by
  let B := KPHilbert.B3 F ζ hζ (Sum.inr v)
  have hL := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1
  have hR := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1
  have hAlt := fun u => ((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.2 u).1
  have dg := diagonal_units F v g hcg
  have dh := diagonal_units F v h hch
  have hzg := product_small F v g h hcg hch
  have dz := diagonal_units F v (g*h) hzg
  let C := Units.mk0 (c F v g) hc
  let E := Units.mk0 (c F v h) he
  let Z := Units.mk0 (c F v (g*h)) hz
  let A := Units.mk0 (a F v g) dg.2.2.1
  let D := Units.mk0 (d F v g) dg.2.2.2
  let H := Units.mk0 (a F v h) dh.2.2.1
  let P := Units.mk0 (a F v (g*h)) dz.2.2.1
  have hAD : B A D = 1 := unit_symbol F v ζ hζ hv _ _ dg.1 dg.2.1 A D rfl rfl
  have hAH : B A H = 1 := unit_symbol F v ζ hζ hv _ _ dg.1 dh.1 A H rfl rfl
  have hDH : B D H = 1 := unit_symbol F v ζ hζ hv _ _ dg.2.1 dh.1 D H rfl rfl
  have hp : B Z P = B Z (A*H) := reduction_symbol F v ζ hζ hv
    ((g*h) 0 0) (g 0 0 * h 0 0) dz.1 (dg.1.mul dh.1) P (A*H) Z rfl rfl
      (product_a_reduction F v g h hch)
  have hk : kappa F v ζ hζ (g*h) = B Z (A*H)⁻¹ := by
    rw [kappa_active F v ζ hζ hv (g*h) hz hzg]
    rw [mk_inv]
    change B Z P⁻¹ = B Z (A*H)⁻¹
    rw [KubotaDefectSymbolAlgebra.inv_right _ _ B hR,
      KubotaDefectSymbolAlgebra.inv_right _ _ B hR, hp]
  have hs := sigma_formula F v ζ hζ g h C E Z
    (X_small F v g hc) (X_small F v h he) (X_small F v (g*h) hz)
      (det_twist_trivial F v ζ hζ hv g h)
  have hs' : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (inclusion F v g) (inclusion F v h) =
      B (Z/C) (Z/(E*(A*D))) := by
    rw [hs]
    simp only [KubotaDefectSymbolAlgebra.div_right _ _ _ hR, hR]
    rw [det_symbol F v ζ hζ hv g hcg (Z/C) A D rfl rfl]
    change _ = KPHilbert.B3 F ζ hζ (Sum.inr v) (Z/C) (Z/(E*(A*D)))
    simp only [KubotaDefectSymbolAlgebra.div_right _ _ _ hR, hR]
  have hsum : B (Z/(C*H)) (Z/(D*E)) = 1 := sum_symbol B hL hR
    (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.1 (C*H) (D*E) Z (by
      simp only [Units.val_mul, Units.val_mk0]
      simp [Z, C, E, D, H, c, a, d, Matrix.mul_apply, Fin.sum_univ_two])
  rw [hk, kappa_active F v ζ hζ hv g hc hcg, kappa_active F v ζ hζ hv h he hch, hs']
  rw [mk_inv, mk_inv]
  change B Z (A*H)⁻¹ = B C A⁻¹ * B E H⁻¹ * B (Z/C) (Z/(E*(A*D)))
  rw [factor_nonzero B hL hR hAlt C E Z A D H hAD hAH hDH, hsum, mul_one]

theorem kappa_mul_small_nonzero_of_product_entry_zero
    (g h : K0 F v) (hc : c F v g ≠ 0) (he : c F v h ≠ 0)
    (hcg : ‖c F v g‖ < 1) (hch : ‖c F v h‖ < 1)
    (hz : c F v (g * h) = 0) :
    kappa F v ζ hζ (g * h) =
      kappa F v ζ hζ g * kappa F v ζ hζ h *
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
          (inclusion F v g) (inclusion F v h) := by
  let B := KPHilbert.B3 F ζ hζ (Sum.inr v)
  have hL := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1
  have hR := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1
  have sk := (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.1
  have hAlt := fun u => ((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.2 u).1
  have dg := diagonal_units F v g hcg
  have dh := diagonal_units F v h hch
  have hzg := product_small F v g h hcg hch
  have dz := diagonal_units F v (g*h) hzg
  let C := Units.mk0 (c F v g) hc
  let E := Units.mk0 (c F v h) he
  let W := Units.mk0 (d F v (g*h)) dz.2.2.2
  let A := Units.mk0 (a F v g) dg.2.2.1
  let D := Units.mk0 (d F v g) dg.2.2.2
  let H := Units.mk0 (a F v h) dh.2.2.1
  have hAD : B A D = 1 := unit_symbol F v ζ hζ hv _ _ dg.1 dg.2.1 A D rfl rfl
  have hAH : B A H = 1 := unit_symbol F v ζ hζ hv _ _ dg.1 dh.1 A H rfl rfl
  have hDH : B D H = 1 := unit_symbol F v ζ hζ hv _ _ dg.2.1 dh.1 D H rfl rfl
  have hWA : B W A = 1 := unit_symbol F v ζ hζ hv _ _ dz.2.1 dg.1 W A rfl rfl
  have hWD : B W D = 1 := unit_symbol F v ζ hζ hv _ _ dz.2.1 dg.2.1 W D rfl rfl
  have hWH : B W H = 1 := unit_symbol F v ζ hζ hv _ _ dz.2.1 dh.1 W H rfl rfl
  have hsum : c F v g * a F v h + d F v g * c F v h = 0 := by
    simpa [c, a, d, Matrix.mul_apply, Fin.sum_univ_two] using hz
  have hC : C = E * ((-1)*D/H) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_neg, Units.val_one, C, E, D, H, Units.val_mk0]
    rw [← mul_div_assoc]
    apply (eq_div_iff dh.2.2.1).2
    linear_combination hsum
  have hm : B (-1) W = 1 := by
    change KPHilbert.B3 F ζ hζ (Sum.inr v) (-1) W = 1
    rw [sk]
    rw [((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.2 W).2.1, inv_one]
  have hCW : B C W = (B W E)⁻¹ := by
    have hdw : B D W = 1 := by
      exact (sk D W).trans (by simpa only [B, hWD, inv_one])
    have hhw : B H W = 1 := by
      exact (sk H W).trans (by simpa only [B, hWH, inv_one])
    rw [hC]
    dsimp only [B] at hm hdw hhw ⊢
    simp only [div_eq_mul_inv, hL, KubotaDefectSymbolAlgebra.inv_left _ _ _ hL,
      hm, hdw, hhw, inv_one, one_mul, mul_one]
    exact sk E W
  have hs := sigma_formula F v ζ hζ g h C E W
    (X_small F v g hc) (X_small F v h he) (X_zero F v (g*h) hz dz.2.2.2)
      (det_twist_trivial F v ζ hζ hv g h)
  have hs' : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (inclusion F v g) (inclusion F v h) =
      B (W/C) (W/(E*(A*D))) := by
    rw [hs]
    simp only [KubotaDefectSymbolAlgebra.div_right _ _ _ hR, hR]
    rw [det_symbol F v ζ hζ hv g hcg (W/C) A D rfl rfl]
    change _ = KPHilbert.B3 F ζ hζ (Sum.inr v) (W/C) (W/(E*(A*D)))
    simp only [KubotaDefectSymbolAlgebra.div_right _ _ _ hR, hR]
  have hvneg : D*E = -(C*H) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, C, E, D, H, Units.val_mk0]
    linear_combination hsum
  have hst : B (C*H) (D*E) = 1 := by
    rw [hvneg]
    exact ((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.2 (C*H)).2.2
  rw [kappa_zero F v ζ hζ (g*h) hz,
    kappa_active F v ζ hζ hv g hc hcg, kappa_active F v ζ hζ hv h he hch, hs', mk_inv, mk_inv]
  change 1 = B C A⁻¹ * B E H⁻¹ * B (W/C) (W/(E*(A*D)))
  rw [factor_zero B hL hR hAlt C E W A D H hAD hAH hDH hWA hWD hCW, hst]

theorem kappa_mul_small_nonzero
    (g h : K0 F v) (hc : c F v g ≠ 0) (he : c F v h ≠ 0)
    (hcg : ‖c F v g‖ < 1) (hch : ‖c F v h‖ < 1) :
    kappa F v ζ hζ (g * h) =
      kappa F v ζ hζ g * kappa F v ζ hζ h *
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
          (inclusion F v g) (inclusion F v h) := by
  by_cases hz : c F v (g * h) = 0
  · exact kappa_mul_small_nonzero_of_product_entry_zero F v ζ hζ hv g h hc he hcg hch hz
  · exact kappa_mul_small_nonzero_of_product_entry_ne_zero F v ζ hζ hv g h hc he hcg hch hz

end
end DedekindZetaZeroFree.KPTameCompact
