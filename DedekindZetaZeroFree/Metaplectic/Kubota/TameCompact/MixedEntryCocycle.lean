module

public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.CorrectionAndDeterminantTwist

@[expose] public section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPTameCompact
noncomputable section
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (K F v) := ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance : (Valued.v : Valuation (K F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
private lemma vle_norm (x : K F v) :
 ‖x‖ ≤ 1 ↔ (ValuativeRel.valuation (K F v)) x ≤ 1 := by
 rw [Valued.toNormedField.norm_le_one_iff]
 exact (ValuativeRel.isEquiv _ _).le_one_iff_le_one
private lemma vlt_norm (x : K F v) :
 ‖x‖ < 1 ↔ (ValuativeRel.valuation (K F v)) x < 1 := by
 rw [Valued.toNormedField.norm_lt_one_iff]
 exact (ValuativeRel.isEquiv _ _).lt_one_iff_lt_one
private lemma unit_of_norm (x : (K F v)ˣ) (hx : ‖(x : K F v)‖ = 1) :
 ∃ u : (O F v)ˣ, unitInclusion F v u = x := by
 let y : O F v := ⟨(x : K F v), (vle_norm F v _).mp hx.le⟩
 have hy : IsUnit y := by
   apply (Valuation.integer.integers (ValuativeRel.valuation (K F v))).isUnit_iff_valuation_eq_one.mpr
   apply le_antisymm y.property
   by_contra hn
   have hlt := lt_of_not_ge hn
   have : ‖(x : K F v)‖ < 1 := (vlt_norm F v _).mpr hlt
   exact hx.not_lt this
 obtain ⟨u, hu⟩ := hy
 refine ⟨u, ?_⟩
 apply Units.ext
 exact congrArg (fun y : O F v => (y : K F v)) hu
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (hv : ringChar (O F v ⧸ p F v) ≠ 3)
include hv
private lemma symbol_units (x y : (K F v)ˣ) (hx : ‖(x : K F v)‖ = 1) (hy : ‖(y : K F v)‖ = 1) :
 KPHilbert.B3 F ζ hζ (Sum.inr v) x y = 1 := by
 obtain ⟨u, rfl⟩ := unit_of_norm F v x hx
 obtain ⟨u', rfl⟩ := unit_of_norm F v y hy
 exact B3_units F v ζ hζ hv u u'
private lemma symbol_congr_right (x y z : (K F v)ˣ)
 (hy : ‖(y : K F v)‖ = 1) (hz : ‖(z : K F v)‖ = 1)
 (he : ‖(y : K F v) - z‖ < 1) :
 KPHilbert.B3 F ζ hζ (Sum.inr v) x y = KPHilbert.B3 F ζ hζ (Sum.inr v) x z := by
 obtain ⟨u, rfl⟩ := unit_of_norm F v y hy
 obtain ⟨u', rfl⟩ := unit_of_norm F v z hz
 apply B3_congruent_right F v ζ hζ hv
 apply Ideal.Quotient.eq.mpr
 change (u : O F v) - u' ∈ IsLocalRing.maximalIdeal (O F v)
 rw [IsLocalRing.mem_maximalIdeal]
 change ¬IsUnit ((u : O F v) - u')
 apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
 exact (vlt_norm F v _).mp he
omit hv
private lemma c_mul (g h : K0 F v) : c F v (g*h) = c F v g * a F v h + d F v g * c F v h := by
 simp [c, a, d, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
private lemma X_c (g : K0 F v) (hc : c F v g ≠ 0) :
 KubotaRankTwo.X (K F v) (inclusion F v g) = Units.mk0 (c F v g) hc := by
 apply Units.ext
 simp [KubotaRankTwo.X, KubotaRankTwo.x, inclusion, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hc]
private lemma X_d (g : K0 F v) (hc : c F v g = 0) :
 (KubotaRankTwo.X (K F v) (inclusion F v g) : K F v) = d F v g := by
 simp [KubotaRankTwo.X, KubotaRankTwo.x, inclusion, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply, hc]
private lemma norm_of_unit (x : O F v) (hx : IsUnit x) : ‖(x : K F v)‖ = 1 := by
 have he := (Valuation.integer.integers (ValuativeRel.valuation (K F v))).isUnit_iff_valuation_eq_one.mp hx
 apply le_antisymm ((vle_norm F v _).mpr x.property)
 exact le_of_not_gt (fun hn => (he.not_lt ((vlt_norm F v _).mp hn)))
private lemma norm_D (g : K0 F v) :
 ‖(KubotaRankTwo.det (K F v) (inclusion F v g) : K F v)‖ = 1 :=
 (det_norm_and_entries F v g).1
include hv
private lemma sigma_raw (g h : K0 F v) :
 KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (inclusion F v g) (inclusion F v h) =
 KPHilbert.B3 F ζ hζ (Sum.inr v)
 (KubotaRankTwo.X (K F v) (inclusion F v (g*h)) / KubotaRankTwo.X (K F v) (inclusion F v g))
 (KubotaRankTwo.X (K F v) (inclusion F v (g*h)) /
 (KubotaRankTwo.X (K F v) (inclusion F v h) * KubotaRankTwo.det (K F v) (inclusion F v g))) := by
 unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
 rw [det_twist_trivial F v ζ hζ hv, mul_one, ← map_mul]
omit hv
private lemma product_small_unit (g h : K0 F v) (hc : ‖c F v g‖ < 1) (he : ‖c F v h‖ = 1) :
 ‖c F v (g*h)‖ = 1 := by
 rw [c_mul F v]
 have hd := norm_of_unit F v (g 1 1) (diagonal_units F v g hc).2.1
 have hca : ‖c F v g * a F v h‖ < 1 := by
   rw [norm_mul]
   exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ((det_norm_and_entries F v h).2 0 0)) hc
 have hde : ‖d F v g * c F v h‖ = 1 := by rw [norm_mul, hd, he, one_mul]
 rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hde]; exact hca.ne), hde, max_eq_right hca.le]
private lemma product_unit_small (g h : K0 F v) (hc : ‖c F v g‖ = 1) (he : ‖c F v h‖ < 1) :
 ‖c F v (g*h)‖ = 1 := by
 rw [c_mul F v]
 have ha := norm_of_unit F v (h 0 0) (diagonal_units F v h he).1
 have hde : ‖d F v g * c F v h‖ < 1 := by
   rw [norm_mul]
   exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ((det_norm_and_entries F v g).2 1 1)) he
 have hca : ‖c F v g * a F v h‖ = 1 := by rw [norm_mul, hc, ha, one_mul]
 rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hca]; exact hde.ne.symm), hca, max_eq_left hde.le]
private lemma nz_norm (x : K F v) (hx : ‖x‖ = 1) : x ≠ 0 := by
 intro h; simpa [h] using hx
include hv
private lemma symbol_congr_left (x y z : (K F v)ˣ)
 (hy : ‖(y : K F v)‖ = 1) (hz : ‖(z : K F v)‖ = 1)
 (he : ‖(y : K F v) - z‖ < 1) :
 KPHilbert.B3 F ζ hζ (Sum.inr v) y x = KPHilbert.B3 F ζ hζ (Sum.inr v) z x := by
 rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.1,
     (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.1 z x,
     symbol_congr_right F v ζ hζ hv x y z hy hz he]
private lemma small_unit (g h : K0 F v)
 (hc : ‖c F v g‖ < 1) (he : ‖c F v h‖ = 1) :
 kappa F v ζ hζ (g*h) = kappa F v ζ hζ g * kappa F v ζ hζ h *
 KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (inclusion F v g) (inclusion F v h) := by
 have hz := product_small_unit F v g h hc he
 have hzn := nz_norm F v _ hz
 have hen := nz_norm F v _ he
 have hd := norm_of_unit F v (g 1 1) (diagonal_units F v g hc).2.1
 have hdn := (diagonal_units F v g hc).2.2.2
 rw [kappa_norm_one F v ζ hζ (g*h) hz, kappa_norm_one F v ζ hζ h he, mul_one,
     sigma_raw F v ζ hζ hv, X_c F v (g*h) hzn, X_c F v h hen]
 let Z : (K F v)ˣ := Units.mk0 (c F v (g*h)) hzn
 let E : (K F v)ˣ := Units.mk0 (c F v h) hen
 let D : (K F v)ˣ := KubotaRankTwo.det (K F v) (inclusion F v g)
 have hnD : ‖(D : K F v)‖ = 1 := norm_D F v g
 change 1 = kappa F v ζ hζ g * KPHilbert.B3 F ζ hζ (Sum.inr v)
     (Z / KubotaRankTwo.X (K F v) (inclusion F v g)) (Z / (E*D))
 have hnQ : ‖((Z / (E*D) : (K F v)ˣ) : K F v)‖ = 1 := by
   simp only [Units.val_div_eq_div_val, Units.val_mul]
   rw [norm_div, norm_mul, show ‖(Z : K F v)‖ = 1 from hz, show ‖(E : K F v)‖ = 1 from he, hnD]; norm_num
 by_cases hcn : c F v g = 0
 · rw [kappa_zero F v ζ hζ g hcn, one_mul]
   symm
   apply symbol_units F v ζ hζ hv _ _ _ hnQ
   simp only [Units.val_div_eq_div_val, X_d F v g hcn]
   rw [norm_div, show ‖(Z : K F v)‖ = 1 from hz, hd]; norm_num
 · rw [X_c F v g hcn]
   let C : (K F v)ˣ := Units.mk0 (c F v g) hcn
   let T : (K F v)ˣ := Units.mk0 (d F v g / Δ F v g)
     (div_ne_zero hdn (Matrix.GeneralLinearGroup.det_ne_zero (inclusion F v g)))
   have hnT : ‖(T : K F v)‖ = 1 := by
     change ‖d F v g / Δ F v g‖ = 1
     rw [norm_div, hd, (det_norm_and_entries F v g).1]; norm_num
   have hQT : ‖((Z/(E*D) : (K F v)ˣ) : K F v) - T‖ < 1 := by
     simp only [Units.val_div_eq_div_val, Units.val_mul]
     change ‖c F v (g*h) / (c F v h * Δ F v g) - d F v g / Δ F v g‖ < 1
     have hi : c F v (g*h) / (c F v h * Δ F v g) - d F v g / Δ F v g =
       (c F v g * a F v h) / (c F v h * Δ F v g) := by
       rw [c_mul F v]; field_simp; ring
     rw [hi, norm_div, norm_mul, norm_mul, he, (det_norm_and_entries F v g).1, one_mul, div_one]
     exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ((det_norm_and_entries F v h).2 0 0)) hc
   have hk : kappa F v ζ hζ g = KPHilbert.B3 F ζ hζ (Sum.inr v) C T := by
     simp [kappa, hcn, hdn, hc, C, T]
   rw [KubotaDefectSymbolAlgebra.div_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).1,
       symbol_units F v ζ hζ hv Z (Z/(E*D)) hz hnQ,
       symbol_congr_right F v ζ hζ hv C (Z/(E*D)) T hnQ hnT hQT, hk]
   simp
private lemma unit_small (g h : K0 F v)
 (hc : ‖c F v g‖ = 1) (he : ‖c F v h‖ < 1) :
 kappa F v ζ hζ (g*h) = kappa F v ζ hζ g * kappa F v ζ hζ h *
 KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (inclusion F v g) (inclusion F v h) := by
 have hz := product_unit_small F v g h hc he
 have hzn := nz_norm F v _ hz
 have hcn := nz_norm F v _ hc
 have ha := norm_of_unit F v (h 0 0) (diagonal_units F v h he).1
 have hd := norm_of_unit F v (h 1 1) (diagonal_units F v h he).2.1
 have han := (diagonal_units F v h he).2.2.1
 rw [kappa_norm_one F v ζ hζ (g*h) hz, kappa_norm_one F v ζ hζ g hc, one_mul,
     sigma_raw F v ζ hζ hv, X_c F v (g*h) hzn, X_c F v g hcn]
 let Z : (K F v)ˣ := Units.mk0 (c F v (g*h)) hzn
 let C : (K F v)ˣ := Units.mk0 (c F v g) hcn
 let D : (K F v)ˣ := KubotaRankTwo.det (K F v) (inclusion F v g)
 have hnD : ‖(D : K F v)‖ = 1 := norm_D F v g
 have hnQ : ‖((Z/C : (K F v)ˣ) : K F v)‖ = 1 := by
   simp only [Units.val_div_eq_div_val]
   rw [norm_div, show ‖(Z : K F v)‖ = 1 from hz, show ‖(C : K F v)‖ = 1 from hc]; norm_num
 change 1 = kappa F v ζ hζ h * KPHilbert.B3 F ζ hζ (Sum.inr v)
     (Z/C) (Z / (KubotaRankTwo.X (K F v) (inclusion F v h)*D))
 by_cases hen : c F v h = 0
 · rw [kappa_zero F v ζ hζ h hen, one_mul]
   symm
   apply symbol_units F v ζ hζ hv _ _ hnQ
   simp only [Units.val_div_eq_div_val, Units.val_mul, X_d F v h hen]
   rw [norm_div, norm_mul, show ‖(Z : K F v)‖ = 1 from hz, hd, hnD]; norm_num
 · rw [X_c F v h hen]
   let E : (K F v)ˣ := Units.mk0 (c F v h) hen
   let A : (K F v)ˣ := Units.mk0 (a F v h) han
   have hnA : ‖(A : K F v)‖ = 1 := ha
   have hQA : ‖((Z/C : (K F v)ˣ) : K F v) - A‖ < 1 := by
     simp only [Units.val_div_eq_div_val]
     change ‖c F v (g*h) / c F v g - a F v h‖ < 1
     have hi : c F v (g*h) / c F v g - a F v h = (d F v g * c F v h) / c F v g := by
       rw [c_mul F v]; field_simp; ring
     rw [hi, norm_div, norm_mul, hc, div_one]
     exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ((det_norm_and_entries F v g).2 1 1)) he
   have hk : kappa F v ζ hζ h = (KPHilbert.B3 F ζ hζ (Sum.inr v) A E) := by
     rw [kappa_active F v ζ hζ hv h hen he]
     have hi : Units.mk0 (a F v h)⁻¹ (inv_ne_zero han) = A⁻¹ := by
       apply Units.ext; simp [A]
     rw [hi, KubotaDefectSymbolAlgebra.inv_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1,
       (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.1 E A, inv_inv]
   rw [KubotaDefectSymbolAlgebra.div_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1,
     symbol_units F v ζ hζ hv (Z/C) Z hnQ hz, one_div,
     (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.1,
     symbol_units F v ζ hζ hv (Z/C) D hnQ hnD, mul_one,
     symbol_congr_left F v ζ hζ hv E (Z/C) A hnQ hnA hQA, hk]
   simp
end

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (hv : ringChar (O F v ⧸ p F v) ≠ 3)

include hv

theorem kappa_mul_small_unit (g h : K0 F v) :
    (‖c F v g‖ < 1 ∧ ‖c F v h‖ = 1) →
      kappa F v ζ hζ (g * h) =
        kappa F v ζ hζ g * kappa F v ζ hζ h *
          KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
            (inclusion F v g) (inclusion F v h) := by
  rintro ⟨hc, he⟩
  exact small_unit F v ζ hζ hv g h hc he

theorem kappa_mul_unit_small (g h : K0 F v) :
    (‖c F v g‖ = 1 ∧ ‖c F v h‖ < 1) →
      kappa F v ζ hζ (g * h) =
        kappa F v ζ hζ g * kappa F v ζ hζ h *
          KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
            (inclusion F v g) (inclusion F v h) := by
  rintro ⟨hc, he⟩
  exact unit_small F v ζ hζ hv g h hc he

end

end DedekindZetaZeroFree.KPTameCompact
