module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CenterInducedDiagonalComparison

@[expose] public section

open scoped NumberField Valued

namespace DedekindZetaZeroFree.KPActualResidueSources
open NumberField IsDedekindDomain
open KPLocalPrincipalSeries KPRankOneCenterInducedDiagonalComparison
open KPActualScalarBinding

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

local notation "K" => KPExceptionalRaw.LocalField F q
local notation "H₀" => KPExceptionalRaw.actualTorus F ζ hζ q

private theorem np_mul (x y : Kˣ) (z : ℂ) :
    normPower K (x*y) z = normPower K x z * normPower K y z := by
  rw [normPower, localAbs_mul, Real.log_mul (localAbs_pos K x).ne' (localAbs_pos K y).ne',
    Complex.ofReal_add, mul_add, Complex.exp_add]
  rfl

private theorem np_add (x : Kˣ) (z w : ℂ) :
    normPower K x (z+w) = normPower K x z * normPower K x w := by
  simp only [normPower, add_mul, Complex.exp_add]

private theorem np_inv (x : Kˣ) (z : ℂ) : normPower K x⁻¹ z = normPower K x (-z) := by
  have h : localAbs K x⁻¹ = (localAbs K x)⁻¹ := by
    have hh := localAbs_mul K x x⁻¹
    simp only [mul_inv_cancel, localAbs_one] at hh
    exact eq_inv_of_mul_eq_one_right hh.symm
  simp only [normPower, h, Real.log_inv, Complex.ofReal_neg, mul_neg, neg_mul]

private theorem pgl_diagonal_injective (L : Type*) [Field L] (u v : Lˣ)
    (huv : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d L u 1) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d L v 1)) : u = v := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp huv
  have h11 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 1 1) hc
  have h00 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply] at h11 h00
  apply Units.ext
  calc
    (u : L) = (u : L) * (c : L) := by simp [h11]
    _ = (v : L) := h00

private theorem pgl_weyl_diagonal (L : Type*) [Field L] (u : Lˣ) :
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w L) *
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d L u⁻¹ 1) =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d L u 1) *
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w L) := by
  rw [← map_mul, ← map_mul]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal_apply]

private theorem coord_weyl (S : ActualKPBinding F ζ hζ q) (h : H₀) :
    S.borel.coordinate (S.borel.weyl h) = (S.borel.coordinate h)⁻¹ := by
  apply pgl_diagonal_injective
  rw [← S.borel.torus_projection, S.borel.weyl_from_lift, map_mul, map_mul,
    map_inv, S.borel.liftedW_projection, S.borel.torus_projection]
  apply mul_left_cancel (a := Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w K))
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact (pgl_weyl_diagonal K (S.borel.coordinate h)).symm

private theorem weyl_twice (S : ActualKPBinding F ζ hζ q) (h : H₀) :
    S.borel.weyl (S.borel.weyl h) = h := by
  have hw : S.borel.liftedW ^ 2 = 1 := by
    rw [(S.openCell S.polarization).weyl_eq]
    simpa only [KPRankOneOpenCellKernel.signedWeyl,
      KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW] using
      KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q)
  have hwi : S.borel.liftedW⁻¹ = S.borel.liftedW :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  apply Subtype.val_injective
  change (S.borel.weyl (S.borel.weyl h) : KPExceptionalRaw.ActualCover F ζ hζ q) = h
  rw [← S.torus_full, S.borel.weyl_from_lift, S.borel.weyl_from_lift, S.torus_full, hwi]
  simp only [← mul_assoc, ← pow_two, hw, one_mul]
  rw [mul_assoc, ← pow_two, hw, mul_one]

private theorem weyl_sheet (S : ActualKPBinding F ζ hζ q) (e : rootsOfUnity 3 F) :
    S.borel.weylCenter (S.central e) = S.central e := by
  apply Subtype.ext
  apply Subtype.ext
  rw [S.borel.weylCenter_coe, ← S.torus_full, S.borel.weyl_from_lift,
    S.torus_full, S.central_actual]
  have hc := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e,rfl⟩)
    S.borel.liftedW
  rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem coord_sheet (S : ActualKPBinding F ζ hζ q) (e : rootsOfUnity 3 F) :
    S.borel.coordinate (S.central e : H₀) = 1 := by
  have he : (S.central e : H₀) = (S.openCell S.polarization).centralTorus e := by
    apply Subtype.ext
    rw [S.central_actual, ← S.torus_full]
    exact ((S.openCell S.polarization).central_eq e).symm
  rw [he]
  exact (S.openCell S.polarization).central_coordinate e

private theorem center_law (S : ActualKPBinding F ζ hζ q) (c : S.heisenberg.C) :
    (S.heisenberg.ω (S.borel.weylCenter c) : ℂ) = (S.heisenberg.ω c : ℂ) *
      normPower K (S.borel.coordinate (c : H₀)) (-1/3) := by
  obtain ⟨e,x,y,rfl⟩ := S.center_parameterization c
  rw [map_mul, weyl_sheet, S.borel.weyl_cube, map_mul, map_mul, Units.val_mul,
    Units.val_mul, S.borel.exceptional_cube, S.borel.exceptional_cube]
  simp only [Subgroup.coe_mul, map_mul, coord_sheet, S.borel.cube_coordinate, one_mul,
    inv_div]
  rw [show (y / x)^3 = ((x/y)^3)⁻¹ by rw [← inv_pow, inv_div], np_inv]
  rw [mul_assoc, ← np_add]
  congr 2
  norm_num

theorem actual_center_weighted_weyl (S : KPActualScalarBinding.ActualKPBinding F ζ hζ q) :
    ∃ E : KPRankOneCenterInducedDiagonalComparison.CenterModule S.heisenberg ≃ₗ[ℂ]
        KPRankOneCenterInducedDiagonalComparison.CenterModule S.heisenberg,
      (∀ (f : KPRankOneCenterInducedDiagonalComparison.CenterModule S.heisenberg)
          (h : KPExceptionalRaw.actualTorus F ζ hζ q),
        (E f).val h =
          KPLocalPrincipalSeries.normPower (KPExceptionalRaw.LocalField F q)
            (S.borel.coordinate h) (1 / 3 : ℂ) * f.val (S.borel.weyl h)) ∧
      (∀ f : KPRankOneCenterInducedDiagonalComparison.CenterModule S.heisenberg, E (E f) = f) ∧
      (∀ (a : KPExceptionalRaw.actualTorus F ζ hζ q)
          (f : KPRankOneCenterInducedDiagonalComparison.CenterModule S.heisenberg),
        E ((KPRankOneCenterInducedDiagonalComparison.centerTorus F ζ hζ q
            S.heisenberg S.borel KPLocalPrincipalSeries.Sign.minus) a f) =
          KPLocalPrincipalSeries.normPower (KPExceptionalRaw.LocalField F q)
            (S.borel.coordinate a) (-1 / 3 : ℂ) •
            (KPRankOneCenterInducedDiagonalComparison.centerTorus F ζ hζ q
              S.heisenberg S.borel KPLocalPrincipalSeries.Sign.plus) a (E f)) := by
  let W : CenterModule S.heisenberg →ₗ[ℂ] CenterModule S.heisenberg := {
    toFun := fun f => ⟨fun h => normPower K (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h), by
      intro c h
      change normPower K (S.borel.coordinate ((c : H₀)*h)) (1/3) *
          f.val (S.borel.weyl ((c : H₀)*h)) = _
      rw [map_mul, np_mul, map_mul, ← S.borel.weylCenter_coe,
        f.property (S.borel.weylCenter c) (S.borel.weyl h)]
      change normPower K (S.borel.coordinate (c : H₀)) (1/3) * normPower K (S.borel.coordinate h) (1/3) *
        ((S.heisenberg.ω (S.borel.weylCenter c) : ℂ) * f.val (S.borel.weyl h)) =
        (S.heisenberg.ω c : ℂ) * (normPower K (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h))
      rw [center_law]
      have hc : normPower K (S.borel.coordinate (c : H₀)) (1/3) *
          normPower K (S.borel.coordinate (c : H₀)) (-1/3) = 1 := by
        rw [← np_add]
        norm_num [normPower]
      calc
        _ = (normPower K (S.borel.coordinate (c : H₀)) (1/3) *
          normPower K (S.borel.coordinate (c : H₀)) (-1/3)) *
          ((S.heisenberg.ω c : ℂ) * (normPower K (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h))) := by ring
        _ = _ := by rw [hc, one_mul]⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext h
      exact mul_add _ _ _
    map_smul' := by
      intro z f
      apply Subtype.ext
      funext h
      change _ * (z * _) = z * (_ * _)
      ring }
  have hW : ∀ f, W (W f) = f := by
    intro f
    apply Subtype.ext
    funext h
    change normPower K (S.borel.coordinate h) (1/3) *
      (normPower K (S.borel.coordinate (S.borel.weyl h)) (1/3) *
        f.val (S.borel.weyl (S.borel.weyl h))) = f.val h
    rw [coord_weyl, np_inv, weyl_twice, ← mul_assoc, ← np_add]
    norm_num [normPower]
  let E : CenterModule S.heisenberg ≃ₗ[ℂ] CenterModule S.heisenberg := {
    __ := W
    invFun := W
    left_inv := hW
    right_inv := hW }
  refine ⟨E, fun f h => rfl, hW, ?_⟩
  intro a f
  apply Subtype.ext
  funext h
  change normPower K (S.borel.coordinate h) (1/3) *
      f.val (S.borel.weyl h * S.borel.weyl a) =
    normPower K (S.borel.coordinate a) (-1/3) *
      (normPower K (S.borel.coordinate (h*a)) (1/3) * f.val (S.borel.weyl (h*a)))
  rw [map_mul, map_mul, np_mul]
  have ha : normPower K (S.borel.coordinate a) (-1/3) *
      normPower K (S.borel.coordinate a) (1/3) = 1 := by
    rw [← np_add]
    norm_num [normPower]
  calc
    _ = (normPower K (S.borel.coordinate a) (-1/3) * normPower K (S.borel.coordinate a) (1/3)) *
      (normPower K (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h * S.borel.weyl a)) := by rw [ha, one_mul]
    _ = _ := by ring

end
end DedekindZetaZeroFree.KPActualResidueSources
