module

public import DedekindZetaZeroFree.Metaplectic.Kubota.PGL.LocalCover

@[expose] public section

namespace DedekindZetaZeroFree.KPCorrectedBruhatLifts

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : KPHilbert.Place F)

 abbrev K := KPHilbert.Completion F v

 abbrev B := KPHilbert.B3 F ζ hζ v
private theorem B_one_left (a : (K F v)ˣ) : B F ζ hζ v 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 a
private theorem B_one_right (a : (K F v)ˣ) : B F ζ hζ v a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 a
private theorem sigma_n_left (x : K F v) (g : KPLocalCover.LocalGL2 F v) :
 KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.n (K F v) x) g = 1 := by
 simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, B_one_right, B_one_left]
private theorem sigma_n_right (x : K F v) (g : KPLocalCover.LocalGL2 F v) :
 KPLocalCover.sigmaTwo F ζ hζ v g (KubotaRankTwo.n (K F v) x) = 1 := by
 simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, B_one_right, B_one_left]

 abbrev L := KPHilbert.Completion F v
 abbrev symb := KPHilbert.B3 F ζ hζ v
private theorem symb_cub (a b : (L F v)ˣ) : symb F ζ hζ v a b ^ 3 = 1 := by
 apply Subtype.ext
 exact (KPHilbert.B3 F ζ hζ v a b).property
private theorem symb_negL (a : (L F v)ˣ) : symb F ζ hζ v (-1) a = 1 :=
 KubotaDefectSymbolAlgebra.neg_one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 (symb_cub F ζ hζ v) a
private theorem symb_negR (a : (L F v)ˣ) : symb F ζ hζ v a (-1) = 1 :=
 KubotaDefectSymbolAlgebra.neg_one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 (symb_cub F ζ hζ v) a
private theorem X_scalar (z : (L F v)ˣ) :
 KubotaRankTwo.X (L F v) (KPScalarSplitCentral.scalarMatrix F v z) = z := by
 apply Units.ext
 simp [KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix, Matrix.scalar]
private theorem X_swap : KubotaRankTwo.X (L F v) (KPStandardLocalRootLifts.weylSwap (L F v)) = 1 := by
 apply Units.ext
 simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
private theorem det_swap : KubotaRankTwo.det (L F v) (KPStandardLocalRootLifts.weylSwap (L F v)) = -1 := by
 apply Units.ext
 simp [KubotaRankTwo.det, KPStandardLocalRootLifts.weylSwap, Matrix.det_fin_two]

theorem upper_diagonal (x : K F v) (y : (K F v)ˣ) :
    KPStandardLocalRootLifts.N F ζ hζ v x * KPStandardLocalRootLifts.A F ζ hζ v y =
      KPStandardLocalRootLifts.A F ζ hζ v y *
        KPStandardLocalRootLifts.N F ζ hζ v (x / (y : K F v)) := by
 unfold KPStandardLocalRootLifts.N KPStandardLocalRootLifts.A
 change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
 congr 1
 · apply Units.ext
   ext i j
   fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.n, KubotaRankTwo.d, Matrix.mul_apply, Matrix.GeneralLinearGroup.coe_mul, mul_comm, div_mul_cancel₀ _ y.ne_zero, KPLocalCover.sectionMap] <;> field_simp
 · simp only [KPLocalCover.sectionMap_g, KPLocalCover.sectionMap_epsilon, one_mul, sigma_n_left, sigma_n_right]

theorem weyl_diagonal (y : (K F v)ˣ) :
    KPStandardLocalRootLifts.W F ζ hζ v * KPStandardLocalRootLifts.A F ζ hζ v y =
      KPScalarSplitCentral.scalarHom F ζ hζ v y *
        KPStandardLocalRootLifts.A F ζ hζ v y⁻¹ * KPStandardLocalRootLifts.W F ζ hζ v := by
 let S := KPScalarSplitCentral.scalarMatrix F v y
 let D := KubotaRankTwo.d (L F v) y⁻¹ 1
 let W := KPStandardLocalRootLifts.weylSwap (L F v)
 have hx1 : KubotaRankTwo.X (L F v) (W * KubotaRankTwo.d (L F v) y 1) = y := by
  apply Units.ext
  simp [W, KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]
 have hx2 : KubotaRankTwo.X (L F v) (S * D) = y := by
  apply Units.ext
  simp [S, D, KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix, Matrix.scalar, Matrix.mul_apply]
 have hx3 : KubotaRankTwo.X (L F v) (S * D * W) = y := by
  apply Units.ext
  simp [S, D, W, KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix, Matrix.scalar, KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply]
 obtain ⟨hL, hR, _, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ v
 have hAlt (a : (L F v)ˣ) := (ha a).1
 have hiL := KubotaDefectSymbolAlgebra.inv_left _ _ _ hL
 have hiR := KubotaDefectSymbolAlgebra.inv_right _ _ _ hR
 change KPLocalCover.sectionMap F ζ hζ v W * KPLocalCover.sectionMap F ζ hζ v (KubotaRankTwo.d (L F v) y 1) =
  KPLocalCover.sectionMap F ζ hζ v S * KPLocalCover.sectionMap F ζ hζ v D * KPLocalCover.sectionMap F ζ hζ v W
 change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
 congr 1
 · apply Units.ext
   ext i j
   fin_cases i <;> fin_cases j <;> simp [S, D, W, KPScalarSplitCentral.scalarMatrix, Matrix.scalar, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d, Matrix.mul_apply, KPLocalCover.sectionMap, MonoidHom.coe_mk] <;> try field_simp
 · dsimp [KPLocalCover.rawMul, KPLocalCover.sectionMap]
   simp only [one_mul, mul_one]
   change KPLocalCover.sigmaTwo F ζ hζ v (W) (KubotaRankTwo.d (L F v) y 1) =
    KPLocalCover.sigmaTwo F ζ hζ v S D * KPLocalCover.sigmaTwo F ζ hζ v (S * D) W
   simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, hx1, hx2, hx3,
    show KubotaRankTwo.X (L F v) S = y from X_scalar F v y,
    show KubotaRankTwo.X (L F v) D = 1 from KubotaRankTwo.X_d _ _ _,
    show KubotaRankTwo.X (L F v) W = 1 from X_swap F v,
    show KubotaRankTwo.det (L F v) W = -1 from det_swap F v,
    show KubotaRankTwo.det (L F v) S = y^2 from by simp [S, KPScalarSplitCentral.scalarMatrix, KubotaRankTwo.det],
    show KubotaRankTwo.det (L F v) D = y⁻¹ from by simp [D],
    KubotaRankTwo.X_d, KubotaRankTwo.det_d, map_mul, mul_one, one_mul]
   simp only [div_eq_mul_inv, pow_two, hL, hR, hiL, hiR, hAlt,
     B_one_left, B_one_right, symb_negL, symb_negR, mul_inv_cancel, inv_mul_cancel,
     inv_one, one_mul, mul_one, one_pow]

theorem weyl_upper (H : (K F v)ˣ) :
    KPStandardLocalRootLifts.W F ζ hζ v *
        KPStandardLocalRootLifts.N F ζ hζ v (H : K F v) =
      KPScalarSplitCentral.scalarHom F ζ hζ v H *
        KPStandardLocalRootLifts.N F ζ hζ v ((H⁻¹ : (K F v)ˣ) : K F v) *
        KPStandardLocalRootLifts.A F ζ hζ v (-(H⁻¹ ^ (2 : ℕ))) *
        KPStandardLocalRootLifts.LowerN F ζ hζ v ((H⁻¹ : (K F v)ˣ) : K F v) := by
 let S := KPScalarSplitCentral.scalarMatrix F v H
 let U := KubotaRankTwo.n (L F v) ((H⁻¹ : (L F v)ˣ) : L F v)
 let D := KubotaRankTwo.d (L F v) (-(H⁻¹ ^ (2 : ℕ))) 1
 let T := KPStandardLocalRootLifts.lowerN (L F v) ((H⁻¹ : (L F v)ˣ) : L F v)
 let W := KPStandardLocalRootLifts.weylSwap (L F v)
 have hxSU : KubotaRankTwo.X (L F v) (S * U) = H := by
  simpa [U] using (KubotaRankTwo.X_mul_n (L F v) S ((H⁻¹ : (L F v)ˣ) : L F v)).trans (X_scalar F v H)
 have hxSUD : KubotaRankTwo.X (L F v) (S * U * D) = H := by
  apply Units.ext
  simp [S, U, D, KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix, Matrix.scalar, Matrix.mul_apply]
 have hxT : KubotaRankTwo.X (L F v) T = H⁻¹ := by
  apply Units.ext
  simp [T, KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.lowerN]
 have hxSUDT : KubotaRankTwo.X (L F v) (S * U * D * T) = 1 := by
  apply Units.ext
  simp [S, U, D, T, KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix, Matrix.scalar, KPStandardLocalRootLifts.lowerN, Matrix.mul_apply]
 have hdT : KubotaRankTwo.det (L F v) T = 1 := by
  apply Units.ext
  simp [T, KubotaRankTwo.det, KPStandardLocalRootLifts.lowerN, Matrix.det_fin_two]
 obtain ⟨hL, hR, _, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ v
 have hAlt (a : (L F v)ˣ) := (ha a).1
 have hiL := KubotaDefectSymbolAlgebra.inv_left _ _ _ hL
 have hiR := KubotaDefectSymbolAlgebra.inv_right _ _ _ hR
 change KPLocalCover.sectionMap F ζ hζ v W * KPLocalCover.sectionMap F ζ hζ v (KubotaRankTwo.n (L F v) (H : L F v)) =
  KPLocalCover.sectionMap F ζ hζ v S * KPLocalCover.sectionMap F ζ hζ v U * KPLocalCover.sectionMap F ζ hζ v D * KPLocalCover.sectionMap F ζ hζ v T
 change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
 congr 1
 · apply Units.ext
   ext i j
   fin_cases i <;> fin_cases j <;>
    simp [S, U, D, T, W, KPScalarSplitCentral.scalarMatrix, Matrix.scalar, KPStandardLocalRootLifts.weylSwap, KPStandardLocalRootLifts.lowerN, KubotaRankTwo.n, KubotaRankTwo.d, Matrix.mul_apply, KPLocalCover.sectionMap] <;> try field_simp <;> try ring
 · dsimp [KPLocalCover.rawMul, KPLocalCover.sectionMap]
   simp only [one_mul, mul_one]
   change KPLocalCover.sigmaTwo F ζ hζ v W (KubotaRankTwo.n (L F v) (H : L F v)) =
    KPLocalCover.sigmaTwo F ζ hζ v S U * KPLocalCover.sigmaTwo F ζ hζ v (S * U) D * KPLocalCover.sigmaTwo F ζ hζ v (S * U * D) T
   rw [sigma_n_right, show KPLocalCover.sigmaTwo F ζ hζ v S U = 1 from sigma_n_right F ζ hζ v _ _, one_mul]
   simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, hxSU, hxSUD, hxSUDT, hxT,
    show KubotaRankTwo.X (L F v) D = 1 from KubotaRankTwo.X_d _ _ _,
    show KubotaRankTwo.det (L F v) S = H^2 from by simp [S, KPScalarSplitCentral.scalarMatrix, KubotaRankTwo.det],
    show KubotaRankTwo.det (L F v) U = 1 from KubotaRankTwo.det_n _ _,
    show KubotaRankTwo.det (L F v) D = -(H⁻¹^2) from by simp [D],
    hdT, map_mul, mul_one, one_mul]
   simp only [div_eq_mul_inv, pow_two, neg_mul, inv_neg, inv_inv, hL, hR, hiL, hiR, hAlt,
     B_one_left, B_one_right, symb_negL, symb_negR, mul_inv_cancel, inv_mul_cancel,
     inv_one, one_mul, mul_one, one_pow]
   simp only [show -(H⁻¹ * H⁻¹) = (-1) * (H⁻¹ * H⁻¹) from by simp, hR, symb_negR, hiR, hAlt, one_mul, mul_one, inv_one]

private theorem quotient_scalar (z : (K F v)ˣ) :
    KPPGLLocalCover.coverQuotient F ζ hζ v (KPScalarSplitCentral.scalarHom F ζ hζ v z) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨z, rfl⟩

theorem quotient_upper_diagonal (x : K F v) (y : (K F v)ˣ) :
    KPPGLLocalCover.N F ζ hζ v x * KPPGLLocalCover.A F ζ hζ v y =
      KPPGLLocalCover.A F ζ hζ v y *
        KPPGLLocalCover.N F ζ hζ v (x / (y : K F v)) := by
  simpa only [KPPGLLocalCover.N, KPPGLLocalCover.A, map_mul] using
    congrArg (KPPGLLocalCover.coverQuotient F ζ hζ v) (upper_diagonal F ζ hζ v x y)

theorem quotient_weyl_diagonal (y : (K F v)ˣ) :
    KPPGLLocalCover.W F ζ hζ v * KPPGLLocalCover.A F ζ hζ v y =
      KPPGLLocalCover.A F ζ hζ v y⁻¹ * KPPGLLocalCover.W F ζ hζ v := by
  simpa only [KPPGLLocalCover.W, KPPGLLocalCover.A, map_mul, quotient_scalar, one_mul] using
    congrArg (KPPGLLocalCover.coverQuotient F ζ hζ v) (weyl_diagonal F ζ hζ v y)

theorem quotient_weyl_upper (H : (K F v)ˣ) :
    KPPGLLocalCover.W F ζ hζ v * KPPGLLocalCover.N F ζ hζ v (H : K F v) =
      KPPGLLocalCover.N F ζ hζ v ((H⁻¹ : (K F v)ˣ) : K F v) *
        KPPGLLocalCover.A F ζ hζ v (-(H⁻¹ ^ (2 : ℕ))) *
        KPPGLLocalCover.LowerN F ζ hζ v ((H⁻¹ : (K F v)ˣ) : K F v) := by
  simpa only [KPPGLLocalCover.W, KPPGLLocalCover.N, KPPGLLocalCover.A,
    KPPGLLocalCover.LowerN, map_mul, quotient_scalar, one_mul] using
    congrArg (KPPGLLocalCover.coverQuotient F ζ hζ v) (weyl_upper F ζ hζ v H)

end
end DedekindZetaZeroFree.KPCorrectedBruhatLifts
