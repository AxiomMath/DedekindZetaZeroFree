module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedResidueCharacterExtensions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameLiteralNormalizationAtomic.DiagonalArithmetic
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem uniformizer_hilbert_powers (π : (LocalField F q)ˣ) (a b : ℤ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (π ^ a) (π ^ b) = 1 := by
  obtain ⟨hL, hR, _, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ (Sum.inr q)
  let L : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun x => KPHilbert.B3 F ζ hζ (Sum.inr q) x (π ^ b)
      map_one' := KubotaDefectSymbolAlgebra.one_left _ _ _ hL _
      map_mul' := fun x y => hL x y _ }
  let R : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) π
      map_one' := KubotaDefectSymbolAlgebra.one_right _ _ _ hR _
      map_mul' := hR π }
  change L (π ^ a) = 1
  rw [map_zpow]
  change R (π ^ b) ^ a = 1
  rw [map_zpow]
  simp [R, (ha π).1]

include S in
theorem diagonal_lift_scalar (π : (LocalField F q)ˣ) (a b : ℤ) :
    diagonalLift F ζ hζ q π (a,b) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ (a-b)) := by
  have hm : KPScalarSplitCentral.scalarMatrix F (Sum.inr q) (π ^ b) *
      KubotaRankTwo.d (LocalField F q) (π ^ (a-b)) 1 =
      KubotaRankTwo.d (LocalField F q) (π ^ a) (π ^ b) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (Matrix.scalar (Fin 2) ((π ^ b : (LocalField F q)ˣ) : LocalField F q) *
      !![((π ^ (a-b) : (LocalField F q)ˣ) : LocalField F q), 0; 0, 1]) i j = _
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
    rw [← zpow_add₀ (Units.ne_zero π)]
    congr 1
    omega
  have hs : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarMatrix F (Sum.inr q) (π ^ b))
      (KubotaRankTwo.d (LocalField F q) (π ^ (a-b)) 1) = 1 := by
    have hX (x y : (LocalField F q)ˣ) : KubotaRankTwo.X (LocalField F q)
        (KubotaRankTwo.d (LocalField F q) x y) = y := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x]
    have hXs (x : (LocalField F q)ˣ) : KubotaRankTwo.X (LocalField F q)
        (KPScalarSplitCentral.scalarMatrix F (Sum.inr q) x) = x := by
      apply Units.ext
      change (if (Matrix.scalar (Fin 2) (x : LocalField F q)) 1 0 = 0 then
        (Matrix.scalar (Fin 2) (x : LocalField F q)) 1 1 else
        (Matrix.scalar (Fin 2) (x : LocalField F q)) 1 0) = _
      simp [Matrix.scalar, Matrix.diagonal_apply]
    have hd (x y : (LocalField F q)ˣ) : KubotaRankTwo.det (LocalField F q)
        (KubotaRankTwo.d (LocalField F q) x y) = x*y := by
      apply Units.ext
      simp [KubotaRankTwo.det]
    simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, hm, hX, hXs,
      KubotaRankTwo.det, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    rw [show (π ^ b / π ^ b : (LocalField F q)ˣ) = 1 by simp,
      show (π ^ b / (1 * (π ^ b) ^ 2) : (LocalField F q)ˣ) = π ^ (-b) by
        rw [one_mul, div_eq_mul_inv, ← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add];
        congr 1; norm_num; ring,
      show (π ^ b : (LocalField F q)ˣ) ^ 2 = π ^ (b*2) by
        rw [← zpow_natCast, ← zpow_mul]; norm_num]
    simp [uniformizer_hilbert_powers, KubotaDefectSymbolAlgebra.one_left _ _ _
      (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1]
  have he := congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q))
    (KPLocalCover.sectionMap_mul F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarMatrix F (Sum.inr q) (π ^ b))
      (KubotaRankTwo.d (LocalField F q) (π ^ (a-b)) 1))
  rw [hs, hm, map_one, one_mul, map_mul] at he
  have hone : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q)
        (KPScalarSplitCentral.scalarMatrix F (Sum.inr q) (π ^ b))) = 1 :=
    S.split_scalars (π ^ b)
  rw [hone, one_mul] at he
  exact he.symm

end DedekindZetaZeroFree.KPTameLiteralNormalizationAtomic.DiagonalArithmetic

end
