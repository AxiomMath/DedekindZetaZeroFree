module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residues.AverageArchimedeanCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPContFlatCuspIncomingEvaluation KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (Haar : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
variable (Transport : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
variable (H : KPMsFixedHaarDisintegration.AllLevels F R.A.zeta12 R.A.primitive_zeta12 Haar Transport)
variable (U : KPMsRationalCompactCrossPairing.Level F R.A.zeta12 R.A.primitive_zeta12)
local instance (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)) :
    MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)) :
    BorelSpace K := ⟨rfl⟩
include D Haar Transport H U in
theorem coreResidue_upper_cusp_height
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    (j : Cusps F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U) (t : ℝ) (b : KPCuspCharts.Shape F) :
    upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12 (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C x) (localGroup F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j t 0 b 1) =
    Complex.exp (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * (2/3) * (t : ℂ)) *
      upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12 (KPWildKernelUpperBound.quotientHaar F)
        (coreResidue R P C x) (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j 1).val := by
  have hhorizontal : KPContinuation.ChamberFlatCasimir.horizontalAdele F R.A.zeta12 R.A.primitive_zeta12
      (KPCuspCharts.toArch F (((0 : KPCuspCharts.Horizontal F), b), t)) = 0 := by
    funext w
    change _ = (0 : InfinitePlace.Completion w)
    simp [KPContinuation.ChamberFlatCasimir.horizontalAdele, KPCuspCharts.toArch]
  have hheights : KPContinuation.ChamberFlatCasimir.heights F R.A.zeta12 R.A.primitive_zeta12
      (KPCuspCharts.toArch F (((0 : KPCuspCharts.Horizontal F), b), t)) =
      (fun w => t + (b.val : Fin (KPCuspLogShape.dimension F) → ℝ)
        (KPContSectorArchSphericalFibers.infinitePlaceEquiv F R.A.zeta12 R.A.primitive_zeta12 w)) := by
    funext w
    simp [KPContinuation.ChamberFlatCasimir.heights, KPCuspCharts.toArch]
  have hb : (∑ w : InfinitePlace F, (b.val : Fin (KPCuspLogShape.dimension F) → ℝ)
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F R.A.zeta12 R.A.primitive_zeta12 w)) = 0 := by
    rw [Equiv.sum_comp (KPContSectorArchSphericalFibers.infinitePlaceEquiv F R.A.zeta12 R.A.primitive_zeta12)]
    exact b.property
  have hN : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
  rw [localGroup, KPContinuation.ChamberFlatCasimir.iwasawa_insertion, hhorizontal, hheights]
  simp only [show ((0,0) : KPGlobalTorusFunctionData.Adeles F) = 0 from rfl,
    hN, one_mul]
  exact coreResidue_upper_mean_height R P C x t _ hb _
theorem coreResidue_average_upper_cusp_height
    (K : Subgroup (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12))
    (hK : IsCompact (K : Set (KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12))) (ν : Measure K) [IsFiniteMeasure ν]
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C))
    (j : Cusps F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U) (t : ℝ) (b : KPCuspCharts.Shape F) :
    upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12 (KPWildKernelUpperBound.quotientHaar F)
      (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x)) (localGroup F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j t 0 b 1) =
    Complex.exp (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * (2/3) * (t : ℂ)) *
      upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12 (KPWildKernelUpperBound.quotientHaar F)
        (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x)) (finiteRepresentative F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U j 1).val := by
  have hhorizontal : KPContinuation.ChamberFlatCasimir.horizontalAdele F R.A.zeta12 R.A.primitive_zeta12
      (KPCuspCharts.toArch F (((0 : KPCuspCharts.Horizontal F), b), t)) = 0 := by
    funext w
    change _ = (0 : InfinitePlace.Completion w)
    simp [KPContinuation.ChamberFlatCasimir.horizontalAdele, KPCuspCharts.toArch]
  have hheights : KPContinuation.ChamberFlatCasimir.heights F R.A.zeta12 R.A.primitive_zeta12
      (KPCuspCharts.toArch F (((0 : KPCuspCharts.Horizontal F), b), t)) =
      (fun w => t + (b.val : Fin (KPCuspLogShape.dimension F) → ℝ)
        (KPContSectorArchSphericalFibers.infinitePlaceEquiv F R.A.zeta12 R.A.primitive_zeta12 w)) := by
    funext w
    simp [KPContinuation.ChamberFlatCasimir.heights, KPCuspCharts.toArch]
  have hb : (∑ w : InfinitePlace F, (b.val : Fin (KPCuspLogShape.dimension F) → ℝ)
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F R.A.zeta12 R.A.primitive_zeta12 w)) = 0 := by
    rw [Equiv.sum_comp (KPContSectorArchSphericalFibers.infinitePlaceEquiv F R.A.zeta12 R.A.primitive_zeta12)]
    exact b.property
  have hN : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
  rw [localGroup, KPContinuation.ChamberFlatCasimir.iwasawa_insertion, hhorizontal, hheights]
  simp only [show ((0,0) : KPGlobalTorusFunctionData.Adeles F) = 0 from rfl,
    hN, one_mul]
  rw [coreResidue_average_upper_arch_covariance R P C
    (H.atlas (KPContActualAllCuspSource.level F R.A.zeta12 R.A.primitive_zeta12 D Haar Transport H U))
    j K hK ν x]
  congr 2
  rw [Finset.sum_add_distrib,hb,add_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [KPContFlatArchDiagonalMultiplier.complexDimension_eq_card F R.A.zeta12 R.A.primitive_zeta12]
  push_cast
  ring

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
