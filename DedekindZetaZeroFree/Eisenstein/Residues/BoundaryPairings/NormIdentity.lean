module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.DifferentialWordAdjoints
public import DedekindZetaZeroFree.Eisenstein.Residues.BoundaryPairings.LevelChange
public import DedekindZetaZeroFree.Eisenstein.Residues.BoundaryPairings.NormExpansion
public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.SourceReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open KPContSectorCoveredQuotientVocabulary KPContFlatCuspIncomingEvaluation
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
variable (HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
variable (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
variable (U : Level F R.A.zeta12 R.A.primitive_zeta12)
local notation "H" => nativeFamily F ζ hζ HR HP
local notation "V" => EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U
local instance ResidualCoreNormIdentityMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualCoreNormIdentityBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

include M D in
theorem exists_core_norm_boundary_identity
    (N : MomentSources.TraceHaarTransport R)
    (J : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F))
    [IsProbabilityMeasure dk] [dk.IsHaarMeasure] (x : Core)
    (hsJ : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
      quotientCoreEvaluator R.A P C x (g*u)=quotientCoreEvaluator R.A P C x g)
    (hxJ : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
      coreResidue R P C x (g*u)=coreResidue R P C x g) :
    ∃ f : smoothAllWordL2 HR,
      (∀g, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g) ∧
      (∫q, star (f.val q)*f.val q ∂ HR.quotientHaar) =
        finiteBoundaryPair R HR HP J dk (quotientCoreEvaluator R.A P C x) (coreResidue R P C x) := by
  obtain ⟨n,Us,m,v,w,a,f,Vnew,hVJ,hVU,hfx,hs,hpair⟩ :=
    exists_core_norm_boundary_expansion R P C D HR HP M J dk x hxJ
  refine ⟨f,hfx,?_⟩
  have hzero (i : Fin n) (j : Fin (m i)) :
      (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val = (v i j).val.val.val := by
    funext g
    simp only [KPContFlatSourceRecipe.flatR_formula,zero_mul,Complex.exp_zero,one_mul]
  calc
    _ = ∑i, ∑j, a i j * (-1 : ℂ)^(w i j).length *
        finiteBoundaryPair R HR HP Vnew dk (v i j).val.val.val
          (actualRightWord F ζ hζ (w i j).reverse (coreResidue R P C x)) := by
            simpa only [hzero] using hpair
    _ = ∑i, ∑j, a i j * finiteBoundaryPair R HR HP Vnew dk
        (actualRightWord F ζ hζ (w i j) (v i j).val.val.val) (coreResidue R P C x) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [finiteBoundaryPair_word_adjoint R P C HR HP N  Vnew dk (v i j).val x f hfx]
      have he : (-1 : ℂ)^(w i j).length * (-1 : ℂ)^(w i j).length = 1 := by
        rw [←mul_pow]; norm_num
      rw [mul_assoc, ←mul_assoc ((-1 : ℂ)^(w i j).length) ((-1 : ℂ)^(w i j).length), he, one_mul]
    _ = finiteBoundaryPair R HR HP Vnew dk (quotientCoreEvaluator R.A P C x) (coreResidue R P C x) := by
      symm
      simpa only [hzero] using finiteBoundaryPair_source_reconstruction R P C HR HP
        n Us m v w a Vnew dk x hs
    _ = _ := finiteBoundaryPair_core_relevel R P C HR HP M Vnew J dk x
      (fun g u hu => hsJ g u (Subgroup.map_mono hVJ hu)) hsJ
      (fun g u hu => hxJ g u (Subgroup.map_mono hVJ hu)) hxJ

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
