module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryPairings.FiniteCenterPairing
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteRefinedBoundaryCenters
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.CoreCompactCovariance

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
local instance ResidualCoreNormExpansionMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualCoreNormExpansionBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

include M D in
theorem exists_core_norm_boundary_expansion
    (J : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F))
    [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (x : Core)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
      coreResidue R P C x (g*u)=coreResidue R P C x g) :
    ∃(n : ℕ) (Us : Fin n → Level F ζ hζ) (m : Fin n → ℕ)
      (v : ∀i, Fin (m i) → KPContActualSphericalFlatStage.Stage F ζ hζ (Us i))
      (w : ∀i, Fin (m i) → List (Fin (groupDimension F)))
      (a : ∀i, Fin (m i) → ℂ) (f : smoothAllWordL2 HR) (Vnew : Level F ζ hζ),
      Vnew.toOpenSubgroup.toSubgroup ≤ J.toOpenSubgroup.toSubgroup ∧
      (∀i, Vnew.toOpenSubgroup.toSubgroup ≤ (Us i).toOpenSubgroup.toSubgroup) ∧
      (∀g, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g) ∧
      (∀g, quotientCoreEvaluator R.A P C x g =
        ∑i, ∑j, a i j * actualRightWord F ζ hζ (w i j)
          (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val g) ∧
      (∫q, star (f.val q)*f.val q ∂ HR.quotientHaar) =
        ∑i, ∑j, a i j * (-1 : ℂ)^(w i j).length *
          finiteBoundaryPair R HR HP Vnew dk
            (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val
            (actualRightWord F ζ hζ (w i j).reverse (coreResidue R P C x)) := by
  let A := TensorActionSource.ownedLiteralResidueFamily (ThetaExpansion.full_product_compact_iwasawa R)
  obtain ⟨n,Us,m,v,w,B,Z,z,hfix,haux,hz,hgraph,hb,hnative,hcus,hsource,hres⟩ :=
    ResidualHilbertCenters.finite_owned_refined_boundary_centers R P C D HR HP H J
      (ThetaExpansion.fullProductCompact R) (ThetaExpansion.full_product_compact_iwasawa R)
      (TensorActionSource.asLiteralFlat (coreFlatInsertion R P C x)) A
  let a := fun i j => B i j 0
  let f : smoothAllWordL2 HR :=
    ⟨ResidualHilbertCenters.finiteCenterSum F ζ hζ D HR HP H Us m w a Z,
      ResidualHilbertCenters.finiteCenterSum_mem F ζ hζ D HR HP H Us m w a Z z hz
        (KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0) hnative⟩
  have hfx (g) : f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g := by
    rw [coreResidue_eq_owned_cleared]
    exact (ResidualHilbertCenters.finiteCenterSum_lift F ζ hζ D HR HP H Us m w a Z g).trans
      (hres g).symm
  obtain ⟨Vnew,hVJ,hVU⟩ := ResidualBoundaryRelevel.exists_common_level F ζ hζ J n Us
  refine ⟨n,Us,m,v,w,a,f,Vnew,hVJ,hVU,hfx,?_,?_⟩
  · intro g
    have hh := hsource g
    change (coreFlatInsertion R P C x).val 0 g = _ at hh
    rw [coreFlatInsertion_zero] at hh
    exact hh
  · exact finite_center_boundary_pairing R P C D HR HP M Us m w a v Z z Vnew hVU hfix
      hz hb hnative dk x
      (fun i g u hu => hx g u (Subgroup.map_mono (haux i) hu)) f hfx

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
