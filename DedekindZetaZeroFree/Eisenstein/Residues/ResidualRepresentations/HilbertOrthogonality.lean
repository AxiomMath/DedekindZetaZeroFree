module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.FinitePlaceActions
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteHilbertOrthogonalCenters

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators

theorem core_residue_hilbert_orthogonal_centers (x : V) :
    ∃ (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
      (HR : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
      (HP : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
      (HH : KPMsFixedHaarDisintegration.AllLevels F ζ hζ HR HP),
    ∃ (n : ℕ) (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (m : Fin n → ℕ) (w : ∀ i, Fin (m i) → List (Fin (groupDimension F)))
      (B : ∀ i, Fin (m i) → ℂ → ℂ)
      (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ M HR HP HH (U i))
      (z : ∀ i, Fin (m i) → KPContActualAllCuspSource.Sector F ζ hζ M HR HP HH (U i)),
      (∀ i j, KPContActualSmoothLineGluing.Represents F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ M HR HP HH (U i)) HR HP HH (Z i j).val (z i j)) ∧
      (∀ i j, (z i j, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) 0 • z i j) ∈
        (ResidualHilbertCenters.sourceLaplacian F ζ hζ M HR HP HH (U i)).graph) ∧
      (∀ i j, ResidualHilbertCenters.CuspEigentestOrthogonal F ζ hζ M HR HP HH (U i) 0 (z i j)) ∧
      (∀ i j g, KPMsGreenFlux.casimir F ζ hζ
        (groupScalar F ζ hζ M HR HP HH (U i) (Z i j)) g =
        KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
          groupScalar F ζ hζ M HR HP HH (U i) (Z i j) g) ∧
      (∀ i j, KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
        F ζ hζ M HR HP HH (U i) (Z i j) → Z i j = 0) ∧
      ∀ g, coreResidue R P C x g = ∑ i, ∑ j, B i j 0 * actualRightWord F ζ hζ (w i j)
        (groupScalar F ζ hζ M HR HP HH (U i) (Z i j)) g := by
  letI : T2Space (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨M, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨HR, _, _, HP, ⟨HH⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ (Measure.haar : Measure (G F ζ hζ)) inferInstance
  let A := ownedLiteralResidueFamily (full_product_compact_iwasawa R)
  obtain ⟨n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, he⟩ :=
    ResidualHilbertCenters.finite_owned_residue_hilbert_orthogonal_centers F ζ hζ M HR HP HH
      (fullProductCompact R) (full_product_compact_iwasawa R)
      (asLiteralFlat (coreFlatInsertion R P C x)) A
  refine ⟨M, HR, HP, HH, n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, ?_⟩
  intro g
  have hpin : coreResidue R P C x = A.cleared (asLiteralFlat (coreFlatInsertion R P C x)) 0 := by
    change A.residue (literalZeroProfileEquiv (full_product_compact_iwasawa R)
      (coreFlatInsertion R P C x)) = _
    exact A.residue_flat _
  rw [hpin]
  exact he g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
