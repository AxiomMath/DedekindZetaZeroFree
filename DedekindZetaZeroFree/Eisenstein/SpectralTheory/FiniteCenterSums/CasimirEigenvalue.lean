module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.QuotientRealization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Classical NumberField BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry ResidualWeakEnergy KPGlobalResidualConstruction
open KPMsClearedTruncationL2.NativeWordBridge
open KPContActualSphericalRightFieldIdentification
open RawWordKFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming actual_eq_word → actual_eq_word
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPSmoothActualFlowData.G F ζ hζ
local notation "NS" => scalarSpace (F := F) (ζ := ζ) (hζ := hζ)

def nativeCasimir : NS →ₗ[ℂ] NS :=
  ∑ v : NumberField.InfinitePlace F, -((1 : ℂ) / 4) •
    ((derivative (v,0)).comp (derivative (v,0)) -
      (derivative (v,1)).comp (derivative (v,1)) + (2 : ℂ) •
      ((derivative (v,2)).comp (derivative (v,4)) +
       (derivative (v,4)).comp (derivative (v,2)) -
       (derivative (v,3)).comp (derivative (v,5)) -
       (derivative (v,5)).comp (derivative (v,3))))

theorem nativeCasimir_val (f : NS) : (nativeCasimir f).val =
    KPMsGreenFlux.casimir F ζ hζ f.val := by
  funext g
  simp only [nativeCasimir, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub,
    Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  rfl

variable (F ζ hζ)
variable (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable {n : ℕ} (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (m : Fin n → ℕ)
variable (w : ∀ i, Fin (m i) → List (Fin (groupDimension F)))
variable (a : ∀ i, Fin (m i) → ℂ)
variable (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ M R P H (U i))

 def centerWord (i : Fin n) (j : Fin (m i)) : NS :=
  let f := originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j)
  let up := fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)
  let hs : NativeSmooth up := by
    intro g
    have hh := ActualSectionLift.lift_arch_smooth F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j) g
    convert hh using 1
    funext x
    exact originalScalar_lift F ζ hζ _ R P H (Z i j) _
  ⟨sixWord ((w i j).map (wordIndexEquiv F)) up,
    sixWord_smooth up hs _⟩

private theorem centerWord_val (i : Fin n) (j : Fin (m i)) :
    (centerWord F ζ hζ M R P H U m w Z i j).val = fun g =>
      KPSmoothActualFlowData.wordDerivative F ζ hζ ((w i j).map (wordIndexEquiv F))
        (originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j))
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  funext g
  rw [← actualRightWord_eq_wordDerivative]
  rw [actual_eq_word]
  rfl

 def finiteCenterVector : NS := ∑ i, ∑ j, a i j • centerWord F ζ hζ M R P H U m w Z i j

private theorem finiteCenterVector_val :
    (finiteCenterVector F ζ hζ M R P H U m w a Z).val = fun g =>
      finiteCenterSum F ζ hζ M R P H U m w a Z (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  funext g
  simp only [finiteCenterVector, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, centerWord_val, finiteCenterSum]

 theorem finiteCenterSum_native_smooth : NativeSmooth (fun g =>
    finiteCenterSum F ζ hζ M R P H U m w a Z (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) := by
  rw [← finiteCenterVector_val]
  exact (finiteCenterVector F ζ hζ M R P H U m w a Z).property

theorem finiteCenterSum_native_eigen (eig : ℂ)
    (he : ∀ i j g, KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) g =
      eig * KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j) g)
    (g : G) :
    KPMsGreenFlux.casimir F ζ hζ (fun x => finiteCenterSum F ζ hζ M R P H U m w a Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x)) g =
      eig * finiteCenterSum F ζ hζ M R P H U m w a Z
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  have hc (i : Fin n) (j : Fin (m i)) :
      nativeCasimir (centerWord F ζ hζ M R P H U m w Z i j) =
        eig • centerWord F ζ hζ M R P H U m w Z i j := by
    apply Subtype.ext
    rw [nativeCasimir_val]
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [centerWord_val]
    let f := originalScalar F ζ hζ (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j)
    have hs : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (b * archChart F ζ hζ x))) (archDomain F) := by
      intro b
      have hh := ActualSectionLift.lift_arch_smooth F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j) b
      convert hh using 1
      funext x
      exact originalScalar_lift F ζ hζ _ R P H (Z i j) _
    have hfe : ∀ g, KPMsGreenFlux.casimir F ζ hζ
        (fun x => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x)) g =
        eig * f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := he i j
    exact original_word_eigen f hs eig hfe _ g
  have hsum : nativeCasimir (finiteCenterVector F ζ hζ M R P H U m w a Z) =
      eig • finiteCenterVector F ζ hζ M R P H U m w a Z := by
    simp only [finiteCenterVector, map_sum, map_smul, hc, Finset.smul_sum]
    congr 1
    funext i
    congr 1
    funext j
    exact smul_comm _ _ _
  have h := congrArg (fun x : NS => x.val g) hsum
  simpa only [nativeCasimir_val, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, finiteCenterVector_val] using h

theorem finiteCenterSum_word_eigen (eig : ℂ)
    (he : ∀ i j g, KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) g =
      eig * KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j) g)
    (q : List (KPSmoothActualFlowData.B F)) (g : G) :
    KPMsGreenFlux.casimir F ζ hζ (fun x => KPSmoothActualFlowData.wordDerivative F ζ hζ q
      (finiteCenterSum F ζ hζ M R P H U m w a Z) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x)) g =
      eig * KPSmoothActualFlowData.wordDerivative F ζ hζ q (finiteCenterSum F ζ hζ M R P H U m w a Z)
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  exact original_word_eigen _ (finiteCenterSum_native_smooth F ζ hζ M R P H U m w a Z) eig
    (finiteCenterSum_native_eigen F ζ hζ M R P H U m w a Z eig he) q g

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
