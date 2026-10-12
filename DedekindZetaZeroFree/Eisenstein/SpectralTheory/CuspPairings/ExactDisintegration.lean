module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ResidualCommutator.CuspPairingDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge
open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContActualCutoffSmoothDescent
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "V" => level F ζ hζ C R P H U
local notation "A" => H.atlas V
local notation "D" => H.disintegration V
local notation "CS" => KPMsFixedHaarDisintegration.CrossSection A
local notation "X" => Covered F ζ hζ C R P H U
local instance exactDisintegrationRoots : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

 theorem source_pairing_cusp_disintegration_exact
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ V R P H T)
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)
    (u : SmoothSections F ζ hζ C R P H U)
    (u_H : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hu_H : ((u_H.val : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V) : X → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F ζ hζ C R P H U] scalar F ζ hζ C R P H U u)
    (s : ℂ) (hs : s ∈ Ω) :
    ∃ (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
      (a : KPMsFixedHaarDisintegration.Spherical F ζ hζ V → ℂ),
      Y = Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * B.τ) ∧
      Measurable a ∧
      (∀ x : X, a (q F ζ hζ V x) =
        star (scalar F ζ hζ C R P H U u x) *
          scalar F ζ hζ C R P H U (source.descent.commutator s) x) ∧
      inner ℂ u_H (source.h s) =
        ((H.disintegration V).beta Set.univ).toReal *
          ∫ r : Set.Ioi Y, ∫ ω, ∫ x, a ((H.disintegration V).chart Y hY (x,r))
            ∂(H.disintegration V).unipotent ω
            ∂KPMsFixedHaarDisintegration.probability A (H.disintegration V).beta
            ∂Transport.cuspRadial Y := by
  let m := KPContActualAllCuspSource.measure F ζ hζ C R P H U
  let v := source.descent.commutator s
  let g : X → ℂ := fun x => star (scalar F ζ hζ C R P H U u x) * scalar F ζ hζ C R P H U v x
  have hint : Integrable g m := by
    apply (L2.integrable_inner u_H.val (source.h s).val).congr
    filter_upwards [hu_H, source.source_ae s hs] with x hx hy
    simp only [hx,hy,RCLike.inner_apply]
    exact mul_comm _ _
  have hpair : (∫ x, inner ℂ (u_H.val x) ((source.h s).val x) ∂m) = ∫ x,g x ∂m := by
    apply integral_congr_ae
    filter_upwards [hu_H, source.source_ae s hs] with x hx hy
    simp only [hx,hy,RCLike.inner_apply]
    exact mul_comm _ _
  have hgm : Measurable g := ((scalar_continuous F ζ hζ C R P H U u).star.measurable).mul
    (scalar_continuous F ζ hζ C R P H U v).measurable
  let Y := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * B.τ)
  have hd : 0 < KPCuspLogShape.dimension F := by
    exact KPCuspCharts.positive_dimension F H.totallyComplex
  have hy : KPMsFixedHaarDisintegration.logHeight (F := F) Y = B.τ := logHeight_exp F B.τ hd
  have hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y :=
    ⟨Real.exp_pos _, by rw [hy]; exact B.chart_threshold_le⟩
  obtain ⟨a,ha,he,hi⟩ := Transport.covered_integral_cusp_disintegration
    F ζ hζ R P H V Y hY g hint hgm (by
      intro x hx
      have hx' : ∀ j, x ∉ ends F ζ hζ C R P H U B j := by
        intro j hj
        apply hx
        unfold KPMsFixedHaarDisintegration.cuspEnds
        rw [hy]
        exact Set.mem_iUnion.mpr ⟨j,hj⟩
      exact mul_eq_zero_of_right _ (source.descent.off_ends s hs x hx').2)
  refine ⟨Y,hY,a,rfl,ha,?_,?_⟩
  · intro x
    rw [he,pairing_centralAverage]
  · change inner ℂ u_H.val (source.h s).val = _
    rw [L2.inner_def,hpair]
    exact hi

end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge

end
