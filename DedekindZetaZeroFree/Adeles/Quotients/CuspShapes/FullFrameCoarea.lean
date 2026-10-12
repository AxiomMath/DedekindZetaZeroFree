module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CoherentLevelsAndNormInvariance
public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteOffsetConstruction
public import DedekindZetaZeroFree.Adeles.Quotients.CuspMeasures.StabilizerAveragesAndCoarea

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.NativeCoarea
open KPMsActualAngularSource KPCompactStabilizerHaarSources KPActualComponentHaarSources
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure renaming actual_high_cusp_joint_coarea → actual_high_cusp_joint_coarea

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
variable (S : KPMsAngularSourceRecipe.OffsetSourceRecipe F ζ hζ R P H)
variable (V : KPMsActualAngularSource.Level F ζ hζ)

theorem actual_full_cusp_coarea
    (j : KPMsFixedHaarDisintegration.CuspIndex
      (H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V)))) :
    ∃ (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
      (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
        (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
      (c : ℝ≥0),
      ν.IsHaarMeasure ∧ SFinite ν ∧ 0 < c ∧
      (∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a) ∧
      (∀ x k i, (e.symm (x,k)) (KPCusp.complexPlace F i) =
        (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
          (k : G (KPCuspLogShape.dimension F))) i) ∧
      ∀ Y, KPMsFixedHaarDisintegration.AdmissibleCutoff
          (H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))) Y →
      ∀ (φ : KPSmoothLocalQuotientCharts.X F ζ hζ → ℝ≥0∞), Measurable φ →
        (∫⁻ y in KPMsActualCuspSource.cuspEnd (H := H)
          (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V)) j Y,
          φ y ∂ R.quotientHaar) =
        (c : ℝ≥0∞) * ∫⁻ p : KPCuspCharts.Coordinates F,
          ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
            φ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (m F ζ hζ (e.symm
                ((((H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))).cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p,z.1),z.2)))
            ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
              (ν.restrict (B F ζ hζ H.totallyComplex
                (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))
                (H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))) j.1))
          ∂((((volume.prod
            (((H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))).cuspAtlas j.1).geometry j.2).shapeMeasure).prod
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
              {p : KPCuspCharts.Coordinates F | p.1 ∈
                (((H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))).cuspAtlas j.1).geometry j.2).fundamentalDomain}).restrict
                    {p : KPCuspCharts.Coordinates F |
                      KPMsFixedHaarDisintegration.logHeight (F := F) Y < p.2}) := by
  obtain ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,hcoarea⟩ := actual_high_cusp_joint_coarea
    H.totallyComplex (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))
    (H.atlas (S.atlasLevel (KPShift81CoherentLevel.level F ζ hζ V))) R
    (toRawTransport F ζ hζ P) j.1
  exact ⟨ν,e,c,hν,hνsf,hc,heBase,heFiber,fun Y hY φ hφ =>
    hcoarea j.2 (KPMsFixedHaarDisintegration.logHeight (F := F) Y) hY.2 φ hφ⟩

theorem actual_coarea_frame_radius
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (σ : KPCuspArithmetic.PGL2 F) (p : KPCuspCharts.Cross F) (t : ℝ)
    (k : K (KPCuspLogShape.dimension F)) (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    (KPMsActualAngularSource.framedRadius F ζ hζ (KPMsAngularSourceRecipe.D F ζ hζ)
      (KPMsActualCuspSource.rationalLift F ζ hζ σ)
      (m F ζ hζ (e.symm (KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t)),k),b))).val =
    (KPMsAngularSourceRecipe.finiteOffset F ζ hζ
      (KPMsActualCuspSource.rationalLift F ζ hζ σ) b.val).val *
        Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  apply KPMsAngularSourceRecipe.actual_frame_norm_factorization
  rw [← heBase, e.apply_symm_apply]

end DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.NativeCoarea

end
