module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.BalancedArchimedeanFibers
public import DedekindZetaZeroFree.Theta.Periods.Cusps.NormalizedScalarRay
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.IntrinsicShapeDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentNativeBoundaryFrame
open KPMsActualAngularSource KPMsNativeOffsetMass
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming actualFrame_spec → actualFrame_spec
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
private theorem actual_ray_right_compact
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U₀ : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U₀)
    (j : KPMsGreenFlux.Cusps A) (p : KPCuspCharts.Cross F)
    (κ k : KPMsGreenFlux.K F) (r : ℝ) (ε : rootsOfUnity 3 F) (u : U₀.toOpenSubgroup) :
    (KPBoundedCuspFrames.actualCuspLift A j p κ r *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val) *
        KPMsGreenFlux.compactInsertion F ζ hζ k =
      KPBoundedCuspFrames.actualCuspLift A j p (κ*k) r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val := by
  have hb : KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p (κ*k) r =
      KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p κ r * (fun w => (k w).val) := by
    funext w
    simp only [KPMsGreenFlux.balancedArch, Pi.mul_apply, Subgroup.coe_mul, mul_assoc]
  have hfinite := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
    F ζ hζ (fun w => (k w).val) (KPBoundedCuspFrames.actualFiniteRepresentative A j *
      KPCuspGenuineMonodromy.central F ζ hζ ε * u.val)
  unfold KPBoundedCuspFrames.actualCuspLift
  rw [hb, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  simp only [Subgroup.coe_mul] at hfinite
  change Commute (KPMsGreenFlux.compactInsertion F ζ hζ k)
    ((KPBoundedCuspFrames.actualFiniteRepresentative A j).val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val) at hfinite
  simpa only [KPMsGreenFlux.compactInsertion, mul_assoc] using
    congrArg (fun z => KPMsGreenFlux.cuspRepresentative A j *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p κ r) * z)) hfinite.eq.symm

theorem native_frame_average
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (φ : G F ζ hζ → ℂ)
    (haφ : ∀ (u : NumberField.InfinitePlace F → ℝ) g,
      φ ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val * g) =
        Complex.exp ((2:ℂ) * ((∑v,u v:ℝ):ℂ)) * φ g)
    (hnφ : ∀ n g, φ (KPGlobalTorusFunctionData.N F ζ hζ n * g) = φ g)
    (hcφ : ∀ ε g, φ (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) = φ g)
    (huφ : ∀ (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ V) g, φ (g*u.val) = φ g)
    (dk : Measure (KPMsGreenFlux.K F)) [dk.IsHaarMeasure]
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ) (hx : x ∈ cuspShell F ζ hζ R P S V j Y) :
    (∫ k, φ (framedNormalization F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ R P S V).radial
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))
      (actualFrame F ζ hζ R P S V j Y x * KPMsGreenFlux.compactInsertion F ζ hζ k)) ∂dk) =
    ((cuspOffset F ζ hζ R P S V j).val:ℂ)⁻¹ *
      ∫ k, φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative (nativeAtlas F ζ hζ R P S V) j).val) ∂dk := by
  obtain ⟨a,p,t,ε,u,ht,ha,he⟩ :=
    (actualFrame_spec F ζ hζ R P S V j Y x hx.1).2
  let A := nativeAtlas F ζ hζ R P S V
  let B := (nativeDisintegration F ζ hζ R P S V).radial
  let σ := KPMsGreenFlux.cuspRepresentative A j
  let r := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)
  obtain ⟨κ,hκ⟩ := CurrentBoundaryArchFiber.arch_fiber_eq_balanced
    (ζ := ζ) (hζ := hζ) _ a p t ha
  have hu : u.val ∈ (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup.toSubgroup.map
      (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype := by
    simpa only [← S.level_matching (cofinalLevel F ζ hζ V)] using u.property
  obtain ⟨u₀,hu₀,hu₀eq⟩ := hu
  let u' : (S.atlasLevel (cofinalLevel F ζ hζ V)).toOpenSubgroup := ⟨u₀,hu₀⟩
  have hu'eq : u'.val.val = u.val := hu₀eq
  have hσ : KPMsActualCuspSource.rationalLift F ζ hζ
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) = σ := by
    have hh := KPMsActualCuspSource.rationalLift_mk F ζ hζ
      (((A.cuspAtlas j.1).representative j.2).out)
    rw [show Matrix.ProjGenLinGroup.mk (((A.cuspAtlas j.1).representative j.2).out) =
      ((A.cuspAtlas j.1).representative j.2) from Quotient.out_eq _] at hh
    exact hh.trans (KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ _).symm
  have hframe : actualFrame F ζ hζ R P S V j Y x =
      KPBoundedCuspFrames.actualCuspLift A j p κ r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u'.val.val := by
    rw [he, hκ, KPBoundedCuspFrames.actualCuspLift_arch_finite_formula, hu'eq]
    rfl
  have hc : CurrentBoundaryFrame.cuspOffset A j ε u' = cuspOffset F ζ hζ R P S V j := by
    unfold CurrentBoundaryFrame.cuspOffset
    simp only [Subgroup.coe_mul]
    rw [hu'eq]
    exact cuspOffset_right_center_cofinal F ζ hζ R P S V j ε u
  let uV : KPGlobalTorusFunctionData.globalLevel F ζ hζ V :=
    ⟨u.val,KPShift81CoherentLevel.globalLevel_le F ζ hζ V u.property⟩
  have hp (k : KPMsGreenFlux.K F) :
      φ (framedNormalization F ζ hζ (nativeDatum F ζ hζ) B σ
        (actualFrame F ζ hζ R P S V j Y x * KPMsGreenFlux.compactInsertion F ζ hζ k)) =
      ((cuspOffset F ζ hζ R P S V j).val:ℂ)⁻¹ *
        φ (KPMsGreenFlux.compactInsertion F ζ hζ (κ*k) *
          (KPBoundedCuspFrames.actualFiniteRepresentative A j).val) := by
    rw [hframe,actual_ray_right_compact]
    rw [CurrentBoundaryFrame.scalar_normalized_actual_ray φ haφ hnφ A B j p (κ*k) ε u' r (Real.exp_pos _)]
    rw [hc,hu'eq]
    rw [huφ uV]
    have hz := Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩)
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun i => ((κ*k) i).val) *
        (KPBoundedCuspFrames.actualFiniteRepresentative A j).val)
    rw [hz,hcφ]
    rfl
  rw [hσ]
  change (∫ k, φ (framedNormalization F ζ hζ (nativeDatum F ζ hζ) B σ
    (actualFrame F ζ hζ R P S V j Y x * KPMsGreenFlux.compactInsertion F ζ hζ k)) ∂dk) = _
  simp_rw [hp]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (μ := dk)
    (fun k => φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
      (KPBoundedCuspFrames.actualFiniteRepresentative A j).val)) κ
end DedekindZetaZeroFree.CurrentNativeBoundaryFrame

end
