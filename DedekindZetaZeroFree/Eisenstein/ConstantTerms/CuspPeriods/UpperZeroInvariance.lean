module

public import DedekindZetaZeroFree.Eisenstein.Induction.SmoothSections.AutomorphicLift
public import DedekindZetaZeroFree.Eisenstein.Continuation.ClearedGerms.UniformCuspidalCenterDisk

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCuspBoundary
open KPGlobalResidualConstruction KPContActualCommonDiskRightHolomorphy
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
local notation "G" => KPLiteralRaw.G F ζ hζ
local notation "A" => KPGlobalTorusFunctionData.Adeles F
local notation "Y" => KPAdditiveQuotient F

theorem lift_upper_rational
    (Z : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (x : A) (t : F) (g : G) :
    lift F ζ hζ U R P H Z (KPGlobalTorusFunctionData.N F ζ hζ
      (x + algebraMap F A t) * g) =
      lift F ζ hζ U R P H Z (KPGlobalTorusFunctionData.N F ζ hζ x * g) := by
  rw [add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc]
  have hr : KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F A t) ∈
      KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPRationalAdelicSplitting.N F ζ hζ (algebraMap F A t)) ∈ _
    rw [KPRationalAdelicSplitting.N_rational]
    exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.n F t), rfl⟩
  have hq : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F A t) *
        (KPGlobalTorusFunctionData.N F ζ hζ x * g)) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPGlobalTorusFunctionData.N F ζ hζ x * g) :=
    Quotient.sound ⟨⟨_, hr⟩, rfl⟩
  simp only [lift, hq]

theorem lift_integrand_mk
    (Z : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (x : A) (g : G) :
    lift F ζ hζ U R P H Z
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk x : Y)) * g) =
    lift F ζ hζ U R P H Z (KPGlobalTorusFunctionData.N F ζ hζ x * g) := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add (AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨t, ht⟩ := r.property
  rw [hr, ← ht]
  exact lift_upper_rational F ζ hζ U R P H Z x t g

theorem lift_integrand_continuous
    (Z : KPContSectorSmoothFramesSupport.smoothSections F ζ hζ U R P H) (g : G) :
    Continuous (fun q : Y => lift F ζ hζ U R P H Z.val
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)) := by
  letI : IsTopologicalGroup G := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply (QuotientAddGroup.isQuotientMap_mk (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  simpa only [Function.comp_def, lift_integrand_mk, Pi.mul_apply] using
    (ActualSectionLift.lift_continuous F ζ hζ U R P H Z).comp
      ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ).mul continuous_const)

open KPGlobalResidualConstruction.CommonSphericalDisk.PolarDetection
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.PolarDetection renaming section_localGroup_frame → section_localGroup_frame
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.PolarDetection renaming section_arch_root_orbit → section_arch_root_orbit
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.PolarDetection renaming section_finite_root_orbit → section_finite_root_orbit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
section ActualKernelPeriodTransport

open NumberField
open KPContFlatCuspIncomingEvaluation
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (Z : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
local notation "lZ" => KPContActualCommonDiskRightHolomorphy.lift F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z.val
variable (a : Cusps F ζ hζ C R P H U) (t : ℝ) (b : KPCuspCharts.Shape F)
theorem section_kernel_period_eq_literal :
    (∫ q, IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U a Z b t q
      ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
    upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F)
      lZ
      (localGroup F ζ hζ C R P H U a t 0 b 1) := by
  let liftZ := lZ
  obtain ⟨K,hc,ho,hroot,hkernel⟩ := KPContinuation.ChamberOutgoingSource.actual_cusp_finite_kernel_level F ζ hζ C R P H U a
  let g := localGroup F ζ hζ C R P H U a t 0 b 1
  let GG : KPCompactFourier.AdditiveQuotient F → ℂ := fun q => lZ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
  have hG : Continuous GG := lift_integrand_continuous F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z g
  have hinv : ∀q h, h ∈ finiteLevelImage K → GG (q+h)=GG q := by
    intro q h hh
    obtain ⟨z,hz,rfl⟩ := hh
    induction q using Quotient.inductionOn with | h x =>
      change GG (QuotientAddGroup.mk x + QuotientAddGroup.mk (finiteParameter F z)) = GG (QuotientAddGroup.mk x)
      rw [← QuotientAddGroup.mk_add]
      change liftZ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk (x + finiteParameter F z))) * g) = liftZ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk x)) * g)
      dsimp only [liftZ]
      rw [lift_integrand_mk F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z.val,
        lift_integrand_mk F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z.val]
      exact section_finite_root_orbit F ζ hζ C R P H U Z a t b z (hroot z hz) x
  letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  obtain ⟨D,hD,hfd⟩ := additiveProductHaar_exists_fundamentalDomain F (KPAdditiveHaar.finiteMeasure F)
  have hnorm : KPAdditiveHaar.finiteMeasure F (integralFiniteAdeles F : Set _) =
    ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|) :=
    (KPAdditiveHaar.finiteMeasure_integral_mass F).trans (KPAdditiveHaar.finiteMass_eq_discriminant F).1
  obtain ⟨GK,hGK,hformula,hint⟩ := finiteLevel_quotient_integral_torus_probability F
    (KPAdditiveHaar.finiteMeasure F) hnorm D hD hfd K hc ho GG hG hinv
  obtain ⟨ν,hν,hprob⟩ := finiteLevel_torus_exists_haar_probability K hc ho
  letI := hν
  letI := hprob
  have hQ : additiveQuotientMeasureFromDomain F (KPAdditiveHaar.finiteMeasure F) D =
      KPWildKernelUpperBound.quotientHaar F := by
    obtain ⟨hhaar,hp,-⟩ := additiveQuotientMeasureFromDomain_haar_probability F (KPAdditiveHaar.finiteMeasure F) hnorm D hD hfd
    letI := hhaar
    letI := hp
    exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hGI : (∫q, GG q ∂KPWildKernelUpperBound.quotientHaar F) = ∫x,GK x ∂ν := by
    rw [← hQ]
    exact hint ν hν hprob
  let L := KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
    (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a)
  have hle := KPContinuation.ChamberOutgoingSource.finiteLevelLattice_le_horizontal_of_rational_kernel F K L hkernel
  let p := KPContinuation.ChamberOutgoingSource.mixedHorizontalQuotientMap F K L hle
  let φ := IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U a Z b t
  have hφ : Continuous φ := by
    apply continuous_coinduced_dom.mpr
    change Continuous (fun x : KPCuspCharts.Horizontal F => φ (QuotientAddGroup.mk x))
    dsimp only [φ]
    simp_rw [IncomingFiberOrthogonality.frameFiber_mk]
    exact (KPContSectorSmoothFramesSupport.cuspCoefficient_smooth F ζ hζ
      (atlasLevel F ζ hζ C R P H U) R P H Z.val Z.property a.1 a.2).continuous.comp
      ((continuous_id.prodMk continuous_const).prodMk continuous_const)
  have heq : GK = φ ∘ p := by
    funext q
    induction q using Quotient.inductionOn with | h x =>
      rw [hformula]
      dsimp only [Function.comp_def,p]
      rw [KPContinuation.ChamberOutgoingSource.mixedHorizontalQuotientMap_mk]
      dsimp only [GG,φ,g]
      change liftZ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk
        (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x,0) : KPGlobalTorusFunctionData.Adeles F))) * localGroup F ζ hζ C R P H U a t 0 b 1) = _
      dsimp only [liftZ]
      rw [lift_integrand_mk F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z.val]
      change lZ (KPGlobalTorusFunctionData.N F ζ hζ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x,0) * localGroup F ζ hζ C R P H U a t 0 b 1) = _
      rw [section_arch_root_orbit F ζ hζ C R P H U Z a t b,
        section_localGroup_frame F ζ hζ C R P H U Z a t b,
        IncomingFiberOrthogonality.frameFiber_mk]
      rw [RingEquiv.apply_symm_apply]
  change (∫ z, φ z ∂_) = ∫q, GG q ∂_
  rw [hGI,heq]
  have hm := KPContinuation.ChamberOutgoingSource.actual_kernelTorus_probabilityHaar_transport F ζ hζ C R P H U a K hc ho hle ν
  letI := finiteLevelLattice_discrete K hc ho
  letI : DiscreteTopology (finiteLevelLattice K).toAddSubgroup := inferInstanceAs (DiscreteTopology (finiteLevelLattice K))
  letI : IsClosed ((finiteLevelLattice K).toAddSubgroup : Set (mixedEmbedding.mixedSpace F)) := AddSubgroup.isClosed_of_discreteTopology
  letI : BorelSpace (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup) := AddCosetSpace.borelSpace
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  rw [← hm]
  exact integral_map (KPContinuation.ChamberOutgoingSource.mixedHorizontalQuotientMap_continuous F K L hle).measurable.aemeasurable hφ.measurable.aestronglyMeasurable

theorem allCuspMeanZero_of_original_upper_zero
    (hz : ∀ g, (∫ q : KPAdditiveQuotient F,
      lZ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
      ∂KPWildKernelUpperBound.quotientHaar F) = 0) :
    IncomingFiberOrthogonality.AllCuspMeanZero F ζ hζ C R P H U Z := by
  intro a b t
  rw [section_kernel_period_eq_literal F ζ hζ C R P H U Z a t b]
  exact hz _

end ActualKernelPeriodTransport

def UpperZero (f : G → ℂ) : Prop :=
  ∀ g, (∫ q : KPAdditiveQuotient F,
    f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
    ∂KPWildKernelUpperBound.quotientHaar F) = 0

end DedekindZetaZeroFree.FourierContinuation.ResidualCuspBoundary

end
