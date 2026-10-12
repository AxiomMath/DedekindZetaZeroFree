module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspPeriods.UpperZeroInvariance
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
local instance : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

 theorem kernel_pairing_eq_mean
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ V R P H T)
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)
    (u : SmoothSections F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ Ω)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ V → ℂ) (ha : Measurable a)
    (he : ∀ v : X, a (q F ζ hζ V v) =
      star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U (source.descent.commutator s) v)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (r : Set.Ioi Y) (ht : B.τ < KPMsFixedHaarDisintegration.logHeight (F := F) r.val)
    (j : KPMsFixedHaarDisintegration.CuspIndex A) (b : KPCuspCharts.Shape F) :
    (∫ x, a ((H.disintegration V).chart Y hY (x,r)) ∂(H.disintegration V).unipotent ⟨j,QuotientAddGroup.mk b⟩) = (KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
      (χ j).toFun s (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) *
      (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U j ι s (f s)
        (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
        (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)).val 0) *
    star (∫ q, IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U j u
      (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
        (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩) (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) q
      ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U j) := by
  obtain ⟨dn,hhaar,hprob,hmap⟩ := (H.disintegration V).fiber_formula j b
  let L := (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U j).L
  let K := KPCuspGenuineMonodromy.kernelLattice
    (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U j)
    (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U j)
    (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U j)
  let μ := KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U j
  let := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U j).compact
  let := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U j
  let := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U j
  let := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U j
  let G := KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U j
  let : MeasurableSpace (KPCuspCharts.CrossQuotient F
    (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U j)) := borel _
  let : BorelSpace (KPCuspCharts.CrossQuotient F
    (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U j)) := ⟨rfl⟩
  obtain ⟨hdisc,_⟩ := G.lattice
  let : DiscreteTopology (KPCuspCharts.translationLattice F L) := hdisc
  let : IsClosed (KPCuspCharts.translationLattice F L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  let : BorelSpace (KPCuspCharts.Torus F L) := QuotientAddGroup.borelSpace
  let : CompactSpace (KPCuspCharts.Torus F L) := G.compact_torus
  let := hhaar
  let := hprob
  let π := Transport.horizontalTorusMap F K L
    (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U j).kernel_le
  have hπ : Measure.map π μ = dn :=
    Transport.horizontalTorusMap_probabilityHaar F K L _ μ dn
  have hf : Measurable (fun z : KPCuspCharts.Torus F L =>
      a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (z,b)⟩,r))) :=
    ha.comp ((H.disintegration V).measurable_chart Y hY |>.comp
      (((continuous_sigmaMk (i := j)).measurable.comp (G.atlas.continuous_lift.measurable.comp
        (measurable_id.prodMk measurable_const))).prodMk measurable_const))
  rw [hmap, integral_map]
  · rw [← hπ, integral_map (Transport.horizontalTorusMap_continuous F K L _).measurable.aemeasurable hf.aestronglyMeasurable]
    have hval (q : KPCuspCharts.Torus F K) :
      a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (π q,b)⟩,r)) =
        star (IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U j u
          (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
            (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)
          (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) q) *
        IncomingFiberOrthogonality.frameFiber F ζ hζ C R P H U j (source.descent.commutator s)
          (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
            (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)
          (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) q := by
      induction q using Quotient.inductionOn with | h x =>
        change a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (QuotientAddGroup.mk x,b)⟩,r)) = _
        rw [G.atlas.lift_formula]
        rw [chart_pairing F ζ hζ C R P H U u (source.descent.commutator s) a he]
        rw [IncomingFiberOrthogonality.frameFiber_mk,IncomingFiberOrthogonality.frameFiber_mk]
    change (∫ x, a ((H.disintegration V).chart Y hY (⟨j,G.atlas.lift (π x,b)⟩,r)) ∂μ) = _
    simp_rw [hval]
    simp_rw [IncomingFiberOrthogonality.commutator_frameFiber_eq_constant
      F ζ hζ C R P H U j ι B Ω f χ source s hs (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
        (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩) (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) ht]
    rw [integral_mul_const, mul_comm]
    congr 1
    exact integral_conj
  · exact ((continuous_sigmaMk (i := j)).measurable.comp (G.atlas.continuous_lift.measurable.comp
      (measurable_id.prodMk measurable_const))).aemeasurable
  · exact (ha.comp ((H.disintegration V).measurable_chart Y hY |>.comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable

 theorem kernel_pairing_eq_upper
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ V R P H T)
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)
    (u : SmoothSections F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ Ω)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ V → ℂ) (ha : Measurable a)
    (he : ∀ v : X, a (q F ζ hζ V v) =
      star (scalar F ζ hζ C R P H U u v) * scalar F ζ hζ C R P H U (source.descent.commutator s) v)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (r : Set.Ioi Y) (ht : B.τ < KPMsFixedHaarDisintegration.logHeight (F := F) r.val)
    (j : KPMsFixedHaarDisintegration.CuspIndex A) (b : KPCuspCharts.Shape F) :
    (∫ x, a ((H.disintegration V).chart Y hY (x,r)) ∂(H.disintegration V).unipotent ⟨j,QuotientAddGroup.mk b⟩) = (KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
      (χ j).toFun s (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) *
      (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U j ι s (f s)
        (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
        (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩)).val 0) *
    star (upperConstantTerm F ζ hζ
      (KPWildKernelUpperBound.quotientHaar F)
      (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ
        (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U) R P H u.val)
      (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U j
        (KPMsFixedHaarDisintegration.logHeight (F := F) r.val) 0 (b + KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
        (H.disintegration V).radial.slot ⟨r.val,lt_trans hY.1 r.property⟩) 1)) := by
  rw [kernel_pairing_eq_mean F ζ hζ C R P H U ι B Ω f χ source u s hs a ha he Y hY r ht j b]
  rw [DedekindZetaZeroFree.FourierContinuation.ResidualCuspBoundary.section_kernel_period_eq_literal]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge

end
