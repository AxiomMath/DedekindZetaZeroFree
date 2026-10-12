module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Bruhat.OpenCellSummand
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.UnipotentOrbit.ArchimedeanCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open KPContFlatCuspIncomingEvaluation
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S) (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
variable (g : KPGlobalTorusFunctionData.G F ζ hζ)
include hι hf hs in
theorem actual_upper_orbit_rational (r:F) (x:KPGlobalTorusFunctionData.Adeles F) :
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F _ r + x) * g) =
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ x * g) := by
 rw [KPGlobalTorusFunctionData.N_add, mul_assoc]
 have hn : KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F _ r) =
   KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F r) := by
   change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPRationalAdelicSplitting.N F ζ hζ (algebraMap F _ r)) = _
   rw [KPRationalAdelicSplitting.N_rational]
   rfl
 rw [hn, (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1]
include hι hf hs in
theorem actual_upper_orbit_mk (x:KPGlobalTorusFunctionData.Adeles F) :
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk x : KPCompactFourier.AdditiveQuotient F)) * g) =
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ x * g) := by
 obtain ⟨r,hr⟩ := QuotientAddGroup.mk_out_eq_add (AdeleRing.principalSubgroup (𝓞 F) F) x
 obtain ⟨r0,hr0⟩ := r.property
 rw [hr, ← hr0, add_comm]
 exact actual_upper_orbit_rational F ζ hζ U ι f hι hf s hs g r0 x
include hι hf hs in

theorem actual_upper_orbit_continuous : Continuous (fun q : KPCompactFourier.AdditiveQuotient F =>
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)) := by
 apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
 change Continuous (fun x : KPGlobalTorusFunctionData.Adeles F =>
   KPContActualChamberNormalSeries.E F ζ hζ U ι f s (KPGlobalTorusFunctionData.N F ζ hζ
     (Quotient.out (QuotientAddGroup.mk x : KPCompactFourier.AdditiveQuotient F)) * g))
 simp_rw [actual_upper_orbit_mk F ζ hζ U ι f hι hf s hs g]
 exact (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf s hs).1.comp
   ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ).mul continuous_const)
end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
