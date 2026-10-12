module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspKernelTorus.ProbabilityHaarTransport
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.AllCuspSource

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.IncomingFiberOrthogonality

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
local notation "K" => KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a
local notation "μ" => KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U

def frameFiber (u : Smooth) (b : KPCuspCharts.Shape F) (t : ℝ) (q : K) : ℂ :=
  KPContActualCutoffSmoothDescent.frameValue F ζ hζ C R P H U u a ((Quotient.out q,b),t)

def AllCuspMeanZero (u : Smooth) : Prop :=
  ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
    ∀ b t, ∫ q, frameFiber F ζ hζ C R P H U a u b t q
      ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a = 0

private theorem frame_horizontal (u : Smooth) (b : KPCuspCharts.Shape F) (t : ℝ) :
    (fun x : KPCuspCharts.Horizontal F =>
      KPContActualCutoffSmoothDescent.frameValue F ζ hζ C R P H U u a ((x,b),t)) ∈
      KPCuspGenuineMonodromy.horizontalSections (ζ := ζ) (hζ := hζ)
        (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.Coefficient F ζ hζ C R P H U) := by
  constructor
  · intro x
    exact (KPContSectorSmoothFramesSupport.cuspCoefficient F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H u.val a.1 a.2 ((x,b),t)).property
  · intro l x
    have h := (KPContSectorSmoothFramesSupport.cuspCoefficient_transition F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H u.val a.1 a.2
      ((KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a).inclusion
        (Multiplicative.ofAdd l)) (x,b) t).1
    have he := KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.crossAction_inclusion
      (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a) l (x,b)
    rw [he] at h
    exact congrArg Subtype.val h

theorem frameFiber_mk (u : Smooth) (b : KPCuspCharts.Shape F) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) :
    frameFiber F ζ hζ C R P H U a u b t (QuotientAddGroup.mk x) =
      KPContActualCutoffSmoothDescent.frameValue F ζ hζ C R P H U u a ((x,b),t) := by
  let v := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).realization.symm
    ⟨_, frame_horizontal F ζ hζ C R P H U a u b t⟩
  have he (y : KPCuspCharts.Horizontal F) : v.val (QuotientAddGroup.mk y) =
      KPContActualCutoffSmoothDescent.frameValue F ζ hζ C R P H U u a ((y,b),t) := by
    have hh := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).realization_formula v y
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  unfold frameFiber
  rw [← he]
  have hq : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk x : K)) : K) =
      QuotientAddGroup.mk x := Quotient.out_eq _
  rw [hq]
  exact he x

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ)

theorem commutator_frameFiber_eq_constant (s : ℂ) (hs : s ∈ Ω)
    (b : KPCuspCharts.Shape F) (t : ℝ) (ht : B.τ < t) (q : K) :
    frameFiber F ζ hζ C R P H U a (source.descent.commutator s) b t q =
      KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
        (χ a).toFun s t *
        (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s (f s) t b).val 0 := by
  rw [frameFiber, source.descent.commutator_frame s hs a ((Quotient.out q,b),t) ht]
  congr 1

theorem commutator_fiber_pairing_eq_zero (s : ℂ) (hs : s ∈ Ω)
    (u : Smooth) (hu : AllCuspMeanZero F ζ hζ C R P H U u)
    (b : KPCuspCharts.Shape F) (t : ℝ) (ht : B.τ < t) :
    (∫ q, frameFiber F ζ hζ C R P H U a (source.descent.commutator s) b t q *
      star (frameFiber F ζ hζ C R P H U a u b t q) ∂μ) = 0 := by
  simp_rw [commutator_frameFiber_eq_constant F ζ hζ C R P H U a ι B Ω f χ source s hs b t ht]
  rw [integral_const_mul]
  have hav : (∫ q, star (frameFiber F ζ hζ C R P H U a u b t q) ∂μ) = 0 := by
    simpa only [map_zero, starRingEnd_apply] using
      (integral_conj (f := frameFiber F ζ hζ C R P H U a u b t)).trans
        (congrArg (starRingEnd ℂ) (hu a b t))
  rw [hav, mul_zero]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.IncomingFiberOrthogonality

end
