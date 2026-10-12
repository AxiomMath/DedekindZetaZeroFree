module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.ArchimedeanInsertion
public import DedekindZetaZeroFree.Adeles.Quotients.CuspCutoffs.RadialJetFormula
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.CoordinateMeasurability

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField NNReal ENNReal Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryFrame
open KPMsGreenFlux KPContFlatArchDiagonalMultiplier
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames renaming balancedArch_eq_section → balancedArch_eq_section
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.GradientCollar renaming balancedArch_basepoint → balancedArch_basepoint
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
def shapeAt (b : KPCuspCharts.Shape F) : NumberField.InfinitePlace F → ℝ := fun w => b.val ((Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}) ⟨w,KPHilbert.infinite_isComplex F ζ hζ w⟩)
theorem shapeAt_sum (b : KPCuspCharts.Shape F) : ∑ w, shapeAt (ζ := ζ) (hζ := hζ) b w = 0 := by
  let e : NumberField.InfinitePlace F ≃ Fin (KPCuspLogShape.dimension F) :=
    (Equiv.subtypeUnivEquiv (fun w => KPHilbert.infinite_isComplex F ζ hζ w)).symm.trans
      (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex})
  change ∑ w, b.val (e w) = 0
  rw [Equiv.sum_comp e]
  exact b.property
theorem heights_sum (p : KPCuspCharts.Cross F) (t : ℝ) :
    ∑ i, KPContinuation.ChamberFlatCasimir.heights F ζ hζ (KPCuspCharts.toArch F (p,t)) i =
      (Fintype.card (NumberField.InfinitePlace F) : ℝ) * t := by
  have he : KPContinuation.ChamberFlatCasimir.heights F ζ hζ (KPCuspCharts.toArch F (p,t)) =
      fun i => t + shapeAt (ζ := ζ) (hζ := hζ) p.2 i := rfl
  rw [he, Finset.sum_add_distrib, shapeAt_sum, add_zero]
  simp

theorem balanced_insertion_factor (p : KPCuspCharts.Cross F)
    (k : KPMsGreenFlux.K F) (r : ℝ) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r) =
    KPGlobalTorusFunctionData.N F ζ hζ
      (KPContinuation.ChamberFlatCasimir.horizontalAdele F ζ hζ
        (KPCuspCharts.toArch F (p,KPMsFixedHaarDisintegration.logHeight (F := F) r)), 0) *
      (aInfinity F ζ hζ (KPContinuation.ChamberFlatCasimir.heights F ζ hζ
        (KPCuspCharts.toArch F (p,KPMsFixedHaarDisintegration.logHeight (F := F) r)))).val *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun i => (k i).val) := by
  have he : KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r =
      KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p 1 r * (fun i => (k i).val) := by
    funext i
    simp only [KPMsGreenFlux.balancedArch, Pi.one_apply, OneMemClass.coe_one,
      mul_one, Pi.mul_apply]
  rw [he, balancedArch_eq_section p _ r rfl,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
    KPContinuation.ChamberFlatCasimir.iwasawa_insertion]

variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

def cuspOffset (j : Cusps A) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) :
    KPMsFixedHaarDisintegration.Radius :=
  KPMsAngularSourceRecipe.finiteOffset F ζ hζ
    (KPMsActualCuspSource.rationalLift F ζ hζ ((A.cuspAtlas j.1).representative j.2))
    ((A.representative j.1 * KPCuspGenuineMonodromy.central F ζ hζ ε * u.val).val)

def actualPoint (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) (r : ℝ) : Cover F ζ hζ :=
  (cuspRepresentative A j)⁻¹ * KPBoundedCuspFrames.actualCuspLift A j p k r *
    KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val

theorem actual_ray_norm (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) (r : ℝ) (hr : 0 < r) :
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) (actualPoint A j p k ε u r) : ℝ≥0) : ℝ) =
        (cuspOffset A j ε u).val * r := by
  let σ := (A.cuspAtlas j.1).representative j.2
  let a := KPMsActualCuspSource.archRational F σ *
    balancedArch (ζ := ζ) (hζ := hζ) p k r
  let c : KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
    A.representative j.1 * KPCuspGenuineMonodromy.central F ζ hζ ε * u.val
  have ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F
        (p,KPMsFixedHaarDisintegration.logHeight (F := F) r)) := by
    rw [KPMsActualCuspSource.archBasepoint_rational_mul, balancedArch_basepoint]
  have hn := KPMsAngularSourceRecipe.actual_frame_norm_factorization
    F ζ hζ σ a c p (KPMsFixedHaarDisintegration.logHeight (F := F) r) ha
  have hσ : KPMsActualCuspSource.rationalLift F ζ hζ σ = cuspRepresentative A j := by
    have h := KPMsActualCuspSource.rationalLift_mk F ζ hζ σ.out
    rw [show Matrix.ProjGenLinGroup.mk σ.out = σ from Quotient.out_eq _] at h
    exact h.trans (KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ _).symm
  have hp : actualPoint A j p k ε u r =
      (KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ *
        KPMsAngularSourceRecipe.frame F ζ hζ a c.val := by
    unfold actualPoint KPMsAngularSourceRecipe.frame
    rw [hσ, KPBoundedCuspFrames.actualCuspLift_arch_finite_formula]
    change (_ * (_ * _)) * _ * _ = _ * (_ * ((_ * _) * _))
    have ha' : a = (fun w => Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map w.embedding ((A.cuspAtlas j.1).representative j.2).out)) *
          balancedArch (ζ := ζ) (hζ := hζ) p k r := rfl
    have hcentral : (KPCuspGenuineMonodromy.central F ζ hζ ε).val =
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := rfl
    rw [ha', hcentral]
    group
  rw [hp]
  have hd : (2 * (KPCuspLogShape.dimension F : ℝ)) ≠ 0 := by
    have h := KPCuspLogShape.dimension_pos F hF
    positivity
  have he : Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) *
      KPMsFixedHaarDisintegration.logHeight (F := F) r) = r := by
    unfold KPMsFixedHaarDisintegration.logHeight
    rw [mul_div_cancel₀ _ hd, Real.exp_log hr]
  exact hn.trans (congrArg (fun x => (cuspOffset A j ε u).val * x) he)

end DedekindZetaZeroFree.CurrentBoundaryFrame

end
