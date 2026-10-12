module

public import DedekindZetaZeroFree.Eisenstein.Residues.UpperRootPreimages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction SharedSource
open KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta → theta
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_zero → theta_zero
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_smooth → theta_smooth
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_chart → theta_chart
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word → word
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_hasDerivAt_of_chart_smooth → rightWord_hasDerivAt_of_chart_smooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming actual_eq_word → actual_eq_word
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev nativeBasis (b : Fin (groupDimension F)) : KPSmoothActualFlowData.B F :=
  KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F
    (lieEnumeration F b)

def nativeCurve (b : Fin (groupDimension F)) (t : ℝ) : G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (nativeBasis F b) t)

theorem actualRight_nativeCurve (b : Fin (groupDimension F)) (f : Functions F ζ hζ) :
    actualRight F ζ hζ b f = fun g => deriv (fun t => f (g * nativeCurve F ζ hζ b t)) 0 := by
  funext g
  unfold actualRight nativeCurve nativeBasis
  simp_rw [KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actual_frame_ray_eq_flow]

def nativeDirection (b : Fin (groupDimension F)) : ArchCoordinates F :=
  deriv (theta F (nativeBasis F b)) 0

theorem nativeCurve_chart (b : Fin (groupDimension F)) :
    (fun t => archChart F ζ hζ (theta F (nativeBasis F b) t)) =ᶠ[𝓝 (0 : ℝ)]
      nativeCurve F ζ hζ b := theta_chart F ζ hζ _

theorem actualRight_chartDerivative (b : Fin (groupDimension F)) (f : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) :
    actualRight F ζ hζ b f = chartDerivative F ζ hζ (nativeDirection F b) f := by
  funext g
  have hb : archBase F ∈ archDomain F := by intro w; simp [archBase]
  have hd := smooth_chart_differentiable F ζ hζ f hf g
  have ht : HasDerivAt (theta F (nativeBasis F b)) (nativeDirection F b) 0 :=
    (theta_smooth F _).differentiableAt (by simp) |>.hasDerivAt
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (theta_zero F _).symm
  have he : (fun t => f (g * nativeCurve F ζ hζ b t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => f (g * archChart F ζ hζ (theta F (nativeBasis F b) t))) := by
    filter_upwards [nativeCurve_chart F ζ hζ b] with t ht
    rw [ht]
  rw [actualRight_nativeCurve]
  change deriv _ 0 = _
  rw [he.deriv_eq]
  exact hh.deriv

theorem actualRight_kFinite (K : Subgroup (G F ζ hζ))
    (b : Fin (groupDimension F)) (f : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) (hk : KFinite F ζ hζ K f) :
    KFinite F ζ hζ K (actualRight F ζ hζ b f) := by
  rw [actualRight_chartDerivative F ζ hζ b f hf]
  exact chartDerivative_kFinite F ζ hζ K f hf hk _

theorem nativeCurve_zero (b : Fin (groupDimension F)) : nativeCurve F ζ hζ b 0 = 1 := by
  unfold nativeCurve
  rw [(KPSmoothActualFlowData.flow_properties F _).1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1]

theorem nativeCurve_add (b : Fin (groupDimension F)) (s t : ℝ) :
    nativeCurve F ζ hζ b (s+t) = nativeCurve F ζ hζ b s * nativeCurve F ζ hζ b t := by
  unfold nativeCurve
  rw [(KPSmoothActualFlowData.flow_properties F _).2.1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]

theorem nativeCurve_continuous (b : Fin (groupDimension F)) :
    Continuous (nativeCurve F ζ hζ b) :=
  (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
    (KPSmoothActualFlowData.flow_properties F _).2.2

theorem nativeCurve_hasDeriv (b : Fin (groupDimension F)) (f : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) (g : G F ζ hζ) :
    HasDerivAt (fun t => f (g * nativeCurve F ζ hζ b t)) (actualRight F ζ hζ b f g) 0 := by
  have hh := rightWord_hasDerivAt_of_chart_smooth F ζ hζ f hf.2.1 [] (nativeBasis F b) g
  rw [actualRight_nativeCurve]
  exact hh

theorem nativeCurve_hasDerivAt (b : Fin (groupDimension F)) (f : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) (g : G F ζ hζ) (t : ℝ) :
    HasDerivAt (fun u => f (g * nativeCurve F ζ hζ b u))
      (actualRight F ζ hζ b f (g * nativeCurve F ζ hζ b t)) t := by
  have h0 := nativeCurve_hasDeriv F ζ hζ b f hf (g * nativeCurve F ζ hζ b t)
  have h0' : HasDerivAt (fun u => f ((g * nativeCurve F ζ hζ b t) * nativeCurve F ζ hζ b u))
      (actualRight F ζ hζ b f (g * nativeCurve F ζ hζ b t)) (t-t) := by simpa using h0
  have ht : HasDerivAt (fun u : ℝ => u-t) 1 t := by simpa using (hasDerivAt_id t).sub_const t
  have hh := h0.scomp_of_eq t ht (by simp)
  have he : (fun u => f ((g * nativeCurve F ζ hζ b t) * nativeCurve F ζ hζ b (u-t))) =
      (fun u => f (g * nativeCurve F ζ hζ b u)) := by
    funext u
    rw [mul_assoc, ← nativeCurve_add, add_sub_cancel]
  simpa only [Function.comp_def, he, one_smul] using hh

end DedekindZetaZeroFree.RootDerivatives

end
