module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.CoordinateMeasurability
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.FullFrameCoarea

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass.ShellTestFrames
open KPMsActualAngularSource KPCompactStabilizerHaarSources
open KPActualComponentHaarSources
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeDomainProjects → nativeDomainProjects
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFrameInvariant → nativeFrameInvariant
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming actualFrame_spec → actualFrame_spec
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ComponentFiber renaming spherical_fiber_formula → spherical_fiber_formula
open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport

def point
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (j : NativeCusp F ζ hζ R P S V) (p : KPCuspCharts.Cross F) (t : ℝ)
    (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    G F ζ hζ :=
  m F ζ hζ (e.symm
    ((((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) •
      KPCuspCharts.toArch F (p,t),z.1),z.2)

theorem finite_frame
    (j : NativeCusp F ζ hζ R P S V) (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hb : b ∈ B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
      (S.atlasLevel (cofinalLevel F ζ hζ V)) (nativeAtlas F ζ hζ R P S V) j.1) :
    ∃ (ε : rootsOfUnity 3 F)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
      b.val = ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
  obtain ⟨ε,u,rfl⟩ := hb
  have hu : u.val.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V) := by
    rw [S.level_matching (cofinalLevel F ζ hζ V)]
    exact ⟨u.val,u.property,rfl⟩
  refine ⟨ε,⟨u.val.val,hu⟩,?_⟩
  change KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε *
    ((nativeAtlas F ζ hζ R P S V).representative j.1).val * u.val.val = _
  rw [Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) _]

theorem coordinate_on_point
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (ht : KPMsFixedHaarDisintegration.logHeight (F := F)
      (Y / (cuspOffset F ζ hζ R P S V j).val) < t)
    (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hz : z.2 ∈ B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
      (S.atlasLevel (cofinalLevel F ζ hζ V)) (nativeAtlas F ζ hζ R P S V) j.1) :
    fullCoordinate F ζ hζ R P S V j Y
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (point S V e j p t z)) =
      KPMsActualAngularDescentSource.framedFullAngular F ζ hζ (nativeDatum F ζ hζ)
        (nativeDisintegration F ζ hζ R P S V).radial
        (KPMsActualCuspSource.rationalLift F ζ hζ (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))
        (point S V e j p t z) := by
  obtain ⟨ε,u,hu⟩ := finite_frame S V j z.2 hz
  have ha : KPMsFixedHaarDisintegration.archBasepoint F
      (e.symm ((((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) •
        KPCuspCharts.toArch F (p,t),z.1)) =
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F (p,t) := by
    rw [← heBase,e.apply_symm_apply]
  have hg : point S V e j p t z ∈
      nativeFullDomain F ζ hζ R P S V j
        (Y / (cuspOffset F ζ hζ R P S V j).val) := by
    refine ⟨_,p,t,ε,u,ht,ha,?_⟩
    change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ _ * z.2.val = _
    rw [hu]
    group
  have hx := nativeDomainProjects F ζ hζ R P S V j _ _ hg
  have hf := actualFrame_spec F ζ hζ R P S V j Y _ hx
  exact nativeFrameInvariant F ζ hζ R P S V j _ (hY j) _ _ hf.2 hg hf.1

open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeDomainImage → nativeDomainImage
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeDomainOpen → nativeDomainOpen
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming fullCoordinate_continuousOn_end → fullCoordinate_continuousOn_end

theorem modulus_on_point
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (KPArch.Space (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (ht : KPMsFixedHaarDisintegration.logHeight (F := F)
      (Y / (cuspOffset F ζ hζ R P S V j).val) < t)
    (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hz : z.2 ∈ B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
      (S.atlasLevel (cofinalLevel F ζ hζ V)) (nativeAtlas F ζ hζ R P S V) j.1) :
    (nativeDisintegration F ζ hζ R P S V).modulus
      (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V))
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (point S V e j p t z))) =
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  let d : ℝ := 2 * (KPCuspLogShape.dimension F : ℝ)
  have hd : 0 < d := mul_pos (by norm_num) (Nat.cast_pos.mpr
    (KPCuspLogShape.dimension_pos F (nativeFamily F ζ hζ R P).totallyComplex))
  let Z := Y / (cuspOffset F ζ hζ R P S V j).val
  have hr : Z < Real.exp (d * t) := by
    have hh : Real.log Z < d * t := by
      simpa only [mul_comm] using (div_lt_iff₀ hd).mp ht
    exact (Real.log_lt_iff_lt_exp (hY j).1).mp hh
  let r : Set.Ioi Z := ⟨Real.exp (d*t),hr⟩
  let D := nativeDisintegration F ζ hζ R P S V
  let q : KPCuspCharts.Cross F := (p.1,p.2 - KPMsFixedHaarDisintegration.sectionShape F
    (nativeFamily F ζ hζ R P).totallyComplex D.radial.slot
      ⟨r.val,lt_trans (hY j).1 r.property⟩)
  have hlog : KPMsFixedHaarDisintegration.logHeight (F := F) r.val = t := by
    change Real.log (Real.exp (d*t)) / d = t
    rw [Real.log_exp,mul_div_cancel_left₀ _ hd.ne']
  have hchart := D.chart_formula Z (hY j) j q r
  simp only [q, hlog, sub_add_cancel] at hchart
  have hproj := spherical_fiber_formula F ζ hζ (toRawTransport F ζ hζ P)
    (S.atlasLevel (cofinalLevel F ζ hζ V))
    ((nativeAtlas F ζ hζ R P S V).representative j.1) z.2 hz
    (e.symm ((((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2) •
      KPCuspCharts.toArch F (p,t),z.1))
  have heBase' : ∀ a, (e a).1 = KPMsFixedHaar.archBasepoint F a := heBase
  rw [← heBase',e.apply_symm_apply] at hproj
  change D.modulus _ = r.val
  change P.projection _ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
    (point S V e j p t z)) = _ at hproj
  rw [hproj,← hchart]
  exact D.chart_modulus Z (hY j) _ r

theorem end_test_measurable
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y)
    (φ : FullOmega F ζ hζ (nativeDatum F ζ hζ) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable ((KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j
        (Y / (cuspOffset F ζ hζ R P S V j).val)).indicator
      (fun x => φ (fullCoordinate F ζ hζ R P S V j Y x))) := by
  let E := KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
    (S.atlasLevel (cofinalLevel F ζ hζ V)) j (Y / (cuspOffset F ζ hζ R P S V j).val)
  have hE : IsOpen E := by
    dsimp only [E]
    rw [← nativeDomainImage F ζ hζ R P S V j Y]
    letI : IsTopologicalGroup (G F ζ hζ) :=
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    exact isOpenMap_quotient_mk'_mul _ (nativeDomainOpen F ζ hζ R P S V j _)
  letI : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  have hc := fullCoordinate_continuousOn_end F ζ hζ R P S V j Y hY
  change Measurable (E.indicator (fun x => φ (fullCoordinate F ζ hζ R P S V j Y x)))
  apply measurable_of_restrict_of_restrict_compl hE.measurableSet
  · have hh : Measurable (fun x : E => φ (fullCoordinate F ζ hζ R P S V j Y x)) :=
      hφ.comp hc.domRestrict.measurable
    convert hh using 1
    funext x
    exact Set.indicator_of_mem x.property _
  · have hh : Measurable (fun _ : (Eᶜ : Set (KPSmoothLocalQuotientCharts.X F ζ hζ)) =>
        (0 : ℝ≥0∞)) := measurable_const
    convert hh using 1
    funext x
    exact Set.indicator_of_notMem x.property _

end DedekindZetaZeroFree.KPMsNativeOffsetMass.ShellTestFrames

end
