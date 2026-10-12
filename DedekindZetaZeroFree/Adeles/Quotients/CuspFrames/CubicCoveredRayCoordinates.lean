module

public import DedekindZetaZeroFree.Metaplectic.Torus.RadialCuspFrames
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Iwasawa.FullAngularCuspCoordinates
public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CoveredLifts
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.ArchimedeanSphericalQuotients

@[expose] public section

open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar renaming compactSubgroup_eq_origin_stabilizer → compactSubgroup_eq_origin_stabilizer
open _root_.DedekindZetaZeroFree.KPContSectorArchSphericalFibers renaming mem_KInfinity_iff_stab → mem_KInfinity_iff_stab
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames renaming archBasepoint_rational_mul → archBasepoint_rational_mul
noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem balancedArch_eq_section (p : KPCuspCharts.Cross F) (t : ℝ)
    (r : ℝ) (hr : KPMsFixedHaarDisintegration.logHeight (F := F) r = t) :
    balancedArch (ζ := ζ) (hζ := hζ) p 1 r =
      KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (p,t)) := by
  funext w
  simp only [balancedArch, Pi.one_apply, OneMemClass.coe_one, mul_one, hr,
    KPContSectorArchSphericalFibers.iwasawaSection]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCplxCharacterHaar.upperUnipotent, KPCplxCharacterHaar.diagonal,
      KPContSectorArchSphericalFibers.sectionGL, KPArithmeticAction.hyperbolicGLSection,
      KPContSectorArchSphericalFibers.infinitePlaceEquiv, KPCuspCharts.toArch,
      KPArch.height, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

theorem admissibleFrame_eq_actualCuspLift
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (j : Cusps A) (x : X F ζ hζ) (g : Cover F ζ hζ)
    (hg : AdmissibleFrame A j Y x g) :
    ∃ (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ)
      (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      Y < r ∧ 0 < r ∧ g = KPBoundedCuspFrames.actualCuspLift A j p k r *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val := by
  obtain ⟨a,p,t,ε,u,ht,ha,he⟩ := hg.2
  let r := Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)
  have hd : 0 < (2 * (KPCuspLogShape.dimension F : ℝ)) := by
    have h := KPCuspLogShape.dimension_pos F hF
    positivity
  have hr : KPMsFixedHaarDisintegration.logHeight (F := F) r = t := by
    unfold KPMsFixedHaarDisintegration.logHeight r
    rw [Real.log_exp]
    have hdne : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by
      have hp := KPCuspLogShape.dimension_pos F hF
      exact_mod_cast ne_of_gt hp
    field_simp [hdne]
  have hYr : Y < r := by
    have hlog : Real.log Y < 2 * (KPCuspLogShape.dimension F : ℝ) * t := by
      simpa only [mul_comm t] using (div_lt_iff₀ hd).mp ht
    have hx := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log hY.1] at hx
  let a₀ := archRational F ((A.cuspAtlas j.1).representative j.2) *
    balancedArch (ζ := ζ) (hζ := hζ) p 1 r
  have hbase : KPMsFixedHaarDisintegration.archBasepoint F a₀ =
      KPMsFixedHaarDisintegration.archBasepoint F a := by
    dsimp only [a₀]
    rw [archBasepoint_rational_mul, balancedArch_eq_section p t r hr,
      KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
    exact ha.symm
  obtain ⟨κ,hκ⟩ := (KPContSectorArchSphericalFibers.archBasepoint_eq_iff F a₀ a).mp hbase
  let k : K F := fun w => ⟨κ.val w, by
    rw [compactSubgroup_eq_origin_stabilizer]
    have hw := (mem_KInfinity_iff_stab F κ.val).mp κ.property
    have hi := (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).left_inv w
    have hww : KPCusp.complexPlace F (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w) = w := hi
    have hkw := hw (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)
    rw [hww] at hkw
    exact hkw⟩
  have hk : balancedArch (ζ := ζ) (hζ := hζ) p k r =
      balancedArch (ζ := ζ) (hζ := hζ) p 1 r * κ.val := by
    funext w
    simp only [balancedArch, Pi.mul_apply, Pi.one_apply, OneMemClass.coe_one, mul_one]
    rfl
  refine ⟨p,k,r,ε,u,hYr,Real.exp_pos _,?_⟩
  rw [KPBoundedCuspFrames.actualCuspLift_arch_finite_formula, hk, ← mul_assoc]
  change g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (a₀ * κ.val) *
    (A.representative j.1).val * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val.val
  rw [← hκ]
  exact he

end DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames

end
