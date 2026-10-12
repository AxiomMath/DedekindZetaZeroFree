module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.OffsetTransport
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.FullFrameCoarea
public import DedekindZetaZeroFree.Adeles.Quotients.CuspMeasures.RadialCoareaDensity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
open KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (S : NativeRecipe F ζ hζ R P)

namespace ShellCoefficientProof

theorem framedNormalization_radial_mul
    (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ g : G F ζ hζ) (r : KPMsFixedHaarDisintegration.Radius) :
    framedNormalization F ζ hζ D B σ
      (σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * (σ⁻¹ * g)) =
      framedNormalization F ζ hζ D B σ g := by
  let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hd : (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) = r.val := by
    change (((KPGlobalTorusFunctionData.ideleAbs F
      (KPGlobalTorusFunctionData.p F ζ hζ t) : ℝ≥0) : ℝ)) = r.val
    rw [B.lift_ratio, B.ell_norm]
  have hr : framedRadius F ζ hζ D σ
      (σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * (σ⁻¹ * g)) =
      ⟨r.val * (framedRadius F ζ hζ D σ g).val,
        mul_pos r.property (framedRadius F ζ hζ D σ g).property⟩ := by
    apply Subtype.ext
    change (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (σ⁻¹ * (σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * (σ⁻¹ * g))) : ℝ≥0) : ℝ)) = _
    have he : σ⁻¹ * (σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * (σ⁻¹ * g)) =
        t.val * (σ⁻¹ * g) := by
      change σ⁻¹ * (σ * t.val * (σ⁻¹ * g)) = t.val * (σ⁻¹ * g)
      group
    rw [he]
    have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul
      F ζ hζ D t 0 (σ⁻¹ * g)
    rw [hn, mul_one] at h
    rw [h]
    simp only [Units.val_mul, NNReal.coe_mul, hd]
    rfl
  unfold framedNormalization
  rw [hr, B.section_mul]
  group

theorem framedFullAngular_radial_upper_transition
    (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ g h : G F ζ hζ) (r : KPMsFixedHaarDisintegration.Radius)
    (n : KPGlobalTorusFunctionData.Adeles F)
    (he : σ⁻¹ * h = KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r *
      KPGlobalTorusFunctionData.N F ζ hζ n * (σ⁻¹ * g)) :
    KPMsActualAngularDescentSource.framedFullAngular F ζ hζ D B σ h =
      KPMsActualAngularDescentSource.framedFullAngular F ζ hζ D B σ g := by
  let g' := σ * KPGlobalTorusFunctionData.N F ζ hζ n * (σ⁻¹ * g)
  have hh : h = σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * (σ⁻¹ * g') := by
    dsimp only [g']
    calc
      h = σ * (σ⁻¹ * h) := by group
      _ = _ := by rw [he]; group
  rw [hh]
  have hr : KPMsActualAngularDescentSource.framedFullAngular F ζ hζ D B σ
      (σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r * (σ⁻¹ * g')) =
      KPMsActualAngularDescentSource.framedFullAngular F ζ hζ D B σ g' := by
    unfold KPMsActualAngularDescentSource.framedFullAngular
      KPMsActualAngularDescentSource.framedNormOne
    congr 2
    exact framedNormalization_radial_mul F ζ hζ D B σ g' r
  rw [hr]
  apply KPMsActualAngularDescentSource.framedFullAngular_upper_transition
    F ζ hζ D B σ g g' 1 n
  dsimp only [g']
  simp only [map_one, Subgroup.coe_one, one_mul]
  group

end ShellCoefficientProof

namespace FullTestProof
open KPMsActualAngularDescentSource KPMsActualCuspSource
open KPCompactStabilizerHaarSources KPActualComponentHaarSources
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace
variable {F ζ hζ}
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
local instance (D : KPMsActualAngularSource.Iwasawa F ζ hζ) :
    BorelSpace (KPMsActualAngularSource.FullOmega F ζ hζ D) := ⟨rfl⟩
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingLift → tilingLift
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming rationalArch → rationalArch
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization renaming full_fiber_test_covariance → full_fiber_test_covariance

open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure renaming actual_rational_Iwasawa_fiber → actual_rational_Iwasawa_fiber
theorem full_fiber_parabolic_invariant
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (V : KPMsFixedHaar.Level F ζ hζ)
    (At : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (i : Fin At.componentCount)
    (a : Fin (At.cuspAtlas i).cuspCount)
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ b, (e b).1 = KPMsFixedHaarDisintegration.archBasepoint F b)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure] [SFinite ν]
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (B₀ : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (φ : KPMsActualAngularSource.FullOmega F ζ hζ D → ℝ≥0∞) (hφ : Measurable φ)
    (η : KPCuspArithmetic.conjugatedStabilizer F (Gi F ζ hζ hF V At i)
      ((At.cuspAtlas i).cusp a) ((At.cuspAtlas i).representative a))
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    (∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (framedFullAngular F ζ hζ D B₀
          (rationalLift F ζ hζ ((At.cuspAtlas i).representative a))
          (m F ζ hζ (e.symm (((At.cuspAtlas i).representative a) •
            KPCuspCharts.toArch F (((At.cuspAtlas i).geometry a).crossAction η p,t),z.1),z.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
        (ν.restrict (B F ζ hζ hF V At i))) =
    ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (framedFullAngular F ζ hζ D B₀
          (rationalLift F ζ hζ ((At.cuspAtlas i).representative a))
          (m F ζ hζ (e.symm (((At.cuspAtlas i).representative a) •
            KPCuspCharts.toArch F (p,t),z.1),z.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
        (ν.restrict (B F ζ hζ hF V At i)) := by
  let σ := (At.cuspAtlas i).representative a
  let Γ := Gi F ζ hζ hF V At i
  let γ : Γ := KPCuspGenuineMonodromy.cuspInclusion F Γ
    ((At.cuspAtlas i).cusp a) σ η
  have hγ : (γ : KPCuspArithmetic.PGL2 F) = σ*η*σ⁻¹ :=
    KPCuspGenuineMonodromy.cuspInclusion_formula F Γ _ σ η
  let Ψ : KPMsRationalCompactCrossPairing.G F ζ hζ → ℝ≥0∞ := fun g =>
    φ (framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ) g)
  let : BorelSpace (KPMsActualAngularSource.FullOmega F ζ hζ D) := ⟨rfl⟩
  have hΨ : Measurable Ψ := hφ.comp
    (framedFullAngular_continuous F ζ hζ D B₀ (rationalLift F ζ hζ σ)).measurable
  have hconj : KPCuspArithmetic.IsUpperTriangular F (σ⁻¹*γ.val*σ) := by
    rw [hγ]
    have h : σ⁻¹ * (σ * η.val * σ⁻¹) * σ = η.val := by group
    rw [h]
    obtain ⟨M,hM,hupper⟩ := ((At.cuspAtlas i).parabolic a).upper η η.property
    exact ⟨M,hM,hupper⟩
  have hinv (g) : Ψ (tilingLift F ζ hζ γ.val*g) = Ψ g := by
    dsimp [Ψ]
    apply congrArg φ
    obtain ⟨y,n,hn⟩ := KPMsActualAngularDescentSource.rational_upper_literal_factorization
      F ζ hζ (σ⁻¹ * γ.val * σ) hconj
    have ht : tilingLift F ζ hζ γ.val = rationalLift F ζ hζ γ.val := by
      change KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (rationalEquiv F γ.val) = _
      induction γ.val using Matrix.ProjGenLinGroup.induction_on with
      | mk M => rw [KPMsActualCuspSource.rationalLift_mk]; rfl
    apply framedFullAngular_upper_transition F ζ hζ D B₀
      (rationalLift F ζ hζ σ) g (tilingLift F ζ hζ γ.val * g) y n
    rw [← hn, KPMsActualAngularTransitionSource.rationalLift_mul,
      KPMsActualAngularTransitionSource.rationalLift_mul,
      KPMsActualAngularTransitionSource.rationalLift_inv, ht]
    group
  have hact : γ.val • (σ • KPCuspCharts.toArch F (p,t)) =
      σ • KPCuspCharts.toArch F (((At.cuspAtlas i).geometry a).crossAction η p,t) := by
    rw [hγ]
    simp only [mul_smul,inv_smul_smul]
    congr 1
    change KPCuspSiegel.action F (η : KPCuspArithmetic.PGL2 F)
      (KPCuspCharts.toArch F (p,t)) = KPCuspCharts.toArch F
        ((((At.cuspAtlas i).geometry a).crossAction η p),t)
    obtain ⟨M,hM,hupper⟩ := ((At.cuspAtlas i).parabolic a).upper η η.property
    rw [((At.cuspAtlas i).geometry a).actual_action η M hM hupper,
      ((At.cuspAtlas i).geometry a).crossAction_formula η M hM hupper]
    rfl
  have hh := full_fiber_test_covariance hF V At i e heBase heFiber ν Ψ hΨ γ hinv
    (σ • KPCuspCharts.toArch F (p,t))
  have hact' : γ • (σ • KPCuspCharts.toArch F (p,t)) =
      σ • KPCuspCharts.toArch F (((At.cuspAtlas i).geometry a).crossAction η p,t) := hact
  rw [hact'] at hh
  exact hh

theorem full_fundamental_shape_shift
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (V : KPMsFixedHaar.Level F ζ hζ)
    (At : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (i : Fin At.componentCount) (a : Fin (At.cuspAtlas i).cuspCount)
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ b, (e b).1 = KPMsFixedHaarDisintegration.archBasepoint F b)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure] [SFinite ν]
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (B₀ : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (φ : KPMsActualAngularSource.FullOmega F ζ hζ D → ℝ≥0∞) (hφ : Measurable φ)
    (b : KPCuspCharts.Shape F) (t : ℝ) :
    (∫⁻ p in ((At.cuspAtlas i).geometry a).fundamentalDomain,
      ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
        φ (framedFullAngular F ζ hζ D B₀
            (rationalLift F ζ hζ ((At.cuspAtlas i).representative a))
            (m F ζ hζ (e.symm (((At.cuspAtlas i).representative a) •
              KPCuspCharts.toArch F ((p.1,p.2+b),t),z.1),z.2)))
        ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
          (ν.restrict (B F ζ hζ hF V At i))
      ∂volume.prod ((At.cuspAtlas i).geometry a).shapeMeasure) =
    ∫⁻ p in ((At.cuspAtlas i).geometry a).fundamentalDomain,
      ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
        φ (framedFullAngular F ζ hζ D B₀
            (rationalLift F ζ hζ ((At.cuspAtlas i).representative a))
            (m F ζ hζ (e.symm (((At.cuspAtlas i).representative a) •
              KPCuspCharts.toArch F (p,t),z.1),z.2)))
        ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
          (ν.restrict (B F ζ hζ hF V At i))
      ∂volume.prod ((At.cuspAtlas i).geometry a).shapeMeasure := by
  let f : KPCuspCharts.Cross F → ℝ≥0∞ := fun p =>
    ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ ((At.cuspAtlas i).representative a))
          (m F ζ hζ (e.symm (((At.cuspAtlas i).representative a) • KPCuspCharts.toArch F (p,t),z.1),z.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod (ν.restrict (B F ζ hζ hF V At i))
  change (∫⁻ p in ((At.cuspAtlas i).geometry a).fundamentalDomain, f (p.1,p.2+b)
    ∂volume.prod ((At.cuspAtlas i).geometry a).shapeMeasure) = _
  apply KPMsFixedHaar.RadialIntegrationSteps.shape_shift_fundamental_lintegral At ⟨i,a⟩ b f
  intro η p
  exact full_fiber_parabolic_invariant hF V At i a e heBase heFiber ν D B₀ φ hφ η p t

theorem full_compact_covariance
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [SFinite ν]
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (B₀ : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ : KPCuspArithmetic.PGL2 F)
    (φ : KPMsActualAngularSource.FullOmega F ζ hζ D → ℝ≥0∞) (hφ : Measurable φ)
    (x : X (KPCuspLogShape.dimension F)) :
    (∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ)
          (m F ζ hζ (e.symm (σ • x,z.1),z.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod ν) =
    ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      φ (framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ)
          (m F ζ hζ (rationalArch F ζ hζ σ * e.symm (x,z.1),z.2)))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod ν := by
  let d := KPCuspLogShape.dimension F
  let : BorelSpace (K d) := stabilizerBorelSpace d
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let : BorelSpace (KPMsActualAngularSource.FullOmega F ζ hζ D) := ⟨rfl⟩
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  obtain ⟨κ,hκ,htrans,hκMP⟩ := actual_rational_Iwasawa_fiber (ζ := ζ) (hζ := hζ) e heBase heFiber σ
  let f : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ → ℝ≥0∞ := fun z =>
    φ (framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ)
        (m F ζ hζ (e.symm (σ • x,z.1),z.2)))
  have hfm : Measurable f := by
    apply hφ.comp
    apply (framedFullAngular_continuous F ζ hζ D B₀ (rationalLift F ζ hζ σ)).measurable.comp
    exact (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
      (e.symm.continuous.comp (continuous_const.prodMk continuous_fst))).mul
        (continuous_subtype_val.comp continuous_snd)).measurable
  have hh := ((hκMP x).prod (MeasurePreserving.id ν)).lintegral_comp hfm
  change (∫⁻ z : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
    f (κ x*z.1,z.2) ∂(stabilizerHaar d).prod ν) =
    ∫⁻ z, f z ∂(stabilizerHaar d).prod ν at hh
  have htest : ∀ z : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      f (κ x*z.1,z.2) = φ (framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ)
          (m F ζ hζ (rationalArch F ζ hζ σ * e.symm (x,z.1),z.2))) := by
    intro z
    dsimp only [f]
    rw [htrans]
  simp only [htest] at hh
  exact hh.symm

open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization renaming source_frame_factorization → source_frame_factorization
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization renaming radial_inverse_section_source → radial_inverse_section_source
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization renaming radialShapeCorrection → radialShapeCorrection
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization renaming radialSlotLog → radialSlotLog
open _root_.DedekindZetaZeroFree.KPContFlatArchProjectionNorm renaming adeleOfArch → adeleOfArch
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming placeEquiv → placeEquiv

theorem full_angular_shape_normalization
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (D : KPMsActualAngularSource.Iwasawa F ζ hζ)
    (B₀ : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ : KPCuspArithmetic.PGL2 F)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (k : K (KPCuspLogShape.dimension F)) (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ)
      (m F ζ hζ (rationalArch F ζ hζ σ * e.symm (KPCuspCharts.toArch F (p,t),k),b)) =
    framedFullAngular F ζ hζ D B₀ (rationalLift F ζ hζ σ)
      (m F ζ hζ (rationalArch F ζ hζ σ * e.symm (KPCuspCharts.toArch F
        ((0,p.2 + radialShapeCorrection (ζ := ζ) (hζ := hζ) B₀.slot t),0),k),b)) := by
  apply ShellCoefficientProof.framedFullAngular_radial_upper_transition F ζ hζ D B₀
    (rationalLift F ζ hζ σ) _ _
    ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩
    (adeleOfArch F ζ hζ (fun v =>
      (Real.exp (-radialSlotLog B₀.slot t v) : ℂ) * p.1 (placeEquiv F ζ hζ v)))
  have hn := radial_inverse_section_source (ζ := ζ) (hζ := hζ) e heFiber B₀.slot p t k
  have hf₁ := source_frame_factorization (F := F) (ζ := ζ) (hζ := hζ) σ
    (e.symm (KPCuspCharts.toArch F (p,t),k)) b
  have hf₂ := source_frame_factorization (F := F) (ζ := ζ) (hζ := hζ) σ
    (e.symm (KPCuspCharts.toArch F
      ((0,p.2 + radialShapeCorrection (ζ := ζ) (hζ := hζ) B₀.slot t),0),k)) b
  simp only [KPMsClearedTruncationL2.rationalLift] at hf₁ hf₂
  rw [hf₁,hf₂]
  calc
    _ = KPMsFixedHaarDisintegration.radialSection F ζ hζ B₀.slot
        ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩ *
      ((KPMsFixedHaarDisintegration.radialSection F ζ hζ B₀.slot
        ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩)⁻¹ *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (e.symm (KPCuspCharts.toArch F (p,t),k))) *
      ((rationalLift F ζ hζ σ)⁻¹ *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (rationalArch F ζ hζ σ) * b.val) := by group
    _ = _ := by rw [hn]; group

theorem full_angular_slices_stationary
    (S : NativeRecipe F ζ hζ R P) (V : KPMsActualAngularSource.Level F ζ hζ)
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure] [SFinite ν]
    (j : NativeCusp F ζ hζ R P S V)
    (φ : FullOmega F ζ hζ (nativeDatum F ζ hζ) → ℝ≥0∞) (hφ : Measurable φ) (t : ℝ) :
    let At := nativeAtlas F ζ hζ R P S V
    let B₀ := (nativeDisintegration F ζ hζ R P S V).radial
    let σ := (At.cuspAtlas j.1).representative j.2
    let μ := (stabilizerHaar (KPCuspLogShape.dimension F)).prod
      (ν.restrict (B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
        (S.atlasLevel (cofinalLevel F ζ hζ V)) At j.1))
    let f := fun p t z => φ (framedFullAngular F ζ hζ (nativeDatum F ζ hζ) B₀
      (rationalLift F ζ hζ σ)
      (m F ζ hζ (e.symm (σ • KPCuspCharts.toArch F (p,t),z.1),z.2)))
    (∫⁻ p in ((At.cuspAtlas j.1).geometry j.2).fundamentalDomain, ∫⁻ z, f p t z ∂μ
      ∂volume.prod ((At.cuspAtlas j.1).geometry j.2).shapeMeasure) =
    ∫⁻ p in ((At.cuspAtlas j.1).geometry j.2).fundamentalDomain, ∫⁻ z, f p 0 z ∂μ
      ∂volume.prod ((At.cuspAtlas j.1).geometry j.2).shapeMeasure := by
  dsimp only
  let At := nativeAtlas F ζ hζ R P S V
  let σ := (At.cuspAtlas j.1).representative j.2
  let B₀ := (nativeDisintegration F ζ hζ R P S V).radial
  let μ := (stabilizerHaar (KPCuspLogShape.dimension F)).prod
    (ν.restrict (B F ζ hζ (nativeFamily F ζ hζ R P).totallyComplex
      (S.atlasLevel (cofinalLevel F ζ hζ V)) At j.1))
  let q := radialShapeCorrection (ζ := ζ) (hζ := hζ) B₀.slot t
  let f := fun (p : KPCuspCharts.Cross F) (t : ℝ)
      (z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ) =>
    φ (framedFullAngular F ζ hζ (nativeDatum F ζ hζ) B₀ (rationalLift F ζ hζ σ)
      (m F ζ hζ (e.symm (σ • KPCuspCharts.toArch F (p,t),z.1),z.2)))
  have hcov (p : KPCuspCharts.Cross F) (u : ℝ) :
      (∫⁻ z, f p u z ∂μ) = ∫⁻ z, φ (framedFullAngular F ζ hζ (nativeDatum F ζ hζ) B₀
        (rationalLift F ζ hζ σ) (m F ζ hζ
          (rationalArch F ζ hζ σ * e.symm (KPCuspCharts.toArch F (p,u),z.1),z.2))) ∂μ :=
    full_compact_covariance e heBase heFiber _ (nativeDatum F ζ hζ) B₀ σ φ hφ _
  have hn (p : KPCuspCharts.Cross F) :
      (∫⁻ z, f p t z ∂μ) = ∫⁻ z, f (p.1,p.2+q) 0 z ∂μ := by
    rw [hcov,hcov]
    apply lintegral_congr
    intro z
    congr 1
    rw [full_angular_shape_normalization e heFiber (nativeDatum F ζ hζ) B₀ σ p t z.1 z.2,
      full_angular_shape_normalization e heFiber (nativeDatum F ζ hζ) B₀ σ (p.1,p.2+q) 0 z.1 z.2]
    have hzero : radialShapeCorrection (ζ := ζ) (hζ := hζ) B₀.slot 0 = 0 := by
      apply Subtype.ext
      funext i
      simp [radialShapeCorrection,radialSlotLog]
    rw [hzero,add_zero]
  change (∫⁻ p in ((At.cuspAtlas j.1).geometry j.2).fundamentalDomain,
    ∫⁻ z, f p t z ∂μ ∂volume.prod ((At.cuspAtlas j.1).geometry j.2).shapeMeasure) = _
  simp_rw [hn]
  exact full_fundamental_shape_shift (nativeFamily F ζ hζ R P).totallyComplex
    (S.atlasLevel (cofinalLevel F ζ hζ V)) At j.1 j.2 e heBase heFiber ν
    (nativeDatum F ζ hζ) B₀ φ hφ q 0

end FullTestProof

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
