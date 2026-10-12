module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LieDerivatives.MatrixFlows
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.ProjectedFlatExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction SharedSource KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.RootDerivatives renaming induced_add → induced_add
open _root_.DedekindZetaZeroFree.RootDerivatives renaming induced_smul → induced_smul
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta → theta
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_zero → theta_zero
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_smooth → theta_smooth
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_add → kfinite_add
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_smul → kfinite_smul
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem actualRight_smooth (b : Fin (groupDimension F)) (f : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) : Smooth F ζ hζ (actualRight F ζ hζ b f) := by
  simpa only [actualRightWord] using actualRightWord_smooth f hf [b]

theorem actualRight_induced (b : Fin (groupDimension F)) (s : ℂ)
    (f : Functions F ζ hζ) (hf : Induced F ζ hζ s f) :
    Induced F ζ hζ s (actualRight F ζ hζ b f) := by
  refine ⟨actualRight_smooth F ζ hζ b f hf.1, ?_⟩
  intro r x g
  simp_rw [actualRight_nativeCurve]
  have he : (fun t => f (((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) *
      nativeCurve F ζ hζ b t)) = fun t =>
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1/2+s) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * f (g * nativeCurve F ζ hζ b t) := by
    funext t
    rw [mul_assoc, hf.2]
  rw [he]
  exact deriv_const_mul _ (nativeCurve_hasDeriv F ζ hζ b f hf.1 g).differentiableAt

def nativeAlpha (b : Fin (groupDimension F)) (g : G F ζ hζ) : ℝ :=
  deriv (fun t => KPContFlatSourceRecipe.alpha F ζ hζ (g * nativeCurve F ζ hζ b t)) 0

theorem nativeAlpha_hasDeriv (b : Fin (groupDimension F)) (g : G F ζ hζ) :
    HasDerivAt (fun t => KPContFlatSourceRecipe.alpha F ζ hζ (g * nativeCurve F ζ hζ b t))
      (nativeAlpha F ζ hζ b g) 0 := by
  have hb : archBase F ∈ archDomain F := by intro w; simp [archBase]
  have hd := ((alpha_right_chart_smooth F ζ hζ g).contDiffAt
    ((KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).mem_nhds hb)).differentiableAt (by simp)
  have ht : HasDerivAt (theta F (nativeBasis F b)) (nativeDirection F b) 0 :=
    (theta_smooth F _).differentiableAt (by simp) |>.hasDerivAt
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (theta_zero F _).symm
  have he : (fun t => KPContFlatSourceRecipe.alpha F ζ hζ (g * archChart F ζ hζ (theta F (nativeBasis F b) t)))
      =ᶠ[𝓝 (0 : ℝ)] (fun t => KPContFlatSourceRecipe.alpha F ζ hζ (g * nativeCurve F ζ hζ b t)) := by
    filter_upwards [nativeCurve_chart F ζ hζ b] with t ht
    rw [ht]
  have h := hh.congr_of_eventuallyEq he.symm
  change HasDerivAt _ (deriv _ 0) 0
  rw [h.deriv]
  exact h

theorem actualRight_scalarWeight (b : Fin (groupDimension F)) (s : ℂ)
    (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f) (g : G F ζ hζ) :
    actualRight F ζ hζ b (scalarWeight F ζ hζ s f) g =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) *
        (actualRight F ζ hζ b f g + s * (nativeAlpha F ζ hζ b g : ℂ) * f g) := by
  have ha := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (nativeAlpha_hasDeriv F ζ hζ b g)
  have h := ((ha.const_mul s).cexp).mul (nativeCurve_hasDeriv F ζ hζ b f hf g)
  rw [actualRight_nativeCurve]
  change deriv (fun t => Complex.exp
    (s * (KPContFlatSourceRecipe.alpha F ζ hζ (g * nativeCurve F ζ hζ b t) : ℂ)) *
      f (g * nativeCurve F ζ hζ b t)) 0 = _
  have hh := h.deriv
  dsimp only [Function.comp_def, Pi.mul_apply, Complex.ofRealCLM_apply, Pi.mul_def] at hh
  rw [hh]
  rw [nativeCurve_zero, mul_one]
  ring

def nativeDisplacement (b : Fin (groupDimension F)) (f : Functions F ζ hζ) : Functions F ζ hζ :=
  scalarWeight F ζ hζ (-1) (actualRight F ζ hζ b (scalarWeight F ζ hζ 1 f)) +
    (-1 : ℂ) • actualRight F ζ hζ b f

theorem nativeDisplacement_value (b : Fin (groupDimension F))
    (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f) (g : G F ζ hζ) :
    nativeDisplacement F ζ hζ b f g = (nativeAlpha F ζ hζ b g : ℂ) * f g := by
  simp only [nativeDisplacement, Pi.add_apply, Pi.smul_apply, smul_eq_mul, scalarWeight]
  rw [actualRight_scalarWeight F ζ hζ b 1 f hf g]
  simp only [one_mul, ← mul_assoc, ← Complex.exp_add, neg_one_mul, neg_add_cancel,
    Complex.exp_zero, one_mul]
  ring

open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta → theta
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_zero → theta_zero
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming theta_smooth → theta_smooth

private theorem generic_weight_induced (s t : ℂ) (f : Functions F ζ hζ)
    (hf : Induced F ζ hζ t f) : Induced F ζ hζ (s+t) (scalarWeight F ζ hζ s f) := by
  refine ⟨scalarWeight_smooth F ζ hζ s f hf.1, ?_⟩
  intro r x g
  change Complex.exp _ * f _ = _
  dsimp only [KPContFlatSourceRecipe.alpha]
  rw [KPContFlatFullProductIwasawa.alpha_borel_mul, hf.2]
  unfold scalarWeight KPGlobalExceptionalParameter.realLogPower
  push_cast
  simp only [add_mul, mul_add, Complex.exp_add]
  ring

private theorem generic_induced_add (s : ℂ) (f h : Functions F ζ hζ)
    (hf : Induced F ζ hζ s f) (hh : Induced F ζ hζ s h) : Induced F ζ hζ s (f+h) := by
  refine ⟨(nativeSmoothSpace F ζ hζ).add_mem hf.1 hh.1, ?_⟩
  intro r x g
  simp only [Pi.add_apply, hf.2, hh.2, mul_add]

private theorem generic_induced_smul (s c : ℂ) (f : Functions F ζ hζ)
    (hf : Induced F ζ hζ s f) : Induced F ζ hζ s (c • f) := by
  refine ⟨(nativeSmoothSpace F ζ hζ).smul_mem c hf.1, ?_⟩
  intro r x g
  simp only [Pi.smul_apply, smul_eq_mul, hf.2]
  ring

theorem native_flat_affine (b : Fin (groupDimension F))
    (f : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
    (hflat : ∀ s g, f.val s g = scalarWeight F ζ hζ s (f.val 0) g) :
    ∃ v u : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K,
      v.val 0 = actualRight F ζ hζ b (f.val 0) ∧
      (∀ s g, v.val s g = scalarWeight F ζ hζ s (v.val 0) g) ∧
      (∀ s g, u.val s g = scalarWeight F ζ hζ s (u.val 0) g) ∧
      ∀ s g, actualRight F ζ hζ b (f.val s) g = v.val s g + s * u.val s g := by
  have hf := f.property.1 0
  obtain ⟨v,hv⟩ := scalar_reflatten F ζ hζ _ (actualRight_induced F ζ hζ b 0 _ hf)
    (actualRight_kFinite F ζ hζ _ b _ hf.1 f.property.2.2)
  have h1 := actualRight_induced F ζ hζ b (1+0) _ (generic_weight_induced F ζ hζ 1 0 (f.val 0) hf)
  have h0 := generic_weight_induced F ζ hζ (-1) (1+0) _ h1
  norm_num at h0
  have hD : Induced F ζ hζ 0 (nativeDisplacement F ζ hζ b (f.val 0)) :=
    generic_induced_add F ζ hζ 0 _ _ h0
      (generic_induced_smul F ζ hζ 0 (-1) _ (actualRight_induced F ζ hζ b 0 _ hf))
  have hk : KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K
      (nativeDisplacement F ζ hζ b (f.val 0)) :=
    kfinite_add F ζ hζ _ _ _
      (scalarWeight_kFinite F ζ hζ (-1) _ (actualRight_kFinite F ζ hζ _ b _
        (scalarWeight_smooth F ζ hζ 1 _ hf.1) (scalarWeight_kFinite F ζ hζ 1 _ f.property.2.2)))
      (kfinite_smul F ζ hζ _ _ (actualRight_kFinite F ζ hζ _ b _ hf.1 f.property.2.2) (-1))
  obtain ⟨u,hu⟩ := scalar_reflatten F ζ hζ _ hD hk
  have hv0 : v.val 0 = actualRight F ζ hζ b (f.val 0) := by ext g; simp [hv, scalarWeight]
  have hu0 : u.val 0 = nativeDisplacement F ζ hζ b (f.val 0) := by ext g; simp [hu, scalarWeight]
  refine ⟨v,u,hv0, ?_, ?_, ?_⟩
  · intro s g; rw [hv,hv0]
  · intro s g; rw [hu,hu0]
  · intro s g
    have he : f.val s = scalarWeight F ζ hζ s (f.val 0) := funext (hflat s)
    rw [he,actualRight_scalarWeight F ζ hζ b s _ hf.1 g,hv,hu]
    simp only [scalarWeight,nativeDisplacement_value F ζ hζ b _ hf.1]
    ring

end DedekindZetaZeroFree.RootDerivatives

end
