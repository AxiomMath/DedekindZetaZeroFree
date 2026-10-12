module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.ScalarReflattening
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LieDerivatives.UpperRootFlows

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem upperLieDerivative_induced (w : InfinitePlace F) (b : Bool) (s : ℂ)
    (f : MomentSources.Functions R) (hf : Induced F R.A.zeta12 R.A.primitive_zeta12 s f) :
    Induced F R.A.zeta12 R.A.primitive_zeta12 s (MomentSources.upperLieDerivative R w b f) := by
  refine ⟨upperLieDerivative_smooth R w b f hf.1, ?_⟩
  intro r x g
  change deriv (fun t => f (((r.val.val * KPGlobalTorusFunctionData.N F R.A.zeta12
    R.A.primitive_zeta12 x) * g) * upperCurve R w b t)) 0 = _
  have he : (fun t => f (((r.val.val * KPGlobalTorusFunctionData.N F R.A.zeta12
      R.A.primitive_zeta12 x) * g) * upperCurve R w b t)) =
      (fun t => KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 r.val : NNReal) : ℝ)) (1/2+s) *
        (KPGlobalCenterRationalCharacter.lambdaR F R.A.zeta12 R.A.primitive_zeta12 r : ℂ) *
        f (g * upperCurve R w b t)) := by
    funext t
    rw [mul_assoc (r.val.val * _) g _, hf.2]
  rw [he]
  exact (deriv_const_mul _ (upperCurve_hasDeriv R w b f hf.1 g).differentiableAt)

def upperAlpha (w : InfinitePlace F) (b : Bool) (g : MomentSources.Group R) : ℝ :=
  deriv (fun t => KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
    (g * upperCurve R w b t)) 0

theorem upperAlpha_hasDeriv (w : InfinitePlace F) (b : Bool) (g : MomentSources.Group R) :
    HasDerivAt (fun t => KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
      (g * upperCurve R w b t)) (upperAlpha R w b g) 0 := by
  have hb : archBase F ∈ archDomain F := by intro v; simp [archBase]
  have hd := ((alpha_right_chart_smooth F R.A.zeta12 R.A.primitive_zeta12 g).contDiffAt
    ((KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).mem_nhds hb)).differentiableAt (by simp)
  have ht := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (upperTransport_hasDeriv w b (archBase F)) (upperTransport_zero w b (archBase F)).symm
  have he : (fun t => KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
      (g * upperCurve R w b t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
        (g * archChart F R.A.zeta12 R.A.primitive_zeta12 (upperCoordinates w b t))) :=
    Filter.Eventually.of_forall (fun t => by dsimp only; rw [upperCoordinates_chart])
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (show HasDerivAt (upperCoordinates w b)
      (upperField w b (archBase F)) 0 from by
      convert upperTransport_hasDeriv w b (archBase F) using 1
      funext t v i
      fin_cases i <;> simp [upperTransport, chartProduct, upperCoordinates, archBase])
    (upperCoordinates_zero w b).symm
  have hh := hc.congr_of_eventuallyEq he
  change HasDerivAt _ (deriv _ 0) 0
  rw [hh.deriv]
  exact hh

theorem upperLieDerivative_scalarWeight (w : InfinitePlace F) (b : Bool) (s : ℂ)
    (f : MomentSources.Functions R) (hf : Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (g : MomentSources.Group R) :
    MomentSources.upperLieDerivative R w b
      (scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s f) g =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12 g : ℂ)) *
        (MomentSources.upperLieDerivative R w b f g + s * (upperAlpha R w b g : ℂ) * f g) := by
  have ha := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (upperAlpha_hasDeriv R w b g)
  have h := ((ha.const_mul s).cexp).mul (upperCurve_hasDeriv R w b f hf g)
  have hh := h.deriv
  dsimp only [Function.comp_def, Pi.mul_apply, Complex.ofRealCLM_apply] at hh
  change deriv (fun t => Complex.exp
    (s * (KPContFlatSourceRecipe.alpha F R.A.zeta12 R.A.primitive_zeta12
      (g * upperCurve R w b t) : ℂ)) * f (g * upperCurve R w b t)) 0 = _
  calc
    _ = _ := hh
    _ = _ := by rw [upperCurve_zero, mul_one]; ring

 theorem induced_add (s : ℂ) (f h : MomentSources.Functions R)
    (hf : Induced F R.A.zeta12 R.A.primitive_zeta12 s f)
    (hh : Induced F R.A.zeta12 R.A.primitive_zeta12 s h) :
    Induced F R.A.zeta12 R.A.primitive_zeta12 s (f+h) := by
  refine ⟨smooth_add _ _ _ _ _ hf.1 hh.1, ?_⟩
  intro r x g
  simp only [Pi.add_apply, hf.2, hh.2, mul_add]

 theorem induced_smul (s c : ℂ) (f : MomentSources.Functions R)
    (hf : Induced F R.A.zeta12 R.A.primitive_zeta12 s f) :
    Induced F R.A.zeta12 R.A.primitive_zeta12 s (c • f) := by
  refine ⟨smooth_smul _ _ _ c _ hf.1, ?_⟩
  intro r x g
  simp only [Pi.smul_apply, smul_eq_mul, hf.2]
  ring

theorem scalarWeight_induced (s t : ℂ) (f : MomentSources.Functions R)
    (hf : Induced F R.A.zeta12 R.A.primitive_zeta12 t f) :
    Induced F R.A.zeta12 R.A.primitive_zeta12 (s+t)
      (scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s f) := by
  refine ⟨scalarWeight_smooth _ _ _ s f hf.1, ?_⟩
  intro r x g
  change Complex.exp _ * f _ = _
  dsimp only [KPContFlatSourceRecipe.alpha]
  rw [KPContFlatFullProductIwasawa.alpha_borel_mul, hf.2]
  unfold scalarWeight KPGlobalExceptionalParameter.realLogPower
  push_cast
  simp only [add_mul, mul_add, Complex.exp_add]
  ring

def upperDisplacement (w : InfinitePlace F) (b : Bool) (f : MomentSources.Functions R) : MomentSources.Functions R :=
  scalarWeight F R.A.zeta12 R.A.primitive_zeta12 (-1)
    (MomentSources.upperLieDerivative R w b (scalarWeight F R.A.zeta12 R.A.primitive_zeta12 1 f)) +
      (-1 : ℂ) • MomentSources.upperLieDerivative R w b f

theorem upperDisplacement_value (w : InfinitePlace F) (b : Bool)
    (f : MomentSources.Functions R) (hf : Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (g : MomentSources.Group R) : upperDisplacement R w b f g = (upperAlpha R w b g : ℂ) * f g := by
  simp only [upperDisplacement, Pi.add_apply, Pi.smul_apply, smul_eq_mul, scalarWeight]
  rw [upperLieDerivative_scalarWeight R w b 1 f hf g]
  simp only [one_mul, ← mul_assoc, ← Complex.exp_add, neg_one_mul, neg_add_cancel,
    Complex.exp_zero, one_mul]
  ring

theorem upperDisplacement_induced (w : InfinitePlace F) (b : Bool)
    (f : MomentSources.Functions R) (hf : Induced F R.A.zeta12 R.A.primitive_zeta12 0 f) :
    Induced F R.A.zeta12 R.A.primitive_zeta12 0 (upperDisplacement R w b f) := by
  have h1 := upperLieDerivative_induced R w b (1+0) _ (scalarWeight_induced R 1 0 f hf)
  have h0 := scalarWeight_induced R (-1) (1+0) _ h1
  norm_num at h0
  exact induced_add R 0 _ _ h0
    (induced_smul R 0 (-1) _ (upperLieDerivative_induced R w b 0 f hf))

open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming kfinite_add → kfinite_add
private theorem kfinite_smul (K : Subgroup (MomentSources.Group R)) (c : ℂ)
    (f : MomentSources.Functions R) (hf : KFinite F R.A.zeta12 R.A.primitive_zeta12 K f) :
    KFinite F R.A.zeta12 R.A.primitive_zeta12 K (c • f) := by
  obtain ⟨T,hT,hfT,hstable⟩ := hf
  exact ⟨T,hT,T.smul_mem c hfT,hstable⟩

theorem upperDisplacement_kFinite (w : InfinitePlace F) (b : Bool)
    (f : MomentSources.Functions R) (hf : Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hk : KFinite F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K f) :
    KFinite F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K (upperDisplacement R w b f) := by
  exact kfinite_add _ _ _ _ _ _
    (scalarWeight_kFinite _ _ _ (-1) _ (upperLieDerivative_kFinite R _ w b _
      (scalarWeight_smooth _ _ _ 1 f hf) (scalarWeight_kFinite _ _ _ 1 f hk)))
    (kfinite_smul R _ (-1) _ (upperLieDerivative_kFinite R _ w b f hf hk))

theorem upper_flat_affine (w : InfinitePlace F) (b : Bool)
    (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
    (hflat : ∀ s g, f.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f.val 0) g) :
    ∃ v u : Flat F R.A.zeta12 R.A.primitive_zeta12
        (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K,
      (v.val 0 = MomentSources.upperLieDerivative R w b (f.val 0)) ∧
      (∀ s g, v.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (v.val 0) g) ∧
      (∀ s g, u.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (u.val 0) g) ∧
      ∀ s g, MomentSources.upperLieDerivative R w b (f.val s) g = v.val s g + s * u.val s g := by
  have hf := (f.property.1 0)
  obtain ⟨v,hv⟩ := scalar_reflatten F R.A.zeta12 R.A.primitive_zeta12 _
    (upperLieDerivative_induced R w b 0 _ hf)
    (upperLieDerivative_kFinite R _ w b _ hf.1 f.property.2.2)
  obtain ⟨u,hu⟩ := scalar_reflatten F R.A.zeta12 R.A.primitive_zeta12 _
    (upperDisplacement_induced R w b _ hf)
    (upperDisplacement_kFinite R w b _ hf.1 f.property.2.2)
  have hv0 : v.val 0 = MomentSources.upperLieDerivative R w b (f.val 0) := by
    ext g; simp [hv, scalarWeight]
  have hu0 : u.val 0 = upperDisplacement R w b (f.val 0) := by
    ext g; simp [hu, scalarWeight]
  refine ⟨v,u,hv0,(by simpa only [hv0] using hv),(by simpa only [hu0] using hu),?_⟩
  intro s g
  rw [show f.val s = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f.val 0) from funext (hflat s)]
  rw [upperLieDerivative_scalarWeight R w b s _ hf.1 g, hv, hu]
  simp only [scalarWeight, upperDisplacement_value R w b _ hf.1]
  ring

end DedekindZetaZeroFree.RootDerivatives

end
