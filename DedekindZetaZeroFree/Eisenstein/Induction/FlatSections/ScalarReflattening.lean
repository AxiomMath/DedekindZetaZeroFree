module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LieDerivatives.ChartCompactFiniteness
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.ProjectedSources

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem alpha_right_chart_smooth (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => KPContFlatSourceRecipe.alpha F ζ hζ
      (g * archChart F ζ hζ x)) (archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨O,q,hO,hxO,hq,hqD,he⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x hx
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => KPContFlatFullProductIwasawa.alpha F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * (g * archChart F ζ hζ x)))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
    (KPContFlatLogNormSmooth.alpha_groupArchChart_mul_contDiffOn F ζ hζ
      (g * archChart F ζ hζ x)).of_le (by simp)
  refine ⟨O,hO,hxO,?_⟩
  exact ((hs.comp hq hqD).congr (fun y hy => congrArg
    (KPContFlatSourceRecipe.alpha F ζ hζ) (he y hy))).mono Set.inter_subset_right

 theorem alpha_uniform_level :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, ∀ g u,
      u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      KPContFlatSourceRecipe.alpha F ζ hζ (g*u) = KPContFlatSourceRecipe.alpha F ζ hζ g := by
  obtain ⟨U,hU⟩ :=
    KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level
      (KPContFlatSourceRecipe.D F ζ hζ)
  refine ⟨U,?_⟩
  intro g u hu
  exact congrArg (fun n : NNRealˣ => Real.log (n.val : ℝ)) (hU g ⟨u,hu⟩)

 def scalarWeight (s : ℂ) (f : Functions F ζ hζ) : Functions F ζ hζ :=
   fun g => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) * f g

 theorem scalarWeight_smooth (s : ℂ) (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f) :
    Smooth F ζ hζ (scalarWeight F ζ hζ s f) := by
  obtain ⟨U,hU⟩ := hf.2.2
  obtain ⟨V,hV⟩ := alpha_uniform_level F ζ hζ
  let W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  refine ⟨?_,?_,W,?_⟩
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (KPContFlatLogNormSmooth.alpha_continuous F ζ hζ))).cexp.mul hf.1
  · intro g
    exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.contDiffOn.comp
      (alpha_right_chart_smooth F ζ hζ g) (fun _ _ => Set.mem_univ _))).cexp).mul (hf.2.1 g)
  · intro g u hu
    obtain ⟨a,ha,he⟩ := hu
    have huU : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U := ⟨a,ha.1,he⟩
    have huV : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V := ⟨a,ha.2,he⟩
    simp only [scalarWeight, hV g u huV, hU g u huU]

 theorem scalarWeight_kFinite (s : ℂ) (f : Functions F ζ hζ)
    (hf : KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K f) :
    KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K (scalarWeight F ζ hζ s f) := by
  let L : Functions F ζ hζ →ₗ[ℂ] Functions F ζ hζ := {
    toFun := scalarWeight F ζ hζ s
    map_add' := by intro f h; ext g; exact mul_add _ _ _
    map_smul' := by intro c f; ext g; change _ * (c * _) = c * (_ * _); ring }
  obtain ⟨T,hT,hfT,ht⟩ := hf
  letI := hT
  refine ⟨T.map L,inferInstance,⟨f,hfT,rfl⟩,?_⟩
  intro k v hv
  obtain ⟨u,hu,rfl⟩ := hv
  refine ⟨rightAction F ζ hζ k.val u,ht k u hu,?_⟩
  funext g
  change Complex.exp _ * u (g*k.val) = Complex.exp _ * u (g*k.val)
  dsimp only [KPContFlatSourceRecipe.alpha]
  rw [KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g k]

 theorem scalar_reflatten (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f)
    (hk : KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K f) :
    ∃ v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K,
      ∀ s g, v.val s g = scalarWeight F ζ hζ s f g := by
  refine ⟨⟨fun s => scalarWeight F ζ hζ s f,?_,?_,?_⟩,fun _ _ => rfl⟩
  · intro s
    refine ⟨scalarWeight_smooth F ζ hζ s f hf.1,?_⟩
    intro r x g
    change Complex.exp _ * f _ = _
    dsimp only [KPContFlatSourceRecipe.alpha]
    rw [KPContFlatFullProductIwasawa.alpha_borel_mul, hf.2]
    unfold scalarWeight KPGlobalExceptionalParameter.realLogPower
    push_cast
    simp only [add_mul, mul_add, Complex.exp_add, add_zero]
    ring
  · intro s t k
    have hn := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) t 0 k
    have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPAdeles F) = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    rw [hN,mul_one] at hn
    change Complex.exp _ * f _ = _ * (Complex.exp _ * f _)
    simp only [zero_mul,Complex.exp_zero,one_mul]
    unfold KPContFlatSourceRecipe.alpha KPContFlatFullProductIwasawa.alpha
    rw [hn]
    rfl
  · change KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K (scalarWeight F ζ hζ 0 f)
    have he : scalarWeight F ζ hζ 0 f = f := by ext g; simp [scalarWeight]
    rw [he]
    exact hk

end DedekindZetaZeroFree.RootDerivatives

end
