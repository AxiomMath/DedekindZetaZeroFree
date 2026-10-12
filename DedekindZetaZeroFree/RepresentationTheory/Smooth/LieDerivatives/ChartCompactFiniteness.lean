module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.UpperRootLieDerivatives
public import DedekindZetaZeroFree.Analysis.SmoothFunctions.MovingJetTaylorSeries
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AffineConjugationDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open KPGlobalResidualConstruction SharedSource
open KPLiteralRaw hiding G
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def chartDerivative (X : ArchCoordinates F) (f : Functions F ζ hζ) : Functions F ζ hζ :=
  fun g => fderiv ℝ (fun x => f (g * archChart F ζ hζ x)) (archBase F) X

theorem smooth_chart_differentiable (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f)
    (g : G F ζ hζ) :
    DifferentiableAt ℝ (fun x => f (g * archChart F ζ hζ x)) (archBase F) := by
  have hb : archBase F ∈ archDomain F := by intro w; simp [archBase]
  exact ((hf.2.1 g).contDiffAt
    ((KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).mem_nhds hb)).differentiableAt
      (by simp)

def chartDerivativeLinear (X : ArchCoordinates F) :
    nativeSmoothSpace F ζ hζ →ₗ[ℂ] Functions F ζ hζ where
  toFun f := chartDerivative F ζ hζ X f.val
  map_add' f h := by
    funext g
    change fderiv ℝ ((fun x => f.val (g * archChart F ζ hζ x)) +
      (fun x => h.val (g * archChart F ζ hζ x))) (archBase F) X = _
    rw [fderiv_add (smooth_chart_differentiable F ζ hζ _ f.property g)
      (smooth_chart_differentiable F ζ hζ _ h.property g)]
    rfl
  map_smul' c f := by
    funext g
    change fderiv ℝ (fun x => c * f.val (g * archChart F ζ hζ x)) (archBase F) X = _
    rw [fderiv_const_mul (smooth_chart_differentiable F ζ hζ _ f.property g)]
    rfl

def chartDerivativeDirection (f : Functions F ζ hζ) :
    ArchCoordinates F →ₗ[ℝ] Functions F ζ hζ where
  toFun X := chartDerivative F ζ hζ X f
  map_add' X Y := by funext g; exact (fderiv ℝ _ (archBase F)).map_add X Y
  map_smul' r X := by funext g; exact (fderiv ℝ _ (archBase F)).map_smul r X

 abbrev directionBasis := Module.finBasis ℝ (ArchCoordinates F)

theorem chartDerivative_kFinite (K : Subgroup (G F ζ hζ))
    (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f) (hk : KFinite F ζ hζ K f)
    (X : ArchCoordinates F) : KFinite F ζ hζ K (chartDerivative F ζ hζ X f) := by
  obtain ⟨S, hS, hfS, hstable⟩ := hk
  letI := hS
  let S' := S.comap (nativeSmoothSpace F ζ hζ).subtype
  have hfin : FiniteDimensional ℂ S' :=
    FiniteDimensional.of_injective
      ((nativeSmoothSpace F ζ hζ).subtype.restrict (fun _ hv => hv :
        ∀ v ∈ S', (nativeSmoothSpace F ζ hζ).subtype v ∈ S))
      (by intro v w h; apply Subtype.ext; apply Subtype.ext
          exact congrArg (fun z : S => z.val) h)
  letI := hfin
  let T : Submodule ℂ (Functions F ζ hζ) :=
    ⨆ i, S'.map (chartDerivativeLinear F ζ hζ (directionBasis F i))
  have hm (v : nativeSmoothSpace F ζ hζ) (hv : v ∈ S') (Y : ArchCoordinates F) :
      chartDerivative F ζ hζ Y v.val ∈ T := by
    have hs := congrArg (chartDerivativeDirection F ζ hζ v.val) ((directionBasis F).sum_repr Y)
    simp only [map_sum, map_smul] at hs
    change (chartDerivativeDirection F ζ hζ v.val) Y ∈ T
    rw [← hs]
    apply Submodule.sum_mem
    intro i hi
    change (↑((directionBasis F).repr Y i) : ℂ) •
      (chartDerivativeLinear F ζ hζ (directionBasis F i)) v ∈ T
    exact Submodule.smul_mem _ _ ((le_iSup (fun i => S'.map
      (chartDerivativeLinear F ζ hζ (directionBasis F i))) i) ⟨v,hv,rfl⟩)
  refine ⟨T, Submodule.finiteDimensional_iSup _, hm ⟨f,hf⟩ hfS X, ?_⟩
  intro k
  change T ≤ T.comap (rightAction F ζ hζ k.val)
  apply iSup_le
  intro i v hv
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨L, hL⟩ := KPActualReflectionData.AffineCompactConjugation.right_derivative_conjugation
    F ζ hζ k.val
  let u' : nativeSmoothSpace F ζ hζ := ⟨rightAction F ζ hζ k.val u.val,
    KPLiteralPeriod.NonzeroResidue.smooth_right_translate F ζ hζ u.val u.property k.val⟩
  have hu' : u' ∈ S' := hstable k u.val hu
  have he : rightAction F ζ hζ k.val (chartDerivative F ζ hζ (directionBasis F i) u.val) =
      chartDerivative F ζ hζ (L (directionBasis F i)) u'.val := by
    funext g
    exact hL u.val (smooth_chart_differentiable F ζ hζ _ u.property) _ g
  change rightAction F ζ hζ k.val (chartDerivative F ζ hζ (directionBasis F i) u.val) ∈ T
  rw [he]
  exact hm u' hu' _

variable {F ζ hζ}
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem upperLieDerivative_chartDerivative (w : NumberField.InfinitePlace F) (b : Bool)
    (f : MomentSources.Functions R) (hf : Smooth F R.A.zeta12 R.A.primitive_zeta12 f) :
    MomentSources.upperLieDerivative R w b f =
      chartDerivative F R.A.zeta12 R.A.primitive_zeta12
        (upperField w b (archBase F)) f := by
  funext g
  have hb : archBase F ∈ archDomain F := by intro v; simp [archBase]
  have h := upperLieDerivative_chart R w b f hf g (archBase F) hb
  simpa only [chartDerivative, KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] using h

theorem upperLieDerivative_kFinite (K : Subgroup (MomentSources.Group R))
    (w : NumberField.InfinitePlace F) (b : Bool) (f : MomentSources.Functions R)
    (hf : Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hk : KFinite F R.A.zeta12 R.A.primitive_zeta12 K f) :
    KFinite F R.A.zeta12 R.A.primitive_zeta12 K (MomentSources.upperLieDerivative R w b f) := by
  rw [upperLieDerivative_chartDerivative R w b f hf]
  exact chartDerivative_kFinite F R.A.zeta12 R.A.primitive_zeta12 K f hf hk _

end DedekindZetaZeroFree.RootDerivatives

end
