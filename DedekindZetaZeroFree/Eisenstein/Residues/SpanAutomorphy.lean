module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslation
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatFiniteSum

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem finite_level_exists :
    Nonempty (KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) := by
  rw [KPGlobalTorusFunctionData.FiniteLevel,
    KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
  obtain ⟨J, _⟩ := ActualFiniteFactor.productLevels_cofinal F ζ hζ Set.univ Filter.univ_mem
  exact ⟨⟨(ActualFiniteFactor.productLevel F ζ hζ J).subgroup,
    (ActualFiniteFactor.productLevel F ζ hζ J).compact⟩⟩

 theorem smooth_zero (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Smooth F ζ hζ (0 : Functions F ζ hζ) := by
  refine ⟨continuous_const, ?_, U, ?_⟩
  · intro g
    exact contDiffOn_const
  · intro g u hu
    rfl

 theorem smooth_add (v w : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) (hw : Smooth F ζ hζ w) :
    Smooth F ζ hζ (v + w) := by
  obtain ⟨hvc, hvd, U, hU⟩ := hv
  obtain ⟨hwc, hwd, V, hV⟩ := hw
  let W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
      U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  refine ⟨hvc.add hwc, fun g => (hvd g).add (hwd g), W, ?_⟩
  intro g u hu
  obtain ⟨a, ha, rfl⟩ := hu
  have haU : (a : G F ζ hζ) ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    ⟨a, ha.1, rfl⟩
  have haV : (a : G F ζ hζ) ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V :=
    ⟨a, ha.2, rfl⟩
  exact congrArg₂ (· + ·) (hU g a haU) (hV g a haV)

 theorem smooth_smul (c : ℂ) (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) : Smooth F ζ hζ (c • v) := by
  obtain ⟨hvc, hvd, U, hU⟩ := hv
  refine ⟨continuous_const.mul hvc, ?_, U, ?_⟩
  · intro g
    exact contDiffOn_const.mul (hvd g)
  · intro g u hu
    change c * v (g * u) = c * v g
    rw [hU g u hu]

end DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy

end
