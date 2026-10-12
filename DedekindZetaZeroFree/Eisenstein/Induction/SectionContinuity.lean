module

public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteLocalSectionContinuity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceContinuity
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 theorem principal_continuous (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    Continuous (fun g : KPCplxCharacterHaar.ComplexGL2 => f g) := by
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f).mp f.property).2.continuousOn
  have hm : Continuous (fun g : KPCplxCharacterHaar.ComplexGL2 =>
      (g : Matrix (Fin 2) (Fin 2) ℂ)) := Units.continuous_val
  have hd : ∀ g : KPCplxCharacterHaar.ComplexGL2, (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    intro g
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  have hc := hf.comp_continuous hm hd
  convert hc using 1
  funext g
  dsimp only [Function.comp_def, KPCplxPrincipalSeriesCharts.matrixFunction]
  rw [dif_pos (hd g)]
  exact congrArg (fun g : KPCplxCharacterHaar.ComplexGL2 => f g) (Units.ext rfl)

 theorem arch_continuous (w : InfinitePlace F) : Continuous (LocalCovariance.arch F ζ hζ w) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have hc : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) := continuous_induced_dom
  have hm : Continuous (LocalCovariance.complexMatrix F ζ hζ w) := by
    have hg : Continuous (fun g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) => g.g) :=
      continuous_fst.comp hc
    have he := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).continuous
    apply Units.continuous_iff.mpr
    constructor
    · have hv : Continuous (fun g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) =>
          (g.g : Matrix (Fin 2) (Fin 2) w.Completion)) := Units.continuous_val.comp hg
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact he.comp ((continuous_apply j).comp ((continuous_apply i).comp hv))
    · have hv : Continuous (fun g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) =>
          g.g.inv) := Units.continuous_coe_inv.comp hg
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact he.comp ((continuous_apply j).comp ((continuous_apply i).comp hv))
  have hphase : Continuous (fun g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) =>
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ)) :=
    (continuous_of_discreteTopology : Continuous (fun ε : rootsOfUnity 3 F =>
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ ε : ℂ))).comp (continuous_snd.comp hc)
  exact hphase.mul ((principal_continuous _ (KPCplxPrincipalSeriesCharts.sphericalSection _)).comp hm)

 theorem archProduct_continuous : Continuous (RawSource.archProduct F ζ hζ) := by
  unfold RawSource.archProduct
  apply continuous_finset_prod
  intro w _
  exact (arch_continuous F ζ hζ w).comp (RestrictedProduct.continuous_eval _)

 theorem scalar_continuous : Continuous (RawSource.scalarValue F ζ hζ P C) := by
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  change Continuous (fun g : RestrictedCover F ζ hζ =>
    RawSource.scalarValue F ζ hζ P C (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)))
  simp_rw [FiniteSourceTopology.scalar_raw_factor]
  exact (archProduct_continuous F ζ hζ).mul
    ((FiniteSourceTopology.finite_scalar_continuous F ζ hζ P C).comp
      (FiniteSourceTopology.finiteQuotient_continuous F ζ hζ))

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceContinuity

end
