module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.VanishingOppositeCompositions
public import DedekindZetaZeroFree.Algebra.CompositionLengthBySubmoduleOrder
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompositionLengthOfIrreducibleExtensions
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalMinusConservativity
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalMinusBruhatExactSequence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField Valued
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

 def lengthRawInducing : KPExceptionalRaw.RawFiniteInducingData F ζ hζ q where
  D := S.D
  groupD := S.groupD
  finiteD := S.finiteD
  cubeClassEquiv := S.cubeClassEquiv
  heisenberg := S.heisenberg
  borel := S.borel
  borel_eq := S.borel_eq
  torus_full := S.torus_full
  coordinate_lift := S.coordinate_lift
  cube_class := S.cube_class
  center_exact := S.center_exact
  cube_actual := S.cube_actual
  central := S.central
  central_actual := S.central_actual
  central_character := S.central_character
  center_parameterization := S.center_parameterization
  prescribed_center := S.prescribed_center
  split_scalars := S.split_scalars
  polarization := S.polarization
  iwasawa := S.iwasawa
  openCell := S.openCell
  openCell_ordinary := S.openCell_ordinary

theorem actual_principal_series_length_le_two : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
    exact
      Module.length (MonoidAlgebra ℂ (ActualCover F ζ hζ q))
        (IPlus S.borel P).asModule ≤ 2 ∧
      Module.length (MonoidAlgebra ℂ (ActualCover F ζ hζ q))
        (IMinus S.borel P).asModule ≤ 2 := by
  let R := lengthRawInducing F ζ hζ q S
  letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
  letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
  have hs := KPJacquetExceptionalFactorSeparation.exceptional_factors_simple S.borel P
  letI := hs.2.1
  letI := hs.2.2
  constructor
  · have hle := KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.length_le_of_strictMono_submodules
      (KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.jacquetSubmoduleImage S.borel (IPlus S.borel P))
      (KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.independent_plus_jacquet_strictMono F ζ hζ q R P)
    obtain ⟨i, p, hi, hp, he⟩ :=
      KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.independent_plus_jacquet_short_exact F ζ hζ q R P
    have hlen := KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.length_two_of_short_exact
      (KPLocalJacquetImage.jacquetRepresentation S.borel (IPlus S.borel P))
      (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P)
      (KPJacquetExceptionalFactorSeparation.factorPlus S.borel P) i p hi hp he
    exact hle.trans hlen.le
  · have hle := KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.length_le_of_strictMono_submodules
      (KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.jacquetSubmoduleImage S.borel (IMinus S.borel P))
      (KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps.independent_minus_jacquet_strictMono F ζ hζ q R P)
    obtain ⟨i, p, hi, hp, he⟩ :=
      KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps.independent_minus_jacquet_short_exact F ζ hζ q R P
    have hlen := KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.length_two_of_short_exact
      (KPLocalJacquetImage.jacquetRepresentation S.borel (IMinus S.borel P))
      (KPJacquetExceptionalFactorSeparation.factorPlus S.borel P)
      (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P) i p hi hp he
    exact hle.trans hlen.le

private theorem length_ge_two_of_opposite_maps
    {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A : ρ.IntertwiningMap σ) (B : σ.IntertwiningMap ρ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hcomp : A.toLinearMap.comp B.toLinearMap = 0) :
    2 ≤ Module.length (MonoidAlgebra ℂ G) ρ.asModule := by
  have hbot : A.ker.asSubmodule ≠ ⊥ := by
    intro H
    apply hB
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    have hw : B w ∈ A.ker.asSubmodule := LinearMap.congr_fun hcomp w
    rw [H] at hw
    exact hw
  have htop : A.ker.asSubmodule ≠ ⊤ := by
    intro H
    apply hA
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ A.ker.asSubmodule := by rw [H]; trivial
    exact hv
  let p : LTSeries (Submodule (MonoidAlgebra ℂ G) ρ.asModule) :=
    RelSeries.fromListIsChain [⊥, A.ker.asSubmodule, ⊤] (by simp)
      (List.IsChain.cons_cons (bot_lt_iff_ne_bot.mpr hbot)
        (List.isChain_pair.mpr (lt_top_iff_ne_top.mpr htop)))
  have hp := Order.LTSeries.length_le_krullDim p
  rw [← Module.coe_length] at hp
  apply WithBot.coe_le_coe.mp
  simpa [p] using hp

theorem actual_principal_series_length_ge_two_of_opposite_maps
    (μ : MeasureTheory.Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (hA : actualCanonicalForwardMap F ζ hζ q S P μ hμ ≠ 0)
    (hB : actualCanonicalReverseMap F ζ hζ q S P μ hμ ≠ 0)
    (hAB : (actualCanonicalForwardMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap = 0)
    (hBA : (actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ).toLinearMap = 0) : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
    exact
      2 ≤ Module.length (MonoidAlgebra ℂ (ActualCover F ζ hζ q))
        (IPlus S.borel P).asModule ∧
      2 ≤ Module.length (MonoidAlgebra ℂ (ActualCover F ζ hζ q))
        (IMinus S.borel P).asModule := by
  letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
  letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
  exact ⟨length_ge_two_of_opposite_maps _ _ _ _ hA hB hAB,
    length_ge_two_of_opposite_maps _ _ _ _ hB hA hBA⟩

theorem actual_principal_series_length_two : by
    letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
    letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
    exact
      Module.length (MonoidAlgebra ℂ (ActualCover F ζ hζ q))
        (IPlus S.borel P).asModule = 2 ∧
      Module.length (MonoidAlgebra ℂ (ActualCover F ζ hζ q))
        (IMinus S.borel P).asModule = 2 := by
  let O : TopologicalSpace.PositiveCompacts (LocalField F q) :=
    ⟨⟨((ValuativeRel.valuation (LocalField F q)).integer : Set (LocalField F q)),
      IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1⟩,
      by
        rw [(ValuativeRel.valuation (LocalField F q)).isOpen_integer.interior_eq]
        exact ⟨0, by simp⟩⟩
  let μ := MeasureTheory.Measure.addHaarMeasure O
  have hμ : μ ((ValuativeRel.valuation (LocalField F q)).integer : Set (LocalField F q)) = 1 :=
    MeasureTheory.Measure.addHaarMeasure_self
  have hnonzero := actual_zero_maps_nonzero F ζ hζ q S P μ hμ
  have hcomp := actual_zero_opposite_compositions F ζ hζ q S P μ hμ
  have hge := actual_principal_series_length_ge_two_of_opposite_maps F ζ hζ q S P μ hμ
    hnonzero.1 hnonzero.2 hcomp.1 hcomp.2
  have hle := actual_principal_series_length_le_two F ζ hζ q S P
  exact ⟨le_antisymm hle.1 hge.1, le_antisymm hle.2 hge.2⟩

end DedekindZetaZeroFree.KPRankOneShellRepair

end
