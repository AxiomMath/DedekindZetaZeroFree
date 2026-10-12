module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ImageRepresentations
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Cubic.ExceptionalLengthTwo
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalIntertwinerImageIdentifications

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField Valued MonoidAlgebra
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.RankoneSteps.JacquetWeightSteps

set_option maxHeartbeats 1000000

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

 def jacquetFactorRawInducing :
    KPExceptionalRaw.RawFiniteInducingData F ζ hζ q where
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

private theorem jacquet_minus_length_two :
    Module.length (MonoidAlgebra ℂ (actualTorus F ζ hζ q))
      (KPLocalJacquetImage.jacquetRepresentation (V := sectionSpace S.borel P .minus 0)
        S.borel (IMinus S.borel P)).asModule = 2 := by
  letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
  have hs := KPJacquetExceptionalFactorSeparation.exceptional_factors_simple S.borel P
  letI : (KPJacquetExceptionalFactorSeparation.factorPlus S.borel P).IsIrreducible := hs.2.1
  letI : (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P).IsIrreducible := hs.2.2
  obtain ⟨i, p, hi, hp, he⟩ :=
    KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps.independent_minus_jacquet_short_exact
      F ζ hζ q (jacquetFactorRawInducing F ζ hζ q S) P
  exact KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps.length_two_of_short_exact
    (KPLocalJacquetImage.jacquetRepresentation S.borel (IMinus S.borel P))
    (KPJacquetExceptionalFactorSeparation.factorPlus S.borel P)
    (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P) i p hi hp he

private theorem simple_of_length_two {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (h : Module.length R M = 2) (N : Submodule R M)
    [Nontrivial N] (hN : N ≠ ⊤) : IsSimpleModule R N := by
  have hf : IsFiniteLength R M := Module.length_ne_top_iff.mp (by rw [h]; norm_num)
  obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hf
  letI := hn
  letI := ha
  apply Module.length_eq_one_iff.mp
  have hl := Submodule.length_lt hN
  rw [h] at hl
  have hp := Module.length_pos (R := R) (M := N)
  exact le_antisymm (by simpa using hl) (ENat.one_le_iff_ne_zero.mpr hp.ne')

private theorem range_irreducible {G V W : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap ρ)
    (hf : f ≠ 0) (hg : g ≠ 0) (hc : g.toLinearMap.comp f.toLinearMap = 0)
    (hl : Module.length ℂ[G] σ.asModule = 2) : f.range.toRepresentation.IsIrreducible := by
  have hf' : f.toLinearMap ≠ 0 := fun he => hf (Representation.IntertwiningMap.ext he)
  haveI : Nontrivial f.range.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr (by
    change f.toLinearMap.range ≠ ⊥
    exact fun he => hf' (LinearMap.range_eq_bot.mp he))
  have hp : f.range ≠ ⊤ := by
    intro he
    apply hg
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    have hw : w ∈ f.range := by rw [he]; trivial
    obtain ⟨v, rfl⟩ := hw
    exact LinearMap.congr_fun hc v
  let i : f.range.toRepresentation.IntertwiningMap σ :=
    ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i
  have hj : Function.Injective j := Subtype.val_injective
  have hN : j.range ≠ ⊤ := by
    intro he
    apply hp
    apply top_unique
    intro v _
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp he v
    exact hx ▸ x.property
  letI : Nontrivial f.range.toRepresentation.asModule :=
    inferInstanceAs (Nontrivial f.range.toSubmodule)
  letI : Nontrivial j.range := (LinearEquiv.ofInjective j hj).symm.toEquiv.nontrivial
  have hs := simple_of_length_two hl j.range hN
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  apply Module.length_eq_one_iff.mp
  rw [(LinearEquiv.ofInjective j hj).length_eq]
  exact Module.length_eq_one_iff.mpr hs

theorem actual_forward_image_jacquet_factor :
    Nonempty ((KPLocalJacquetImage.jacquetRepresentation S.borel
      (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ)).Equiv
        (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P)) := by
  letI : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
  letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
  have hA : actualCanonicalForwardMap F ζ hζ q S P μ hμ ≠ 0 :=
    (actual_zero_maps_nonzero F ζ hζ q S P μ hμ).1
  have hB : actualCanonicalReverseMap F ζ hζ q S P μ hμ ≠ 0 :=
    (actual_zero_maps_nonzero F ζ hζ q S P μ hμ).2
  have hBA : (actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ).toLinearMap = 0 :=
    (actual_zero_opposite_compositions F ζ hζ q S P μ hμ).2
  let fJ := KPLocalJacquetImage.jacquetMap
    (V := sectionSpace S.borel P .plus 0) (W := sectionSpace S.borel P .minus 0)
    S.borel (ρ := IPlus S.borel P) (σ := IMinus S.borel P)
    (actualCanonicalForwardMap F ζ hζ q S P μ hμ)
  let gJ := KPLocalJacquetImage.jacquetMap
    (V := sectionSpace S.borel P .minus 0) (W := sectionSpace S.borel P .plus 0)
    S.borel (ρ := IMinus S.borel P) (σ := IPlus S.borel P)
    (actualCanonicalReverseMap F ζ hζ q S P μ hμ)
  have hfJ : fJ ≠ 0 := by
    intro hz
    apply jacquetEvaluation_comp_ne_zero S.borel P .minus
      (IPlus S.borel P) (actualCanonicalForwardMap F ζ hζ q S P μ hμ) hA
    show (principalSeriesJacquetEvaluation S.borel P .minus).comp fJ = 0
    rw [hz]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp
  have hgJ : gJ ≠ 0 := by
    intro hz
    apply jacquetEvaluation_comp_ne_zero S.borel P .plus
      (IMinus S.borel P) (actualCanonicalReverseMap F ζ hζ q S P μ hμ) hB
    show (principalSeriesJacquetEvaluation S.borel P .plus).comp gJ = 0
    rw [hz]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    simp
  have hcJ : gJ.toLinearMap.comp fJ.toLinearMap = 0 := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro v
    change Representation.Coinvariants.mk
      ((IPlus S.borel P).comp (KPLocalJacquetImage.root S.borel))
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ)
        ((actualCanonicalForwardMap F ζ hζ q S P μ hμ) v)) = 0
    have he := LinearMap.congr_fun hBA v
    change (actualCanonicalReverseMap F ζ hζ q S P μ hμ)
      ((actualCanonicalForwardMap F ζ hζ q S P μ hμ) v) = 0 at he
    rw [he, map_zero]
  haveI hfJirr : fJ.range.toRepresentation.IsIrreducible :=
    range_irreducible fJ gJ hfJ hgJ hcJ (jacquet_minus_length_two F ζ hζ q S P)
  haveI hfac : (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P).IsIrreducible :=
    (KPJacquetExceptionalFactorSeparation.exceptional_factors_simple S.borel P).2.2
  let e := jacquetRangeEvaluation S.borel P .minus
    (IPlus S.borel P) (actualCanonicalForwardMap F ζ hζ q S P μ hμ)
  have hsurj : Function.Surjective e :=
    jacquetRangeEvaluation_surjective S.borel P .minus
      (IPlus S.borel P) (actualCanonicalForwardMap F ζ hζ q S P μ hμ) hA
  haveI hnt : Nontrivial (KPLocalStoneVonNeumann.InducedModule P) :=
    (KPJacquetExceptionalFactorSeparation.exceptional_factors_simple S.borel P).1
  have hne : e ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : KPLocalStoneVonNeumann.InducedModule P)
    obtain ⟨x, hx⟩ := hsurj v
    rw [hz] at hx
    exact hv (by simpa using hx.symm)
  have hinj : Function.Injective e :=
    (Representation.IsIrreducible.injective_or_eq_zero e).resolve_right hne
  have htarget : Nonempty ((KPLocalJacquetImage.jacquetMap
      (V := sectionSpace S.borel P .plus 0) (W := sectionSpace S.borel P .minus 0)
      S.borel (ρ := IPlus S.borel P) (σ := IMinus S.borel P)
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ)).range.toRepresentation.Equiv
        (KPJacquetExceptionalFactorSeparation.factorMinus S.borel P)) :=
    ⟨e.ofBijective ⟨hinj, hsurj⟩⟩
  obtain ⟨e0⟩ := KPExceptionalRaw.FiniteSource.RankoneSteps.jacquet_image_equiv
    (V := sectionSpace S.borel P .plus 0) (W := sectionSpace S.borel P .minus 0) S.borel
    (ρ := IPlus S.borel P) (σ := IMinus S.borel P)
    (actualCanonicalForwardMap F ζ hζ q S P μ hμ)
    (principalSeries_smooth S.borel P .minus 0)
  exact ⟨e0.trans htarget.some⟩

end DedekindZetaZeroFree.KPRankOneShellRepair

end
