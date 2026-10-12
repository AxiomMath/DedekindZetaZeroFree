module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdditiveAdelicQuotientDomains
public import DedekindZetaZeroFree.Adeles.Lattices.AdditiveFundamentalDomain
public import DedekindZetaZeroFree.Theta.Periods.KernelPeriodRealizationAndCoinvariants

@[expose] public section

noncomputable section
open scoped NumberField Classical ENNReal
open MeasureTheory NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F]

private theorem archMeasure_eq : KPAdditiveHaar.archMeasure F =
    Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (QuotientProbability.finiteLevelInfiniteHaar F) := by
  have hcoord : (fun x : PoissonArch.Space F =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (mixedEmbedding.euclidean.toMixed F x)) = (PoissonArch.infiniteAdeleToSpace F).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    simp only [RingEquiv.apply_symm_apply]
    rw [← PoissonArch.infiniteAdeleToSpace_coordinates,
      ContinuousLinearEquiv.apply_symm_apply]
  have hm : Measurable (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
    have he := (PoissonArch.infiniteAdeleToSpace F).symm.continuous.measurable
    have he2 := (mixedEmbedding.euclidean.toMixed F).symm.continuous.measurable
    have heq : (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm =
        (PoissonArch.infiniteAdeleToSpace F).symm ∘ (mixedEmbedding.euclidean.toMixed F).symm := by
      funext x
      have hh := congrFun hcoord ((mixedEmbedding.euclidean.toMixed F).symm x)
      simpa only [ContinuousLinearEquiv.apply_symm_apply, Function.comp_apply] using hh
    rw [heq]
    exact he.comp he2
  rw [show QuotientProbability.finiteLevelInfiniteHaar F =
    Measure.map (mixedEmbedding.euclidean.toMixed F) (PoissonArch.traceMeasure F) from
    (PoissonArch.traceMeasure_map_toMixed F).symm]
  rw [Measure.map_map hm (mixedEmbedding.euclidean.toMixed F).continuous.measurable]
  change Measure.map _ _ = Measure.map _ _
  rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ∘
      (mixedEmbedding.euclidean.toMixed F) = (PoissonArch.infiniteAdeleToSpace F).symm from hcoord]

private theorem archInverse_measurable : Measurable (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  have heq : (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm =
      (PoissonArch.infiniteAdeleToSpace F).symm ∘ (mixedEmbedding.euclidean.toMixed F).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    rw [RingEquiv.apply_symm_apply, Function.comp_apply,
      ← PoissonArch.infiniteAdeleToSpace_coordinates,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [heq]
  exact (PoissonArch.infiniteAdeleToSpace F).symm.continuous.measurable.comp
    (mixedEmbedding.euclidean.toMixed F).symm.continuous.measurable

theorem adelicMeasure_eq_product : KPAdditiveHaar.adelicMeasure F =
    additiveProductHaar F (KPAdditiveHaar.finiteMeasure F) := by
  letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  letI : (QuotientProbability.finiteLevelInfiniteHaar F).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume
      (ENNReal.ofReal_pos.mpr (PoissonArch.haarScalar_pos F)).ne' ENNReal.ofReal_ne_top
  unfold KPAdditiveHaar.adelicMeasure
  rw [archMeasure_eq F]
  have hid : KPAdditiveHaar.finiteMeasure F = Measure.map id (KPAdditiveHaar.finiteMeasure F) :=
    Measure.map_id.symm
  conv_lhs => arg 2; arg 2; rw [hid]
  rw [Measure.map_prod_map]
  · have hm := (archInverse_measurable F).prodMap (measurable_id : Measurable
      (id : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F → _))
    have heq : (MeasurableSpace.prod inferInstance inferInstance :
        MeasurableSpace (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) =
        borel (AdeleRing (𝓞 F) F) := BorelSpace.measurable_eq
    have hc : @Measurable (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (AdeleRing (𝓞 F) F) (MeasurableSpace.prod inferInstance inferInstance) (borel _)
        (fun x => x) := by
      rw [heq]
      exact measurable_id
    exact Measure.map_map hc hm
  · exact archInverse_measurable F
  · exact measurable_id

private theorem fundamentalDomain_of_op {A : Type*} [AddCommGroup A] [MeasurableSpace A]
    (L : AddSubgroup A) (D : Set A) (μ : Measure A)
    (h : IsAddFundamentalDomain L.op D μ) : IsAddFundamentalDomain L D μ := by
  have hv (g : L) (x : A) : (L.equivOp g) +ᵥ x = g +ᵥ x := by
    change x + g.val = g.val + x
    exact add_comm _ _
  refine ⟨h.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [h.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    refine ⟨L.equivOp.symm g, ?_⟩
    simpa only [← hv, Equiv.apply_symm_apply] using hg
  · intro a b hab
    have hh := h.aedisjoint (show L.equivOp a ≠ L.equivOp b from
      fun he => hab (L.equivOp.injective he))
    simpa only [Function.onFun, ← Set.image_vadd, hv] using hh

theorem actual_quotientHaar_compatible : KPChamberAdditivePeriodization.CompatibleHaar F
    (KPAdditiveHaar.adelicMeasure F) (KPWildKernelUpperBound.quotientHaar F) := by
  letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  obtain ⟨D, hD, hfd⟩ := additiveProductHaar_exists_fundamentalDomain F
    (KPAdditiveHaar.finiteMeasure F)
  have hnorm : KPAdditiveHaar.finiteMeasure F (integralFiniteAdeles F : Set _) =
      ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|) :=
    (KPAdditiveHaar.finiteMeasure_integral_mass F).trans (KPAdditiveHaar.finiteMass_eq_discriminant F).1
  obtain ⟨hhaar, hprob, hmass⟩ := additiveQuotientMeasureFromDomain_haar_probability F
    (KPAdditiveHaar.finiteMeasure F) hnorm D hD hfd
  let dq := additiveQuotientMeasureFromDomain F (KPAdditiveHaar.finiteMeasure F) D
  letI : dq.IsAddHaarMeasure := hhaar
  letI : IsProbabilityMeasure dq := hprob
  have heq : dq = KPWildKernelUpperBound.quotientHaar F :=
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hup : additiveProductHaar F (KPAdditiveHaar.finiteMeasure F) =
      KPAdditiveHaar.adelicMeasure F := (adelicMeasure_eq_product F).symm
  refine ⟨D, hD, hup ▸ fundamentalDomain_of_op _ _ _ hfd, ?_, ?_⟩
  · have h := hmass
    unfold additiveQuotientMeasureFromDomain at h
    rw [Measure.map_apply (f := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
      QuotientAddGroup.continuous_mk.measurable MeasurableSet.univ] at h
    simpa only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, hup] using h
  · apply heq.symm.trans
    change dq = _
    unfold dq additiveQuotientMeasureFromDomain
    rw [hup]

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
