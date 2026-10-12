module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactConjugationInvariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.WeakEnergyCutoffExhaustion

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactHaar

 theorem compact_hom_one {K : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
    (χ : K →* ℝ≥0) (hχ : Continuous χ) (hpos : ∀ k, 0 < χ k) : ∀ k, χ k = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).exists_bound_of_continuousOn
    (NNReal.continuous_coe.comp hχ).continuousOn
  have hb (k : K) : (χ k : ℝ) ≤ C := by
    exact (le_abs_self _).trans (by simpa only [Function.comp_apply, Real.norm_eq_abs] using hC k (Set.mem_univ k))
  have hle (k : K) : χ k ≤ 1 := by
    by_contra hh
    have hhR : (1 : ℝ) < χ k := by exact_mod_cast lt_of_not_ge hh
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt C hhR
    have h := hb (k ^ n)
    rw [map_pow, NNReal.coe_pow] at h
    exact (not_lt_of_ge h) hn
  intro k
  apply le_antisymm (hle k)
  have h := hle k⁻¹
  have he : χ k * χ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hp := hpos k
  nlinarith [mul_le_mul_of_nonneg_left h hp.le]

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 def compactHom : KPMsGreenFlux.K F →* KPSmoothLocalQuotientCharts.ActualCover F ζ hζ where
  toFun := KPMsGreenFlux.compactInsertion F ζ hζ
  map_one' := by
    change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ 1 = 1
    exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
  map_mul' k l := by
    change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun w => ((k*l) w).val) = _
    exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1 _ _

private theorem compact_modular_one (k : KPMsGreenFlux.K F) :
    letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
    letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
    letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
    Measure.modularCharacter (KPMsGreenFlux.compactInsertion F ζ hζ k) = 1 := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : ∀ w : NumberField.InfinitePlace F, CompactSpace KPCplxPrincipalSeriesCharts.compactSubgroup :=
    fun _ => isCompact_iff_compactSpace.mp KPCplxPrincipalSeriesCharts.compactSubgroup_isCompact
  letI : CompactSpace (KPMsGreenFlux.K F) := inferInstance
  have hc : Continuous (compactHom (F := F) (ζ := ζ) (hζ := hζ)) :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
      (continuous_pi fun w => continuous_subtype_val.comp (continuous_apply w))
  exact compact_hom_one ((Measure.modularCharacter).comp compactHom)
    (KPSpatialSmoothing.ArchKernel.CompactHaar.continuous_modularCharacter.comp hc)
    (fun k => Measure.modularCharacterFun_pos _) k

 theorem quotient_compact_measurePreserving
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (k : KPMsGreenFlux.K F) :
    MeasurePreserving (KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPMsGreenFlux.compactInsertion F ζ hζ k)) R.quotientHaar R.quotientHaar := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  have hq_meas : Measurable (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    continuous_quotient_mk'.measurable
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (KubotaRankTwo.GL2 F) := Units.val_injective.countable
  letI : Countable (KPRationalAdelicSplitting.RationalPGL2 F) :=
    (Quotient.mk'_surjective (s := QuotientGroup.leftRel
      (KPRationalAdelicSplitting.rationalScalars F))).countable
  letI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :=
    Set.Countable.to_subtype (Set.countable_range (KPSmoothLocalQuotientCharts.rationalSplit F ζ hζ))
  letI : IsTopologicalGroup (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := ⟨rfl⟩
  letI := R.adelic_isHaar
  let c := KPMsGreenFlux.compactInsertion F ζ hζ k
  have hmulc_meas : Measurable (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) :=
    (continuous_id.mul continuous_const).measurable
  have hmp : MeasurePreserving (fun g : KPMsGreenFlux.Cover F ζ hζ => g * c)
      R.adelicHaar R.adelicHaar := by
    refine ⟨hmulc_meas, ?_⟩
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
    change (Measure.modularCharacter c : ℝ≥0) • R.adelicHaar = _
    rw [compact_modular_one, one_smul]
  have hmp_inv : MeasurePreserving (fun g : KPMsGreenFlux.Cover F ζ hζ => g * c⁻¹)
      R.adelicHaar R.adelicHaar := by
    have he : c⁻¹ = KPMsGreenFlux.compactInsertion F ζ hζ k⁻¹ :=
      (map_inv (compactHom (F := F) (ζ := ζ) (hζ := hζ)) k).symm
    refine ⟨(continuous_id.mul continuous_const).measurable, ?_⟩
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
    change (Measure.modularCharacter c⁻¹ : ℝ≥0) • R.adelicHaar = _
    rw [he, compact_modular_one, one_smul]
  have hD' : IsFundamentalDomain (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
      ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain) R.adelicHaar := by
    refine IsFundamentalDomain.image_of_equiv (ν := R.adelicHaar) (μ := R.adelicHaar)
      R.domain_fundamental (Equiv.mulRight c) ?_ (Equiv.refl _) ?_
    · exact hmp_inv.quasiMeasurePreserving
    · intro g x
      show ((g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * x) * c =
        (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * (x * c)
      rw [mul_assoc]
  have hmap_mulc :
      Measure.map (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c)
        (R.adelicHaar.restrict R.domain) =
      R.adelicHaar.restrict
        ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain) := by
    let e : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ ≃ᵐ
        KPSmoothLocalQuotientCharts.ActualCover F ζ hζ :=
      (Homeomorph.mulRight c).toMeasurableEquiv
    have he : ⇑e = (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) := rfl
    have hmap_e : Measure.map (⇑e) R.adelicHaar = R.adelicHaar := by
      rw [he]; exact hmp.map_eq
    have hpre : ⇑e ⁻¹'
        ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain)
        = R.domain := by
      rw [he]
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := mul_right_cancel hyx
        rwa [← this]
      · intro hx
        exact ⟨x, hx, rfl⟩
    have h := MeasurableEquiv.restrict_map e R.adelicHaar
      ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain)
    rw [hmap_e, hpre] at h
    rw [h, he]
  have hcont : Continuous (KPSmoothActualFlowData.rightTranslate F ζ hζ c) :=
    (continuous_id.mul continuous_const).quotient_map' _
  have ht_meas : Measurable (KPSmoothActualFlowData.rightTranslate F ζ hζ c) := hcont.borel_measurable
  have hdom_eq : Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
        (R.adelicHaar.restrict
          ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain)) =
      Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
        (R.adelicHaar.restrict R.domain) := by
    ext A hA
    have hA₀ : MeasurableSet (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹' A) := hq_meas hA
    rw [Measure.map_apply hq_meas hA, Measure.map_apply hq_meas hA,
      Measure.restrict_apply hA₀, Measure.restrict_apply hA₀]
    refine IsFundamentalDomain.measure_set_eq hD' R.domain_fundamental hA₀ (fun γ => ?_)
    ext x
    simp only [Set.mem_preimage]
    have hsmul : (γ • x : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) =
        (γ : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * x := rfl
    rw [hsmul]
    have h : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        ((γ : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * x) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x := by
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simpa using (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem γ.property
    rw [h]
  have hcomp : KPSmoothActualFlowData.rightTranslate F ζ hζ c ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘
        (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) := by
    funext g
    rfl
  refine ⟨ht_meas, ?_⟩
  rw [← R.quotient_normalization]
  rw [Measure.map_map ht_meas hq_meas, hcomp,
    ← Measure.map_map hq_meas hmulc_meas, hmap_mulc, hdom_eq]

end DedekindZetaZeroFree.FourierContinuation.ResidualCompactHaar

end
