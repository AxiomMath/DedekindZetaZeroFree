module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.HaarPushforwardsAndSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorCentralHaarInvariance

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def t (ε : rootsOfUnity 3 F) :
    KPSmoothLocalQuotientCharts.X F ζ hζ → KPSmoothLocalQuotientCharts.X F ζ hζ :=
  KPSmoothActualFlowData.rightTranslate F ζ hζ
    (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε)

theorem t_quotientMap (ε : rootsOfUnity 3 F)
    (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :
    t F ζ hζ ε (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) := rfl

theorem t_measurePreserving
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (ε : rootsOfUnity 3 F) :
    MeasurePreserving (t F ζ hζ ε) R.quotientHaar R.quotientHaar := by
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
  set c := KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε with hc
  have hmem : c ∈ Subgroup.center (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩
  have hcentral : ∀ g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ, g * c = c * g :=
    fun g => Subgroup.mem_center_iff.mp hmem g
  have hmulc_meas : Measurable (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) :=
    (continuous_id.mul continuous_const).measurable
  have hmp : MeasurePreserving (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c)
      R.adelicHaar R.adelicHaar := by
    have heq : (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) =
        fun g => c * g := by
      funext g; exact hcentral g
    rw [heq]
    exact measurePreserving_mul_left R.adelicHaar c
  have hmp_inv : MeasurePreserving (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c⁻¹)
      R.adelicHaar R.adelicHaar := by
    have hmem' : c⁻¹ ∈ Subgroup.center (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
      Subgroup.inv_mem _ hmem
    have hc' : ∀ g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ, g * c⁻¹ = c⁻¹ * g :=
      fun g => Subgroup.mem_center_iff.mp hmem' g
    have heq : (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c⁻¹) =
        fun g => c⁻¹ * g := by
      funext g; exact hc' g
    rw [heq]
    exact measurePreserving_mul_left R.adelicHaar c⁻¹
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
  have hcont : Continuous (KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε)) :=
    (continuous_id.mul continuous_const).quotient_map' _
  have ht_meas : Measurable (t F ζ hζ ε) := hcont.borel_measurable
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
  have hcomp : t F ζ hζ ε ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘
        (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) := by
    funext g
    exact t_quotientMap F ζ hζ ε g
  refine ⟨ht_meas, ?_⟩
  rw [← R.quotient_normalization]
  rw [Measure.map_map ht_meas hq_meas, hcomp,
    ← Measure.map_map hq_meas hmulc_meas, hmap_mulc, hdom_eq]

private theorem exists_arch_mul_finite
    (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :
    ∃ (a : KPSmoothActualFlowData.GInfinity F)
      (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ),
      g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (c : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := by
  obtain ⟨e, he, _, _, hker, _, _⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  let p := e.symm g
  have hp : (p.2 : PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ) ∈
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
    rw [hker]
    exact p.2.property
  have hc : (p.2 : PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ) ∈
      KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ :=
    KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.complex_kernel_mem
      F ζ hζ (MonoidHom.mem_ker.mp hp)
  refine ⟨p.1, ⟨p.2, hc⟩, ?_⟩
  have hg := he p.1 p.2
  rw [show e p = g from e.apply_symm_apply g] at hg
  exact hg

theorem piTilde_t (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ε : rootsOfUnity 3 F) :
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U ∘ t F ζ hζ ε =
      KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε ∘
        KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U := by
  funext x
  refine Quotient.inductionOn x (fun g => ?_)
  change KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
    (t F ζ hζ ε (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = _
  obtain ⟨a, c, rfl⟩ := exists_arch_mul_finite F ζ hζ g
  rw [t_quotientMap]
  have hcentral : (c : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * c :=
    Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c
  rw [mul_assoc, hcentral]
  change KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
    (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((KPCuspGenuineMonodromy.central F ζ hζ ε * c :
          KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ) :
            KPSmoothLocalQuotientCharts.ActualCover F ζ hζ))) = _
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap]
  change _ = KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε
    (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c)))
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
    KPContSectorCoveredQuotientVocabulary.z_mk]

theorem z_measurePreserving
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) (ε : rootsOfUnity 3 F) :
    MeasurePreserving (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε)
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U)
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) := by
  have hz : Measurable (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε) :=
    (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U ε).continuous.borel_measurable
  have hp : Measurable (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U) :=
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ U).borel_measurable
  have ht : Measurable (t F ζ hζ ε) := (t_measurePreserving F ζ hζ R ε).measurable
  refine ⟨hz, ?_⟩
  rw [KPContSectorFixedPushforwardSupport.coveredMeasure]
  rw [Measure.map_map hz hp, ← piTilde_t F ζ hζ U ε,
    ← Measure.map_map hp ht, (t_measurePreserving F ζ hζ R ε).map_eq]

end DedekindZetaZeroFree.KPContSectorCentralHaarInvariance

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
