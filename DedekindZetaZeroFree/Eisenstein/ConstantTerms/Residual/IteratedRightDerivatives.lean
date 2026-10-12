module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.DifferentialWords.SmoothL2Space

@[expose] public section

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualIntrinsicJets
open KPMsGreenFlux KPMsGreenFlux.IntrinsicAveraging KPSmoothActualFlowData
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
theorem wordIntegrand_joint_continuous
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (word : List (B F)) :
    Continuous (fun p : KPCompactFourier.AdditiveQuotient F × Cover F ζ hζ =>
      wordIntegrand A j f word p.1 p.2) := by
  exact FiniteSlabActualMean.integrand_joint_continuous A j
    (IntrinsicAveraging.pullback (wordDerivative F ζ hζ word f)) ((hf word).1.comp continuous_quot_mk)
    (IntrinsicAveraging.pullback_rational _)

theorem wordIntegrand_integrable
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (word : List (B F)) (g : Cover F ζ hζ) :
    Integrable (fun q => wordIntegrand A j f word q g) dn := by
  have hc := (wordIntegrand_joint_continuous A j f hf word).comp
    (continuous_id.prodMk (continuous_const (y := g)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem flow_word_joint_continuous
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (word : List (B F)) (b : B F) (g : Cover F ζ hζ) :
    Continuous (fun p : ℝ × KPCompactFourier.AdditiveQuotient F =>
      wordIntegrand A j f word p.2
        (g * archimedeanInsertion F ζ hζ (flow F b p.1))) := by
  letI : IsTopologicalGroup (Cover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hflow : Continuous (flow F b) := (flow_properties F b).2.2
  have hins : Continuous (archimedeanInsertion F ζ hζ) :=
    (archimedean_insertion_properties F ζ hζ).2.2.1
  have hmap : Continuous (fun p : ℝ × KPCompactFourier.AdditiveQuotient F =>
      (p.2, g * archimedeanInsertion F ζ hζ (flow F b p.1))) :=
    continuous_snd.prodMk (continuous_const.mul (hins.comp (hflow.comp continuous_fst)))
  change Continuous ((fun p : KPCompactFourier.AdditiveQuotient F × Cover F ζ hζ =>
    wordIntegrand A j f word p.1 p.2) ∘
      (fun p : ℝ × KPCompactFourier.AdditiveQuotient F =>
        (p.2, g * archimedeanInsertion F ζ hζ (flow F b p.1))))
  exact Continuous.comp (wordIntegrand_joint_continuous A j f hf word) hmap

theorem mean_word_flow_hasDerivAt
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (word : List (B F)) (b : B F) (g : Cover F ζ hζ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ q, wordIntegrand A j f word q
      (g * archimedeanInsertion F ζ hζ (flow F b s)) ∂dn)
      (∫ q, wordIntegrand A j f (b :: word) q
        (g * archimedeanInsertion F ζ hζ (flow F b t)) ∂dn) t := by
  let P : ℝ → KPCompactFourier.AdditiveQuotient F → ℂ := fun s q => wordIntegrand A j f word q
    (g * archimedeanInsertion F ζ hζ (flow F b s))
  let P' : ℝ → KPCompactFourier.AdditiveQuotient F → ℂ := fun s q => wordIntegrand A j f (b :: word) q
    (g * archimedeanInsertion F ζ hζ (flow F b s))
  have hc : Continuous (Function.uncurry P) := by
    change Continuous (fun p : ℝ × KPCompactFourier.AdditiveQuotient F =>
      wordIntegrand A j f word p.2
        (g * archimedeanInsertion F ζ hζ (flow F b p.1)))
    exact
    flow_word_joint_continuous A j f hf word b g
  have hc' : Continuous (Function.uncurry P') := by
    change Continuous (fun p : ℝ × KPCompactFourier.AdditiveQuotient F =>
      wordIntegrand A j f (b :: word) p.2
        (g * archimedeanInsertion F ζ hζ (flow F b p.1)))
    exact
    flow_word_joint_continuous A j f hf (b :: word) b g
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (t - 1) (t + 1))).prod (isCompact_univ : IsCompact
      (Set.univ : Set (KPCompactFourier.AdditiveQuotient F)))).exists_bound_of_continuousOn
        hc'.continuousOn
  have hi (s : ℝ) : Integrable (P s) dn := by
    change Integrable (fun q => wordIntegrand A j f word q
      (g * archimedeanInsertion F ζ hζ (flow F b s))) dn
    exact wordIntegrand_integrable A dn j f hf word _
  have hi' (s : ℝ) : Integrable (P' s) dn := by
    change Integrable (fun q => wordIntegrand A j f (b :: word) q
      (g * archimedeanInsertion F ζ hζ (flow F b s))) dn
    exact wordIntegrand_integrable A dn j f hf (b :: word) _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := dn) (F := P) (F' := P')
    (x₀ := t)
    (s := Set.Icc (t - 1) (t + 1)) (bound := fun _ => C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (hi s).aestronglyMeasurable)
    (hi t)
    ((hi' t).aestronglyMeasurable)
    (Eventually.of_forall fun q s hsq => hC (s,q) ⟨hsq, Set.mem_univ q⟩)
    (integrable_const C)
    (Eventually.of_forall fun q s _ => wordIntegrand_flow_hasDerivAt A j f (hf []) word b g q s)).2

theorem rightDerivative_constantTerm_word
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (word : List (B F)) (w : NumberField.InfinitePlace F) (i : Fin 6) :
    rightDerivative F ζ hζ w i
      (constantTerm A dn j (IntrinsicAveraging.pullback (wordDerivative F ζ hζ word f))) =
    constantTerm A dn j
      (IntrinsicAveraging.pullback (wordDerivative F ζ hζ ((w,i) :: word) f)) := by
  funext g
  have hd := (mean_word_flow_hasDerivAt A dn j f hf word (w,i) g 0).deriv
  simpa only [rightDerivative, constantTerm, wordIntegrand,
    (flow_properties F (w,i)).1, (archimedean_insertion_properties F ζ hζ).1,
    mul_one] using hd

end DedekindZetaZeroFree.FourierContinuation.ResidualIntrinsicJets

end
