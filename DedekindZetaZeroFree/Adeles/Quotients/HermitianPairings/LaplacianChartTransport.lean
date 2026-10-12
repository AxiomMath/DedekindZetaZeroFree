module

public import DedekindZetaZeroFree.Adeles.Quotients.HermitianPairings.CompactScalarTransport
public import DedekindZetaZeroFree.Adeles.Quotients.HermitianPairings.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualPartitionPairing
open KPContActualCutoffSmoothDescent KPContActualCutoffTestPairingHolomorphy
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentOverlapRationalBranches KPContActualCotangentPieceHilbertSum
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {C : KPGlobalTorusInducingPlan.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {U : KPMsRationalCompactCrossPairing.Level F ζ hζ}

namespace LaplacianReindex
variable {d d' : ℕ}
 def reindex (e : Fin d ≃ Fin d') : HyperbolicChart.Space d ≃ₗᵢ[ℝ] HyperbolicChart.Space d' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.prodCongr (Equiv.refl (Fin 3)))
private theorem vector_reindex (e : Fin d ≃ Fin d') (i : Fin d) (k : Fin 3) :
    reindex e (HyperbolicChart.coordinateVector d i k) =
      HyperbolicChart.coordinateVector d' (e i) k := by
  ext j
  rcases j with ⟨j, l⟩
  obtain ⟨j, rfl⟩ := e.surjective j
  simp [reindex, HyperbolicChart.coordinateVector, LinearIsometryEquiv.piLpCongrLeft,
    Equiv.prodCongr]
private theorem deriv_reindex (e : Fin d ≃ Fin d') (g : HyperbolicChart.Space d' → ℂ)
    (i : Fin d) (k : Fin 3) (x : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k (g ∘ reindex e) x =
      HyperbolicChart.coordinateDerivative d' (e i) k g (reindex e x) := by
  change fderiv ℝ (g ∘ (reindex e).toContinuousLinearEquiv) x
    (HyperbolicChart.coordinateVector d i k) = _
  rw [(reindex e).toContinuousLinearEquiv.comp_right_fderiv]
  change fderiv ℝ g (reindex e x) (reindex e (HyperbolicChart.coordinateVector d i k)) = _
  rw [vector_reindex]
  rfl
private theorem lap_reindex (e : Fin d ≃ Fin d') (g : HyperbolicChart.Space d' → ℂ)
    (x : HyperbolicChart.Space d) :
    HyperbolicChart.laplacian d (g ∘ reindex e) x =
      HyperbolicChart.laplacian d' g (reindex e x) := by
  have hd (i : Fin d) (k : Fin 3) : HyperbolicChart.coordinateDerivative d i k (g ∘ reindex e) =
      HyperbolicChart.coordinateDerivative d' (e i) k g ∘ reindex e := by
    funext x; exact deriv_reindex e g i k x
  unfold HyperbolicChart.laplacian
  simp only [hd, deriv_reindex]
  rw [← Equiv.sum_comp e]
  congr 1
  funext i
  have hcoord : reindex e x (e i, 2) = x (i, 2) := by simp [reindex]
  rw [hcoord]
end LaplacianReindex

private theorem toArch_reindex (x : M F) :
    KPCuspCutoffGraph.toArch F (LaplacianReindex.reindex (placeEquiv F ζ hζ) x) =
      labeledA (placeEquiv F ζ hζ) x := by
  funext k
  simp [KPCuspCutoffGraph.toArch, LaplacianReindex.reindex, labeledA, CotangentLogCoframe.A,
    Complex.ext_iff]
private theorem fromArch_reindex (x : M F) :
    KPCuspCutoffGraph.fromArch F (labeledA (placeEquiv F ζ hζ) x) =
      LaplacianReindex.reindex (placeEquiv F ζ hζ) x := by
  ext j
  rcases j with ⟨i,k⟩
  fin_cases k <;> simp [KPCuspCutoffGraph.fromArch, LaplacianReindex.reindex, labeledA,
    CotangentLogCoframe.A, Complex.ext_iff]
private theorem coefficient_eq (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ
    (level F ζ hζ C R P H U) R P H)
    (a : ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  simp [sectionFields, LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

theorem canonical_laplacian_chart (φ : Tests F ζ hζ C R P H U)
    (a : ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H) (x : omega a) :
    sectionFields (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
      ⟨φ.val, φ.property.1⟩) a x =
      HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
        (liftExtension a (sectionFields φ.val a)) x.val := by
  rw [coefficient_eq]
  change HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    ((φ.val a.component).val ∘ KPCuspCutoffGraph.toArch F)
    (KPCuspCutoffGraph.fromArch F (labeledA (placeEquiv F ζ hζ) x.val)) = _
  rw [fromArch_reindex, ← LaplacianReindex.lap_reindex]
  apply KPCuspCutoffGraphApproximation.laplacian_congr_nhds
  have hopen : IsOpen (omega a) := by
    apply a.domain_open.preimage
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  filter_upwards [hopen.mem_nhds x.property] with y hy
  change (φ.val a.component).val (KPCuspCutoffGraph.toArch F
    (LaplacianReindex.reindex (placeEquiv F ζ hζ) y)) = _
  rw [toArch_reindex]
  simp only [liftExtension, dif_pos hy]
  exact (coefficient_eq φ.val a ⟨y,hy⟩).symm

private theorem smooth_laplacian {d : ℕ} (g : HyperbolicChart.Space d → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.laplacian d g) := by
  have hd (f : HyperbolicChart.Space d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (k : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.coordinateDerivative d i k f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  unfold HyperbolicChart.laplacian
  apply ContDiff.sum
  intro i hi
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space d => (Real.exp (2 * q (i, 2)) : ℂ)) := by
    have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space d => Real.exp (2 * q (i,2))) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp hreal
  exact ((hd _ (hd g hg i 2) i 2).neg.add (contDiff_const.mul (hd g hg i 2))).sub
    (he.mul ((hd _ (hd g hg i 0) i 0).add (hd _ (hd g hg i 1) i 1)))
private theorem continuous_laplacian_section (ψ : Tests F ζ hζ C R P H U) :
    ∀ i, Continuous (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
      ⟨ψ.val, ψ.property.1⟩ i).val := by
  intro i
  have hi := ψ.property.1 i
  have hg : ContDiff ℝ (⊤ : ℕ∞) ((ψ.val i).val ∘ KPCuspCutoffGraph.toArch F) :=
    hi.comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)
  change Continuous (HyperbolicChart.laplacian _ _ ∘ KPCuspCutoffGraph.fromArch F)
  exact (smooth_laplacian _ hg).continuous.comp (by
    change Continuous (CotangentLogCoframe.A (KPCuspLogShape.dimension F)).symm
    exact (CotangentLogCoframe.A _).symm.continuous)
private theorem basePoint_continuous (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    Continuous (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
      (H.atlas (level F ζ hζ C R P H U)) i) := by
  have he : KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
      (H.atlas (level F ζ hζ C R P H U)) i =
      fun z => (H.atlas (level F ζ hζ C R P H U)).components ⟨i, Quotient.mk _ z⟩ := by
    funext z
    rw [(H.atlas _).components_formula]
    rfl
  rw [he]
  exact (H.atlas _).components.continuous.comp (continuous_sigmaMk.comp continuous_quot_mk)
private theorem laplacian_supported (ψ : Tests F ζ hζ C R P H U)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U))) (hK : IsCompact K)
    (hs : ∀ j z, KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
      (H.atlas (level F ζ hζ C R P H U)) j z ∉ K → (ψ.val j).val z = 0) :
    ∀ j z, KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
      (H.atlas (level F ζ hζ C R P H U)) j z ∉ K →
      (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
        (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
        ⟨ψ.val, ψ.property.1⟩ j).val z = 0 := by
  intro j z hz
  have hN : ∀ᶠ y in nhds z, KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j y ∉ K :=
    (basePoint_continuous j).continuousAt (hK.isClosed.isOpen_compl.mem_nhds hz)
  have hc : Continuous (KPCuspCutoffGraph.toArch F) := (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F).continuous
  have hN' : Filter.Tendsto (KPCuspCutoffGraph.toArch F)
      (nhds (KPCuspCutoffGraph.fromArch F z))
      (nhds (KPCuspCutoffGraph.toArch F (KPCuspCutoffGraph.fromArch F z))) := hc.continuousAt
  have heq : KPCuspCutoffGraph.toArch F (KPCuspCutoffGraph.fromArch F z) = z :=
    KPCuspCutoffGraphApproximation.cutoff_toArch_fromArch F z
  rw [heq] at hN'
  have he : ((ψ.val j).val ∘ KPCuspCutoffGraph.toArch F) =ᶠ[nhds (KPCuspCutoffGraph.fromArch F z)]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hN' hN] with y hy
    exact hs j _ hy
  change HyperbolicChart.laplacian _ _ _ = _
  rw [KPCuspCutoffGraphApproximation.laplacian_congr_nhds _ he]
  have hd (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
      HyperbolicChart.coordinateDerivative (KPCuspLogShape.dimension F) i k (fun _ => (0 : ℂ)) =
        fun _ => 0 := by funext y; simp [HyperbolicChart.coordinateDerivative]
  simp only [HyperbolicChart.laplacian, hd, neg_zero, mul_zero, add_zero, sub_zero,
    Finset.sum_const_zero]

theorem single_chart_pairing (ψ : Tests F ζ hζ C R P H U)
    (a : ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H)
    (hψ : ∃ K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U)),
      IsCompact K ∧ K ⊆ a.baseDomain ∧ ∀ j z,
        KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
          (H.atlas (level F ζ hζ C R P H U)) j z ∉ K → (ψ.val j).val z = 0)
    (w : SmoothSections F ζ hζ C R P H U) :
    Integrable (coveredPair F ζ hζ C R P H U w (testScalar F ζ hζ C R P H U ψ))
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)) ∧
    Integrable (coveredPair F ζ hζ C R P H U w (testLaplacian F ζ hζ C R P H U ψ))
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)) ∧
    ((∫ x, coveredPair F ζ hζ C R P H U w (testScalar F ζ hζ C R P H U ψ) x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)) =
      ∫ y, sectionFields w.val a (coordinates a y) *
        star (sectionFields ψ.val a (coordinates a y)) ∂a.liftedMeasure) ∧
    ((∫ x, coveredPair F ζ hζ C R P H U w (testLaplacian F ζ hζ C R P H U ψ) x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)) =
      ∫ y, sectionFields w.val a (coordinates a y) *
        star (HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
          (liftExtension a (sectionFields ψ.val a)) (coordinates a y).val)
        ∂a.liftedMeasure) := by
  obtain ⟨K,hK,hKa,hψK⟩ := hψ
  have hw : ∀ i, Continuous (w.val i).val := fun i => (w.property i).continuous
  have hψc : ∀ i, Continuous (ψ.val i).val := fun i => (ψ.property.1 i).continuous
  have hp := KPContActualPartitionTransport.compact_original_scalar_chart_transport
    (level F ζ hζ C R P H U) w.val ψ.val hw hψc a K hK hKa hψK
  have hpΔ := KPContActualPartitionTransport.compact_original_scalar_chart_transport
    (level F ζ hζ C R P H U) w.val
    (KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
      (H.atlas (level F ζ hζ C R P H U)) ⟨ψ.val, ψ.property.1⟩)
    hw (continuous_laplacian_section ψ) a K hK hKa (laplacian_supported ψ K hK hψK)
  refine ⟨hp.1, hpΔ.1, hp.2, hpΔ.2.trans ?_⟩
  apply integral_congr_ae
  filter_upwards [] with y
  rw [canonical_laplacian_chart]
end DedekindZetaZeroFree.KPContActualPartitionPairing

end
