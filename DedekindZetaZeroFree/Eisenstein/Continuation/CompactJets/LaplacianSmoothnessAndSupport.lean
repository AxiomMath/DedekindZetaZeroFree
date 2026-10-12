module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.CompactInterior
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualGlobalGreen

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem contDiff_exp_height (i : Fin (d F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => (Real.exp (2 * p (i, 2)) : ℂ)) := by
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => p (i, 2)) := by
    convert (EuclideanSpace.proj (i, 2) : M F →L[ℝ] ℝ).contDiff (n := (⊤ : ℕ∞)) using 1
    ext p
    simp [PiLp.proj_apply]
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => 2 * p (i, 2)) :=
    (contDiff_const (c := (2 : ℝ))).mul hproj
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun p : M F => ((2 * p (i, 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h2
  simpa only [Complex.ofReal_exp] using h.cexp

private theorem cd_congr (f g : M F → ℂ) (x : M F) (he : f =ᶠ[𝓝 x] g)
    (i : Fin (d F)) (k : Fin 3) :
    HyperbolicChart.coordinateDerivative (d F) i k f x =
      HyperbolicChart.coordinateDerivative (d F) i k g x := by
  simp only [HyperbolicChart.coordinateDerivative]
  rw [he.fderiv_eq]

private theorem cd_eventuallyEq (f g : M F → ℂ) (x : M F) (he : f =ᶠ[𝓝 x] g)
    (i : Fin (d F)) (k : Fin 3) :
    (fun y => HyperbolicChart.coordinateDerivative (d F) i k f y) =ᶠ[𝓝 x]
      (fun y => HyperbolicChart.coordinateDerivative (d F) i k g y) := by
  filter_upwards [he.eventuallyEq_nhds] with y hy using cd_congr f g y hy i k

private theorem laplacian_congr (f g : M F → ℂ) (x : M F) (he : f =ᶠ[𝓝 x] g) :
    HyperbolicChart.laplacian (d F) f x = HyperbolicChart.laplacian (d F) g x := by
  unfold HyperbolicChart.laplacian
  apply Finset.sum_congr rfl
  intro i _
  have h22 := cd_eventuallyEq f g x he i 2
  have h00 := cd_eventuallyEq f g x he i 0
  have h11 := cd_eventuallyEq f g x he i 1
  rw [cd_congr _ _ x h22 i 2, cd_congr f g x he i 2,
    cd_congr _ _ x h00 i 0, cd_congr _ _ x h11 i 1]

private theorem coordinateDerivative_zero (i : Fin (d F)) (k : Fin 3) :
    HyperbolicChart.coordinateDerivative (d F) i k (0 : M F → ℂ) = 0 := by
  funext p
  simp [HyperbolicChart.coordinateDerivative]

private theorem laplacian_zero :
    (fun x : M F => HyperbolicChart.laplacian (d F) (0 : M F → ℂ) x) = 0 := by
  funext x
  simp [HyperbolicChart.laplacian, coordinateDerivative_zero]

private theorem contDiffAt_coordinateDerivative (f : M F → ℂ) (x : M F)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (i : Fin (d F)) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p => HyperbolicChart.coordinateDerivative (d F) i k f p) x := by
  have h := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
  simpa only [HyperbolicChart.coordinateDerivative] using h.clm_apply contDiffAt_const

private theorem contDiffAt_laplacian (g : M F → ℂ) (x : M F)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => HyperbolicChart.laplacian (d F) g y) x := by
  have key : ∀ i : Fin (d F), ContDiffAt ℝ (⊤ : ℕ∞) (fun p : M F =>
      -HyperbolicChart.coordinateDerivative (d F) i 2
          (HyperbolicChart.coordinateDerivative (d F) i 2 g) p +
        2 * HyperbolicChart.coordinateDerivative (d F) i 2 g p -
      (Real.exp (2 * p (i, 2)) : ℂ) *
        (HyperbolicChart.coordinateDerivative (d F) i 0
            (HyperbolicChart.coordinateDerivative (d F) i 0 g) p +
          HyperbolicChart.coordinateDerivative (d F) i 1
            (HyperbolicChart.coordinateDerivative (d F) i 1 g) p)) x := by
    intro i
    have h22 := contDiffAt_coordinateDerivative g x hg i 2
    have h00 := contDiffAt_coordinateDerivative g x hg i 0
    have h11 := contDiffAt_coordinateDerivative g x hg i 1
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : M F =>
        HyperbolicChart.coordinateDerivative (d F) i 2
          (HyperbolicChart.coordinateDerivative (d F) i 2 g) p) x :=
      contDiffAt_coordinateDerivative _ x h22 i 2
    have h0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : M F =>
        HyperbolicChart.coordinateDerivative (d F) i 0
          (HyperbolicChart.coordinateDerivative (d F) i 0 g) p) x :=
      contDiffAt_coordinateDerivative _ x h00 i 0
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : M F =>
        HyperbolicChart.coordinateDerivative (d F) i 1
          (HyperbolicChart.coordinateDerivative (d F) i 1 g) p) x :=
      contDiffAt_coordinateDerivative _ x h11 i 1
    have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : M F => (Real.exp (2 * p (i, 2)) : ℂ)) x :=
      (contDiff_exp_height i).contDiffAt
    have h22' : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : M F =>
        2 * HyperbolicChart.coordinateDerivative (d F) i 2 g p) x :=
      contDiffAt_const.mul h22
    exact (h2.neg.add h22').sub (he.mul (h0.add h1))
  simpa only [HyperbolicChart.laplacian] using ContDiffAt.sum (fun i _ => key i)

private theorem contDiffOn_laplacian (a : ActualChart (U := U) (H := H)) (g : M F → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (omega a)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => HyperbolicChart.laplacian (d F) g y) (omega a) := by
  intro x hx
  have hxa : ContDiffAt ℝ (⊤ : ℕ∞) g x :=
    hg.contDiffAt ((isOpen_omega_actual a).mem_nhds hx)
  exact (contDiffAt_laplacian g x hxa).contDiffWithinAt

private theorem smoothOnLift_laplacian (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    SmoothOnLift a (fun x => HyperbolicChart.laplacian (d F) (liftExtension a f) x.val) := by
  obtain ⟨g, hg, hge⟩ := hf
  refine ⟨fun x => HyperbolicChart.laplacian (d F) g x, contDiffOn_laplacian a g hg, ?_⟩
  intro x
  exact (laplacian_congr (liftExtension a f) g x.val (by
    filter_upwards [(isOpen_omega_actual a).mem_nhds x.property] with y hy
    rw [liftExtension, dif_pos hy]
    exact (hge ⟨y, hy⟩).symm)).symm

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem coefficient_isotropyChart (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (x : M F) :
    (isotropyChart a).coefficient s x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x) := by
  simp [isotropyChart, KPContCotangentActualOverlap.LiftedChart.coefficient,
    ChartKind.representative, chi_coe]

private theorem sectionFields_apply (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  simp [sectionFields, coefficient_isotropyChart]

private theorem labeledA_labeledAInv (z : SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
  funext k
  simp only [labeledA, labeledAInv]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp

private theorem contDiff_labeledAInv :
    ContDiff ℝ (⊤ : ℕ∞) (labeledAInv (placeEquiv F ζ hζ) : SymmetricSpace F → M F) := by
  have h : (labeledAInv (placeEquiv F ζ hζ) : SymmetricSpace F → M F) =
      fun z => (CotangentLogCoframe.A (d F)).symm (fun k => z ((placeEquiv F ζ hζ) k)) := rfl
  rw [h]
  refine (CotangentLogCoframe.A (d F)).symm.contDiff.comp ?_
  apply contDiff_pi.mpr
  intro k
  exact contDiff_apply ℝ KPArch.H3 ((placeEquiv F ζ hζ) k)

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualGlobalGreen

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem shrink_at (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
    ∃ C : ActualChart (U := U) (H := H), C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ U R P H i p)
  letI : Finite (MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p) :=
    KPContSectorPhaseComponentCharts.chart_stabilizer_finite F ζ hζ U R P H i p O
  letI := Fintype.ofFinite (MulAction.stabilizer
    (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p)
  obtain ⟨W, hWo, hpW, hWsub, hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p,
    (fun x : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i, p, O, V, hopen, hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub, ?_⟩, rfl, rfl, hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h * g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x, ?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h * g⁻¹)

private theorem continuous_labeledA :
    Continuous (labeledA (placeEquiv F ζ hζ) : M F → SymmetricSpace F) := by
  apply continuous_pi
  intro k
  exact ((continuous_apply ((placeEquiv F ζ hζ).symm k)).comp
    (CotangentLogCoframe.A (d F)).continuous)

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualGlobalGreen

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem contDiffAt_section (s : Sections F ζ hζ U R P H)
    (hchart : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (sectionFields s a))
    (i : Fin (H.atlas U).componentCount) (p : SymmetricSpace F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (s i).val x) p := by
  obtain ⟨C, hcomp, hcenter, hpdom⟩ := shrink_at (F := F) (ζ := ζ) (hζ := hζ) i p
  obtain ⟨g, hg, hge⟩ := hchart C
  have hmem : ∀ z ∈ C.domain, labeledAInv (placeEquiv F ζ hζ) z ∈ omega C := by
    intro z hz
    show labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) ∈ C.domain
    rw [labeledA_labeledAInv]
    exact hz
  have hginv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : SymmetricSpace F => g (labeledAInv (placeEquiv F ζ hζ) z)) C.domain :=
    hg.comp contDiff_labeledAInv.contDiffOn hmem
  have heq : ∀ z ∈ C.domain,
      (s i).val z = g (labeledAInv (placeEquiv F ζ hζ) z) := by
    intro z hz
    have hy := hmem z hz
    have h1 : (s i).val z = (isotropyChart C).coefficient s (labeledAInv (placeEquiv F ζ hζ) z) := by
      rw [coefficient_isotropyChart, hcomp, labeledA_labeledAInv]
    have h2 : (isotropyChart C).coefficient s (labeledAInv (placeEquiv F ζ hζ) z) =
        sectionFields s C ⟨labeledAInv (placeEquiv F ζ hζ) z, hy⟩ := rfl
    rw [h1, h2, ← hge ⟨_, hy⟩]
  have hcont : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : SymmetricSpace F => g (labeledAInv (placeEquiv F ζ hζ) z)) p :=
    hginv.contDiffAt (C.domain_open.mem_nhds hpdom)
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards [C.domain_open.mem_nhds hpdom] with z hz
  exact heq z hz

private theorem isSmoothSections_of_chartSmooth (s : Sections F ζ hζ U R P H)
    (hchart : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (sectionFields s a)) :
    IsSmoothSections F ζ hζ U R P H s := by
  intro i
  rw [contDiff_iff_contDiffAt]
  intro p
  exact contDiffAt_section s hchart i p

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualGlobalGreen

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem sectionValue_eq_zero_of_base_mem (w v : ℂ → Sections F ζ hζ U R P H) (s : ℂ)
    (Vv : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hVvo : IsOpen Vv)
    (hVv0 : ∀ y ∈ Vv, sectionNorm F ζ hζ U R P H (w s) y = 0)
    (hlap : ∀ a : ActualChart (U := U) (H := H), ∀ x : omega a,
      (isotropyChart a).coefficient (v s) x.val =
        HyperbolicChart.laplacian (d F) (liftExtension a (sectionFields (w s) a)) x.val)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ Vv) :
    (v s i).val x = 0 := by
  obtain ⟨C, hcomp, hcenter, hpdom⟩ := shrink_at (F := F) (ζ := ζ) (hζ := hζ) i x
  set x0 := labeledAInv (placeEquiv F ζ hζ) x with hx0
  have hx0mem : x0 ∈ omega C := by
    show labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x) ∈ C.domain
    rwa [labeledA_labeledAInv]
  have hbase_cont : Continuous (fun y : M F =>
      (H.atlas U).components ⟨i, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) y)⟩) :=
    (H.atlas U).components.continuous.comp
      (continuous_sigmaMk.comp (continuous_quotient_mk'.comp continuous_labeledA))
  have hval0 : (H.atlas U).components ⟨i, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x0)⟩ ∈ Vv := by
    rw [hx0, labeledA_labeledAInv]
    exact hx
  have hcontU : ∀ᶠ y in 𝓝 x0,
      (H.atlas U).components ⟨i, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) y)⟩ ∈ Vv :=
    hbase_cont.continuousAt (hVvo.mem_nhds hval0)
  have hev : liftExtension C (sectionFields (w s) C) =ᶠ[𝓝 x0] 0 := by
    filter_upwards [(isOpen_omega_actual C).mem_nhds hx0mem, hcontU] with y hy hyU
    rw [liftExtension, dif_pos hy]
    have h1 : sectionFields (w s) C ⟨y, hy⟩ =
        ((w s) i).val (labeledA (placeEquiv F ζ hζ) y) := by
      rw [sectionFields_apply, hcomp]
    rw [h1]
    have h0 := hVv0 _ hyU
    rw [sectionNorm_component] at h0
    exact norm_eq_zero.mp h0
  have hz : HyperbolicChart.laplacian (d F) (liftExtension C (sectionFields (w s) C)) x0 = 0 := by
    rw [laplacian_congr _ (0 : M F → ℂ) x0 hev]
    exact congrFun laplacian_zero x0
  have h := hlap C ⟨x0, hx0mem⟩
  rw [coefficient_isotropyChart, hcomp, labeledA_labeledAInv] at h
  rw [h, hz]

private theorem tsupport_sectionNorm_subset (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (w v : ℂ → Sections F ζ hζ U R P H) (s : ℂ)
    (hw : tsupport (sectionNorm F ζ hζ U R P H (w s)) ⊆ K)
    (hlap : ∀ a : ActualChart (U := U) (H := H), ∀ x : omega a,
      (isotropyChart a).coefficient (v s) x.val =
        HyperbolicChart.laplacian (d F) (liftExtension a (sectionFields (w s) a)) x.val) :
    tsupport (sectionNorm F ζ hζ U R P H (v s)) ⊆ K := by
  have hmain : tsupport (sectionNorm F ζ hζ U R P H (v s)) ⊆
      tsupport (sectionNorm F ζ hζ U R P H (w s)) := by
    intro b hb
    by_contra hnot
    have hVv : ∃ Vv ∈ 𝓝 b, ∀ y ∈ Vv, sectionNorm F ζ hζ U R P H (w s) y = 0 := by
      refine ⟨(tsupport (sectionNorm F ζ hζ U R P H (w s)))ᶜ,
        (isClosed_tsupport _).isOpen_compl.mem_nhds hnot, ?_⟩
      intro y hy
      by_contra h
      exact hy (subset_tsupport _ h)
    obtain ⟨Vv, hVvo, hbVv, hVv0⟩ : ∃ Vv, IsOpen Vv ∧ b ∈ Vv ∧
        ∀ y ∈ Vv, sectionNorm F ζ hζ U R P H (w s) y = 0 := by
      obtain ⟨V, hV, hV0⟩ := hVv
      obtain ⟨Vv, hVvsub, hVvo, hbVv⟩ := mem_nhds_iff.mp hV
      exact ⟨Vv, hVvo, hbVv, fun y hy => hV0 y (hVvsub hy)⟩
    have hzero : ∀ y ∈ Vv, sectionNorm F ζ hζ U R P H (v s) y = 0 := by
      intro y hy
      set q := (H.atlas U).components.symm y with hq
      obtain ⟨x, hx⟩ : ∃ x : SymmetricSpace F, Quotient.mk _ x = q.2 :=
        ⟨Quotient.out q.2, Quotient.out_eq q.2⟩
      have hy_eq : y = (H.atlas U).components ⟨q.1, Quotient.mk _ x⟩ := by
        conv_lhs => rw [← Homeomorph.apply_symm_apply (H.atlas U).components y]
        rw [← hq, hx]
      rw [hy_eq, sectionNorm_component, norm_eq_zero]
      exact sectionValue_eq_zero_of_base_mem w v s Vv hVvo hVv0 hlap q.1 x (by rw [← hy_eq]; exact hy)
    have hsub : Vv ⊆ (Function.support (sectionNorm F ζ hζ U R P H (v s)))ᶜ := by
      intro y hy
      simp only [Set.mem_compl_iff, Function.mem_support, not_not]
      exact hzero y hy
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hb Vv hVvo hbVv
    exact hsub hy1 hy2
  exact hmain.trans hw

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy
open KPContActualGlobalGreen

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem local_laplacian_smooth_support_source
    (O : Set ℂ) (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (w v : ℂ → Sections F ζ hζ U R P H)
    (_hsm : ∀ s ∈ O, IsSmoothSections F ζ hζ U R P H (w s))
    (_hsup : ∀ s ∈ O, tsupport (sectionNorm F ζ hζ U R P H (w s)) ⊆ K)
    (_hlap : IsLocalLaplacianFamily w v O) :
    ∀ s ∈ O, IsSmoothSections F ζ hζ U R P H (v s) ∧
      tsupport (sectionNorm F ζ hζ U R P H (v s)) ⊆ K := by
  intro s hs
  have hchart_w : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (sectionFields (w s) a) :=
    fun a => smoothOnLift_sectionFields a (w s) (_hsm s hs)
  have hchart_v : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (sectionFields (v s) a) := by
    intro a
    have h := smoothOnLift_laplacian a (sectionFields (w s) a) (hchart_w a)
    have hfun : (fun x => HyperbolicChart.laplacian (d F)
        (liftExtension a (sectionFields (w s) a)) x.val) = sectionFields (v s) a := by
      funext x
      exact (_hlap s hs a x).symm
    rwa [hfun] at h
  refine ⟨isSmoothSections_of_chartSmooth (v s) hchart_v, ?_⟩
  exact tsupport_sectionNorm_subset K w v s (_hsup s hs) (fun a x => _hlap s hs a x)

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
