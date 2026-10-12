module

public import DedekindZetaZeroFree.Analysis.RightFrame.CauchyCoefficient
public import DedekindZetaZeroFree.Eisenstein.Continuation.RationalSummands.MixedJets
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContinuation.ChamberJetGeometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 abbrev B := KPSmoothActualFlowData.B F
 abbrev X := B F → ℝ

open scoped Manifold ContDiff Matrix.Norms.Operator
open Topology Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open KPContActualSphericalRightFieldIdentification
private theorem section_smooth (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    letI := actualLieChartedSpace F
    ContMDiff (𝓘(ℝ, KPContSectorCoveredQuotientVocabulary.SymmetricSpace F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ) := by
  letI := actualLieChartedSpace F
  let S := KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
  have hc : Continuous S := KPContSectorArchSphericalFibers.section_continuous F ζ hζ
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨hc.continuousAt,?_⟩
  have hchart (a : KPSmoothLocalQuotientCharts.ArchGroup F) :
      chartAt (KPSmoothLocalQuotientCharts.Coordinates F) a =
        (LocalQuotientCharts.ExponentialHaarFrame.rawAffineChart F a).symm :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (LocalQuotientCharts.ExponentialHaarFrame.raw_lie_exponential_data F)))).2.2 a
  have hraw (a b : KPSmoothLocalQuotientCharts.ArchGroup F) :
      (LocalQuotientCharts.ExponentialHaarFrame.rawAffineChart F a).symm b =
        (LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F).symm
          ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F))
            (fun w => PGLComplex.affineChart.symm ((a w)⁻¹ * b w))) := rfl
  have hd : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => fun w => PGLComplex.affineChart.symm ((S x w)⁻¹ * S y w)) x := by
    apply contDiffAt_pi.mpr
    intro w
    let a := (S x w).out
    let M := fun y => a⁻¹ * KPContSectorArchSphericalFibers.sectionGL F ζ hζ y w
    have hM (y) : Matrix.ProjGenLinGroup.mk (M y) = (S x w)⁻¹ * S y w := by
      simp only [M, map_mul, map_inv]
      rw [show Matrix.ProjGenLinGroup.mk a = S x w from Quotient.out_eq _]
      rfl
    have ht : Matrix.ProjGenLinGroup.mk (M x) ∈ PGLComplex.affineTarget := by
      rw [hM]; simpa using PGLComplex.one_mem_affineTarget
    have hden : (M x).val 0 0 ≠ 0 := by
      obtain ⟨z,hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
        ((Quotient.out_eq (Matrix.ProjGenLinGroup.mk (M x))).symm)
      change (Matrix.ProjGenLinGroup.mk (M x)).out.val 0 0 ≠ 0 at ht
      rw [← hz] at ht
      simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal] using ht
    let m := fun y => a⁻¹.val * KPContSectorArchSphericalFibers.sectionMatrix F ζ hζ y w
    have hm (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => m y i j) := by
      simp only [m, Matrix.mul_apply, Fin.sum_univ_two,
        KPContSectorArchSphericalFibers.sectionMatrix_formula]
      have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun y : KPFiniteCuspAtlas.SymmetricSpace F =>
        (y (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2) := by fun_prop
      have he := Complex.ofRealCLM.contDiff.comp hproj.exp
      fin_cases j
      · change ContDiff ℝ (⊤ : ℕ∞) (fun y : KPFiniteCuspAtlas.SymmetricSpace F => a⁻¹.val i 0 *
          (Real.exp (y (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2 : ℂ) + a⁻¹.val i 1 * 0)
        simpa only [mul_zero, add_zero, Function.comp_def, Complex.ofRealCLM_apply] using! contDiff_const.mul he
      · change ContDiff ℝ (⊤ : ℕ∞) (fun y : KPFiniteCuspAtlas.SymmetricSpace F => a⁻¹.val i 0 *
          (y (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).1 + a⁻¹.val i 1 * 1)
        exact (contDiff_const.mul (by fun_prop)).add contDiff_const
    have hme (y) : (M y).val = m y := rfl
    have hrat : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => PGLComplex.matrixRatios (m y)) x := by
      have hr (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => m y i j / m y 0 0) x :=
        by
        simpa only [div_eq_mul_inv] using!
          (hm i j).contDiffAt.mul ((hm 0 0).contDiffAt.inv (hme x ▸ hden))
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> simp only [PGLComplex.matrixRatios, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val,
        Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      · exact (Complex.reCLM.contDiff.comp_contDiffAt x (hr 1 1)).sub contDiffAt_const
      · exact Complex.imCLM.contDiff.comp_contDiffAt x (hr 1 1)
      · exact Complex.reCLM.contDiff.comp_contDiffAt x (hr 0 1)
      · exact Complex.imCLM.contDiff.comp_contDiffAt x (hr 0 1)
      · exact Complex.reCLM.contDiff.comp_contDiffAt x (hr 1 0)
      · exact Complex.imCLM.contDiff.comp_contDiffAt x (hr 1 0)
    apply hrat.congr_of_eventuallyEq
    have hn' : ∀ᶠ y in 𝓝 x, Matrix.ProjGenLinGroup.mk (M y) ∈ PGLComplex.affineTarget := by
      have hcc : ContinuousAt (fun y => (S x w)⁻¹ * S y w) x :=
        continuousAt_const.mul ((continuous_apply w).continuousAt.comp hc.continuousAt)
      have hh := hcc.preimage_mem_nhds (PGLComplex.affineChart.open_target.mem_nhds
        (by rw [PGLComplex.affineChart_target]; simpa using PGLComplex.one_mem_affineTarget))
      filter_upwards [hh] with y hy
      simpa only [hM, PGLComplex.affineChart_target, Set.mem_preimage] using hy
    filter_upwards [hn'] with y hy
    rw [← hM, PGLComplex.affineChart_symm_apply _ hy, PGLComplex.matrixRatios_mk, hme]
  have hfinal := (LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F).symm.contDiff.comp_contDiffAt x
    ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).contDiff.comp_contDiffAt x hd)
  have hself {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
      (𝓘(ℝ,V)).toPartialEquiv = PartialEquiv.refl V := by ext <;> rfl
  simp only [extChartAt, OpenPartialHomeomorph.extend, hself, PartialEquiv.trans_refl,
    chartAt_self_eq, hchart]
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y => (LocalQuotientCharts.ExponentialHaarFrame.rawAffineChart F (S x)).symm
      (S y)) _ x
  simpa only [hraw, Function.comp_def] using hfinal.contDiffWithinAt

private theorem frame_words
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (g : KPSmoothLocalQuotientCharts.ArchGroup F)
    (E : OpenPartialHomeomorph (KPSmoothLocalQuotientCharts.Coordinates F)
      (KPSmoothLocalQuotientCharts.ArchGroup F))
    (hE : ∀ y ∈ E.source, E y = g * KPSmoothLocalQuotientCharts.matrixExp F y)
    (hEi : letI := actualLieChartedSpace F
      ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) E.symm E.target)
    (v : LieIndex F → KPSmoothLocalQuotientCharts.Coordinates F → KPSmoothLocalQuotientCharts.Coordinates F)
    (hv : ∀ b y, v b y = deriv (fun t : ℝ => E.symm (E y *
      KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1))) 0)
    (hvs : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (v b) E.source) :
    let r := LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F
    let e := KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F
    let O := r.symm ⁻¹' E.source
    let ℓ := fun x : X F => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (E (r.symm x)) * c.val
    let fields := fun b x => r (v (e.symm b) (r.symm x))
    ∀ u, KPMsGreenFlux.Smooth F ζ hζ u →
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ ℓ) O ∧ ∀ w x, x ∈ O →
        KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x) =
          RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ) x := by
  dsimp only
  let r := LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F
  let e := KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F
  let O := r.symm ⁻¹' E.source
  let ℓ := fun x : X F => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (E (r.symm x)) * c.val
  let fields := fun b x => r (v (e.symm b) (r.symm x))
  have hO : IsOpen O := E.open_source.preimage r.symm.continuous
  have hfs : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O := fun b =>
    r.contDiff.comp_contDiffOn ((hvs (e.symm b)).comp r.symm.contDiff.contDiffOn (fun _ hx => hx))
  intro u hu
  have hus : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ ℓ) O := by
    apply (hu.2 (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * c.val)).contDiffOn.congr
    intro x hx
    dsimp only [Function.comp_def, ℓ]
    rw [hE _ hx]
    rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    rw [← KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actual_exponential_coordinate_reindex F,
      r.apply_symm_apply]
    have hc := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
      F ζ hζ (KPSmoothActualFlowData.exponential F x) c
    rw [mul_assoc, hc.eq, ← mul_assoc]
  have hd : ∀ (f : KPContActualChamberNormalSeries.G F ζ hζ → ℂ),
      ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ ℓ) O → ∀ b x, x ∈ O →
        KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f (ℓ x) =
          fderiv ℝ (f ∘ ℓ) x (fields b x) := by
    intro f hf b x hx
    letI := actualLieChartedSpace F
    letI := actualLieGroup F
    let y := r.symm x
    let curve := fun t : ℝ => E y * KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (e.symm b) 1)
    have hex : ContMDiff (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
        (KPSmoothLocalQuotientCharts.matrixExp F) := by
      simpa only [actualLieData_exponential] using (actualLieData F).exponential_smooth
    have hex0 : KPSmoothLocalQuotientCharts.matrixExp F 0 = 1 := by
      simpa only [actualLieData_exponential] using (actualLieData F).exponential_zero
    have hcurve : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (⊤ : ℕ∞) curve := contMDiff_const.mul (hex.comp ((contDiff_id.smul contDiff_const).contMDiff))
    have h0 : curve 0 = E y := by simp [curve,hex0]
    have hymem : y ∈ E.source := hx
    have htarget : curve 0 ∈ E.target := h0 ▸ E.map_source hymem
    have hinv : DifferentiableAt ℝ (fun t => E.symm (curve t)) 0 :=
      ((hEi.contMDiffAt (E.open_target.mem_nhds htarget)).comp 0 hcurve.contMDiffAt).contDiffAt.differentiableAt (by simp)
    let z := fun t : ℝ => r (E.symm (curve t))
    have hz0 : z 0 = x := by dsimp [z]; rw [h0,E.left_inv hymem,r.apply_symm_apply]
    have hz : HasDerivAt z (fields b x) 0 := by
      have hh := r.hasFDerivAt.comp_hasDerivAt 0 hinv.hasDerivAt
      simpa only [fields, z, hv, y, curve, Function.comp_def, ContinuousLinearEquiv.coe_coe] using! hh
    have hfd : HasFDerivAt (f ∘ ℓ) (fderiv ℝ (f ∘ ℓ) x) (z 0) := by
      rw [hz0]
      exact ((hf x hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt
    have heq : (fun t => f (ℓ x * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t))) =ᶠ[𝓝 0] (fun t => (f ∘ ℓ) (z t)) := by
      have hn := hcurve.continuous.continuousAt.preimage_mem_nhds (E.open_target.mem_nhds htarget)
      filter_upwards [hn] with t ht
      congr 1
      dsimp [ℓ,z,Function.comp_def]
      rw [r.symm_apply_apply, E.right_inv ht]
      dsimp [curve]
      rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
      have hc := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
        F ζ hζ (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (e.symm b) 1)) c
      rw [KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actual_frame_ray_eq_flow,
        e.apply_symm_apply] at hc ⊢
      rw [mul_assoc, ← hc.eq, ← mul_assoc]
    exact ((hfd.comp_hasDerivAt 0 hz).congr_of_eventuallyEq heq).deriv
  refine ⟨hus, ?_⟩
  intro w
  have hi : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x)) O ∧
      ∀ x ∈ O, KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x) =
        RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ) x := by
    induction w with
    | nil => exact ⟨hus,fun _ _ => rfl⟩
    | cons b w ih =>
      have hsm := (ih.1.fderiv_of_isOpen hO (by simp)).clm_apply (hfs b)
      have he : ∀ x ∈ O, KPContActualChamberNormalSeries.rightWord F ζ hζ (b :: w) u (ℓ x) =
          fderiv ℝ (fun y => KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ y)) x (fields b x) :=
        hd _ ih.1 b
      refine ⟨hsm.congr he,?_⟩
      intro x hx
      rw [he x hx]
      change _ = fderiv ℝ (RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ)) x (fields b x)
      rw [(Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_iff_exists_mem.mpr ⟨O,hO.mem_nhds hx,ih.2⟩))]
  exact hi.2

theorem local_iwasawa_frame
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (z₀ : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F) :
    ∃ (O : Set (X F)) (V : Set (KPContSectorCoveredQuotientVocabulary.SymmetricSpace F))
      (ℓ : X F → KPContActualChamberNormalSeries.G F ζ hζ)
      (ψ : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F → X F)
      (fields : B F → X F → X F),
      IsOpen O ∧ IsOpen V ∧ z₀ ∈ V ∧
      ContinuousOn ℓ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ V ∧ Set.MapsTo ψ V O ∧
      (∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O) ∧
      (∀ x ∈ O, ∃ e : Module.Basis (B F) ℝ (X F), ∀ b, e b = fields b x) ∧
      (∀ z ∈ V, ℓ (ψ z) =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val) ∧
      (∀ (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ),
        KPMsGreenFlux.Smooth F ζ hζ u →
        ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ ℓ) O ∧
        ∀ w x, x ∈ O →
          KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x) =
            RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ) x) := by
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  let S := KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
  let g := S z₀
  obtain ⟨E,h0,hE,hEs,hEi,hvs,hbasis⟩ :=
    PGLExponential.translated_exponential_frame (actualLieData F) g
  let r := LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F
  let e := KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F
  let O := r.symm ⁻¹' E.source
  let V := S ⁻¹' E.target
  let ℓ := fun x : X F => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (E (r.symm x)) * c.val
  let ψ := fun z => r (E.symm (S z))
  let v := fun b y => deriv (fun t : ℝ => E.symm (E y *
    KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1))) 0
  let fields := fun b x => r (v (e.symm b) (r.symm x))
  have hEx (y) (hy : y ∈ E.source) : E y = g * KPSmoothLocalQuotientCharts.matrixExp F y := by
    simpa only [actualLieData_exponential] using hE y hy
  have hvg : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (v b) E.source := by
    intro b
    simpa only [v, actualLieData_exponential, actualLieData_basis] using hvs b
  have hvb (y) (hy : y ∈ E.source) : ∃ b : Module.Basis (LieIndex F) ℝ
      (KPSmoothLocalQuotientCharts.Coordinates F), ∀ i, b i = v i y := by
    simpa only [v, actualLieData_exponential, actualLieData_basis] using hbasis y hy
  have hS : ContMDiff (𝓘(ℝ, KPContSectorCoveredQuotientVocabulary.SymmetricSpace F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) S := section_smooth F ζ hζ
  have hV : IsOpen V := E.open_target.preimage hS.continuous
  have hEg : E 0 = g := by
    rw [hE 0 h0, (actualLieData F).exponential_zero, mul_one]
  refine ⟨O,V,ℓ,ψ,fields,E.open_source.preimage r.symm.continuous,hV,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change g ∈ E.target
    rw [← hEg]
    exact E.map_source h0
  · exact (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.continuousOn).comp
      (E.continuousOn.comp r.symm.continuous.continuousOn (fun _ hx => hx))
      (fun _ _ => Set.mem_univ _)).mul_const c.val
  · exact r.contDiff.comp_contDiffOn ((hEi.comp hS.contMDiffOn (fun _ hz => hz)).contDiffOn)
  · intro z hz
    change r.symm (r (E.symm (S z))) ∈ E.source
    rw [r.symm_apply_apply]
    exact E.map_target hz
  · intro b
    exact r.contDiff.comp_contDiffOn ((hvg (e.symm b)).comp r.symm.contDiff.contDiffOn (fun _ hx => hx))
  · intro x hx
    obtain ⟨b,hb⟩ := hvb (r.symm x) hx
    refine ⟨(b.map r.toLinearEquiv).reindex e,?_⟩
    intro i
    simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [hb]
  · intro z hz
    dsimp [ℓ,ψ]
    rw [r.symm_apply_apply,E.right_inv hz]
  · exact frame_words F ζ hζ c g E hEx hEi v (fun _ _ => rfl) hvg

end DedekindZetaZeroFree.KPContinuation.ChamberJetGeometry

end
