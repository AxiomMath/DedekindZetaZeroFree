module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.SmoothDescent
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.IsometryNaturality

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffLocalCommutator

open KPContActualCutoffSmoothDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev d := Module.finrank ℚ F / 2

private theorem smooth_height (d : ℕ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : KPArch.Space d => KPArch.height (z i)) := by
  exact (contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)).exp
private theorem smooth_density (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (KPArch.volumeDensity d) := by
  unfold KPArch.volumeDensity
  apply contDiff_prod
  intro i _
  exact ((smooth_height d i).inv (fun z => Real.exp_ne_zero _)).pow 2
private theorem density_ne_zero (d : ℕ) (z : KPArch.Space d) :
    KPArch.volumeDensity d z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (inv_ne_zero (Real.exp_ne_zero _))
 theorem smooth_laplacian (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (KPContActualSphericalFlatStage.localLaplacian d f) := by
  unfold KPContActualSphericalFlatStage.localLaplacian
  apply ContDiff.neg
  apply ContDiff.mul
  · exact (Complex.ofRealCLM.contDiff.comp (smooth_density d)).inv
      (fun z => Complex.ofReal_ne_zero.mpr (density_ne_zero d z))
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    have hw : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : KPArch.Space d => KPContActualSphericalFlatStage.inverseMetricWeight d y i j) := by
      unfold KPContActualSphericalFlatStage.inverseMetricWeight
      split_ifs
      · exact contDiff_const
      · exact (smooth_height d i).pow 2
    have hc := (Complex.ofRealCLM.contDiff.comp ((smooth_density d).mul hw)).mul
      ((hf.fderiv_right (by simp)).clm_apply
        (contDiff_const (c := KPContActualSphericalFlatStage.coordinateDirection d i j)))
    exact (hc.fderiv_right (by simp)).clm_apply contDiff_const

 def meanCLM (d : ℕ) : KPArch.Space d →L[ℝ] ℝ :=
  (d : ℝ)⁻¹ • ∑ i : Fin d, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj i)
private theorem meanCLM_apply (d : ℕ) (z : KPArch.Space d) :
    meanCLM d z = KPCuspLogShape.meanHeight d z := by
  simp [meanCLM, KPCuspLogShape.meanHeight, div_eq_mul_inv, mul_comm]
private theorem mean_direction (d : ℕ) (i : Fin d) (j : Fin 3) :
    meanCLM d (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j) =
      if j = 2 then (d : ℝ)⁻¹ else 0 := by
  rw [meanCLM_apply]
  have he (a : ℂ × ℝ) : (∑ x : Fin d, ((Pi.single i a : KPArch.Space d) x).2) = a.2 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  fin_cases j <;> simp [KPCuspLogShape.meanHeight,
    KPContFlatCuspCasimirSpecialization.coordinateDirection, he]
private theorem radial_arch (d : ℕ) (hd : d ≠ 0) (w : ℝ → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (z : KPArch.Space d) :
    KPContActualSphericalFlatStage.localLaplacian d
      (fun y => w (KPCuspLogShape.meanHeight d y)) z =
      KPIncomingCasimir.radialLaplacian d w (KPCuspLogShape.meanHeight d z) := by
  have hmeq : ⇑(meanCLM d) = KPCuspLogShape.meanHeight d := funext (meanCLM_apply d)
  have hmean : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) :=
    hmeq ▸ (meanCLM d).contDiff
  have hdw : Differentiable ℝ w := hw.differentiable (by simp)
  have hdw' : Differentiable ℝ (deriv w) :=
    (hw.of_le (by simp)).differentiable_deriv_two
  have hfirst (i : Fin d) (j : Fin 3) (y : KPArch.Space d) :
      fderiv ℝ (fun y => w (KPCuspLogShape.meanHeight d y)) y
        (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j) =
      if j = 2 then ((d : ℝ)⁻¹ : ℂ) * deriv w (KPCuspLogShape.meanHeight d y) else 0 := by
    have hm := (meanCLM d).hasFDerivAt (x := y)
    rw [hmeq] at hm
    have hh := (hdw (KPCuspLogShape.meanHeight d y)).hasDerivAt.hasFDerivAt.comp y hm
    change HasFDerivAt (fun y => w (KPCuspLogShape.meanHeight d y)) _ y at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      mean_direction, smul_eq_mul, Complex.real_smul]
    split_ifs <;> simp [mul_comm]
  have hsecond (i : Fin d) (j : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (fun y => w (KPCuspLogShape.meanHeight d y)) y
        (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j)) z
        (KPContFlatCuspCasimirSpecialization.coordinateDirection d i j) =
      if j = 2 then ((d : ℝ)⁻¹ : ℂ)^2 * deriv (deriv w) (KPCuspLogShape.meanHeight d z) else 0 := by
    simp_rw [hfirst]
    split_ifs with hj
    · have hm := (meanCLM d).hasFDerivAt (x := z)
      rw [hmeq] at hm
      have hh := ((hdw' (KPCuspLogShape.meanHeight d z)).hasDerivAt.hasFDerivAt.comp z hm).const_mul ((d : ℝ)⁻¹ : ℂ)
      change HasFDerivAt (fun y => ((d : ℝ)⁻¹ : ℂ) * deriv w (KPCuspLogShape.meanHeight d y)) _ z at hh
      rw [hh.fderiv]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply, mean_direction, hj, if_true,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    · simp
  change KPContFlatCuspCasimirSpecialization.Δloc d _ z = _
  have hsm : ContDiff ℝ 2 (fun y => w (KPCuspLogShape.meanHeight d y)) := by
    simpa only [Function.comp_def] using (hw.comp hmean).of_le (by simp)
  rw [KPContFlatCuspCasimirSpecialization.Δloc_coordinate_expression d _ hsm z]
  simp_rw [hsecond]
  simp only [hfirst]
  simp only [Fin.reduceEq, if_true, if_false, zero_add, mul_zero, sub_zero,
    smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold KPIncomingCasimir.radialLaplacian
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  <;> ring

private theorem localLaplacian_congr (d : ℕ) (f g : KPArch.Space d → ℂ)
    (z : KPArch.Space d) (he : f =ᶠ[nhds z] g) :
    KPContActualSphericalFlatStage.localLaplacian d f z =
      KPContActualSphericalFlatStage.localLaplacian d g z := by
  unfold KPContActualSphericalFlatStage.localLaplacian
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hd := he.eventuallyEq_nhds.mono (fun y hy => hy.fderiv_eq (𝕜 := ℝ))
  have hc : (fun y => ((KPArch.volumeDensity d y *
        KPContActualSphericalFlatStage.inverseMetricWeight d y i j : ℝ) : ℂ) *
        fderiv ℝ f y (KPContActualSphericalFlatStage.coordinateDirection d i j)) =ᶠ[nhds z]
      (fun y => ((KPArch.volumeDensity d y *
        KPContActualSphericalFlatStage.inverseMetricWeight d y i j : ℝ) : ℂ) *
        fderiv ℝ g y (KPContActualSphericalFlatStage.coordinateDirection d i j)) :=
    hd.mono (fun y hy => by dsimp only; rw [hy])
  exact congrArg (fun A : KPArch.Space d →L[ℝ] ℂ =>
    A (KPContActualSphericalFlatStage.coordinateDirection d i j)) hc.fderiv_eq

private theorem localLaplacian_zero (n : ℕ) :
    KPContActualSphericalFlatStage.localLaplacian n 0 = 0 := by
  funext z
  unfold KPContActualSphericalFlatStage.localLaplacian
  simp only [fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply, mul_zero]
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, Finset.sum_const_zero,
    mul_zero, neg_zero]

def Δloc (w : SmoothSections F ζ hζ C R P H U) :
    SmoothSections F ζ hζ C R P H U :=
  ⟨fun i => ⟨fun z => KPContActualSphericalFlatStage.localLaplacian
    (KPCuspLogShape.dimension F) (w.val i).val z, by
      refine ⟨?_, ?_⟩
      · intro z
        rcases (H.atlas (level F ζ hζ C R P H U)).line i |>.rank with hzero | htop
        · have hwzero : (w.val i).val = 0 := by
            funext y
            have hy := (w.val i).property.1 y
            rwa [hzero] at hy
          rw [hwzero]
          simp only [KPContActualSphericalFlatStage.localLaplacian, fderiv_zero,
            Pi.zero_apply, ContinuousLinearMap.zero_apply, mul_zero,
            fderiv_const, Finset.sum_const_zero, neg_zero]
          simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, Finset.sum_const_zero,
            mul_zero, neg_zero]
          exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ
            (level F ζ hζ C R P H U)).zero_mem
        · rw [htop]
          trivial
      · intro γ z
        obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
          (γ : KPCuspArithmetic.PGL2 F)
        let g : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
          fun j => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding A
        have ha (y : KPArch.Space (KPCuspLogShape.dimension F)) :
            KPArch.productAction _ g y = (γ : KPCuspArithmetic.PGL2 F) • y := by
          change _ = KPCuspSiegel.action F _ y
          rw [← hA, KPCuspSiegel.action_mk]
          rfl
        have hc : (fun y => (w.val i).val (KPArch.productAction _ g y)) =ᶠ[nhds z]
            fun y => (KPCuspGenuineMonodromy.chi F ζ hζ
              ((H.atlas (level F ζ hζ C R P H U)).line i |>.rho γ) : ℂ) * (w.val i).val y := by
          apply Filter.Eventually.of_forall
          intro y
          dsimp only
          rw [ha]
          exact (w.val i).property.2 γ y
        have he := KPContArchLaplacianNaturality.equivariant _ g _ z _ (w.property i) hc
        rw [ha] at he
        exact he⟩,
      fun i => smooth_laplacian _ _ (w.property i)⟩

private theorem rational_laplacian (γ : KPCuspArithmetic.PGL2 F)
    (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian _ (fun y => f (γ • y)) z =
      KPContActualSphericalFlatStage.localLaplacian _ f (γ • z) := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  let g := fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A
  have ha (y : KPArch.Space (KPCuspLogShape.dimension F)) :
      KPArch.productAction _ g y = γ • y := by
    change _ = KPCuspSiegel.action F _ y
    rw [← hA, KPCuspSiegel.action_mk]
    rfl
  have he := KPContArchLaplacianNaturality.pullback _ g f hf z
  simpa only [ha] using he

theorem localLaplacian_chart
    (w : SmoothSections F ζ hζ C R P H U)
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H))
    (x : KPContCotangentOverlapRationalBranches.omega a) :
    KPContActualSectorSmoothTestModules.sectionFields
      (Δloc F ζ hζ C R P H U w).val a x =
    HyperbolicChart.laplacian (d F)
      (KPContActualSectorTestDifferentialDescent.liftExtension a
        (KPContActualSectorSmoothTestModules.sectionFields w.val a)) x.val := by
  let A := KPContCotangentActualOverlap.labeledA
    (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
  have he : KPContActualSectorTestDifferentialDescent.liftExtension a
      (KPContActualSectorSmoothTestModules.sectionFields w.val a) =ᶠ[nhds x.val]
        fun y => (w.val a.component).val (A y) := by
    have ho : IsOpen (KPContCotangentOverlapRationalBranches.omega a) :=
      a.domain_open.preimage KPContActualGlobalGreen.contDiff_labeledA.continuous
    filter_upwards [ho.mem_nhds x.property] with y hy
    simp only [KPContActualSectorTestDifferentialDescent.liftExtension, dif_pos hy]
    simp [KPContActualSectorSmoothTestModules.sectionFields,
      KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.ChartKind.representative, A]
  rw [KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) he]
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F)
    (KPCuspLogShape.dimension F) (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
    (w.val a.component).val (w.property a.component) x.val
  simp only [KPContActualSectorSmoothTestModules.sectionFields,
    KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
    KPContCotangentActualOverlap.ChartKind.representative, map_one, Units.val_one,
    one_mul, one_smul]
  exact hb

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
variable (f : ℂ → S)
variable (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (D : Descent F ζ hζ C R P H U ι B Ω f χ)

private theorem cutoff_zero_nhds (a : Cusps F ζ hζ C R P H U)
    (χ : KPCutoffSource.SmoothCuspCutoff T)
    (x : Covered F ζ hζ C R P H U) (hx : x ∉ ends F ζ hζ C R P H U B a) :
    ∀ᶠ y in nhds x, y ∈ ends F ζ hζ C R P H U B a →
      χ.toFun (height F ζ hζ C R P H U B a y) = 0 ∧
      deriv χ.toFun (height F ζ hζ C R P H U B a y) = 0 ∧
      deriv (deriv χ.toFun) (height F ζ hζ C R P H U B a y) = 0 := by
  let q := KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
  let E := KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H B.τ a
  have hc : Continuous q := KPContSectorQuotientRelationsComparison.q_continuous _ _ _ _
  by_cases hxcl : q x ∈ closure E
  · have hxf : q x ∈ frontier E := by
      rw [frontier, (B.open_ends a).interior_eq]
      exact ⟨hxcl, hx⟩
    obtain ⟨V, hV, hxV, hz⟩ := B.boundary_zero_extension a (q x) hxf
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV)] with y hy he
    have he' : q y ∈ KPContActualCollarBuffer.endSet F ζ hζ
        (level F ζ hζ C R P H U) R P H B.τ a := he
    simpa only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he',
      KPContActualCutoffSmoothDescent.height, q]
      using hz χ (q y) hy
  · filter_upwards [hc.continuousAt.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hxcl)] with y hy he
    exact False.elim (hy (subset_closure he))
private theorem cutoff_commutator_zero_nhds (s : ℂ) (hs : s ∈ Ω)
    (x : Covered F ζ hζ C R P H U) (hx : ∀ a, x ∉ ends F ζ hζ C R P H U B a) :
    ∀ᶠ y in nhds x,
      scalar F ζ hζ C R P H U (D.cutoff s) y = 0 ∧
      scalar F ζ hζ C R P H U (D.commutator s) y = 0 := by
  have hz : ∀ᶠ y in nhds x, ∀ a, y ∈ ends F ζ hζ C R P H U B a →
      (χ a).toFun (height F ζ hζ C R P H U B a y) = 0 ∧
      deriv (χ a).toFun (height F ζ hζ C R P H U B a y) = 0 ∧
      deriv (deriv (χ a).toFun) (height F ζ hζ C R P H U B a y) = 0 :=
    Filter.eventually_all.mpr (fun a => cutoff_zero_nhds F ζ hζ C R P H U B a (χ a) x (hx a))
  filter_upwards [hz] with y hy
  rw [D.cutoff_formula s hs, D.commutator_formula s hs]
  constructor
  · unfold cutoffScalar KPCutoffSource.cutoffSum
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with he
    · dsimp only
      rw [(hy a he).1, Complex.ofReal_zero, zero_mul]
    · rfl
  · unfold commutatorScalar KPCutoffSource.commutatorSum
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with he
    · simp only [KPCutoffSource.incomingCommutatorMultiplier,
        (hy a he).2.1, (hy a he).2.2, Complex.ofReal_zero, mul_zero, add_zero, sub_self, zero_mul]
    · rfl

private theorem scalar_phase_value (w : SmoothSections F ζ hζ C R P H U)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (ε : rootsOfUnity 3 F) (z : KPCuspGenuineMonodromy.SymmetricSpace F) :
    scalar F ζ hζ C R P H U w
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U)) (z, KPCuspGenuineMonodromy.central F ζ hζ ε *
          (H.atlas (level F ζ hζ C R P H U)).representative i)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (w.val i).val z := by
  have he := KPContSectorSmoothFramesSupport.phase_lift_formula F ζ hζ
    (level F ζ hζ C R P H U) R P H
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).symm w).val i ε z
  change scalar F ζ hζ C R P H U w _ = _ at he
  have hrec : KPContSectorScalarLineAlgebra.S F ζ hζ
      (level F ζ hζ C R P H U) R P H
      ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
        (level F ζ hζ C R P H U) R P H).symm w).val = w.val :=
    congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).apply_symm_apply w)
  rw [hrec] at he
  exact he

private theorem scalar_laplacian_zero_of_zero_nhds
    (w : SmoothSections F ζ hζ C R P H U)
    (x : Covered F ζ hζ C R P H U)
    (hx : scalar F ζ hζ C R P H U w =ᶠ[nhds x] 0) :
    scalar F ζ hζ C R P H U (Δloc F ζ hζ C R P H U w) x = 0 := by
  obtain ⟨⟨i,p⟩, hp⟩ :=
    (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ
      (level F ζ hζ C R P H U) R P H).surjective x
  obtain ⟨⟨m,z⟩, rfl⟩ := Quotient.exists_rep p
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective
    (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (level F ζ hζ C R P H U)) m
  change (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ
    (level F ζ hζ C R P H U) R P H) ⟨i, Quotient.mk _
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ
        (level F ζ hζ C R P H U) ε, z)⟩ = x at hp
  rw [KPContSectorPhaseComponentCharts.componentHomeomorph_mk] at hp
  let Q := fun y : KPArch.Space (KPCuspLogShape.dimension F) =>
    Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
      (level F ζ hζ C R P H U)) (y, KPCuspGenuineMonodromy.central F ζ hζ ε *
        (H.atlas (level F ζ hζ C R P H U)).representative i)
  have hc : Continuous Q := continuous_quot_mk.comp (continuous_id.prodMk continuous_const)
  have hh : (fun y => (w.val i).val y) =ᶠ[nhds z] 0 := by
    have htz : Filter.Tendsto Q (nhds z) (nhds x) := by
      have h := hc.continuousAt (x := z)
      change Filter.Tendsto Q (nhds z) (nhds (Q z)) at h
      change Q z = x at hp
      rwa [hp] at h
    have he := hx.comp_tendsto htz
    filter_upwards [he] with y hy
    have hv := scalar_phase_value F ζ hζ C R P H U w i ε y
    change scalar F ζ hζ C R P H U w (Q y) = 0 at hy
    rw [hv] at hy
    exact (mul_eq_zero.mp hy).resolve_left (by
      exact Units.ne_zero (KPCuspGenuineMonodromy.chi F ζ hζ ε))
  rw [← hp, scalar_phase_value]
  change (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
    KPContActualSphericalFlatStage.localLaplacian _ (w.val i).val z = 0
  rw [localLaplacian_congr _ _ 0 z hh, localLaplacian_zero]
  exact mul_zero _

private theorem cutoff_laplacian_commutator_zero_nhds (s : ℂ) (hs : s ∈ Ω)
    (x : Covered F ζ hζ C R P H U) (hx : ∀ a, x ∉ ends F ζ hζ C R P H U B a) :
    ∃ V ∈ nhds x, ∀ y ∈ V,
      scalar F ζ hζ C R P H U (D.cutoff s) y = 0 ∧
      scalar F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s)) y = 0 ∧
      scalar F ζ hζ C R P H U (D.commutator s) y = 0 := by
  have he := cutoff_commutator_zero_nhds F ζ hζ C R P H U ι B Ω f χ D s hs x hx
  obtain ⟨V, hz, hV, hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V, hV.mem_nhds hxV, ?_⟩
  intro y hy
  refine ⟨(hz hy).1, ?_, (hz hy).2⟩
  apply scalar_laplacian_zero_of_zero_nhds
  filter_upwards [hV.mem_nhds hy] with z hzV
  exact (hz hzV).1

private theorem incomingValue_radial (a : Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (z : KPCuspCharts.Coordinates F) :
    incomingValue F ζ hζ C R P H U ι a s v z =
      KPIncomingCasimir.heightFactor (d F) s z.2 *
        KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U a
          (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v) := by
  rw [incomingValue_height_formula F ζ hζ C R P H U ι a s hs v z,
    KPContFlatCuspIncomingEvaluation.b_formula,
    KPContFlatCuspIncomingEvaluation.zeroProjection_formula]

include B in
private theorem radial_cutoff_equation (a : Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ Ω) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    let t := KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z
    let b := KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U a
      (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s))
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (fun y => KPCutoffSource.radialCutoff (d F) (χ a).toFun s b
        (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) y)) z -
      KPContinuation.spectralCoordinate (d F : ℤ) s *
        KPCutoffSource.radialCutoff (d F) (χ a).toFun s b t =
      KPCutoffSource.incomingCommutatorMultiplier (d F) (χ a).toFun s t *
        (KPIncomingCasimir.heightFactor (d F) s t * b) := by
  dsimp only
  rw [radial_arch _ (Nat.ne_of_gt B.positive_dimension) _
    (KPCutoffSource.radialCutoff_smooth _ (χ a) _ _) z]
  conv_lhs => arg 1; arg 1; rw [B.dimension_formula]
  exact KPCutoffSource.radialCutoff_equation _
    (B.dimension_formula ▸ B.positive_dimension) (χ a) _ _ _

include hΩ in
private theorem cutoff_cusp_laplacian (s : ℂ) (hs : s ∈ Ω)
    (a : Cusps F ζ hζ C R P H U) (p : KPCuspCharts.Coordinates F) (hp : B.τ < p.2) :
    frameValue F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s)) a p -
      KPContinuation.spectralCoordinate (d F : ℤ) s *
        frameValue F ζ hζ C R P H U (D.cutoff s) a p =
      frameValue F ζ hζ C R P H U (D.commutator s) a p := by
  let b := KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U a
    (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s (f s))
  let γ := ((H.atlas (level F ζ hζ C R P H U)).cuspAtlas a.1).representative a.2
  let Q := KPCuspCharts.toArchHomeomorph F B.positive_dimension
  have hg : (fun y : KPArch.Space (KPCuspLogShape.dimension F) =>
      ((D.cutoff s).val a.1).val (γ • y)) =ᶠ[nhds (KPCuspCharts.toArch F p)]
      fun y => KPCutoffSource.radialCutoff (d F) (χ a).toFun s b
        (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) y) := by
    have ho : IsOpen {y : KPArch.Space (KPCuspLogShape.dimension F) | B.τ < (Q.symm y).2} :=
      isOpen_lt continuous_const (continuous_snd.comp Q.symm.continuous)
    have hm : KPCuspCharts.toArch F p ∈ {y | B.τ < (Q.symm y).2} := by
      change B.τ < (Q.symm (Q p)).2
      simpa using hp
    filter_upwards [ho.mem_nhds hm] with y hy
    have h := D.cutoff_frame s hs a (Q.symm y) hy
    rw [incomingValue_radial F ζ hζ C R P H U ι a s (hΩ hs) (f s) (Q.symm y)] at h
    have hQ : KPCuspCharts.toArch F (Q.symm y) = y := Q.apply_symm_apply y
    change ((D.cutoff s).val a.1).val (γ • KPCuspCharts.toArch F (Q.symm y)) = _ at h
    rw [hQ] at h
    change ((D.cutoff s).val a.1).val (γ • y) =
      ((χ a).toFun (KPCuspLogShape.meanHeight _ y) : ℂ) *
        KPIncomingCasimir.heightFactor (d F) s (KPCuspLogShape.meanHeight _ y) * b
    change ((D.cutoff s).val a.1).val (γ • y) =
      ((χ a).toFun (KPCuspLogShape.meanHeight _ y) : ℂ) *
        (KPIncomingCasimir.heightFactor (d F) s (KPCuspLogShape.meanHeight _ y) * b) at h
    exact h.trans (mul_assoc _ _ _).symm
  have hr := rational_laplacian F γ ((D.cutoff s).val a.1).val
    ((D.cutoff s).property a.1) (KPCuspCharts.toArch F p)
  have he := localLaplacian_congr _ _ _ (KPCuspCharts.toArch F p) hg
  rw [hr] at he
  change frameValue F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s)) a p = _ at he
  rw [he, D.cutoff_frame s hs a p hp, D.commutator_frame s hs a p hp,
    incomingValue_radial F ζ hζ C R P H U ι a s (hΩ hs) (f s) p]
  have ht := KPCuspCharts.toArch_meanHeight F B.positive_dimension p
  have hx := radial_cutoff_equation F ζ hζ C R P H U ι B Ω f χ a s hs
    (KPCuspCharts.toArch F p)
  dsimp only at hx
  rw [ht] at hx
  simpa only [KPCutoffSource.radialCutoff, b, mul_assoc] using hx

private theorem scalar_cusp_value (w : SmoothSections F ζ hζ C R P H U)
    (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (p : KPCuspCharts.Coordinates F) :
    scalar F ζ hζ C R P H U w (coveredPoint F ζ hζ C R P H U a ε p) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * frameValue F ζ hζ C R P H U w a p :=
  scalar_phase_value F ζ hζ C R P H U w a.1 ε
    (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ
      (level F ζ hζ C R P H U) R P H a.1 a.2 p)

include hΩ in
private theorem scalar_equation (s : ℂ) (hs : s ∈ Ω)
    (x : Covered F ζ hζ C R P H U) :
    scalar F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s)) x -
      KPContinuation.spectralCoordinate (d F : ℤ) s *
        scalar F ζ hζ C R P H U (D.cutoff s) x =
      scalar F ζ hζ C R P H U (D.commutator s) x := by
  by_cases hx : ∃ a, x ∈ ends F ζ hζ C R P H U B a
  · obtain ⟨l⟩ := (endLift_iff_mem_end F ζ hζ C R P H U B x).mpr hx
    rw [← l.point]
    simp only [scalar_cusp_value]
    have he := cutoff_cusp_laplacian F ζ hζ C R P H U ι B Ω hΩ f χ D
      s hs l.cusp l.coordinates l.high
    calc _ = (KPCuspGenuineMonodromy.chi F ζ hζ l.sheet : ℂ) *
        (frameValue F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s))
          l.cusp l.coordinates - KPContinuation.spectralCoordinate (d F : ℤ) s *
          frameValue F ζ hζ C R P H U (D.cutoff s) l.cusp l.coordinates) := by ring
      _ = _ := congrArg _ he
  · have hn : ∀ a, x ∉ ends F ζ hζ C R P H U B a := fun a ha => hx ⟨a, ha⟩
    obtain ⟨V, hV, hz⟩ := cutoff_laplacian_commutator_zero_nhds F ζ hζ C R P H U
      ι B Ω f χ D s hs x hn
    obtain ⟨hC, hΔ, hh⟩ := hz x (mem_of_mem_nhds hV)
    rw [hC, hΔ, hh, mul_zero, sub_self]

include hΩ in
private theorem section_equation (s : ℂ) (hs : s ∈ Ω) :
    Δloc F ζ hζ C R P H U (D.cutoff s) -
      KPContinuation.spectralCoordinate (d F : ℤ) s • D.cutoff s = D.commutator s := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  funext z
  have he := scalar_equation F ζ hζ C R P H U ι B Ω hΩ f χ D s hs
    (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
      (level F ζ hζ C R P H U)) (z, (H.atlas (level F ζ hζ C R P H U)).representative i))
  have hp (w : SmoothSections F ζ hζ C R P H U) :
      scalar F ζ hζ C R P H U w
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U)) (z, (H.atlas (level F ζ hζ C R P H U)).representative i)) =
        (w.val i).val z := by
    simpa using scalar_phase_value F ζ hζ C R P H U w i 1 z
  simp only [hp] at he
  exact he

structure Properties : Prop where

  equation : ∀ s ∈ Ω,
    Δloc F ζ hζ C R P H U (D.cutoff s) -
      KPContinuation.spectralCoordinate (d F : ℤ) s • D.cutoff s = D.commutator s

  chart_equation : ∀ (s : ℂ), s ∈ Ω →
    ∀ (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H))
      (x : KPContCotangentOverlapRationalBranches.omega a),
    HyperbolicChart.laplacian (d F)
      (KPContActualSectorTestDifferentialDescent.liftExtension a
        (KPContActualSectorSmoothTestModules.sectionFields (D.cutoff s).val a)) x.val -
      KPContinuation.spectralCoordinate (d F : ℤ) s *
        KPContActualSectorSmoothTestModules.sectionFields (D.cutoff s).val a x =
      KPContActualSectorSmoothTestModules.sectionFields (D.commutator s).val a x

  end_equation : ∀ (s : ℂ) (hs : s ∈ Ω) (a : Cusps F ζ hζ C R P H U)
      (z : KPCuspCharts.Coordinates F), B.τ < z.2 →
    frameValue F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s)) a z -
      KPContinuation.spectralCoordinate (d F : ℤ) s *
        frameValue F ζ hζ C R P H U (D.cutoff s) a z =
    KPCutoffSource.incomingCommutatorMultiplier (d F) (χ a).toFun s z.2 *
      (Complex.exp ((d F : ℂ) * ((4 : ℂ) / 3 + 2 * s) * (z.2 : ℂ)) *
        ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s (hΩ hs)
          (f s)).val z.1.2).val (QuotientAddGroup.mk z.1.1))

  off_ends_locally : ∀ s ∈ Ω, ∀ x : Covered F ζ hζ C R P H U,
    (∀ a, x ∉ ends F ζ hζ C R P H U B a) →
    ∃ V ∈ nhds x, ∀ y ∈ V,
      scalar F ζ hζ C R P H U (D.cutoff s) y = 0 ∧
      scalar F ζ hζ C R P H U (Δloc F ζ hζ C R P H U (D.cutoff s)) y = 0 ∧
      scalar F ζ hζ C R P H U (D.commutator s) y = 0

end DedekindZetaZeroFree.KPContActualCutoffLocalCommutator

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cutoff_local_commutator
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T)
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι B Ω f χ) :
    KPContActualCutoffLocalCommutator.Properties F ζ hζ C R P H U ι B Ω hΩ f χ D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact KPContActualCutoffLocalCommutator.section_equation F ζ hζ C R P H U
      ι B Ω hΩ f χ D
  · intro s hs a x
    rw [← KPContActualCutoffLocalCommutator.localLaplacian_chart]
    have he := KPContActualCutoffLocalCommutator.section_equation F ζ hζ C R P H U
      ι B Ω hΩ f χ D s hs
    have hv := congrArg (fun w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U =>
      KPContActualSectorSmoothTestModules.sectionFields w.val a x) he
    simp only [KPContActualSectorSmoothTestModules.sectionFields,
      KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.ChartKind.representative, map_one, Units.val_one,
      one_mul, one_smul] at hv ⊢
    exact hv
  · intro s hs a z hz
    have he := KPContActualCutoffLocalCommutator.cutoff_cusp_laplacian F ζ hζ C R P H U
      ι B Ω hΩ f χ D s hs a z hz
    refine he.trans ?_
    rw [D.commutator_frame s hs a z hz,
      KPContActualCutoffSmoothDescent.incomingValue_height_formula F ζ hζ C R P H U
        ι a s (hΩ hs) (f s) z]
    rfl
  · exact KPContActualCutoffLocalCommutator.cutoff_laplacian_commutator_zero_nhds F ζ hζ
      C R P H U ι B Ω f χ D

end DedekindZetaZeroFree

end
