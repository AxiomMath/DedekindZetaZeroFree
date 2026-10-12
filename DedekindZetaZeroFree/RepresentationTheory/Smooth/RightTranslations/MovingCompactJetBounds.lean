module

public import DedekindZetaZeroFree.Eisenstein.Continuation.MovingCharts.LocalExponentialInverse
public import DedekindZetaZeroFree.Eisenstein.Continuation.MovingCharts.PhaseMatchedCoefficients

@[expose] public section

noncomputable section
open scoped Classical NumberField Pointwise
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingCompactGeometry

section CompactGlue

open KPContLocalNorm
open scoped Topology ContDiff BigOperators

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

private theorem base_continuous (i : Fin (H.atlas U).componentCount) :
    Continuous (KPContActualChartRestrictionDensity.basePoint F ζ hζ U R P H i) := by
  exact (H.atlas U).components.continuous.comp
    (continuous_sigmaMk.comp (continuous_quot_mk.comp
      (KPContActualChartRestrictionDensity.coordinates F).continuous))

 def restrict_group_chart
    (Q : KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H)
    (T : LocalBall (KPContActualSphericalRightFieldIdentification.groupDimension F))
    (hT0 : (0 : Space (KPContActualSphericalRightFieldIdentification.groupDimension F)) ∈ T.carrier)
    (hTQ : T.carrier ⊆ Q.T.carrier) :
    KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H :=
  { Q with
    T := T
    zero_mem := hT0
    closure_source := (Set.image_mono (closure_mono hTQ)).trans Q.closure_source
    image_inside := fun x hx => Q.image_inside x (closure_mono hTQ hx) }

theorem group_chart_restrict_neighborhood
    (Q : KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H)
    (V : Set (Space (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (hV : IsOpen V) (h0 : (0 : Space (KPContActualSphericalRightFieldIdentification.groupDimension F)) ∈ V)
    (hVQ : V ⊆ Q.T.carrier) :
    ∃ Q' : KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H,
      Q'.T.carrier ⊆ V ∧ Q'.groupLift = Q.groupLift ∧ Q'.fields = Q.fields ∧
      Q'.π = Q.π ∧ Q'.frame = Q.frame ∧ Q'.exponential.chart = Q.exponential.chart ∧
      Q'.finiteRepresentative = Q.finiteRepresentative := by
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 h0
  let T : LocalBall (KPContActualSphericalRightFieldIdentification.groupDimension F) :=
    ⟨Q.T.dimension_pos, 0, r, hr⟩
  have hTV : T.carrier ⊆ V := hrV
  let Q' := restrict_group_chart F ζ hζ U R P H Q T (Metric.mem_ball_self hr) (hTV.trans hVQ)
  exact ⟨Q', hTV, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem section_lift_finite_level
    (u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (g : G F ζ hζ) (v : U.toOpenSubgroup) :
    KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u
      (g * ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ)) =
    KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u g := by
  unfold KPContActualCommonDiskRightHolomorphy.lift
  congr 1
  unfold KPContSectorQuotientRelationsComparison.piTilde
  simp only [Function.comp_apply, KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk]
  apply congrArg (fun z => (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H u).val
    (KPContSectorQuotientRelationsComparison.e F ζ hζ U z))
  symm
  apply DoubleCoset.eq.mpr
  refine ⟨1, Subgroup.one_mem _, ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ), ?_, ?_⟩
  · apply Subgroup.subset_closure
    exact Or.inr ⟨v, v.property, rfl⟩
  · simp

theorem right_word_finite_level
    (f : G F ζ hζ → ℂ)
    (hf : ∀ g (v : U.toOpenSubgroup), f (g * ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ)) = f g)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    ∀ g (v : U.toOpenSubgroup),
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w f
      (g * ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ)) =
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w f g := by
  induction w with
  | nil => exact hf
  | cons b w ih =>
    intro g v
    unfold KPContActualSphericalRightFieldIdentification.actualRightWord
      KPContActualSphericalRightFieldIdentification.actualRight
    congr 1
    funext t
    have hc := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
      F ζ hζ (KPSmoothLocalQuotientCharts.matrixExp F
        (t • Pi.single (KPContActualSphericalRightFieldIdentification.lieEnumeration F b) 1))
      (v : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, ih]

private theorem word_congr_open {d b : ℕ} (V : Set (Space d)) (hV : IsOpen V)
    (fields : Fin b → Space d → Space d) (w : List (Fin b)) (f h : Space d → ℂ)
    (heq : Set.EqOn f h V) : Set.EqOn (KPContRightJets.rightWord fields w f)
      (KPContRightJets.rightWord fields w h) V := by
  induction w with
  | nil => exact heq
  | cons b w ih =>
    intro x hx
    exact congrArg (fun L : Space d →L[ℝ] ℂ => L (fields b x))
      (Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hV.mem_nhds hx) fun y hy => ih hy))

theorem local_moving_word_normal_form (g : G F ζ hζ) (x : ArchCoordinates F)
    (hx : x ∈ archDomain F) :
    ∃ Q : KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H,
    ∃ W : Set (G F ζ hζ × ArchCoordinates F), IsOpen W ∧ (g,x) ∈ W ∧
      W ⊆ Set.univ ×ˢ archDomain F ∧
    ∃ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H,
    ∃ ρ : Space (KPContActualSphericalRightFieldIdentification.groupDimension F) →
      Space (KPCuspLogShape.dimension F * 3),
    ∃ τ : G F ζ hζ × ArchCoordinates F → Space (KPContActualSphericalRightFieldIdentification.groupDimension F),
      ContDiffOn ℝ (⊤ : ℕ∞) ρ Q.T.carrier ∧ Set.MapsTo ρ Q.T.carrier A.ball.carrier ∧
      ContinuousOn τ W ∧ Set.MapsTo τ W Q.T.carrier ∧
      (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => τ (a,y)) {y | (a,y) ∈ W}) ∧
      (∀ n, ContinuousOn (fun p : G F ζ hζ × ArchCoordinates F =>
        iteratedFDeriv ℝ n (fun y => τ (p.1,y)) p.2) W) ∧
      (∀ p ∈ W, KPContActualCommonDiskRightHolomorphy.baseProjection F ζ hζ U (p.1 * archChart F ζ hζ p.2) =
        KPContActualChartRestrictionDensity.basePoint F ζ hζ U R P H A.component (ρ (τ p))) ∧
      ∀ (u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H),
        ContDiffOn ℝ (⊤ : ℕ∞)
          (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A) A.ball.carrier →
        ∀ w, ∀ p ∈ W,
          KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
            (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
            (p.1 * archChart F ζ hζ p.2) =
          KPContRightJets.rightWord Q.fields w
            (fun y => KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A (ρ y)) (τ p) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨e,he,Q,W,hWo,hpx,hWd,τ,hτeq,hτ0,hτc,hτQ,hτsm,hτj,hprod⟩ :=
    ActualMovingLocal.moving_inverse_local F ζ hζ U R P H g x hx
  obtain ⟨V,hVo,h0,hVQ,A,ρ,hρeq,hAcomp,hAphase,hρsm,hρA,hbase,hlift⟩ :=
    ActualMovingLocal.section_lift_chart F ζ hζ U R P H Q
  obtain ⟨Q',hQ'V,hQL,hQf,hQπ,hQframe,hQexp,hQfinite⟩ :=
    group_chart_restrict_neighborhood F ζ hζ U R P H Q V hVo h0 hVQ
  obtain ⟨W',hW'o,hpW',hW'W,hW'Q⟩ : ∃ W', IsOpen W' ∧ (g,x) ∈ W' ∧
      W' ⊆ W ∧ Set.MapsTo τ W' Q'.T.carrier := by
    have hpre : (g,x) ∈ W ∩ τ ⁻¹' Q'.T.carrier := ⟨hpx, by change τ (g,x) ∈ Q'.T.carrier; rw [hτ0]; exact Q'.zero_mem⟩
    refine ⟨W ∩ τ ⁻¹' Q'.T.carrier, ?_, hpre, Set.inter_subset_left, fun p hp => hp.2⟩
    exact hτc.isOpen_inter_preimage hWo Metric.isOpen_ball
  have hρ' := hρsm.mono hQ'V
  have hρ'A : Set.MapsTo ρ Q'.T.carrier A.ball.carrier := fun y hy => hρA (hQ'V hy)
  have htj : ∀ n, ContinuousOn (fun p : G F ζ hζ × ArchCoordinates F =>
        iteratedFDeriv ℝ n (fun y => τ (p.1,y)) p.2) W' := fun n => (hτj n).mono hW'W
  refine ⟨Q',W',hW'o,hpW',hW'W.trans hWd,A,ρ,τ,hρ',hρ'A,hτc.mono hW'W,hW'Q,
    (fun a => (hτsm a).mono (fun y hy => hW'W hy)),htj,?_,?_⟩
  · intro p hp
    obtain ⟨v,hv⟩ := hprod p (hW'W hp)
    have hlevel : KPContActualCommonDiskRightHolomorphy.baseProjection F ζ hζ U
        (Q.groupLift (τ p) * ((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ)) =
        KPContActualCommonDiskRightHolomorphy.baseProjection F ζ hζ U (Q.groupLift (τ p)) := by
      unfold KPContActualCommonDiskRightHolomorphy.baseProjection
      unfold KPContSectorQuotientRelationsComparison.piTilde
      simp only [Function.comp_apply, KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk]
      apply congrArg (fun z => KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
        (KPContSectorQuotientRelationsComparison.e F ζ hζ U z))
      symm
      apply DoubleCoset.eq.mpr
      refine ⟨1,Subgroup.one_mem _,((v : KPFiniteCuspAtlas.FiniteCover F ζ hζ) : G F ζ hζ),?_,?_⟩
      · exact Subgroup.subset_closure (Or.inr ⟨v,v.property,rfl⟩)
      · simp
    rw [hv,hlevel]
    exact hbase _ (hQ'V (hW'Q hp))
  · intro u hu w p hp
    have hscalar : Set.EqOn (fun y => KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u (Q'.groupLift y))
        (fun y => KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A (ρ y)) Q'.T.carrier := by
      intro y hy
      rw [hQL]
      exact hlift u y (hQ'V hy)
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u (Q'.groupLift y)) Q'.T.carrier :=
      (hu.comp hρ' hρ'A).congr hscalar
    obtain ⟨v,hv⟩ := hprod p (hW'W hp)
    rw [hv,right_word_finite_level F ζ hζ U
      (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
      (section_lift_finite_level F ζ hζ U R P H u) w]
    rw [← hQL, (Q'.identification).right_iteration _ hsm w _ (hW'Q hp)]
    exact word_congr_open Q'.T.carrier Metric.isOpen_ball Q'.fields w _ _ hscalar (hW'Q hp)

end CompactGlue

section WordExpansion
open KPContLocalNorm KPContRightJets
open scoped Topology ContDiff BigOperators

private lemma coord_smooth {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private lemma vector_decomp {n : ℕ} (v : Space n) :
    v = ∑ i : Fin n, (v i) • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  simp [EuclideanSpace.single, Pi.single_apply, Finset.sum_ite_eq']

private lemma pull_deriv {n m : ℕ} {U : Set (Space m)} {V : Set (Space n)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space n)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U) (himage : π '' U ⊆ V)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u V)
    (l : List (Fin n)) (g : Space m) (hg : g ∈ U) (v : Space m) :
    fderiv ℝ (fun x => coordinateDerivativeList l u (π x)) g v =
      ∑ i : Fin n, ((fderiv ℝ π g v) i : ℂ) * coordinateDerivativeList (i :: l) u (π g) := by
  have hgV := himage ⟨g, hg, rfl⟩
  have hdπ := (hπ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hdu := ((coord_smooth hV u hu l).differentiableOn (by simp)).differentiableAt (hV.mem_nhds hgV)
  change fderiv ℝ (coordinateDerivativeList l u ∘ π) g v = _
  rw [fderiv_comp g hdu hdπ]
  change fderiv ℝ (coordinateDerivativeList l u) (π g) (fderiv ℝ π g v) = _
  conv_lhs => arg 2; rw [vector_decomp (fderiv ℝ π g v)]
  rw [map_sum]
  simp [coordinateDerivativeList]

theorem smooth_word_coefficient_expansion {n m b : ℕ} {U : Set (Space m)} {V : Set (Space n)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space n) (frame : Space m → ℂ)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U)
    (hframe : ContDiffOn ℝ (⊤ : ℕ∞) frame U)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) U)
    (himage : π '' U ⊆ V) (w : List (Fin b)) :
    ∃ ts : List ((Space m → ℂ) × List (Fin n)),
      (∀ t ∈ ts, ContDiffOn ℝ (⊤ : ℕ∞) t.1 U ∧ t.2.length ≤ w.length) ∧
      ∀ u : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u V →
        ∀ g ∈ U, rightWord fields w (scalarLift π frame u) g =
          (ts.map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
  induction w with
  | nil =>
    refine ⟨[(frame, [])], ?_, ?_⟩
    · intro t ht; simp only [List.mem_singleton] at ht; subst t; exact ⟨hframe, by simp⟩
    · intro u hu g hg; simp [rightWord, scalarLift, coordinateDerivativeList]
  | cons i w ih =>
    obtain ⟨ts, hts, heq⟩ := ih
    let expand : ((Space m → ℂ) × List (Fin n)) → List ((Space m → ℂ) × List (Fin n)) :=
      fun t => (fun g => fderiv ℝ t.1 g (fields i g), t.2) ::
        (List.finRange n).map (fun j =>
          (fun g => t.1 g * ((fderiv ℝ π g (fields i g)) j : ℂ), j :: t.2))
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨hsm, hsl⟩ := hts s hs
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨j, hj, rfl⟩
      · exact ⟨(hsm.fderiv_of_isOpen hU (by simp)).clm_apply (hfields i), by simpa using hsl.trans (Nat.le_succ _)⟩
      · refine ⟨hsm.mul ?_, by simpa using Nat.succ_le_succ hsl⟩
        have hdπ : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ π) U := hπ.fderiv_of_isOpen hU (by simp)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn
          (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn (hdπ.clm_apply (hfields i))))
    · intro u hu g hg
      have hevent : rightWord fields w (scalarLift π frame u) =ᶠ[nhds g]
          (fun x => (ts.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) :=
        Filter.Eventually.mono (hU.mem_nhds hg) fun x hx => heq u hu x hx
      simp only [rightWord]
      rw [hevent.fderiv_eq]
      have term_deriv (s : (Space m → ℂ) × List (Fin n)) (hs : s ∈ ts) :
          fderiv ℝ (fun x => s.1 x * coordinateDerivativeList s.2 u (π x)) g (fields i g) =
          ((expand s).map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
        have hd1 := ((hts s hs).1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
        have hdc := ((coord_smooth hV u hu s.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩)).differentiableOn (by simp)
        dsimp only [Function.comp_def] at hdc
        rw [fderiv_fun_mul hd1 (hdc.differentiableAt (hU.mem_nhds hg))]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [pull_deriv hU hV π hπ himage u hu s.2 g hg (fields i g)]
        simp only [expand, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
        rw [← List.ofFn_eq_map, List.sum_ofFn]
        simp only [Finset.mul_sum]
        ring_nf
      have sum_deriv : ∀ ss : List ((Space m → ℂ) × List (Fin n)),
          (∀ s ∈ ss, s ∈ ts) →
          fderiv ℝ (fun x => (ss.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) g (fields i g) =
          ((ss.flatMap expand).map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
        intro ss hss
        induction ss with
        | nil => simp
        | cons s ss ih =>
          have hs := hss s (by simp)
          have hterm (t) (ht : t ∈ ss) := (hts t (hss t (by simp [ht]))).1.mul
            ((coord_smooth hV u hu t.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩))
          have list_smooth : ∀ ll : List ((Space m → ℂ) × List (Fin n)),
              (∀ t ∈ ll, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => t.1 x * coordinateDerivativeList t.2 u (π x)) U) →
              ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (ll.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) U := by
            intro ll hall
            induction ll with
            | nil => exact contDiffOn_const
            | cons t ll ih =>
              exact (hall t (by simp)).add (ih (fun z hz => hall z (by simp [hz])))
          have htail := list_smooth ss hterm
          have hhead := (hts s hs).1.mul ((coord_smooth hV u hu s.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩))
          dsimp only [Function.comp_def] at hhead
          simp only [List.map_cons, List.sum_cons]
          rw [fderiv_fun_add (hhead.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hg))
            (htail.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hg))]
          simp only [ContinuousLinearMap.add_apply, List.flatMap_cons, List.map_append, List.sum_append]
          rw [term_deriv s hs, ih (fun t ht => hss t (by simp [ht]))]
      exact sum_deriv ts (fun _ h => h)

private theorem vector_decomp' {d : ℕ} (v : Space d) :
    v = ∑ i : Fin d, v i • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  simp [EuclideanSpace.single, Pi.single_apply, Finset.sum_ite_eq']

theorem euclidean_multilinear_coordinate_expansion {d n : ℕ} (L : Space d [×n]→L[ℝ] ℂ) :
    L = ∑ a : Fin n → Fin d,
      (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) 1 |>.compContinuousLinearMap
        (fun i => EuclideanSpace.proj (a i))).smulRight
          (L (fun i => EuclideanSpace.single (a i) 1)) := by
  ext v
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smulRight_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, one_smul]
  simp only [smul_eq_mul, mul_one]
  change L v = ∑ a : Fin n → Fin d, (∏ i, v i (a i)) • L (fun i => EuclideanSpace.single (a i) 1)
  conv_lhs => arg 2; rw [show v = fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j 1 by
    funext i; exact vector_decomp' (v i)]
  rw [L.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [L.map_smul_univ]

private lemma coord_smooth' {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    (u : Space d → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (l : List (Fin d)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem iterated_coordinate (n : ℕ) {d : ℕ} (u : Space d → ℂ)
    (U : Set (Space d)) (hU : IsOpen U) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (x : Space d) (hx : x ∈ U) (a : Fin n → Fin d) :
    iteratedFDeriv ℝ n u x (fun i => EuclideanSpace.single (a i) 1) =
      coordinateDerivativeList (List.ofFn a) u x := by
  induction n generalizing x with
  | zero => simp [coordinateDerivativeList, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y
        (fun i => EuclideanSpace.single (a i.succ) 1)) =ᶠ[nhds x]
        coordinateDerivativeList (List.ofFn (fun i => a i.succ)) u :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy _
    change fderiv ℝ (fun y => iteratedFDeriv ℝ n u y
      (fun i => EuclideanSpace.single (a i.succ) 1)) x (EuclideanSpace.single (a 0) 1) = _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, coordinateDerivativeList]

private lemma coord_perm' {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    (u : Space d → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    {l r : List (Fin d)} (hp : l.Perm r) :
    Set.EqOn (coordinateDerivativeList l u) (coordinateDerivativeList r u) U := by
  induction hp with
  | nil => intro x hx; rfl
  | cons i hp ih =>
    intro x hx
    have heq : coordinateDerivativeList _ u =ᶠ[nhds x] coordinateDerivativeList _ u :=
      Filter.Eventually.mono (hU.mem_nhds hx) fun y hy => ih hy
    exact congrArg (fun f : Space d →L[ℝ] ℂ => f (EuclideanSpace.single i 1)) heq.fderiv_eq
  | swap i j l =>
    intro x hx
    let f := coordinateDerivativeList l u
    have hf := coord_smooth' hU u hu l
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
    have hd := hfd.differentiableOn (by simp)
    have hfx := (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hdx := hd.differentiableAt (hU.mem_nhds hx)
    have hsym := second_derivative_symmetric_of_eventually_of_real
      (Filter.Eventually.mono (hU.mem_nhds hx) fun y hy =>
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)).hasFDerivAt)
      hdx.hasFDerivAt (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp only [coordinateDerivativeList]
    rw [fderiv_clm_apply hdx (differentiableAt_const _),
      fderiv_clm_apply hdx (differentiableAt_const _)]
    simpa using hsym.symm
  | trans h1 h2 ih1 ih2 => exact fun x hx => (ih1 hx).trans (ih2 hx)

private lemma list_index' {d k : ℕ} (l : List (Fin d)) (hl : l.length ≤ k) :
    ∃ α : MultiIndex d k, α.directions.Perm l := by
  classical
  have hsum : ∑ i : Fin d, l.count i = l.length := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.count_cons, beq_iff_eq]
      simp [Finset.sum_add_distrib, ih (by simpa using Nat.le_of_succ_le hl)]
  let α : MultiIndex d k := ⟨fun i => ⟨l.count i, Nat.lt_succ_of_le (List.count_le_length.trans hl)⟩,
    by simpa using hsum.trans_le hl⟩
  refine ⟨α, List.perm_iff_count.mpr ?_⟩
  intro i
  simp only [MultiIndex.directions, List.count_flatMap, Function.comp_def, List.count_replicate]
  change ((List.finRange d).map (fun j => if (j == i) = true then l.count j else 0)).sum = l.count i
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

private lemma coord_append {d : ℕ} (l r : List (Fin d)) (u : Space d → ℂ) :
    coordinateDerivativeList l (coordinateDerivativeList r u) = coordinateDerivativeList (l++r) u := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, coordinateDerivativeList, ih]

theorem coordinate_list_controlled {d m : ℕ} (B : LocalBall d) (K : Set (Space d))
    (hK : IsCompact K) (hKB : K ⊆ B.carrier) (u : Space d → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (l : List (Fin d)) (hl : l.length ≤ m)
    (x : Space d) (hx : x ∈ K) :
    ‖coordinateDerivativeList l u x‖ ≤ compactJetSeminorm m B K hK hKB u hu := by
  obtain ⟨α,hα⟩ := list_index' l hl
  rw [← coord_perm' Metric.isOpen_ball u hu hα (hKB hx)]
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (ContinuousMap.norm_coe_le_norm (compactJet B K hKB u hu α) ⟨x,hx⟩).trans
    (norm_le_pi_norm (compactJet (m := m) B K hKB u hu) α)

theorem iterated_coordinate_controlled {d m : ℕ} (B : LocalBall d) (K : Set (Space d))
    (hK : IsCompact K) (hKB : K ⊆ B.carrier) (u : Space d → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (l : List (Fin d))
    (n : ℕ) (hn : n + l.length ≤ m) (x : Space d) (hx : x ∈ K) :
    ‖iteratedFDeriv ℝ n (coordinateDerivativeList l u) x‖ ≤
      (∑ a : Fin n → Fin d,
        ‖(ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (1 : ℝ) |>.compContinuousLinearMap
          (fun i => EuclideanSpace.proj (a i)))‖) * compactJetSeminorm m B K hK hKB u hu := by
  rw [euclidean_multilinear_coordinate_expansion (iteratedFDeriv ℝ n (coordinateDerivativeList l u) x)]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [ContinuousMultilinearMap.norm_smulRight,
    iterated_coordinate n _ _ Metric.isOpen_ball (coord_smooth' Metric.isOpen_ball u hu l) x (hKB hx) a,
    coord_append]
  exact mul_le_mul_of_nonneg_left (coordinate_list_controlled B K hK hKB u hu _
    (by simpa only [List.length_append,List.length_ofFn] using hn) x hx) (norm_nonneg _)

end WordExpansion

section JetComposition
open KPContLocalNorm
open scoped Topology ContDiff BigOperators
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem spatial_jet_comp_formula {A : Type*} [TopologicalSpace A]
    (W : Set (A × E)) (hW : IsOpen W) (U : Set F) (hU : IsOpen U)
    (τ : A × E → F) (hτ : Set.MapsTo τ W U)
    (hsm : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => τ (a,y)) {y | (a,y) ∈ W})
    (f : F → V) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (n : ℕ)
    (p : A × E) (hp : p ∈ W) :
    iteratedFDeriv ℝ n (fun y => f (τ (p.1,y))) p.2 =
      FormalMultilinearSeries.taylorComp (fun k => iteratedFDeriv ℝ k f (τ p))
        (fun k => iteratedFDeriv ℝ k (fun y => τ (p.1,y)) p.2) n := by
  let S : Set E := {y | (p.1,y) ∈ W}
  have hS : IsOpen S := hW.preimage (continuous_const.prodMk continuous_id)
  have ht : Set.MapsTo (fun y => τ (p.1,y)) S U := fun y hy => hτ hy
  have hh := (hf.ftaylorSeriesWithin hU.uniqueDiffOn).comp
    ((hsm p.1).ftaylorSeriesWithin hS.uniqueDiffOn) ht
  have heq := hh.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) (by simp)
    hS.uniqueDiffOn hp
  rw [iteratedFDerivWithin_of_isOpen n hS hp] at heq
  apply heq.symm.trans
  congr 1
  · funext k
    exact iteratedFDerivWithin_of_isOpen k hU (hτ hp)
  · funext k
    exact iteratedFDerivWithin_of_isOpen k hS hp

theorem continuousOn_taylorComp {A : Type*} [TopologicalSpace A]
    (W : Set A) (q : A → FormalMultilinearSeries ℝ F V)
    (p : A → FormalMultilinearSeries ℝ E F)
    (hq : ∀ n, ContinuousOn (fun a => q a n) W)
    (hp : ∀ n, ContinuousOn (fun a => p a n) W) (n : ℕ) :
    ContinuousOn (fun a => (q a).taylorComp (p a) n) W := by
  unfold FormalMultilinearSeries.taylorComp
  apply continuousOn_finset_sum
  intro c _
  let L := c.compAlongOrderedFinpartitionL ℝ E F V
  have hL : ContinuousOn (fun a => L (q a c.length)) W :=
    L.continuous.comp_continuousOn (hq _)
  have hP : ContinuousOn (fun a => fun i : Fin c.length => p a (c.partSize i)) W :=
    continuousOn_pi.mpr fun i => hp _
  exact continuous_eval.comp_continuousOn (hL.prodMk hP)

theorem joint_spatial_jets_comp {A : Type*} [TopologicalSpace A]
    (W : Set (A × E)) (hW : IsOpen W) (U : Set F) (hU : IsOpen U)
    (τ : A × E → F) (hτ : Set.MapsTo τ W U) (hτc : ContinuousOn τ W)
    (hsm : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => τ (a,y)) {y | (a,y) ∈ W})
    (hj : ∀ n, ContinuousOn (fun p : A × E =>
      iteratedFDeriv ℝ n (fun y => τ (p.1,y)) p.2) W)
    (f : F → V) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (n : ℕ) :
    ContinuousOn (fun p : A × E => iteratedFDeriv ℝ n (fun y => f (τ (p.1,y))) p.2) W := by
  have hfc (k : ℕ) : ContinuousOn (fun p : A × E => iteratedFDeriv ℝ k f (τ p)) W := by
    have hh := hf.continuousOn_iteratedFDerivWithin (m := k) (by simp) hU.uniqueDiffOn
    have hh' : ContinuousOn (iteratedFDeriv ℝ k f) U := hh.congr (iteratedFDerivWithin_of_isOpen k hU).symm
    exact hh'.comp hτc hτ
  have hc := continuousOn_taylorComp W
    (fun p k => iteratedFDeriv ℝ k f (τ p))
    (fun p k => iteratedFDeriv ℝ k (fun y => τ (p.1,y)) p.2) hfc hj n
  apply hc.congr
  intro p hp
  exact spatial_jet_comp_formula W hW U hU τ hτ hsm f hf n p hp

end JetComposition

section WeightedBounds
open KPContLocalNorm
open scoped Topology ContDiff BigOperators
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace A]

private lemma coord_sm {d : ℕ} (B : LocalBall d) (u : Space d → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (l : List (Fin d)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) B.carrier := by
  induction l with
  | nil => exact hu
  | cons i l ih => exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const

private lemma semi_nonneg {d m : ℕ} (B : LocalBall d) (K : Set (Space d))
    (hK : IsCompact K) (hKB : K ⊆ B.carrier) (u : Space d → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) :
    0 ≤ compactJetSeminorm m B K hK hKB u hu := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact norm_nonneg _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem compact_weighted_coordinate_jet_bound {d : ℕ}
    (W : Set (A × E)) (hW : IsOpen W) (K : Set (A × E)) (hK : IsCompact K) (hKW : K ⊆ W)
    (B : LocalBall d) (ψ : A × E → Space d) (hψ : ContinuousOn ψ W)
    (hψB : Set.MapsTo ψ W B.carrier)
    (hψsm : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ψ (a,y)) {y | (a,y) ∈ W})
    (hψj : ∀ i, ContinuousOn (fun p : A × E => iteratedFDeriv ℝ i (fun y => ψ (p.1,y)) p.2) W)
    (c : A × E → ℂ)
    (hcsm : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => c (a,y)) {y | (a,y) ∈ W})
    (hcj : ∀ i, ContinuousOn (fun p : A × E => iteratedFDeriv ℝ i (fun y => c (p.1,y)) p.2) W)
    (l : List (Fin d)) (n m : ℕ) (hnm : n + l.length ≤ m) :
    ∃ M : ℝ, 0 < M ∧ ∀ (u : Space d → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier), ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n (fun y => c (p.1,y) * coordinateDerivativeList l u (ψ (p.1,y))) p.2‖ ≤
        M * compactJetSeminorm m B (ψ '' K)
          (hK.image_of_continuousOn (hψ.mono hKW)) (fun z hz => by
            obtain ⟨p,hp,rfl⟩ := hz; exact hψB (hKW hp)) u hu := by
  let T (i : ℕ) : ℝ := ∑ a : Fin i → Fin d,
    ‖(ContinuousMultilinearMap.mkPiRing ℝ (Fin i) (1 : ℝ) |>.compContinuousLinearMap
      (fun j => EuclideanSpace.proj (a j)))‖
  let Tsum : ℝ := ∑ i ∈ Finset.range (n+1), T i
  have hT (i : ℕ) : 0 ≤ T i := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hTsum : 0 ≤ Tsum := Finset.sum_nonneg fun _ _ => hT _
  have hjc : ContinuousOn (fun p : A × E =>
      ∑ i ∈ Finset.range (n+1), (‖iteratedFDeriv ℝ i (fun y => c (p.1,y)) p.2‖ +
        ‖iteratedFDeriv ℝ i (fun y => ψ (p.1,y)) p.2‖)) K :=
    continuousOn_finset_sum _ fun i _ => ((hcj i).mono hKW).norm.add (((hψj i).mono hKW).norm)
  obtain ⟨b,hb⟩ := hK.exists_bound_of_continuousOn hjc
  let D : ℝ := max 0 b + 1
  have hD : 1 ≤ D := by dsimp [D]; exact le_add_of_nonneg_left (le_max_left _ _)
  have hDj (p : A × E) (hp : p ∈ K) (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun y => c (p.1,y)) p.2‖ ≤ D ∧
      ‖iteratedFDeriv ℝ i (fun y => ψ (p.1,y)) p.2‖ ≤ D := by
    have hsumle := hb p hp
    have hs : ‖iteratedFDeriv ℝ i (fun y => c (p.1,y)) p.2‖ +
        ‖iteratedFDeriv ℝ i (fun y => ψ (p.1,y)) p.2‖ ≤ D := by
      apply (Finset.single_le_sum (fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_range.mpr (show i < n+1 by omega))).trans
      exact (le_abs_self _).trans ((hb p hp).trans
        ((le_max_right 0 b).trans (le_add_of_nonneg_right zero_le_one)))
    exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans hs,
      (le_add_of_nonneg_left (norm_nonneg _)).trans hs⟩
  let M₀ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * D * ((n-i).factorial * Tsum * D^(n-i))
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨M₀+1, add_pos_of_nonneg_of_pos hM₀ zero_lt_one, ?_⟩
  intro u hu p hp
  let J := compactJetSeminorm m B (ψ '' K)
    (hK.image_of_continuousOn (hψ.mono hKW)) (fun z hz => by
      obtain ⟨p,hp,rfl⟩ := hz; exact hψB (hKW hp)) u hu
  have hJ : 0 ≤ J := semi_nonneg _ _ _ _ _ _
  let S : Set E := {y | (p.1,y) ∈ W}
  have hS : IsOpen S := hW.preimage (continuous_const.prodMk continuous_id)
  have hpS : p.2 ∈ S := hKW hp
  have hmaps : Set.MapsTo (fun y => ψ (p.1,y)) S B.carrier := fun y hy => hψB hy
  have hsψ := hψsm p.1
  have hsu := coord_sm B u hu l
  have hcomp (q : ℕ) (hq : q ≤ n) :
      ‖iteratedFDeriv ℝ q (fun y => coordinateDerivativeList l u (ψ (p.1,y))) p.2‖ ≤
        q.factorial * (Tsum * J) * D^q := by
    have hout (i : ℕ) (hi : i ≤ q) :
        ‖iteratedFDerivWithin ℝ i (coordinateDerivativeList l u) B.carrier (ψ p)‖ ≤ Tsum * J := by
      rw [iteratedFDerivWithin_of_isOpen i (show IsOpen B.carrier from Metric.isOpen_ball) (hψB (hKW hp))]
      apply (iterated_coordinate_controlled B (ψ '' K) _ _ u hu l i (show i+l.length ≤ m by omega) (ψ p) ⟨p,hp,rfl⟩).trans
      change T i * J ≤ Tsum * J
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hT j) (Finset.mem_range.mpr (by omega))) hJ
    have hin (i : ℕ) (hi1 : 1 ≤ i) (hiq : i ≤ q) :
        ‖iteratedFDerivWithin ℝ i (fun y => ψ (p.1,y)) S p.2‖ ≤ D^i := by
      rw [iteratedFDerivWithin_of_isOpen i hS hpS]
      exact (hDj p hp i (hiq.trans hq)).2.trans (le_self_pow₀ hD (by omega))
    have hh := norm_iteratedFDerivWithin_comp_le hsu hsψ (by simp : (q : ℕ∞ω) ≤ (⊤ : ℕ∞))
      (show IsOpen B.carrier from Metric.isOpen_ball).uniqueDiffOn hS.uniqueDiffOn hmaps hpS hout hin
    rw [iteratedFDerivWithin_of_isOpen q hS hpS] at hh
    exact hh
  have hmul := norm_iteratedFDerivWithin_mul_le (hcsm p.1) (hsu.comp hsψ hmaps)
    hS.uniqueDiffOn hpS (by simp : (n : ℕ∞ω) ≤ (⊤ : ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hS hpS] at hmul
  have hrewrite (i : ℕ) :
      iteratedFDerivWithin ℝ i (fun y => c (p.1,y)) S p.2 = iteratedFDeriv ℝ i (fun y => c (p.1,y)) p.2 :=
    iteratedFDerivWithin_of_isOpen i hS hpS
  have hrewrite' (i : ℕ) :
      iteratedFDerivWithin ℝ i (fun y => coordinateDerivativeList l u (ψ (p.1,y))) S p.2 =
      iteratedFDeriv ℝ i (fun y => coordinateDerivativeList l u (ψ (p.1,y))) p.2 :=
    iteratedFDerivWithin_of_isOpen i hS hpS
  have hmul' : ‖iteratedFDeriv ℝ n
      (fun y => c (p.1,y) * coordinateDerivativeList l u (ψ (p.1,y))) p.2‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => c (p.1,y)) p.2‖ *
        ‖iteratedFDeriv ℝ (n-i) (fun y => coordinateDerivativeList l u (ψ (p.1,y))) p.2‖ := by
    apply hmul.trans
    apply Finset.sum_le_sum
    intro i hi
    rw [hrewrite]
    rw [iteratedFDerivWithin_of_isOpen (n-i) hS hpS]
    exact le_rfl
  apply hmul'.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * D * ((n-i).factorial * (Tsum * J) * D^(n-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simp only [Finset.mem_range] at hi; omega
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hDj p hp i hin).1 (by positivity))
        (hcomp (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = M₀ * J := by
      dsimp [M₀]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (M₀+1) * J := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hJ

private lemma smooth_list_sum {d : ℕ} (B : LocalBall d) (u : Space d → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (W : Set (A × E))
    (ψ : A × E → Space d) (hψB : Set.MapsTo ψ W B.carrier)
    (hψsm : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ψ (a,y)) {y | (a,y) ∈ W})
    (ts : List ((A × E → ℂ) × List (Fin d)))
    (hts : ∀ t ∈ ts, ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => t.1 (a,y)) {y | (a,y) ∈ W}) :
    ∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (ts.map (fun t => t.1 (a,y) * coordinateDerivativeList t.2 u (ψ (a,y)))).sum)
      {y | (a,y) ∈ W} := by
  have hc (l : List (Fin d)) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) B.carrier := by
    induction l with
    | nil => exact hu
    | cons i l ih => exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
  induction ts with
  | nil => intro a; exact contDiffOn_const
  | cons t ts ih =>
    intro a
    exact ((hts t (by simp) a).mul ((hc t.2).comp (hψsm a) (fun y hy => hψB hy))).add
      (ih (fun t ht => hts t (by simp [ht])) a)

set_option maxHeartbeats 600000 in
theorem compact_list_coordinate_jet_bound {d : ℕ}
    (W : Set (A × E)) (hW : IsOpen W) (K : Set (A × E)) (hK : IsCompact K) (hKW : K ⊆ W)
    (B : LocalBall d) (ψ : A × E → Space d) (hψ : ContinuousOn ψ W)
    (hψB : Set.MapsTo ψ W B.carrier)
    (hψsm : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ψ (a,y)) {y | (a,y) ∈ W})
    (hψj : ∀ i, ContinuousOn (fun p : A × E => iteratedFDeriv ℝ i (fun y => ψ (p.1,y)) p.2) W)
    (ts : List ((A × E → ℂ) × List (Fin d)))
    (hts : ∀ t ∈ ts, (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => t.1 (a,y)) {y | (a,y) ∈ W}) ∧
      (∀ i, ContinuousOn (fun p : A × E => iteratedFDeriv ℝ i (fun y => t.1 (p.1,y)) p.2) W))
    (n m : ℕ) (hnm : ∀ t ∈ ts, n + t.2.length ≤ m) :
    ∃ M : ℝ, 0 < M ∧ ∀ (u : Space d → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier), ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n (fun y => (ts.map
        (fun t => t.1 (p.1,y) * coordinateDerivativeList t.2 u (ψ (p.1,y)))).sum) p.2‖ ≤
        M * compactJetSeminorm m B (ψ '' K)
          (hK.image_of_continuousOn (hψ.mono hKW)) (fun z hz => by
            obtain ⟨p,hp,rfl⟩ := hz; exact hψB (hKW hp)) u hu := by
  induction ts with
  | nil =>
    refine ⟨1,zero_lt_one,?_⟩
    intro u hu p hp
    simp only [List.map_nil,List.sum_nil,iteratedFDeriv_zero_fun]
    have hJ : 0 ≤ compactJetSeminorm m B (ψ '' K)
        (hK.image_of_continuousOn (hψ.mono hKW)) (fun z hz => by
          obtain ⟨p,hp,rfl⟩ := hz; exact hψB (hKW hp)) u hu := by
      letI : CompactSpace (ψ '' K) := isCompact_iff_compactSpace.mp (hK.image_of_continuousOn (hψ.mono hKW))
      exact norm_nonneg _
    simpa using hJ
  | cons t ts ih =>
    obtain ⟨M,hM,hMb⟩ := compact_weighted_coordinate_jet_bound W hW K hK hKW B ψ hψ hψB
      hψsm hψj t.1 (hts t (by simp)).1 (hts t (by simp)).2 t.2 n m (hnm t (by simp))
    obtain ⟨N,hN,hNb⟩ := ih (fun t ht => hts t (by simp [ht])) (fun t ht => hnm t (by simp [ht]))
    refine ⟨M+N,add_pos hM hN,?_⟩
    intro u hu p hp
    have hS : IsOpen {y | (p.1,y) ∈ W} := hW.preimage (continuous_const.prodMk continuous_id)
    have htail := smooth_list_sum B u hu W ψ hψB hψsm ts (fun t ht => (hts t (by simp [ht])).1) p.1
    have hc (l : List (Fin d)) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) B.carrier := by
      induction l with
      | nil => exact hu
      | cons i l ih => exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
    have hhead := ((hts t (by simp)).1 p.1).mul ((hc t.2).comp (hψsm p.1) (fun y hy => hψB hy))
    simp only [List.map_cons,List.sum_cons]
    have hadd := iteratedFDeriv_add_apply (i := n) (hhead p.2 (hKW hp) |>.contDiffAt (hS.mem_nhds (hKW hp)) |>.of_le (by simp))
      (htail p.2 (hKW hp) |>.contDiffAt (hS.mem_nhds (hKW hp)) |>.of_le (by simp))
    change iteratedFDeriv ℝ n (fun y => t.1 (p.1,y) * coordinateDerivativeList t.2 u (ψ (p.1,y)) +
      (ts.map (fun t => t.1 (p.1,y) * coordinateDerivativeList t.2 u (ψ (p.1,y)))).sum) p.2 = _ at hadd
    rw [hadd]
    exact (norm_add_le _ _).trans ((add_le_add (hMb u hu p hp) (hNb u hu p hp)).trans_eq (add_mul _ _ _).symm)

end WeightedBounds

section FinalAssembly
open KPContLocalNorm KPContRightJets
open scoped Topology ContDiff BigOperators

private theorem combo_expansion {d m b : ℕ} {U : Set (Space m)} {V : Set (Space d)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space d)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) U)
    (himage : Set.MapsTo π U V) (D : List (ℂ × List (Fin b))) :
    ∃ ts : List ((Space m → ℂ) × List (Fin d)),
      (∀ t ∈ ts, ContDiffOn ℝ (⊤ : ℕ∞) t.1 U ∧ t.2.length ≤ combinationOrder D) ∧
      ∀ u : Space d → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u V → ∀ x ∈ U,
        rightCombination fields D (fun y => u (π y)) x =
          (ts.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum := by
  induction D with
  | nil => exact ⟨[], by simp, fun u hu x hx => rfl⟩
  | cons t D ih =>
    obtain ⟨ts,hts,heq⟩ := smooth_word_coefficient_expansion hU hV π (fun _ => 1)
      fields hπ contDiffOn_const hf (by rintro _ ⟨x,hx,rfl⟩; exact himage hx) t.2
    obtain ⟨rs,hrs,hreq⟩ := ih
    let ss := ts.map (fun s => ((fun x => t.1 * s.1 x),s.2)) ++ rs
    refine ⟨ss,?_,?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
        exact ⟨contDiffOn_const.mul (hts q hq).1, (hts q hq).2.trans (by simp [combinationOrder])⟩
      · exact ⟨(hrs s hs).1, (hrs s hs).2.trans (by simp [combinationOrder])⟩
    · intro u hu x hx
      have hw := heq u hu x hx
      have hsl : scalarLift π (fun _ => (1 : ℂ)) u = (fun y => u (π y)) := by
        funext y; exact one_mul _
      rw [hsl] at hw
      change t.1 * rightWord fields t.2 (fun y => u (π y)) x +
        rightCombination fields D (fun y => u (π y)) x = _
      rw [hw,hreq u hu x hx]
      simp only [ss,List.map_append,List.sum_append,List.map_map,Function.comp_def]
      rw [← List.sum_map_mul_left]
      congr 2
      apply List.map_congr_left
      intro q hq
      exact (mul_assoc t.1 (q.1 x) (coordinateDerivativeList q.2 u (π x))).symm

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

set_option maxHeartbeats 600000 in
private theorem local_compact_bound
    (D : KPContActualCommonDiskRightHolomorphy.Combination F) (n : ℕ)
    (g : G F ζ hζ) (x : ArchCoordinates F) (hx : x ∈ archDomain F) :
    ∃ W : Set (G F ζ hζ × ArchCoordinates F), IsOpen W ∧ (g,x) ∈ W ∧
    ∃ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H,
    ∃ ψ : G F ζ hζ × ArchCoordinates F → Space (KPCuspLogShape.dimension F * 3),
      ∃ hψ : ContinuousOn ψ W, ∃ hψA : Set.MapsTo ψ W A.ball.carrier,
      (∀ p ∈ W, KPContActualCommonDiskRightHolomorphy.baseProjection F ζ hζ U (p.1 * archChart F ζ hζ p.2) =
        KPContActualChartRestrictionDensity.basePoint F ζ hζ U R P H A.component (ψ p)) ∧
      ∀ K : Set (G F ζ hζ × ArchCoordinates F), ∀ hK : IsCompact K, ∀ hKW : K ⊆ W,
      ∃ M : ℝ, 0 < M ∧
        ∀ u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H,
        ∀ hu : ContDiffOn ℝ (⊤ : ℕ∞)
          (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A) A.ball.carrier,
        ∀ p ∈ K,
          ‖iteratedFDeriv ℝ n
            (fun y => KPContActualCommonDiskRightHolomorphy.rightCombination F ζ hζ D
              (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
              (p.1 * archChart F ζ hζ y)) p.2‖ ≤
            M * compactJetSeminorm (n + combinationOrder D) A.ball (ψ '' K)
              (hK.image_of_continuousOn (hψ.mono hKW))
              (by rintro _ ⟨p,hp,rfl⟩; exact hψA (hKW hp))
              (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A) hu := by
  obtain ⟨Q,W,hWo,hgx,hWd,A,ρ,τ,hρ,hρA,hτ,hτQ,hτsm,hτj,hbase,hwords⟩ :=
    local_moving_word_normal_form F ζ hζ U R P H g x hx
  let ψ : G F ζ hζ × ArchCoordinates F → Space (KPCuspLogShape.dimension F * 3) := ρ ∘ τ
  have hψ : ContinuousOn ψ W := hρ.continuousOn.comp hτ hτQ
  have hψA : Set.MapsTo ψ W A.ball.carrier := hρA.comp hτQ
  have hψsm (a : G F ζ hζ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ψ (a,y)) {y | (a,y) ∈ W} :=
    hρ.comp (hτsm a) (fun y hy => hτQ hy)
  have hψj (i : ℕ) : ContinuousOn (fun p : G F ζ hζ × ArchCoordinates F =>
      iteratedFDeriv ℝ i (fun y => ψ (p.1,y)) p.2) W :=
    joint_spatial_jets_comp W hWo Q.T.carrier Metric.isOpen_ball τ hτQ hτ hτsm hτj ρ hρ i
  obtain ⟨ts,hts,heq⟩ := combo_expansion Metric.isOpen_ball Metric.isOpen_ball ρ Q.fields
    hρ Q.identification.fields_smooth hρA D
  let ss : List (((G F ζ hζ × ArchCoordinates F) → ℂ) × List (Fin (KPCuspLogShape.dimension F * 3))) :=
    ts.map (fun t => (t.1 ∘ τ,t.2))
  have hss : ∀ s ∈ ss,
      (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => s.1 (a,y)) {y | (a,y) ∈ W}) ∧
      (∀ i, ContinuousOn (fun p : G F ζ hζ × ArchCoordinates F => iteratedFDeriv ℝ i (fun y => s.1 (p.1,y)) p.2) W) := by
    intro s hs
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
    refine ⟨fun a => (hts t ht).1.comp (hτsm a) (fun y hy => hτQ hy), ?_⟩
    intro i
    exact joint_spatial_jets_comp W hWo Q.T.carrier Metric.isOpen_ball τ hτQ hτ hτsm hτj t.1 (hts t ht).1 i
  have hlen : ∀ s ∈ ss, n + s.2.length ≤ n + combinationOrder D := by
    intro s hs
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
    exact Nat.add_le_add_left (hts t ht).2 n
  have hidentity (u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
      (hu : ContDiffOn ℝ (⊤ : ℕ∞) (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A) A.ball.carrier)
      (p : G F ζ hζ × ArchCoordinates F) (hp : p ∈ W) :
      KPContActualCommonDiskRightHolomorphy.rightCombination F ζ hζ D
        (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
        (p.1 * archChart F ζ hζ p.2) =
      (ss.map (fun t => t.1 p * coordinateDerivativeList t.2
        (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A) (ψ p))).sum := by
    have hw := hwords u hu
    have hD : KPContActualCommonDiskRightHolomorphy.rightCombination F ζ hζ D
        (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
        (p.1 * archChart F ζ hζ p.2) =
        rightCombination Q.fields D (fun y => KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A (ρ y)) (τ p) := by
      unfold KPContActualCommonDiskRightHolomorphy.rightCombination rightCombination
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [hw t.2 p hp]
    rw [hD,heq _ hu _ (hτQ hp)]
    simp only [ss,List.map_map,Function.comp_def,ψ]
  refine ⟨W,hWo,hgx,A,ψ,hψ,hψA,hbase,?_⟩
  intro K hK hKW
  obtain ⟨M,hM,hMb⟩ := compact_list_coordinate_jet_bound W hWo K hK hKW A.ball ψ hψ hψA
    hψsm hψj ss hss n (n+combinationOrder D) hlen
  refine ⟨M,hM,?_⟩
  intro u hu p hp
  have hS : IsOpen {y | (p.1,y) ∈ W} := hWo.preimage (continuous_const.prodMk continuous_id)
  have hevent : (fun y => KPContActualCommonDiskRightHolomorphy.rightCombination F ζ hζ D
      (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
      (p.1 * archChart F ζ hζ y)) =ᶠ[nhds p.2]
      (fun y => (ss.map (fun t => t.1 (p.1,y) * coordinateDerivativeList t.2
        (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A) (ψ (p.1,y)))).sum) :=
    Filter.eventually_of_mem (hS.mem_nhds (hKW hp)) fun y hy => hidentity u hu (p.1,y) hy
  rw [(hevent.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  exact hMb _ hu p hp

end FinalAssembly

set_option maxHeartbeats 1200000 in
theorem actual_moving_compact_joint_jet_bound
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (C : Set (G F ζ hζ)) (hC : IsCompact C)
    (X : Set (ArchCoordinates F)) (hX : IsCompact X) (hXd : X ⊆ archDomain F)
    (D : KPContActualCommonDiskRightHolomorphy.Combination F) (n : ℕ) :
    ∃ (cover : KPContActualCommonDiskRightHolomorphy.CompactBaseCover
        F ζ hζ U R P H (C * (archChart F ζ hζ '' X))) (M : ℝ),
      0 < M ∧
      ∀ (u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
        (hu : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
          (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (cover.chart j))
          (cover.chart j).ball.carrier),
        ∀ g ∈ C, ∀ x ∈ X,
          ‖iteratedFDeriv ℝ n
            (fun y => KPContActualCommonDiskRightHolomorphy.rightCombination F ζ hζ D
              (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u)
              (g * archChart F ζ hζ y)) x‖ ≤
            M * ∑ j, KPContLocalNorm.compactJetSeminorm
              (n + KPContRightJets.combinationOrder D) (cover.chart j).ball
              (cover.compact j) (cover.isCompact j) (cover.contained j)
              (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (cover.chart j))
              (hu j) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let S : Set (G F ζ hζ × ArchCoordinates F) := C ×ˢ X
  have hS : IsCompact S := hC.prod hX
  choose W hWo hpW A ψ hψ hψA hbase hbound using
    (fun p : S => local_compact_bound F ζ hζ U R P H D n p.val.1 p.val.2 (hXd p.property.2))
  have hcover : S ⊆ ⋃ p : S, W p := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hpW ⟨p,hp⟩⟩
  obtain ⟨t,ht⟩ := hS.elim_finite_subcover W hWo hcover
  obtain ⟨K,hK,hKW,hSK⟩ := hS.finite_compact_cover t W (fun p _ => hWo p) ht
  let e : Fin t.card ≃ t := t.equivFin.symm
  let charts : Fin t.card → KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H := fun j => A (e j).val
  let compacts : Fin t.card → Set (KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :=
    fun j => ψ (e j).val '' K (e j).val
  have hcp (j : Fin t.card) : IsCompact (compacts j) :=
    (hK _).image_of_continuousOn ((hψ _).mono (hKW _))
  have hcb (j : Fin t.card) : compacts j ⊆ (charts j).ball.carrier := by
    rintro _ ⟨p,hp,rfl⟩
    exact hψA _ (hKW _ hp)
  let base := ⋃ j : Fin t.card,
    KPContActualChartRestrictionDensity.basePoint F ζ hζ U R P H (charts j).component '' compacts j
  have hbc : IsCompact base := isCompact_iUnion (fun j =>
    (hcp j).image (base_continuous F ζ hζ U R P H (charts j).component))
  have hpcover (p : G F ζ hζ × ArchCoordinates F) (hp : p ∈ S) :
      ∃ j : Fin t.card, p ∈ K (e j).val := by
    rw [hSK] at hp
    obtain ⟨q,hqt,hpq⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨j,hj⟩ := e.surjective ⟨q,hqt⟩
    exact ⟨j,by simpa only [hj] using hpq⟩
  have hproject : KPContActualCommonDiskRightHolomorphy.baseProjection F ζ hζ U ''
      (C * (archChart F ζ hζ '' X)) ⊆ base := by
    rintro z ⟨g,hg,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := hg
    obtain ⟨x,hx,rfl⟩ := hb
    obtain ⟨j,hj⟩ := hpcover (a,x) ⟨ha,hx⟩
    rw [hbase _ (a,x) (hKW _ hj)]
    exact Set.mem_iUnion.mpr ⟨j,⟨ψ (e j).val (a,x),⟨(a,x),hj,rfl⟩,rfl⟩⟩
  let cover : KPContActualCommonDiskRightHolomorphy.CompactBaseCover
      F ζ hζ U R P H (C * (archChart F ζ hζ '' X)) :=
    ⟨t.card,charts,compacts,hcp,hcb,base,hbc,rfl,hproject⟩
  choose b hb hbnd using (fun j : Fin t.card => hbound (e j).val (K (e j).val) (hK _) (hKW _))
  let M := (∑ j, b j) + 1
  refine ⟨cover,M,by
    dsimp [M]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hb i).le)) zero_lt_one,?_⟩
  intro u hu g hg x hx
  obtain ⟨j,hj⟩ := hpcover (g,x) ⟨hg,hx⟩
  let Q : Fin t.card → ℝ := fun i => KPContLocalNorm.compactJetSeminorm
    (n+KPContRightJets.combinationOrder D) (charts i).ball (compacts i) (hcp i) (hcb i)
    (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u (charts i)) (hu i)
  have hQ (i : Fin t.card) : 0 ≤ Q i := by
    letI : CompactSpace (compacts i) := isCompact_iff_compactSpace.mp (hcp i)
    exact norm_nonneg _
  have hQj : Q j ≤ ∑ i, Q i := Finset.single_le_sum (fun i _ => hQ i) (Finset.mem_univ j)
  have hbj : b j ≤ M := (Finset.single_le_sum (fun i _ => (hb i).le) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_right zero_le_one)
  exact (hbnd j u (hu j) (g,x) hj).trans
    (mul_le_mul hbj hQj (hQ j) (by
      dsimp [M]
      exact add_nonneg (Finset.sum_nonneg (fun i _ => (hb i).le)) zero_le_one))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingCompactGeometry

end
