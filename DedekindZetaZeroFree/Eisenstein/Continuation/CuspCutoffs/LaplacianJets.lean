module

public import DedekindZetaZeroFree.Analysis.Holomorphy.SpatialJets.PositiveHyperbolicLaplacian
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberJets.NormalSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.SmoothSupportedSections
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.AllCuspSource

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff BigOperators
open Topology

namespace DedekindZetaZeroFree.KPContActualAllCuspSourceLaplacianJets

open Filter
set_option maxHeartbeats 2400000
open KPContSectorSmoothFramesSupport KPContCotangentActualOverlap

section CoordinateConversion
open KPContLocalNorm
private theorem list_index {n : ℕ} (l : List (Fin n)) :
    ∃ m, ∃ α : MultiIndex n m, l.Perm α.directions := by
  classical
  let m := ∑ i : Fin n, l.count i
  let α : MultiIndex n m := ⟨fun i => ⟨l.count i, by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (l.count j)) (Finset.mem_univ i)
    dsimp [m]; omega⟩, by simp [m]⟩
  refine ⟨m, α, List.perm_iff_count.mpr ?_⟩
  intro i
  rw [MultiIndex.directions, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [α, Function.comp_def, List.count_replicate]

private theorem flat_word (n : ℕ) (w : List (Fin n)) (u : Space n → ℂ) :
    RightFrame.PullbackWords.directionalWord (fun i _ => EuclideanSpace.single i (1:ℝ)) w u =
      coordinateDerivativeList w u := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [RightFrame.PullbackWords.directionalWord, coordinateDerivativeList, ih]

private theorem compact_coordinate_jets_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (B : LocalBall d) (O : Set ℂ)
    (g : ℂ → Space d → ℂ) (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O)
    (D : Set E) (hD : IsOpen D) (ψ : E → Space d)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ D) (hψB : Set.MapsTo ψ D B.carrier)
    (K : Set E) (hK : IsCompact K) (hKD : K ⊆ D) (n : ℕ) (v : Fin n → E) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : K,
      j z x = iteratedFDerivWithin ℝ n (g z ∘ ψ) D x.val v := by
  apply KPContActualChamberCasimirJets.normalSeries_transported_compact_jet
    B.carrier Metric.isOpen_ball D hD
    (fun i _ => EuclideanSpace.single i (1:ℝ)) (fun _ => contDiffOn_const)
    (fun x _ => ⟨(EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
      fun i => EuclideanSpace.basisFun_apply (Fin d) ℝ i⟩)
    ψ hψ hψB O g hg.1 ?_ K hK hKD n v
  intro w C hC hCB
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨m,α,hperm⟩ := list_index w
  obtain ⟨j,hj,hjval⟩ := hg.2 C hC hCB m
  let L : CompactJets C m →L[ℂ] C(C,ℂ) := ContinuousLinearMap.proj α
  refine ⟨fun z => L (j z), L.differentiable.comp_differentiableOn hj, ?_⟩
  intro z hz x
  rw [flat_word, WeakJets.Raw.coordinateDerivativeList_perm_on hperm (hg.1 z hz) (hCB x.property)]
  exact hjval z hz α x
end CoordinateConversion

section SourceCalculus
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {C : KPGlobalTorusInducingPlan.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {U : KPMsRationalCompactCrossPairing.Level F ζ hζ}
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable {ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U}
variable {f : ℂ → S} {T : ℝ}
variable {buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T}
variable {χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T}
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

 def original (b : Bool) (z : ℂ) :=
  if b then source.descent.commutator z else source.descent.cutoff z

private theorem component_holomorphy (b : Bool) (O : Set ℂ) (hO : IsOpen O)
    (hOΩ : O ⊆ KPContinuation.spectralDomain)
    (i : Fin (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).componentCount) :
    ∀ (K : Set (M F)) (hK : IsCompact K), K ⊆ Set.univ →
      ∀ (n : ℕ) (v : Fin n → M F),
        letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
        ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : K,
          j z x = iteratedFDerivWithin ℝ n
            (fun y => ((original source b z).val i).val (labeledA (placeEquiv F ζ hζ) y))
            Set.univ x.val v := by
  let ψ : M F → KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3) :=
    fun x => WithLp.toLp 2 (fun k =>
      x (finProdFinEquiv.symm k |>.1 |> (placeEquiv F ζ hζ).symm,
        (finProdFinEquiv.symm k).2))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro k
    exact (EuclideanSpace.proj (𝕜 := ℝ)
      ((placeEquiv F ζ hζ).symm (finProdFinEquiv.symm k).1,
        (finProdFinEquiv.symm k).2)).contDiff
  have hcoords : ∀ x, KPContActualChartRestrictionDensity.coordinates F (ψ x) =
      labeledA (placeEquiv F ζ hζ) x := by
    intro x
    have hp : ∀ i j, (finProdFinEquiv.symm (finProdFinEquiv (i,j)) :
        Fin (KPCuspLogShape.dimension F) × Fin 3) = (i,j) := fun _ _ => Equiv.symm_apply_apply _ _
    funext i
    apply Prod.ext
    · apply Complex.ext <;> change x ((placeEquiv F ζ hζ).symm
        (finProdFinEquiv.symm (finProdFinEquiv (i,_))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (i,_))).2) = _
      all_goals rw [hp]; simp [labeledA, CotangentLogCoframe.A]
    · change x ((placeEquiv F ζ hζ).symm
        (finProdFinEquiv.symm (finProdFinEquiv (i,2))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (i,2))).2) = _
      rw [hp]
      rfl
  let g := fun t => KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
    (original source b t) i
    (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) 1)
  have hvalue : ∀ t x, g t (ψ x) =
      ((original source b t).val i).val (labeledA (placeEquiv F ζ hζ) x) := by
    intro t x
    unfold g KPContActualAllCuspSource.chartCoefficient
    rw [KPContActualChartRestrictionDensity.frameCoefficient_class]
    simp only [map_one, Circle.coe_one, one_mul]
    rw [show KPContSectorScalarLineAlgebra.S F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
      (((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm
        (original source b t)).val) = (original source b t).val from
        congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).apply_symm_apply _)]
    rw [hcoords]
  intro K hK hKω n v
  apply KPContActualChamberCasimirJets.normalSeries_compact_family_of_local O hO Set.univ
    (fun t x => iteratedFDerivWithin ℝ n
      (fun y => ((original source b t).val i).val (labeledA (placeEquiv F ζ hζ) y))
      Set.univ x v) ?_ K hK hKω
  intro x hx
  let p := labeledA (placeEquiv F ζ hζ) x
  let a := Classical.choice (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
    (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H i p)
  have hd : IsOpen (KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H i p a) :=
    a.isOpen.preimage (KPContActualChartRestrictionDensity.coordinates F).continuous
  have hxD : ψ x ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H i p a := by
    change KPContActualChartRestrictionDensity.coordinates F (ψ x) ∈ a.neighborhood
    rw [hcoords]
    exact a.center_mem
  obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hd.mem_nhds hxD)
  let B : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3) :=
    ⟨by simpa [KPCuspLogShape.dimension] using
      mul_pos (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2 (by norm_num : (0:ℕ)<3),
      ψ x, r/2, by positivity⟩
  have hBD : KPContLocalCubeEmbedding.closedCarrier B ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H i p a :=
    (Metric.closedBall_subset_ball (by dsimp [B]; linarith)).trans hrD
  have hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O := by
    have hh := source.local_holomorphy i p a
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) 1) B hBD
    have hh' : KPCutoffSource.ChartSmoothHolomorphicOn B g KPContinuation.spectralDomain := by
      cases b <;> simp only [g, original, Bool.false_eq_true, if_false, if_true]
      · exact hh.1
      · exact hh.2.1
    exact ⟨fun t hz => hh'.1 t (hOΩ hz),
      fun C hC hCB m => by
        obtain ⟨j,hj,hjval⟩ := hh'.2 C hC hCB m
        exact ⟨j,hj.mono hOΩ, fun t hz => hjval t (hOΩ hz)⟩⟩
  let D := ψ ⁻¹' B.carrier
  have hD : IsOpen D := Metric.isOpen_ball.preimage hψ.continuous
  have hxD' : x ∈ D := Metric.mem_ball_self B.radius_pos
  obtain ⟨C,hC,hxC,hCD⟩ := exists_compact_subset (hD) hxD'
  refine ⟨C,hC,hxC,fun _ _ => Set.mem_univ _,?_⟩
  obtain ⟨j,hj,hjval⟩ := compact_coordinate_jets_transport B O g hg D hD ψ hψ.contDiffOn
    (fun y hy => hy) C hC hCD n v
  refine ⟨j,hj,?_⟩
  intro t hz y
  rw [hjval t hz y]
  have he : (g t ∘ ψ) = fun y => ((original source b t).val i).val (labeledA (placeEquiv F ζ hζ) y) :=
    funext (fun x => hvalue t x)
  rw [he, iteratedFDerivWithin_of_isOpen n hD (hCD y.property), iteratedFDerivWithin_univ]

private theorem labeled_smooth (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) :
    ContDiff ℝ (⊤ : ℕ∞) (labeledA p) := by
  apply contDiff_pi.mpr
  intro k
  exact ((contDiff_apply ℝ (ℂ × ℝ) (p.symm k)).comp (CotangentLogCoframe.A (d F)).contDiff)

private theorem inverse_smooth (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) :
    ContDiff ℝ (⊤ : ℕ∞) (labeledAInv p) := by
  apply (CotangentLogCoframe.A (d F)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro k
  exact contDiff_apply ℝ (ℂ × ℝ) (p k)

private theorem inverse_pin (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (y : KPFiniteCuspAtlas.SymmetricSpace F) : labeledA p (labeledAInv p y) = y := by
  funext k
  simp [labeledA, labeledAInv]

private theorem component_calculus (b : Bool) (O : Set ℂ) (hO : IsOpen O)
    (hOΩ : O ⊆ KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ O)
    (i : Fin (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).componentCount) :
    ContDiff ℝ (⊤ : ℕ∞)
        (fun y => iteratedDerivWithin k (fun z => ((original source b z).val i).val y) O s) ∧
    ∀ y, KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        (fun y => iteratedDerivWithin k (fun z => ((original source b z).val i).val y) O s) y =
      iteratedDerivWithin k (fun z => KPContActualSphericalFlatStage.localLaplacian
        (KPCuspLogShape.dimension F) ((original source b z).val i).val y) O s := by
  let p := placeEquiv F ζ hζ
  let u := fun z x => ((original source b z).val i).val (labeledA p x)
  have hu : ∀ z ∈ O, ContDiff ℝ (⊤ : ℕ∞) (u z) :=
    fun z _ => ((original source b z).property i).comp (labeled_smooth p)
  have h := KPContSpatialParameterPositiveLaplacian.parameter_jets_positive_laplacian
    (d F) Set.univ isOpen_univ O hO u (fun z hz => (hu z hz).contDiffOn)
    (component_holomorphy source b O hO hOΩ i) k s hs
  let jet := fun y => iteratedDerivWithin k (fun z => ((original source b z).val i).val y) O s
  have hj : ContDiff ℝ (⊤ : ℕ∞) jet := by
    have hc := contDiffOn_univ.mp h.1
    have he : jet = (fun x => iteratedDerivWithin k (fun z => u z x) O s) ∘ labeledAInv p := by
      funext y
      simp only [Function.comp_def, u, inverse_pin, jet]
    rw [he]
    exact hc.comp (inverse_smooth p)
  refine ⟨hj, ?_⟩
  intro y
  have hcomm := h.2 (labeledAInv p y) (Set.mem_univ _)
  have heq : (fun x => iteratedDerivWithin k (fun z => u z x) O s) = jet ∘ labeledA p := rfl
  rw [heq] at hcomm
  have hbjet := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F)
    (KPCuspLogShape.dimension F) p jet hj (labeledAInv p y)
  change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) jet
    (labeledA p (labeledAInv p y)) = HyperbolicChart.laplacian (d F)
      (jet ∘ labeledA p) (labeledAInv p y) at hbjet
  rw [← hbjet] at hcomm
  change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) jet
    (labeledA p (labeledAInv p y)) = _ at hcomm
  rw [inverse_pin] at hcomm
  rw [hcomm]
  apply iteratedDerivWithin_congr ?_ hs
  intro z hz
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F)
    (KPCuspLogShape.dimension F) p ((original source b z).val i).val
    ((original source b z).property i) (labeledAInv p y)
  change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
    ((original source b z).val i).val (labeledA p (labeledAInv p y)) =
    HyperbolicChart.laplacian (d F) (u z) (labeledAInv p y) at hb
  rw [inverse_pin] at hb
  exact hb.symm

private theorem component_point_holo (b : Bool) (O : Set ℂ) (hO : IsOpen O)
    (hOΩ : O ⊆ KPContinuation.spectralDomain)
    (i : Fin (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    DifferentiableOn ℂ (fun z => ((original source b z).val i).val y) O := by
  let x := labeledAInv (placeEquiv F ζ hζ) y
  have hK : IsCompact ({x} : Set (M F)) := isCompact_singleton
  letI : CompactSpace ({x} : Set (M F)) := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,he⟩ := component_holomorphy source b O hO hOΩ i {x} hK (Set.subset_univ _) 0 Fin.elim0
  have hd := (ContinuousMap.evalCLM ℂ (⟨x,rfl⟩ : ({x} : Set (M F)))).differentiable.comp_differentiableOn hj
  apply hd.congr
  intro z hz
  simpa [iteratedFDerivWithin_zero_apply, x, inverse_pin] using (he z hz ⟨x,rfl⟩).symm

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

private theorem action_smooth (g : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : KPFiniteCuspAtlas.SymmetricSpace F => g • x) := by
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [← hG]
  have he : (fun x : KPFiniteCuspAtlas.SymmetricSpace F =>
      (Matrix.ProjGenLinGroup.mk G : KPCuspArithmetic.PGL2 F) • x) = KPCuspSiegel.glAction F G := by
    funext x; exact KPCuspSiegel.action_mk F G x
  rw [he]
  exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
    (fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding G)).of_le le_top

private theorem action_laplacian (g : KPCuspArithmetic.PGL2 F)
    (f : KPFiniteCuspAtlas.SymmetricSpace F → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (fun y => f (g • y)) y =
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f (g • y) := by
  obtain ⟨G,hG⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  subst g
  have he : (fun y : KPFiniteCuspAtlas.SymmetricSpace F =>
      (Matrix.ProjGenLinGroup.mk G : KPCuspArithmetic.PGL2 F) • y) =
      KPArch.productAction (KPCuspLogShape.dimension F)
        (fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding G) := by
    funext y
    exact KPCuspSiegel.action_mk F G y
  simp_rw [congrFun he]
  exact KPContArchLaplacianNaturality.pullback _ _ f hf y

private theorem chart_laplacian
    (w : KPContSectorSmoothFramesSupport.Sections F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    (hw : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H w)
    (i) (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := KPContActualAllCuspSource.level F ζ hζ C R P H U) (R := R) (P := P) (H := H) i)
    (x : M F) (hx : x ∈ a.omega) :
    HyperbolicChart.laplacian (d F) (a.coefficient w) x =
      (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ) *
        KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
          (w i).val (a.kind.representative • labeledA a.places x) := by
  let c : ℂ := (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ)
  let f := fun y : KPFiniteCuspAtlas.SymmetricSpace F => (w i).val (a.kind.representative • y)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (hw i).comp (action_smooth a.kind.representative)
  have hphase := a.splitting_locallyConstant.eventually_eq (⟨x,hx⟩ : a.omega)
  have hm := map_nhds_subtype_val (⟨x,hx⟩ : a.omega)
  rw [a.isOpen_omega.nhdsWithin_eq hx] at hm
  have hspl : ∀ᶠ y in 𝓝 x, a.splitting y = a.splitting x := by
    rw [← hm]
    exact hphase
  have he : a.coefficient w =ᶠ[𝓝 x] (fun y => c * f (labeledA a.places y)) := by
    filter_upwards [hspl] with y hy
    simp only [LiftedChart.coefficient, hy, c, f]
  rw [laplacian_congr _ _ x he]
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F)
    (KPCuspLogShape.dimension F) a.places (fun y => c * f y) (contDiff_const.mul hf) x
  change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
    (fun y => c * f y) (labeledA a.places x) =
    HyperbolicChart.laplacian (d F) (fun y => c * f (labeledA a.places y)) x at hb
  rw [← hb, KPContArchLaplacianNaturality.localLaplacian_const_mul _ f hf]
  rw [action_laplacian a.kind.representative (w i).val (hw i)]

end SourceCalculus

private theorem spectral_high (D : ℤ) (O : Set ℂ) (hO : IsOpen O) (s : ℂ) (hs : s ∈ O)
    (j : ℕ) (hj : 2 < j) :
    iteratedDerivWithin j (KPContinuation.spectralCoordinate D) O s = 0 := by
  have hderiv1 : deriv (KPContinuation.spectralCoordinate D) = fun z => -4 * (D : ℂ) * (1 / 3 + 2 * z) := by
    funext z
    change deriv (KPContinuation.spectralCoordinate D) z =
      -4 * (D : ℂ) * (1 / 3 + 2 * z)
    rw [(KPContinuation.spectralCoordinate_hasDerivAt D z).deriv]
  have hderiv2 : deriv (fun z : ℂ => -4 * (D : ℂ) * (1 / 3 + 2 * z)) =
      fun _ => -8 * (D : ℂ) := by
    funext z
    have h1 : HasDerivAt (fun z : ℂ => (1 : ℂ) / 3 + 2 * z) 2 z := by
      simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).const_add ((1 : ℂ) / 3)
    have h2 : HasDerivAt (fun z : ℂ => -4 * (D : ℂ) * (1 / 3 + 2 * z))
        (-8 * (D : ℂ)) z := by
      have hh := h1.const_mul (-4 * (D : ℂ))
      rw [show (-4 * (D : ℂ)) * 2 = -8 * (D : ℂ) by ring_nf] at hh
      exact hh
    exact h2.deriv
  have h1 : iteratedDeriv 1 (KPContinuation.spectralCoordinate D) = fun z => -4 * (D : ℂ) * (1 / 3 + 2 * z) := by
    rw [iteratedDeriv_one]; exact hderiv1
  have h2 : iteratedDeriv 2 (KPContinuation.spectralCoordinate D) = fun _ => -8 * (D : ℂ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]; exact hderiv2
  have h3 : iteratedDeriv 3 (KPContinuation.spectralCoordinate D) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, h2]
    funext z; simp
  have hk : ∀ j : ℕ, 3 ≤ j → iteratedDeriv j (KPContinuation.spectralCoordinate D) = 0 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact h3
    | succ n hn ih =>
        rw [iteratedDeriv_succ, ih]
        funext z; simp
  rw [iteratedDerivWithin_of_isOpen hO hs, hk j (by omega)]
  rfl

private theorem spectral_product (D : ℤ) (O : Set ℂ) (hO : IsOpen O)
    (c : ℂ → ℂ) (hc : DifferentiableOn ℂ c O) (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    iteratedDerivWithin k (fun z => KPContinuation.spectralCoordinate D z * c z) O s =
      KPContinuation.spectralCoordinate D s * iteratedDerivWithin k c O s +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        iteratedDerivWithin j (KPContinuation.spectralCoordinate D) O s *
        iteratedDerivWithin (k-j) c O s := by
  rw [show iteratedDerivWithin k (fun z => KPContinuation.spectralCoordinate D z * c z) O s =
      ∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℂ) *
        iteratedDerivWithin j (KPContinuation.spectralCoordinate D) O s *
        iteratedDerivWithin (k-j) c O s by
    exact iteratedDerivWithin_mul hs hO.uniqueDiffOn
      (by unfold KPContinuation.spectralCoordinate; fun_prop)
      ((hc.contDiffOn hO).contDiffWithinAt hs)]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.sub_zero, iteratedDerivWithin_zero, Nat.cast_one, one_mul]
  rw [add_comm]
  apply congrArg (fun z => KPContinuation.spectralCoordinate D s * iteratedDerivWithin k c O s + z)
  let T := fun j => (Nat.choose k j : ℂ) *
    iteratedDerivWithin j (KPContinuation.spectralCoordinate D) O s * iteratedDerivWithin (k-j) c O s
  change (∑ j ∈ Finset.range k, T (j+1)) = ∑ j ∈ Finset.Icc 1 (min k 2), T j
  have hshift : (∑ j ∈ Finset.range k, T (j+1)) = ∑ j ∈ Finset.Icc 1 k, T j := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [hshift]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    exact ⟨hj.1, hj.2.trans (min_le_left _ _)⟩
  · intro j hj hn
    have hlarge : 2 < j := by
      simp only [Finset.mem_Icc] at hj hn
      omega
    dsimp [T]
    rw [spectral_high D O hO s hs j hlarge]
    simp

theorem actual_source_laplacian_jets
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) {T : ℝ}
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
      KPContinuation.spectralDomain f χ)
    (O : Set ℂ) (hO : IsOpen O) (hOΩ : O ⊆ KPContinuation.spectralDomain) :
    let cjet := KPContActualCompactSectionL2Jets.pointwiseJets
      (fun z => (source.descent.cutoff z).val) O
    let hjet := KPContActualCompactSectionL2Jets.pointwiseJets
      (fun z => (source.descent.commutator z).val) O
    let lam := KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)
    (∀ k s, s ∈ O → ∀ i (y : KPFiniteCuspAtlas.SymmetricSpace F),
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        (cjet k s i).val y = lam s * (cjet k s i).val y + (hjet k s i).val y +
          ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
            iteratedDerivWithin j lam O s * (cjet (k-j) s i).val y) ∧
    (∀ k s, s ∈ O →
      ∀ (i : Fin (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).componentCount)
        (a : KPContCotangentActualOverlap.LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
          (U := KPContActualAllCuspSource.level F ζ hζ C R P H U)
          (R := R) (P := P) (H := H) i)
        (x : HyperbolicChart.Space (KPContCotangentActualOverlap.d F)), x ∈ a.omega →
      HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
        (a.coefficient (cjet k s)) x =
        lam s * a.coefficient (cjet k s) x + a.coefficient (hjet k s) x +
          ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
            iteratedDerivWithin j lam O s * a.coefficient (cjet (k-j) s) x) := by
  dsimp only
  let cjet := KPContActualCompactSectionL2Jets.pointwiseJets
    (fun z => (source.descent.cutoff z).val) O
  let hjet := KPContActualCompactSectionL2Jets.pointwiseJets
    (fun z => (source.descent.commutator z).val) O
  let lam := KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)
  have component (k : ℕ) (s : ℂ) (hs : s ∈ O)
      (i : Fin (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).componentCount)
      (y : KPFiniteCuspAtlas.SymmetricSpace F) :
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        (cjet k s i).val y = lam s * (cjet k s i).val y + (hjet k s i).val y +
        ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
          iteratedDerivWithin j lam O s * (cjet (k-j) s i).val y := by
    have hc := component_point_holo source false O hO hOΩ i y
    have hh := component_point_holo source true O hO hOΩ i y
    simp only [original, Bool.false_eq_true, ite_false, ite_true] at hc hh
    have hcomm := (component_calculus source false O hO hOΩ k s hs i).2 y
    simp only [original, Bool.false_eq_true, ite_false] at hcomm
    change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (cjet k s i).val y = _ at hcomm
    rw [hcomm]
    have he : Set.EqOn
        (fun z => KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
          ((source.descent.cutoff z).val i).val y)
        (fun z => lam z * ((source.descent.cutoff z).val i).val y +
          ((source.descent.commutator z).val i).val y) O := by
      intro z hz
      exact sub_eq_iff_eq_add'.mp (source.local_equation z (hOΩ hz) i y)
    rw [iteratedDerivWithin_congr he hs]
    rw [iteratedDerivWithin_fun_add hs hO.uniqueDiffOn
      (((by unfold lam KPContinuation.spectralCoordinate; fun_prop : ContDiffOn ℂ k lam O).mul
        (hc.contDiffOn hO)).contDiffWithinAt hs)
      ((hh.contDiffOn hO).contDiffWithinAt hs)]
    rw [spectral_product _ O hO _ hc k s hs]
    change (lam s * (cjet k s i).val y +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        iteratedDerivWithin j lam O s * (cjet (k-j) s i).val y) + (hjet k s i).val y = _
    ring
  refine ⟨component, ?_⟩
  intro k s hs i a x hx
  have hsm : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (cjet k s) := by
    intro i
    exact (component_calculus source false O hO hOΩ k s hs i).1
  rw [chart_laplacian (cjet k s) hsm i a x hx, component k s hs i]
  simp only [LiftedChart.coefficient]
  rw [mul_add, mul_add, Finset.mul_sum]
  dsimp only [cjet, hjet, lam]
  ring_nf

end DedekindZetaZeroFree.KPContActualAllCuspSourceLaplacianJets

end
