module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions
public import DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualDifferentialData

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archDomain_isOpen : IsOpen (archDomain F) := by
  change IsOpen {x : ArchCoordinates F | ∀ w, x w 1 ≠ 0}
  have he : {x : ArchCoordinates F | ∀ w, x w 1 ≠ 0} =
      ⋂ w, {x | x w 1 ≠ 0} := by ext x; simp
  rw [he]
  exact isOpen_iInter_of_finite (fun w => isOpen_ne.preimage
    ((continuous_apply 1).comp (continuous_apply w)))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualDifferentialData

end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open Set Filter

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualNativeActionGeometry.CompactParameter
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X] [CompactSpace X]

def flip (a : C(X, E →L[ℝ] F)) : E →L[ℝ] C(X, F) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun y => a y v, (ContinuousLinearMap.apply ℝ F v).continuous.comp a.continuous⟩
      map_add' := by intro v w; ext y; exact (a y).map_add v w
      map_smul' := by intro c v; ext y; exact (a y).map_smul c v }
    ‖a‖ (by
      intro v
      apply (ContinuousMap.norm_le (C := ‖a‖ * ‖v‖) _ (mul_nonneg (norm_nonneg a) (norm_nonneg v))).mpr
      intro y
      exact (a y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm y) (norm_nonneg v)))

@[simp] theorem flip_apply (a : C(X, E →L[ℝ] F)) (v : E) (y : X) : flip a v y = a y v := rfl

def flipL : C(X, E →L[ℝ] F) →L[ℝ] (E →L[ℝ] C(X, F)) :=
  LinearMap.mkContinuous
    { toFun := fun a : C(X, E →L[ℝ] F) => flip a
      map_add' := by intro a b; ext v y; exact add_apply (a y) (b y) v
      map_smul' := by intro c a; ext v y; rfl }
    1 (by
      intro a
      rw [one_mul]
      change ‖flip a‖ ≤ ‖a‖
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
      intro v
      apply (ContinuousMap.norm_le (C := ‖a‖ * ‖v‖) _ (mul_nonneg (norm_nonneg a) (norm_nonneg v))).mpr
      intro y
      exact (a y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (a.norm_coe_le_norm y) (norm_nonneg v)))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualNativeActionGeometry.CompactParameter

noncomputable section
open scoped NumberField Classical Topology

set_option maxHeartbeats 1200000
open Set Filter

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualNativeActionGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter

variable {E V K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace K] [CompactSpace K]

 def compactDerivativeLinear (q : C(K, E →L[ℝ] V)) : E →ₗ[ℝ] C(K,V) where
  toFun v := ⟨fun k => q k v, q.continuous.clm_apply continuous_const⟩
  map_add' v w := by ext k; exact (q k).map_add v w
  map_smul' c v := by ext k; exact (q k).map_smul c v

 def compactDerivative (q : C(K, E →L[ℝ] V)) : E →L[ℝ] C(K,V) :=
  (compactDerivativeLinear q).mkContinuous ‖q‖ (by
    intro v
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg q) (norm_nonneg v))).2
    intro k
    exact (q k).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (q.norm_coe_le_norm k) (norm_nonneg _)))

 lemma compactDerivative_apply (q : C(K, E →L[ℝ] V)) (v : E) (k : K) :
    compactDerivative q v k = q k v := rfl

 def compactDerivativeMap : C(K,E →L[ℝ] V) →L[ℝ] E →L[ℝ] C(K,V) := by
  let A : C(K,E →L[ℝ] V) →ₗ[ℝ] E →L[ℝ] C(K,V) :=
    { toFun := fun q => compactDerivative q
      map_add' := by intro q r; ext v k; simp [compactDerivative_apply]
      map_smul' := by intro c q; ext v k; simp [compactDerivative_apply] }
  refine LinearMap.mkContinuous (E := C(K,E →L[ℝ] V)) (F := E →L[ℝ] C(K,V)) A 1 ?_
  intro (q : C(K,E →L[ℝ] V))
  change ‖compactDerivative q‖ ≤ 1 * ‖q‖
  simp only [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q)
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg q) (norm_nonneg v))).2
  intro k
  exact (q k).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (q.norm_coe_le_norm k) (norm_nonneg _))

private lemma compactDerivativeMap_apply (q : C(K,E →L[ℝ] V)) :
    compactDerivativeMap q = compactDerivative q := rfl

private theorem compact_family_hasFDerivAt
    (f : E → C(K,V)) (q : E → C(K,E →L[ℝ] V)) (U : Set E)
    (hU : IsOpen U) (hq : ContinuousOn q U)
    (hf : ∀ x ∈ U, ∀ k, HasFDerivAt (fun y => f y k) (q x k) x)
    (x : E) (hx : x ∈ U) : HasFDerivAt f (compactDerivative (q x)) x := by
  apply HasFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont := (hq x hx).continuousAt (hU.mem_nhds hx)
  have hsubq : ContinuousAt (fun y => q y - q x) x := hcont.sub continuousAt_const
  have hnq : ContinuousAt (fun y => ‖q y - q x‖) x := by
    exact ContinuousAt.norm (E := C(K,E →L[ℝ] V)) hsubq
  have hnε : {y | ‖q y - q x‖ < ε} ∈ nhds x := by
    have hε' : ‖q x - q x‖ < ε := by
      rw [sub_self]
      change ‖(0 : C(K,E →L[ℝ] V))‖ < ε
      rw [@norm_zero C(K,E →L[ℝ] V) inferInstance]
      exact hε
    exact hnq (gt_mem_nhds hε')
  have hn : {y | ‖q y - q x‖ < ε} ∩ U ∈ nhds x :=
    inter_mem hnε (hU.mem_nhds hx)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro k
  have hb (z : E) (hz : z ∈ Metric.ball x δ) :
      ‖q z k - q x k‖ ≤ ε := by
    exact ((q z - q x).norm_coe_le_norm k).trans (hsub hz).1.le
  have hd (z : E) (hz : z ∈ Metric.ball x δ) :
      HasFDerivWithinAt (fun y => f y k) (q z k) (Metric.ball x δ) z :=
    (hf z (hsub hz).2 k).hasFDerivWithinAt
  simpa only [ContinuousMap.sub_apply, compactDerivative_apply] using
    (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' hd hb
      (Metric.mem_ball_self hδ) hy

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [CompactSpace K] in

theorem compact_family_continuousOn (f : E → C(K,V)) (U : Set E)
    (hf : ContinuousOn (fun p : E × K => f p.1 p.2) (U ×ˢ Set.univ)) :
    ContinuousOn f U := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h := hf.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
    (show Set.MapsTo (fun p : U × K => (p.1.val,p.2)) Set.univ (U ×ˢ Set.univ) from
      fun p _ => ⟨p.1.property, Set.mem_univ _⟩)
  have hh : Continuous (fun p : U × K => f p.1.val p.2) := by
    simpa [Function.comp_def, continuousOn_univ] using h
  exact hh

theorem compact_family_contDiffOn
    (f : E → C(K,V)) (U : Set E) (hU : IsOpen U)
    (hf : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f x k) U)
    (J : ∀ m : ℕ, E → C(K,ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V))
    (hJ : ∀ m, ContinuousOn (J m) U)
    (hbind : ∀ m x, x ∈ U → ∀ k, J m x k = iteratedFDeriv ℝ m (fun y => f y k) x) :
    ContDiffOn ℝ (⊤ : ℕ∞) f U := by
  have hjets : ∀ n : ℕ, ∀ m : ℕ, ContDiffOn ℝ n (J m) U := by
    intro n
    induction n with
    | zero => intro m; exact contDiffOn_zero.mpr (hJ m)
    | succ n ih =>
      intro m
      let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V) := inferInstance
      let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V) := inferInstance
      let : NormedAddCommGroup (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V) := inferInstance
      let L : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => E) V →L[ℝ] E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) V).toContinuousLinearEquiv.toContinuousLinearMap
      let q := fun x => ContinuousLinearMap.compLeftContinuous ℝ K L (J (m+1) x)
      have hq : ContDiffOn ℝ n q U := by
        exact (ContinuousLinearMap.compLeftContinuous ℝ K L).contDiff.comp_contDiffOn (ih (m+1))
      have hd (x : E) (hx : x ∈ U) : HasFDerivAt (J m) (compactDerivative (q x)) x := by
        refine compact_family_hasFDerivAt (J m) q U hU hq.continuousOn ?_ x hx
        intro y hy k
        have hs := (hf k).contDiffAt (hU.mem_nhds hy)
        have ht := (hs.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (i := m) (by simp)).differentiableAt (by simp)
        have he : (fun z => J m z k) =ᶠ[nhds y] iteratedFDeriv ℝ m (fun z => f z k) :=
          Filter.Eventually.mono (hU.mem_nhds hy) (fun z hz => hbind m z hz k)
        have hd := ht.hasFDerivAt.congr_of_eventuallyEq he
        convert hd using 1
        change L (J (m+1) y k) = _
        rw [hbind (m+1) y hy k]
        rfl
      rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).2
      refine ⟨by simp, fun x => compactDerivative (q x), ?_, fun x hx => (hd x hx).hasFDerivWithinAt⟩
      simpa only [Function.comp_def, compactDerivativeMap_apply] using
        (compactDerivativeMap (E := E) (K := K) (V := ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V)).contDiff.comp_contDiffOn hq
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) V) := inferInstance
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) V) := inferInstance
  let Z := (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
  have h0 : ContDiffOn ℝ (⊤ : ℕ∞) (J 0) U := contDiffOn_infty.mpr (fun n => hjets n 0)
  have hZ := (ContinuousLinearMap.compLeftContinuous ℝ K Z).contDiff.comp_contDiffOn h0
  apply hZ.congr
  intro x hx
  ext k
  change f x k = Z (J 0 x k)
  rw [hbind 0 x hx k]
  simp [Z]

theorem compact_family_contDiffOn_of_joint_jets
    (f : E → C(K,V)) (U : Set E) (hU : IsOpen U)
    (hf : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f x k) U)
    (hjets : ∀ m : ℕ, ContinuousOn
      (fun p : E × K => iteratedFDeriv ℝ m (fun y => f y p.2) p.1)
      (U ×ˢ Set.univ)) : ContDiffOn ℝ (⊤ : ℕ∞) f U := by
  classical
  let J : ∀ m : ℕ, E → C(K,ContinuousMultilinearMap ℝ (fun _ : Fin m => E) V) :=
    fun m x => if hx : x ∈ U then
      ⟨fun k => iteratedFDeriv ℝ m (fun y => f y k) x,
        by
          have h := (hjets m).comp (continuous_const.prodMk continuous_id).continuousOn
            (show Set.MapsTo (fun k : K => (x,k)) Set.univ (U ×ˢ Set.univ) from
              fun k _ => ⟨hx,Set.mem_univ _⟩)
          simpa [continuousOn_univ, Function.comp_def] using h⟩
      else 0
  have hb (m : ℕ) (x : E) (hx : x ∈ U) (k : K) :
      J m x k = iteratedFDeriv ℝ m (fun y => f y k) x := by simp only [J, dite_eq_left hx, ContinuousMap.coe_mk]
  apply compact_family_contDiffOn f U hU hf J
  · intro m
    apply compact_family_continuousOn
    apply (hjets m).congr
    intro p hp
    exact hb m p.1 hp.1 p.2
  · exact hb

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualNativeActionGeometry

end
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualDifferentialData

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archBase_mem_domain : archBase F ∈ archDomain F := by
  intro w; simp [archBase]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualDifferentialData

end
end
