module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain Topology

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.AngularBound

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

open KPGlobalTorusBorelTwistCompatibility KPAdelicCoverRestrictedProduct
local instance (v : KPHilbert.Place F) : TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) := localTopology F ζ hζ v
local instance rawGroup (v : KPHilbert.Place F) : IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
  | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _ (depth_admissible F ζ hζ q)).2.2
local instance : Fact (∀ v : KPHilbert.Place F, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) := ⟨compact_open F ζ hζ⟩
local instance : IsTopologicalGroup (RestrictedCover F ζ hζ) := RestrictedProduct.isTopologicalGroup (R := fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (B := compact F ζ hζ)

 def finiteTruncate (x : RestrictedCover F ζ hζ) : RestrictedCover F ζ hζ :=
  RestrictedProduct.mapAlong _ _ id Filter.tendsto_id
    (fun v y => match v with | Sum.inl _ => 1 | Sum.inr _ => y)
    (Filter.Eventually.of_forall (fun v y hy => by cases v <;> simpa using hy)) x

private theorem finiteTruncate_continuous : Continuous (finiteTruncate (F := F) (ζ := ζ) (hζ := hζ)) := by
  unfold finiteTruncate
  apply RestrictedProduct.mapAlong_continuous
  intro v
  cases v
  · exact continuous_const
  · exact continuous_id

 def rawToG : RestrictedCover F ζ hζ →* KPGlobalTorusFunctionData.G F ζ hζ :=
  (scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)

private theorem rawToG_continuous : Continuous (rawToG (F := F) (ζ := ζ) (hζ := hζ)) :=
  continuous_quot_mk.comp continuous_quot_mk

private theorem gauss_matrix {K : Type*} [Field K] (g : KubotaRankTwo.GL2 K)
    (ha : g 0 0 ≠ 0) :
    g = Matrix.GeneralLinearGroup.scalar (Fin 2) (g.det / Units.mk0 (g 0 0) ha) *
      (KPStandardLocalRootLifts.lowerN K (g 1 0 / g 0 0) *
        KubotaRankTwo.d K ((Units.mk0 (g 0 0) ha)^2 / g.det) 1 *
        KubotaRankTwo.n K (g 0 1 / g 0 0)) := by
  have hd : (g.det : K) ≠ 0 := Units.ne_zero _
  have he : (g.det : K) = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) (g.det / Units.mk0 (g 0 0) ha) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 2) ((g.det : K) / g 0 0) := by simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_div_eq_div_val, Units.val_mk0]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, hs]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      KPStandardLocalRootLifts.lowerN, KubotaRankTwo.d, KubotaRankTwo.n]
  all_goals simp only [← Matrix.GeneralLinearGroup.val_det_apply]
  all_goals field_simp
  all_goals rw [he] <;> ring

 def archUnits (c : ∀ w : InfinitePlace F, w.Completionˣ) : Ideles F where
  val := (fun w => (c w : w.Completion), 1)
  inv := (fun w => ((c w)⁻¹ : w.Completion), 1)
  val_inv := by
    apply Prod.ext
    · funext w; exact mul_inv_cancel₀ (Units.ne_zero (c w))
    · exact one_mul _
  inv_val := by
    apply Prod.ext
    · funext w; exact inv_mul_cancel₀ (Units.ne_zero (c w))
    · exact one_mul _

 def gaussCoords (x : RestrictedCover F ζ hζ) : GroupArch F :=
  fun w => ![
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)) ((x (Sum.inl w)).g 1 0 / (x (Sum.inl w)).g 0 0),
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)) (((x (Sum.inl w)).g 0 0)^2 / ((x (Sum.inl w)).g.det : w.Completion)),
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)) ((x (Sum.inl w)).g 0 1 / (x (Sum.inl w)).g 0 0)]

 def gaussScalar (x : RestrictedCover F ζ hζ) : Ideles F :=
  archUnits (fun w => if h : (x (Sum.inl w)).g 0 0 = 0 then 1 else
    (x (Sum.inl w)).g.det / Units.mk0 ((x (Sum.inl w)).g 0 0) h)

private theorem gauss_decomposition (x : RestrictedCover F ζ hζ)
    (ha : ∀ w : InfinitePlace F, (x (Sum.inl w)).g 0 0 ≠ 0)
    (he : ∀ w : InfinitePlace F, (x (Sum.inl w)).epsilon = 1) :
    x = scalarTuple F ζ hζ (gaussScalar x) * groupArchTuple F ζ hζ (gaussCoords x) * finiteTruncate x := by
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q =>
    have hu : Units.map (adeleEval F (Sum.inr q)).toMonoidHom (gaussScalar x) = 1 := by
      apply Units.ext
      rfl
    change x (Sum.inr q) = KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q)
      (Units.map (adeleEval F (Sum.inr q)).toMonoidHom (gaussScalar x)) * 1 * x (Sum.inr q)
    rw [hu, map_one, one_mul, one_mul]
  | inl w =>
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)
    have hz : e (((x (Sum.inl w)).g 0 0)^2 / ((x (Sum.inl w)).g.det : w.Completion)) ≠ 0 := by
      apply (map_ne_zero e).mpr
      exact div_ne_zero (pow_ne_zero 2 (ha w)) (Units.ne_zero _)
    have hmul (a b : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
        (a * b).epsilon = a.epsilon * b.epsilon := by
      change _ * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) a.g b.g = _
      rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
    have hscalar : Units.map (adeleEval F (Sum.inl w)).toMonoidHom (gaussScalar x) =
        (x (Sum.inl w)).g.det / Units.mk0 ((x (Sum.inl w)).g 0 0) (ha w) := by
      apply Units.ext
      change (if h : (x (Sum.inl w)).g 0 0 = 0 then (1 : w.Completionˣ) else
        (x (Sum.inl w)).g.det / Units.mk0 ((x (Sum.inl w)).g 0 0) h).val = _
      simp only [dif_neg (ha w)]
    have hy : (if h : (gaussCoords x) w 1 = 0 then (1 : w.Completionˣ) else
        Units.mk0 (e.symm ((gaussCoords x) w 1)) (by
          intro h0; apply h; simpa using congrArg e h0)) =
        (Units.mk0 ((x (Sum.inl w)).g 0 0) (ha w))^2 / (x (Sum.inl w)).g.det := by
      have hz' : (gaussCoords x) w 1 = e (((x (Sum.inl w)).g 0 0)^2 / ((x (Sum.inl w)).g.det : w.Completion)) := rfl
      simp only [hz', dif_neg hz]
      apply Units.ext
      simp only [Units.val_mk0, e.symm_apply_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    apply (KPLocalChartTopology.complexCoordinates F ζ hζ w).injective
    apply Prod.ext
    · change (x (Sum.inl w)).g = ((scalarTuple F ζ hζ (gaussScalar x) * groupArchTuple F ζ hζ (gaussCoords x) * finiteTruncate x) (Sum.inl w)).g
      change (x (Sum.inl w)).g = (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w)
        (Units.map (adeleEval F (Sum.inl w)).toMonoidHom (gaussScalar x)) *
          (KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm ((gaussCoords x) w 0)) *
           KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) _ *
           KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm ((gaussCoords x) w 2))) * 1).g
      rw [mul_one, hscalar, hy]
      have h0 : e.symm ((gaussCoords x) w 0) = (x (Sum.inl w)).g 1 0 / (x (Sum.inl w)).g 0 0 := e.symm_apply_apply _
      have h2 : e.symm ((gaussCoords x) w 2) = (x (Sum.inl w)).g 0 1 / (x (Sum.inl w)).g 0 0 := e.symm_apply_apply _
      rw [h0, h2]
      exact gauss_matrix (x (Sum.inl w)).g (ha w)
    · change (x (Sum.inl w)).epsilon = ((scalarTuple F ζ hζ (gaussScalar x) * groupArchTuple F ζ hζ (gaussCoords x) * finiteTruncate x) (Sum.inl w)).epsilon
      change (x (Sum.inl w)).epsilon = (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) _ *
          (KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) _ *
           KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) _ *
           KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) _) * 1).epsilon
      simp only [mul_one, hmul, he w]
      change 1 = 1 * (1 * 1 * (1 : rootsOfUnity 3 F))
      simp

 def finiteImageConj (a x : RestrictedCover F ζ hζ) : KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  ⟨rawToG (a⁻¹ * finiteTruncate x * a), by
    apply Subgroup.mem_map.mpr
    refine ⟨a⁻¹ * finiteTruncate x * a, ?_, rfl⟩
    simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w
    change (a (Sum.inl w))⁻¹ * 1 * a (Sum.inl w) = 1
    simp⟩

private theorem finiteImageConj_continuous (a : RestrictedCover F ζ hζ) :
    Continuous (finiteImageConj a) := by
  exact (rawToG_continuous.comp ((continuous_const.mul finiteTruncate_continuous).mul continuous_const)).subtype_mk _

private theorem archEntry_continuous (w : InfinitePlace F) (i j : Fin 2) :
    Continuous (fun x : RestrictedCover F ζ hζ => (x (Sum.inl w)).g i j) := by
  have hc := (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.2.1.continuous
  exact (continuous_apply j).comp ((continuous_apply i).comp
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) w.Completion)).comp (hc.comp (RestrictedProduct.continuous_eval _))))

private theorem archDet_continuous (w : InfinitePlace F) :
    Continuous (fun x : RestrictedCover F ζ hζ => ((x (Sum.inl w)).g.det : w.Completion)) := by
  have hc := (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.2.1.continuous
  exact Units.continuous_val.comp (Matrix.GeneralLinearGroup.continuous_det.comp (hc.comp (RestrictedProduct.continuous_eval _)))

private theorem gaussCoords_continuousAt : ContinuousAt (gaussCoords (F := F) (ζ := ζ) (hζ := hζ)) 1 := by
  apply continuousAt_pi.mpr
  intro w
  have he : Continuous (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)) :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)).continuous
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact he.continuousAt.comp ((archEntry_continuous w 1 0).continuousAt.div (archEntry_continuous w 0 0).continuousAt (by simp))
  · exact he.continuousAt.comp (((archEntry_continuous w 0 0).continuousAt.pow 2).div (archDet_continuous w).continuousAt (by simp))
  · exact he.continuousAt.comp ((archEntry_continuous w 0 1).continuousAt.div (archEntry_continuous w 0 0).continuousAt (by simp))

private theorem gaussCoords_one_mem : gaussCoords (1 : RestrictedCover F ζ hζ) ∈ groupArchDomain F := by
  intro w
  simp [gaussCoords]

private theorem good_arch_eventually : ∀ᶠ x : RestrictedCover F ζ hζ in 𝓝 1,
    (∀ w : InfinitePlace F, (x (Sum.inl w)).g 0 0 ≠ 0) ∧
    (∀ w : InfinitePlace F, (x (Sum.inl w)).epsilon = 1) := by
  have ha : ∀ w : InfinitePlace F, ∀ᶠ x : RestrictedCover F ζ hζ in 𝓝 1, (x (Sum.inl w)).g 0 0 ≠ 0 := by
    intro w
    exact (archEntry_continuous w 0 0).continuousAt.eventually_ne (by simp)
  have he : ∀ w : InfinitePlace F, ∀ᶠ x : RestrictedCover F ζ hζ in 𝓝 1, (x (Sum.inl w)).epsilon = 1 := by
    intro w
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    letI : DiscreteTopology (rootsOfUnity 3 F) := discreteTopology_bot _
    have hi : IsInducing (KPLocalChartTopology.complexCoordinates F ζ hζ w) := ⟨rfl⟩
    have hc : Continuous (fun x : RestrictedCover F ζ hζ => (x (Sum.inl w)).epsilon) :=
      continuous_snd.comp (hi.continuous.comp (RestrictedProduct.continuous_eval _))
    exact hc.continuousAt.eventually ((isOpen_discrete ({1} : Set (rootsOfUnity 3 F))).mem_nhds (by rfl))
  exact (Filter.eventually_all.mpr ha).and (Filter.eventually_all.mpr he)

private theorem rawToG_gauss (x : RestrictedCover F ζ hζ)
    (ha : ∀ w : InfinitePlace F, (x (Sum.inl w)).g 0 0 ≠ 0)
    (he : ∀ w : InfinitePlace F, (x (Sum.inl w)).epsilon = 1) :
    rawToG x = groupArchChart F ζ hζ (gaussCoords x) * rawToG (finiteTruncate x) := by
  have hs : rawToG (scalarTuple F ζ hζ (gaussScalar x)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨gaussScalar x, rfl⟩
  calc
    rawToG x = rawToG (scalarTuple F ζ hζ (gaussScalar x) * groupArchTuple F ζ hζ (gaussCoords x) * finiteTruncate x) := congrArg rawToG (gauss_decomposition x ha he)
    _ = _ := by rw [map_mul, map_mul, hs, one_mul]; rfl

set_option maxHeartbeats 800000 in

private theorem scalar_raw_continuousAt_one
    (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ P J) (a : RestrictedCover F ζ hζ) :
    ContinuousAt (fun x : RestrictedCover F ζ hζ => (f.val.val (rawToG (x * a))).val.val 1) 1 := by
  have hc := (f.property.1 (rawToG a)).continuousOn.continuousAt
    ((groupArchDomain_open F).mem_nhds (gaussCoords_one_mem (ζ := ζ) (hζ := hζ)))
  have hc' : ContinuousAt (fun x : RestrictedCover F ζ hζ =>
      (f.val.val (groupArchChart F ζ hζ (gaussCoords x) * rawToG a)).val.val 1) 1 :=
    hc.comp gaussCoords_continuousAt
  apply hc'.congr_of_eventuallyEq
  have hj : ∀ᶠ x : RestrictedCover F ζ hζ in 𝓝 1, finiteImageConj a x ∈ J.toOpenSubgroup := by
    apply (finiteImageConj_continuous a).continuousAt.eventually
    apply J.toOpenSubgroup.isOpen.mem_nhds
    have hi : finiteImageConj a 1 = 1 := by
      apply Subtype.ext
      change rawToG (a⁻¹ * finiteTruncate 1 * a) = 1
      have htr : finiteTruncate (1 : RestrictedCover F ζ hζ) = 1 := by
        ext v; cases v <;> rfl
      rw [htr, mul_one, inv_mul_cancel, map_one]
    rw [hi]
    exact J.toOpenSubgroup.one_mem
  filter_upwards [good_arch_eventually, hj] with x hx hjx
  have hlev : rawToG (a⁻¹ * finiteTruncate x * a) ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
    apply Subgroup.mem_map.mpr
    exact ⟨finiteImageConj a x, hjx, rfl⟩
  have heq : rawToG (x * a) = (groupArchChart F ζ hζ (gaussCoords x) * rawToG a) *
      rawToG (a⁻¹ * finiteTruncate x * a) := by
    rw [map_mul, rawToG_gauss x hx.1 hx.2]
    simp only [map_mul, map_inv]
    group
  rw [heq, f.property.2 _ ⟨_, hlev⟩]

private theorem scalar_raw_continuous
    (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ P J) :
    Continuous (fun x : RestrictedCover F ζ hζ => (f.val.val (rawToG x)).val.val 1) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hc0 := scalar_raw_continuousAt_one P J f a
  have hc1 : ContinuousAt (fun x : RestrictedCover F ζ hζ => x * a⁻¹) a :=
    (continuous_id.mul continuous_const).continuousAt
  have hc := (show ContinuousAt (fun x : RestrictedCover F ζ hζ => (f.val.val (rawToG (x * a))).val.val 1) ((fun x : RestrictedCover F ζ hζ => x * a⁻¹) a) by simpa using hc0).comp (f := fun x : RestrictedCover F ζ hζ => x * a⁻¹) (x := a) hc1
  simpa only [Function.comp_def, inv_mul_cancel_right] using hc

theorem inducedLevel_scalar_continuous
    (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J) :
    Continuous (fun g : KPGlobalTorusFunctionData.G F ζ hζ =>
      (f.val.val g).val.val 1) := by
  have hq : IsQuotientMap (rawToG (F := F) (ζ := ζ) (hζ := hζ)) :=
    (QuotientGroup.isQuotientMap_mk (splitScalarSubgroup F ζ hζ)).comp
      (QuotientGroup.isQuotientMap_mk (M F ζ hζ))
  exact hq.continuous_iff.mpr (scalar_raw_continuous P J f)

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.AngularBound

end
