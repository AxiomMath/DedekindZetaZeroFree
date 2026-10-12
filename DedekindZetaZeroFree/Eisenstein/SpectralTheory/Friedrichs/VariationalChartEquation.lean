module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.ProjectedTestPairings

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContFriedrichsChartVariational

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

open KPContActualCotangentCountableShrinking

private theorem orbifold_action_mem (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (y : SymmetricSpace F) (hy : y ∈ O.neighborhood) :
    (σ.val : KPCuspArithmetic.PGL2 F) • y ∈ O.neighborhood := by
  let τ : MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x :=
    ⟨⟨complexProjectiveEmbedding F σ.val.val,
      ⟨σ.val.val, σ.val.property, rfl⟩⟩, by
      change complexProjectiveEmbedding F σ.val.val • x = x
      rw [complexProjectiveEmbedding_smul]
      exact σ.property⟩
  have h := Set.mem_image_of_mem (fun z : SymmetricSpace F => τ • z) hy
  rw [O.invariant τ] at h
  change complexProjectiveEmbedding F σ.val.val • y ∈ O.neighborhood at h
  simpa only [complexProjectiveEmbedding_smul] using h

private theorem compact_shrinking (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (K : Set (SymmetricSpace F)) (hK : IsCompact K) (hKO : K ⊆ O.neighborhood) :
    ∃ a : ShrunkChart F ζ hζ U R P H,
      a.component = i ∧ a.center = x ∧ K ⊆ a.domain := by
  let G := MulAction.stabilizer (Component F ζ hζ U R P H i) x
  letI : Finite G := chart_stabilizer_finite F ζ hζ U R P H i x O
  letI := Fintype.ofFinite G
  let L := ⋃ g : G, (fun y : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • y) '' K
  have hLc : IsCompact L := isCompact_iUnion fun g =>
    hK.image (KPCuspSiegel.continuous_action F g.val.val)
  have hLO : L ⊆ O.neighborhood := by
    intro y hy
    obtain ⟨g, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
    exact orbifold_action_mem F ζ hζ U R P H i x O g z (hKO hz)
  obtain ⟨W, hWo, hLW, hWsub, hWc⟩ :=
    exists_open_between_and_isCompact_closure hLc O.isOpen hLO
  let V := ⋂ g : G, (fun y : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • y) ⁻¹' W
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hVW : V ⊆ W := by
    intro y hy
    simpa using Set.mem_iInter.mp hy (1 : G)
  have hKV : K ⊆ V := by
    intro y hy
    apply Set.mem_iInter.mpr
    intro g
    exact hLW (Set.mem_iUnion.mpr ⟨g, y, hy, rfl⟩)
  refine ⟨⟨i, x, O, V, hVo,
    hWc.of_isClosed_subset isClosed_closure (closure_mono hVW),
    (closure_mono hVW).trans hWsub, ?_⟩, rfl, rfl, hKV⟩
  intro g
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply Set.mem_iInter.mpr
    intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using
      Set.mem_iInter.mp hz (h * g)
  · intro hy
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • y, ?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr
    intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul] using
      Set.mem_iInter.mp hy (h * g⁻¹)

theorem closed_ball_shrinking (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆
      chartDomain F ζ hζ U R P H i x O) :
    ∃ a : KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H,
      a.component = i ∧ a.center = x ∧
        coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain := by
  exact compact_shrinking F ζ hζ U R P H i x O _
    ((isCompact_closedBall A.center A.radius).image (coordinates F).continuous)
    (by rintro y ⟨p, hp, rfl⟩; exact hA hp)

open KPContLocalEnergy in
private theorem weighted_test_integrable {n : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (D : Coefficients B cρ Cρ κ Λ)
    (w : BallL2 B) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => (D.density x : ℂ) * w x * star (φ x))
      (volume.restrict B.carrier) := by
  have hD : MemLp (fun x => (D.density x : ℂ)) ⊤ (volume.restrict B.carrier) := by
    apply memLp_top_of_bound
      ((Complex.ofRealCLM.continuous.comp_continuousOn D.density_smooth.continuousOn).aestronglyMeasurable
        B.toOpens.isOpen.measurableSet) (max |cρ| |Cρ|)
    apply ae_restrict_of_forall_mem B.toOpens.isOpen.measurableSet
    intro x hx
    change ‖(D.density x : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hb := D.density_bounds x hx
    exact abs_le_max_abs_abs hb.1 hb.2
  have hw : MemLp (fun x => (D.density x : ℂ) * w x) 2
      (volume.restrict B.carrier) := hD.fun_mul (Lp.memLp w)
  exact hw.integrable_mul
    ((φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).star)

open KPContLocalEnergy in

theorem weakEquation_shift {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (ξ : IntegerSobolev B 1)
    (h : BallL2 B) (hξ : WeakEquation D 0 ξ h) (z : ℂ) :
    WeakEquation D z ξ (h - z • value ξ) := by
  intro φ
  have he := hξ φ
  simp only [zero_mul, sub_zero] at he
  have hr : (∫ x in B.carrier, (D.density x : ℂ) *
      (h - z • value ξ) x * star (φ x)) =
      (∫ x in B.carrier, (D.density x : ℂ) * h x * star (φ x)) -
        z * (∫ x in B.carrier, (D.density x : ℂ) * value ξ x * star (φ x)) := by
    calc
      _ = ∫ x in B.carrier, ((D.density x : ℂ) * h x * star (φ x) -
          z * ((D.density x : ℂ) * value ξ x * star (φ x))) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub h (z • value ξ), Lp.coeFn_smul z (value ξ)] with x hx hs
        rw [hx]
        simp only [Pi.sub_apply]
        rw [hs]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by
        rw [integral_sub (weighted_test_integrable D h φ)
          ((weighted_test_integrable D (value ξ) φ).const_mul z), integral_const_mul]
  exact he ▸ hr.symm

theorem chart_normalization_pos (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x) :
    0 < ((H.disintegration U).componentWeight i /
      (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal := by
  apply ENNReal.toReal_pos
  · exact (ENNReal.div_pos (ne_of_gt ((H.disintegration U).positive_componentWeight i))
      (ENNReal.natCast_ne_top (isotropyOrder F ζ hζ U R P H i x))).ne'
  · exact (ENNReal.div_lt_top ((H.disintegration U).finite_componentWeight i).ne
      (by exact_mod_cast (isotropyOrder_pos F ζ hζ U R P H i x O).ne')).ne

open KPContLocalEnergy

 def reindexedBall {n m : ℕ} (e : Fin n ≃ Fin m) (A : LocalBall n) : LocalBall m where
  dimension_pos := by
    have hnm : n = m := by simpa using Fintype.card_congr e
    exact hnm ▸ A.dimension_pos
  center := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e A.center
  radius := A.radius
  radius_pos := A.radius_pos
 def reindexedIndex {n m : ℕ} (e : Fin n ≃ Fin m) (α : MultiIndex n 1) : MultiIndex m 1 :=
  ⟨fun j => α.val (e.symm j), by
    change (∑ j, (α.val (e.symm j)).val) ≤ 1
    rw [e.symm.sum_comp (fun i => (α.val i).val)]
    exact α.property⟩
 theorem reindexedBall_preimage {n m : ℕ} (e : Fin n ≃ Fin m) (A : LocalBall n) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) ⁻¹' (reindexedBall e A).carrier = A.carrier := by
  ext p
  simp only [LocalBall.carrier, reindexedBall, Set.mem_preimage, Metric.mem_ball]
  rw [(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).isometry.dist_eq]
private theorem index_cases {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n 1 ∨ ∃ i : Fin n, α = firstIndex i := by
  by_cases hz : ∀ i, (α.val i).val = 0
  · left
    apply Subtype.ext
    funext i
    exact Fin.ext (hz i)
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right
    refine ⟨i, ?_⟩
    have hone : (α.val i).val = 1 := by omega
    apply Subtype.ext
    funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j; simpa [firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (α.val i).val)
          (show ({i,j} : Finset (Fin n)) ⊆ Finset.univ from Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
        have h := α.property
        simp [Finset.sum_pair (Ne.symm hji), hone] at hsum
        omega
      simpa [firstIndex, hji] using hj
 theorem reindexed_zero {n m : ℕ} (e : Fin n ≃ Fin m) :
    reindexedIndex e (zeroIndex n 1) = zeroIndex m 1 := by rfl
private theorem reindexed_first {n m : ℕ} (e : Fin n ≃ Fin m) (j : Fin n) :
    reindexedIndex e (firstIndex j) = firstIndex (e j) := by
  apply Subtype.ext
  funext k
  simp [reindexedIndex, firstIndex, e.symm_apply_eq]
private theorem reindex_direction {n m : ℕ} (e : Fin n ≃ Fin m) (j : Fin n) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e (EuclideanSpace.single j 1) =
      EuclideanSpace.single (e j) 1 := by
  ext k
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, EuclideanSpace.single_apply,
    e.symm_apply_eq, Pi.single_apply]
 def pullbackTest {n m : ℕ} (e : Fin n ≃ Fin m) (A : LocalBall n)
    (φ : TestFunction A.toOpens ℂ ⊤) : TestFunction (reindexedBall e A).toOpens ℂ ⊤ where
  toFun := fun p => φ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm p)
  contDiff' := φ.contDiff.comp (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm.toHomeomorph
  tsupport_subset' := by
    let he := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm.toHomeomorph
    have hs : Function.support (φ ∘ he) = he ⁻¹' Function.support φ := rfl
    have heq : (fun p => φ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm p)) =
        φ ∘ he := by
      funext p
      simp [he, Function.comp_def, LinearIsometryEquiv.coe_toHomeomorph]
    rw [heq, tsupport]
    rw [hs, ← he.preimage_closure]
    intro p hp
    have hp' := φ.tsupport_subset hp
    have hx : (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) (he p) ∈ (reindexedBall e A).carrier := by
      rw [← Set.mem_preimage, reindexedBall_preimage]
      exact hp'
    change p ∈ (reindexedBall e A).carrier
    simpa only [he, LinearIsometryEquiv.coe_toHomeomorph,
      LinearIsometryEquiv.apply_symm_apply] using hx
 theorem reindex_test_derivative {n m : ℕ} (e : Fin n ≃ Fin m) (A : LocalBall n)
    (φ : TestFunction A.toOpens ℂ ⊤) (α : MultiIndex n 1) (p : Space n) :
    coordinateDerivative α (fun q => φ q) p =
      coordinateDerivative (reindexedIndex e α)
        (fun q => pullbackTest e A φ q) (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e p) := by
  let E : Space n ≃ₗᵢ[ℝ] Space m := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  rcases index_cases α with rfl | ⟨j,rfl⟩
  · rw [reindexed_zero]
    rw [show coordinateDerivative (zeroIndex n 1) (fun q => φ q) = (fun q => φ q) from
      KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_zeroIndex _]
    rw [show coordinateDerivative (zeroIndex m 1) (fun q => pullbackTest e A φ q) =
        (fun q => pullbackTest e A φ q) from KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_zeroIndex _]
    change φ p = φ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e p))
    rw [LinearIsometryEquiv.symm_apply_apply]
  · rw [reindexed_first]
    have hd : ∀ {k : ℕ} (i : Fin k), (firstIndex i).directions = [i] :=
      fun i => KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions i
    simp only [coordinateDerivative, hd, coordinateDerivativeList]
    change fderiv ℝ (fun q => φ q) p (EuclideanSpace.single j 1) =
      fderiv ℝ (fun q => φ (E.symm q)) (E p) (EuclideanSpace.single (e j) 1)
    have h := φ.contDiff.differentiable (by simp)
    change fderiv ℝ (fun q => φ q) p (EuclideanSpace.single j 1) =
      fderiv ℝ (φ ∘ E.symm) (E p) (EuclideanSpace.single (e j) 1)
    rw [fderiv_comp _ (h (E.symm (E p))) E.symm.differentiableAt]
    simp only [ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.symm_apply_apply]
    have hf : fderiv ℝ (E.symm : Space m → Space n) (E p) =
        E.symm.toContinuousLinearEquiv.toContinuousLinearMap := E.symm.toContinuousLinearEquiv.hasFDerivAt.fderiv
    rw [hf]
    change _ = fderiv ℝ (fun q => φ q) p (E.symm (EuclideanSpace.single (e j) 1))
    rw [← reindex_direction e j]
    simp only [E, LinearIsometryEquiv.symm_apply_apply]

 theorem reindexed_degree {n m : ℕ} (e : Fin n ≃ Fin m) (α : MultiIndex n 1) :
    (reindexedIndex e α).degree = α.degree := by
  unfold MultiIndex.degree
  change (∑ j, (α.val (e.symm j)).val) = _
  exact e.symm.sum_comp (fun i => (α.val i).val)
 def sobolevPullback {n m : ℕ} (e : Fin n ≃ Fin m) (A : LocalBall n)
    (h : IntegerSobolev (reindexedBall e A) 1) : IntegerSobolev A 1 where
  derivatives α := Lp.compMeasurePreserving (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
    (by
      have hm := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).measurePreserving.restrict_preimage
        (reindexedBall e A).toOpens.isOpen.measurableSet
      change MeasurePreserving (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
        (volume.restrict ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) ⁻¹' (reindexedBall e A).carrier))
        (volume.restrict (reindexedBall e A).carrier) at hm
      rw [reindexedBall_preimage] at hm
      exact hm) (h.derivatives (reindexedIndex e α))
  weak_derivatives := by
    intro α φ
    let E : Space n ≃ₗᵢ[ℝ] Space m := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
    have hm : MeasurePreserving E (volume.restrict A.carrier)
        (volume.restrict (reindexedBall e A).carrier) := by
      have hh := E.measurePreserving.restrict_preimage (reindexedBall e A).toOpens.isOpen.measurableSet
      change MeasurePreserving E
        (volume.restrict (E ⁻¹' (reindexedBall e A).carrier))
        (volume.restrict (reindexedBall e A).carrier) at hh
      change MeasurePreserving (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
        (volume.restrict ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) ⁻¹' (reindexedBall e A).carrier))
        (volume.restrict (reindexedBall e A).carrier) at hh
      rw [reindexedBall_preimage] at hh
      exact hh
    have he := h.weak_derivatives (reindexedIndex e α) (pullbackTest e A φ)
    rw [reindexed_degree] at he
    have hz := reindexed_zero e
    have hz' : reindexedIndex e (⟨fun _ => 0, by simp⟩ : MultiIndex n 1) =
        (⟨fun _ => 0, by simp⟩ : MultiIndex m 1) := hz
    rw [← hm.integral_comp E.toHomeomorph.measurableEmbedding
      (fun x => h.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex m 1) x *
        coordinateDerivative (reindexedIndex e α) (fun y => pullbackTest e A φ y) x),
      ← hm.integral_comp E.toHomeomorph.measurableEmbedding
        (fun x => h.derivatives (reindexedIndex e α) x * pullbackTest e A φ x)] at he
    have hval := Lp.coeFn_compMeasurePreserving (h.derivatives (reindexedIndex e (zeroIndex n 1))) hm
    have hder := Lp.coeFn_compMeasurePreserving (h.derivatives (reindexedIndex e α)) hm
    have hl : (∫ x in A.carrier,
        (Lp.compMeasurePreserving E hm (h.derivatives (reindexedIndex e (zeroIndex n 1)))) x *
          coordinateDerivative α (fun y => φ y) x) =
        ∫ x in A.carrier, h.derivatives (zeroIndex m 1) (E x) *
          coordinateDerivative (reindexedIndex e α) (fun y => pullbackTest e A φ y) (E x) := by
      apply integral_congr_ae
      filter_upwards [hval] with x hx
      rw [hx, reindexed_zero, reindex_test_derivative]
      rfl
    have hr : (∫ x in A.carrier,
        (Lp.compMeasurePreserving E hm (h.derivatives (reindexedIndex e α))) x * φ x) =
        ∫ x in A.carrier, h.derivatives (reindexedIndex e α) (E x) * pullbackTest e A φ (E x) := by
      apply integral_congr_ae
      filter_upwards [hder] with x hx
      rw [hx]
      change h.derivatives (reindexedIndex e α) (E x) * φ x =
        h.derivatives (reindexedIndex e α) (E x) * φ (E.symm (E x))
      rw [LinearIsometryEquiv.symm_apply_apply]
    change (∫ x in A.carrier, (Lp.compMeasurePreserving E hm
        (h.derivatives (reindexedIndex e (zeroIndex n 1)))) x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ)^α.degree * (∫ x in A.carrier, (Lp.compMeasurePreserving E hm
        (h.derivatives (reindexedIndex e α))) x * φ x)
    rw [hl, hr]
    exact he

 def canonicalIndex : Fin (KPCuspLogShape.dimension F * 3) ≃
    Fin (3 * KPContCotangentActualOverlap.d F) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr
    (KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm (Equiv.refl _)).trans
      (KPContActualCotangentChartRestriction.coefficientIndex (F := F)))

private theorem canonical_coordinate (p : Space (KPCuspLogShape.dimension F * 3)) :
    KPContActualSectorChartEquivariantInputs.toActual (F := F) (ζ := ζ) (hζ := hζ)
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (canonicalIndex F ζ hζ) p) = coordinates F p := by
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [KPContActualSectorChartEquivariantInputs.toActual,
      KPContActualSectorChartEquivariantInputs.baseReindex,
      KPContCotangentActualOverlap.labeledA, CotangentLogCoframe.A,
      KPContActualCotangentChartRestriction.coefficientIndex, canonicalIndex,
      LinearIsometryEquiv.piLpCongrLeft_apply, coordinates, KPArchRealCoordinates.coordinates]
  · simp [KPContActualSectorChartEquivariantInputs.toActual,
      KPContActualSectorChartEquivariantInputs.baseReindex,
      KPContCotangentActualOverlap.labeledA, CotangentLogCoframe.A,
      KPContActualCotangentChartRestriction.coefficientIndex, canonicalIndex,
      LinearIsometryEquiv.piLpCongrLeft_apply, coordinates, KPArchRealCoordinates.coordinates]

private theorem canonical_ball_inside (i : Fin (H.atlas U).componentCount)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (a : ShrunkChart F ζ hζ U R P H) (ha : coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain) :
    KPContActualSectorFormWeakLocalization.InteriorBall (H := H) a
      (reindexedBall (canonicalIndex F ζ hζ) A) := by
  constructor
  · change IsCompact (closure (Metric.ball
      (reindexedBall (canonicalIndex F ζ hζ) A).center A.radius))
    rw [closure_ball _ (ne_of_gt A.radius_pos)]
    exact isCompact_closedBall _ _
  · intro p hp
    let E : Space (KPCuspLogShape.dimension F * 3) ≃ₗᵢ[ℝ]
        Space (3 * KPContCotangentActualOverlap.d F) :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (canonicalIndex F ζ hζ)
    have hp' : E.symm p ∈ KPContLocalCubeEmbedding.closedCarrier A := by
      change E.symm p ∈ Metric.closedBall A.center A.radius
      change p ∈ closure (Metric.ball (E A.center) A.radius) at hp
      rw [closure_ball _ (ne_of_gt A.radius_pos)] at hp
      rw [Metric.mem_closedBall] at hp ⊢
      have hd := E.isometry.dist_eq (E.symm p) A.center
      rw [LinearIsometryEquiv.apply_symm_apply] at hd
      rw [hd] at hp
      exact hp
    change KPContActualSectorChartEquivariantInputs.toActual p ∈ a.domain
    have he := canonical_coordinate F ζ hζ (E.symm p)
    change KPContActualSectorChartEquivariantInputs.toActual (E (E.symm p)) = _ at he
    rw [LinearIsometryEquiv.apply_symm_apply] at he
    rw [he]
    exact ha ⟨_,hp',rfl⟩

private theorem exists_sobolev_value (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (v : (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain) :
    ∃ ξ : IntegerSobolev A 1, value ξ = restriction F ζ hζ U R P H i x O m A hA v.val := by
  obtain ⟨a, hai, hac, ha⟩ := closed_ball_shrinking F ζ hζ U R P H i x O A hA
  let e := canonicalIndex F ζ hζ
  let E : Space (KPCuspLogShape.dimension F * 3) ≃ₗᵢ[ℝ]
      Space (3 * KPContCotangentActualOverlap.d F) := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let B := reindexedBall e A
  have hB := canonical_ball_inside F ζ hζ U R P H i A a ha
  obtain ⟨s, r, hs, hr, hw⟩ := (kp_cont_actual_sector_form_weak_localization
    F ζ hζ μG hμG U R hR P H realization).closed_gradient v
  obtain ⟨ε,hε⟩ := QuotientGroup.mk_surjective m
  change phaseClass F ζ hζ U ε = m at hε
  obtain ⟨h, hv, hd⟩ := hw a B hB ε
  obtain ⟨g,hg,hgLp,hgU,f₀,hf₀,hfLp,havg,hfU,hgen,hiso⟩ :=
    KPContSectorExactBorelRepresentatives.exists_exact_borel_representative F ζ hζ R U v.val
  let f : BorelL2Scalars F ζ hζ U R := ⟨⟨f₀,hgen⟩,hf₀,hfLp⟩
  have hf : scalarEmbedding F ζ hζ U R P H f = v.val := by
    apply Subtype.ext
    rw [scalarEmbedding_coe]
    exact hfU
  have ht : mk F ζ hζ U R P H s = mk F ζ hζ U R P H (borelS F ζ hζ U R P H f) := by
    rw [← hs, ← sectorLineIsometry_toSector F ζ hζ U R P H f]
    exact congrArg (sectorLineIsometry F ζ hζ U R P H) hf.symm
  have hscalar := KPContActualSectorCoordinateNullEquivalence.scalar_ae_of_mk_eq s
    (borelS F ζ hζ U R P H f) ht a B hB
  have hm : MeasurePreserving E (volume.restrict A.carrier) (volume.restrict B.carrier) := by
    have hh := E.measurePreserving.restrict_preimage B.toOpens.isOpen.measurableSet
    change MeasurePreserving E (volume.restrict (E ⁻¹' B.carrier)) (volume.restrict B.carrier) at hh
    have he : E ⁻¹' B.carrier = A.carrier := reindexedBall_preimage e A
    rwa [he] at hh
  have hvp := hm.quasiMeasurePreserving.ae (hv.and hscalar)
  refine ⟨sobolevPullback e A h, ?_⟩
  apply Lp.ext
  have hp := Lp.coeFn_compMeasurePreserving (h.derivatives (reindexedIndex e (zeroIndex _ 1))) hm
  have hre := restriction_representative F ζ hζ U R P H i x O m A hA v.val f hf
  filter_upwards [hp, hvp, hre, ae_restrict_mem A.toOpens.isOpen.measurableSet] with p hp hvp hre hpa
  change value (sobolevPullback e A h) p = restriction F ζ hζ U R P H i x O m A hA v.val p
  change (Lp.compMeasurePreserving E hm (h.derivatives (reindexedIndex e (zeroIndex _ 1)))) p = _
  rw [hp, reindexed_zero]
  change h.derivatives (KPContActualSectorFormWeakLocalization.zeroIndex _) (E p) = _
  rw [hvp.1, hre]
  have hsp : KPContActualSectorFormWeakLocalization.scalarCoordinate s a (E p) =
      KPContActualSectorFormWeakLocalization.scalarCoordinate (borelS F ζ hζ U R P H f) a (E p) := hvp.2
  rw [hsp, ← hε, frameCoefficient_class]
  congr 1
  have hmem : (KPContActualSectorChartEquivariantInputs.baseReindex (F := F)).symm (E p) ∈
      KPContCotangentOverlapRationalBranches.omega a :=
    hB.2 (subset_closure (show E p ∈ B.carrier from by
      rw [← Set.mem_preimage, reindexedBall_preimage]; exact hpa))
  simp only [KPContActualSectorFormWeakLocalization.scalarCoordinate,
    KPContActualSectorTestDifferentialDescent.liftExtension]
  rw [dif_pos hmem]
  simp only [KPContActualSectorSmoothTestModules.sectionFields,
    KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
    KPContCotangentActualOverlap.ChartKind.representative, map_one, Units.val_one, one_mul, one_smul]
  change ((borelS F ζ hζ U R P H f).val a.component).val
    (KPContActualSectorChartEquivariantInputs.toActual (E p)) = _
  rw [hai]
  have he := canonical_coordinate F ζ hζ p
  change KPContActualSectorChartEquivariantInputs.toActual (E p) = coordinates F p at he
  rw [he]
  rfl

private theorem diagonal_pairing {n : ℕ} (a : Fin n → ℝ) (b c : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, ((Matrix.diagonal a) i j : ℂ) * b j * c i) =
      ∑ i : Fin n, (a i : ℂ) * b i * c i := by
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.diagonal_apply, apply_ite (fun t : ℝ => (t : ℂ)),
    mul_ite, ite_mul]

private theorem weakEquation_zero_of_diagonal_pairing {n : ℕ} {A : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (D : Coefficients A cρ Cρ κ Λ)
    (ρ : Space n → ℝ) (g : Space n → Fin n → ℝ)
    (hρ : D.density = ρ) (hg : D.matrix = fun p => Matrix.diagonal (g p))
    (ξ : IntegerSobolev A 1) (h : BallL2 A)
    (he : ∀ φ : TestFunction A.toOpens ℂ ⊤,
      (∫ p in A.carrier, (ρ p : ℂ) * ∑ j, (g p j : ℂ) * gradient ξ j p *
        star (coordinateDerivativeList [j] (fun q => φ q) p)) =
      ∫ p in A.carrier, (ρ p : ℂ) * h p * star (φ p)) :
    WeakEquation D 0 ξ h := by
  intro φ
  simp only [zero_mul, sub_zero]
  rw [hρ,hg]
  have hdiag : (fun p => (ρ p : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
      ((Matrix.diagonal (g p)) i j : ℂ) * gradient ξ j p *
        star (coordinateDerivativeList [i] (fun q => φ q) p)) =
      fun p => (ρ p : ℂ) * ∑ j : Fin n, (g p j : ℂ) * gradient ξ j p *
        star (coordinateDerivativeList [j] (fun q => φ q) p) := by
    funext p
    rw [diagonal_pairing]
  rw [hdiag]
  exact he φ

theorem exists_xi (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    {cρ Cρ κ Λ : ℝ} (D : KPContLocalEnergy.Coefficients A cρ Cρ κ Λ)
    (hρ : D.density = density F)
    (hg : D.matrix = fun p => Matrix.diagonal (fun j =>
      let ik := finProdFinEquiv.symm j
      if ik.2 = 2 then 1 else Real.exp (2 * (coordinates F p ik.1).2)))
    (u : (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization).domain)
    (z : ℂ) :
    ∃ ξ : IntegerSobolev A 1,
      KPContLocalEnergy.value ξ = restriction F ζ hζ U R P H i x O m A hA u.val ∧
      KPContLocalEnergy.WeakEquation D z ξ
        (restriction F ζ hζ U R P H i x O m A hA
          (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization u - z • u.val)) := by
  have hv := (kp_cont_actual_sector_friedrichs_synthesis
    F ζ hζ μG hμG U R hR P H realization).variational
  obtain ⟨hu, hvar⟩ := (hv u.val
    (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization u)).mp
      ⟨u.property,rfl⟩
  obtain ⟨ξ,hξ⟩ := exists_sobolev_value F ζ hζ U R P H μG hμG hR realization i x O m A hA ⟨u.val,hu⟩
  refine ⟨ξ,hξ,?_⟩
  have hzero : WeakEquation D 0 ξ
      (restriction F ζ hζ U R P H i x O m A hA
        (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization u)) := by
    apply weakEquation_zero_of_diagonal_pairing D (density F)
      (fun p j => if (finProdFinEquiv.symm j).2 = 2 then 1 else
        Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) hρ hg
    intro φ
    obtain ⟨f,_,_,hs,hg'⟩ := KPContFriedrichsChartProjectedPairings.projected_test_pairings
      F ζ hζ U R P H μG hμG hR realization i x O m A hA φ
    have he := congrArg star (hvar
      (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f))
    change star (closedGradientForm
      (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization)
      ⟨u.val,hu⟩ (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f)) =
      star (inner ℂ (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization u)
        (KPContActualSectorTestEmbeddings.iota f)) at he
    rw [hg' ⟨u.val,hu⟩ ξ hξ, hs] at he
    have hc : (((H.disintegration U).componentWeight i /
        (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℂ) ≠ 0 := by
      exact_mod_cast (chart_normalization_pos F ζ hζ U R P H i x O).ne'
    exact mul_left_cancel₀ hc he
  have ht := weakEquation_shift D ξ _ hzero z
  rw [hξ] at ht
  simpa only [map_sub, map_smul] using ht

end DedekindZetaZeroFree.KPContFriedrichsChartVariational

end
