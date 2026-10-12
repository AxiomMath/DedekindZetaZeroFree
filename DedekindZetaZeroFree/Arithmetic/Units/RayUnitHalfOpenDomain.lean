module

public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitLogLattice
public import DedekindZetaZeroFree.Theta.Unfolding.MixedRadialJacobian

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField Module MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type) [Field K] [NumberField K]

def logHyperplaneCoordinateMap (v : InfinitePlace K) :
    RayCoset.logHyperplane K →ₗ[ℝ] ({w : InfinitePlace K // w ≠ v} → ℝ) where
  toFun h w := h.val w.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bijective_logHyperplaneCoordinateMap (v : InfinitePlace K) :
    Function.Bijective (logHyperplaneCoordinateMap K v) := by
  have hv : (v.mult : ℝ) ≠ 0 := by exact_mod_cast v.mult_ne_zero
  have hsum (h : RayCoset.logHyperplane K) :
      ∑ w : InfinitePlace K, (w.mult : ℝ) * h.val w = 0 := by
    simpa [RayCoset.logHyperplane, RayCoset.weightedLogSum] using h.property
  constructor
  · intro h g heq
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst w
      have hrest : ∑ w ∈ Finset.univ.erase v, (w.mult : ℝ) * h.val w =
          ∑ w ∈ Finset.univ.erase v, (w.mult : ℝ) * g.val w := by
        apply Finset.sum_congr rfl
        intro w hw
        congr 1
        exact congr_fun heq ⟨w, (Finset.mem_erase.mp hw).1⟩
      have hh := hsum h
      have hg := hsum g
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hh hg
      apply (mul_left_cancel₀ hv)
      linarith
    · exact congr_fun heq ⟨w, hw⟩
  · intro x
    let y : InfinitePlace K → ℝ := fun w =>
      if hw : w = v then
        -(∑ z : {w : InfinitePlace K // w ≠ v}, (z.val.mult : ℝ) * x z) /
          (v.mult : ℝ)
      else x ⟨w, hw⟩
    have hy : ∑ w : InfinitePlace K, (w.mult : ℝ) * y w = 0 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ v]
      have he (w : {w : InfinitePlace K // w ≠ v}) : y w.val = x w := by
        simp [y, w.property]
      simp only [y, dif_pos rfl] at *
      simp only [he]
      field_simp
      ring
    refine ⟨⟨y, ?_⟩, ?_⟩
    · simpa [RayCoset.logHyperplane, RayCoset.weightedLogSum] using hy
    · funext w
      simp [logHyperplaneCoordinateMap, y, w.property]

def logHyperplaneCoordinateEquiv (v : InfinitePlace K) :
    RayCoset.logHyperplane K ≃L[ℝ] ({w : InfinitePlace K // w ≠ v} → ℝ) :=
  (LinearEquiv.ofBijective (logHyperplaneCoordinateMap K v)
    (bijective_logHyperplaneCoordinateMap K v)).toContinuousLinearEquiv

def normalizedLogHaar : Measure (RayCoset.logHyperplane K) :=
  ENNReal.ofReal (1 / (Units.dirichletUnitTheorem.w₀ (K := K)).mult : ℝ) •
    Measure.map (logHyperplaneCoordinateEquiv K
      (Units.dirichletUnitTheorem.w₀ (K := K))).symm volume

instance isAddHaarMeasure_normalizedLogHaar :
    (normalizedLogHaar K).IsAddHaarMeasure := by
  unfold normalizedLogHaar
  apply Measure.IsAddHaarMeasure.smul
  · exact (ENNReal.ofReal_pos.mpr (one_div_pos.mpr
      (by exact_mod_cast (Units.dirichletUnitTheorem.w₀ (K := K)).mult_pos))).ne'
  · exact ENNReal.ofReal_ne_top

def radialAngularLogMap (sh : ℝ × RayCoset.logHyperplane K) :
    InfinitePlace K → ℝ :=
  fun v => sh.1 / (Module.finrank ℚ K : ℝ) + sh.2.val v

variable {ι : Type} [Fintype ι] [DecidableEq ι]
 def split (v : ι) : (ι → ℝ) ≃ᵐ ℝ × ({w : ι // w ≠ v} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun w => w = v)).trans
    ((MeasurableEquiv.piUnique (fun _ : {w : ι // w = v} => ℝ)).prodCongr
      (MeasurableEquiv.refl _))
private theorem split_mp (v : ι) : MeasurePreserving (split v) volume volume := by
  apply MeasurePreserving.comp
    ((volume_preserving_piUnique (fun _ : {w : ι // w = v} => ℝ)).prod
      (MeasurePreserving.id (volume : Measure ({w : ι // w ≠ v} → ℝ))))
    (by
      convert (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ))
        (fun w => w = v)) using 1
      all_goals congr! 3
      have he : Fintype.subtypeEq v = (Subtype.fintype (fun w : ι => w = v)) := Subsingleton.elim _ _
      simp only [volume_pi, he]
      congr! 4)

variable (K : Type) [Field K] [NumberField K]
 def rowMap (v : InfinitePlace K) : (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ) where
  toFun x := Function.update x v (RayCoset.weightedLogSum K x)
  map_add' x y := by ext w; by_cases hw : w = v <;> simp [hw]
  map_smul' c x := by ext w; by_cases hw : w = v <;> simp [hw]
 theorem rowMap_det (v : InfinitePlace K) : LinearMap.det (rowMap K v) = (v.mult : ℝ) := by
  have he : LinearMap.toMatrix' (rowMap K v) =
      (1 : Matrix (InfinitePlace K) (InfinitePlace K) ℝ).updateRow v
        (fun w => (w.mult : ℝ)) := by
    ext w z
    simp only [LinearMap.toMatrix'_apply, rowMap, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hw : w = v
    · subst w
      simp [RayCoset.weightedLogSum, Matrix.updateRow, Function.update, Pi.single_apply, eq_comm]
    · simp [hw, Matrix.updateRow, Function.update, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [← LinearMap.det_toMatrix', he]
  have hs : (fun w : InfinitePlace K => (w.mult : ℝ)) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) • (1 : Matrix (InfinitePlace K) (InfinitePlace K) ℝ) w := by
    ext z
    simp [Matrix.one_apply, eq_comm]
  rw [hs, Matrix.det_updateRow_sum]
  simp

 def rowEquiv (v : InfinitePlace K) :
    (InfinitePlace K → ℝ) ≃L[ℝ] (InfinitePlace K → ℝ) :=
  (LinearEquiv.ofIsUnitDet (v := Pi.basisFun ℝ (InfinitePlace K))
    (v' := Pi.basisFun ℝ (InfinitePlace K)) (f := rowMap K v)
    (by rw [LinearMap.det_toMatrix, rowMap_det];
        exact isUnit_iff_ne_zero.mpr (by exact_mod_cast v.mult_ne_zero))).toContinuousLinearEquiv

private theorem weightedLogSum_radialAngularLogMap (sh : ℝ × RayCoset.logHyperplane K) :
    RayCoset.weightedLogSum K (radialAngularLogMap K sh) = sh.1 := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hh : ∑ w : InfinitePlace K, (w.mult : ℝ) * sh.2.val w = 0 := by
    have hmem := (sh.2 : RayCoset.logHyperplane K).property
    change RayCoset.weightedLogSum K sh.2.val = 0 at hmem
    simpa [RayCoset.weightedLogSum] using hmem
  simp only [RayCoset.weightedLogSum, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, radialAngularLogMap, mul_add, Finset.sum_add_distrib]
  rw [hh, add_zero, ← Finset.sum_mul]
  have hs : ∑ w : InfinitePlace K, (w.mult : ℝ) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast InfinitePlace.sum_mult_eq (K := K)
  rw [hs]
  field_simp

theorem map_volume_prod_normalizedLogHaar_radialAngularLogMap :
    Measure.map (radialAngularLogMap K)
      (volume.prod (normalizedLogHaar K)) = volume := by
  let v := Units.dirichletUnitTheorem.w₀ (K := K)
  let c := ENNReal.ofReal (1 / (v.mult : ℝ))
  let coord := logHyperplaneCoordinateEquiv K v
  let e := ((rowEquiv K v).toHomeomorph.toMeasurableEquiv).trans (split v)
  have hr : Measurable (radialAngularLogMap K) := by
    apply measurable_pi_lambda
    intro w
    exact (measurable_fst.div_const _).add
      ((measurable_pi_apply w).comp (measurable_subtype_coe.comp measurable_snd))
  have hv : (v.mult : ℝ) ≠ 0 := by exact_mod_cast v.mult_ne_zero
  have er (x : InfinitePlace K → ℝ) : e x =
      (RayCoset.weightedLogSum K x, fun w : {w : InfinitePlace K // w ≠ v} => x w.val) := by
    apply Prod.ext
    · change Function.update x v (RayCoset.weightedLogSum K x) v = _
      simp
    · funext w
      change Function.update x v (RayCoset.weightedLogSum K x) w.val = _
      simp [w.property]
  have hev : Measure.map e volume = c • (volume.prod volume) := by
    change Measure.map ((split v) ∘ (rowEquiv K v)) volume = _
    rw [← Measure.map_map (split v).measurable (rowEquiv K v).continuous.measurable]
    have hrow : Measure.map (rowEquiv K v) volume = c • volume := by
      change Measure.map (rowMap K v) volume = _
      rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [rowMap_det]; exact hv),
        rowMap_det, abs_of_pos (inv_pos.mpr (by exact_mod_cast v.mult_pos))]
      simp [c, one_div]
    rw [hrow, Measure.map_smul c (split v).measurable.aemeasurable, (split_mp v).map_eq]
    rfl
  let shear : ℝ × ({w : InfinitePlace K // w ≠ v} → ℝ) →
      ℝ × ({w : InfinitePlace K // w ≠ v} → ℝ) :=
    fun sx => (sx.1, fun w => sx.1 / (Module.finrank ℚ K : ℝ) + sx.2 w)
  have hs : MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
    exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun s (x : {w : InfinitePlace K // w ≠ v} → ℝ) =>
        fun w => s / (Module.finrank ℚ K : ℝ) + x w)
      (by
        apply measurable_pi_lambda
        intro w
        exact (measurable_fst.div_const _).add ((measurable_pi_apply w).comp measurable_snd))
      (Filter.Eventually.of_forall (fun s =>
        (measurePreserving_add_left (volume : Measure ({w : InfinitePlace K // w ≠ v} → ℝ))
          (fun _ => s / (Module.finrank ℚ K : ℝ))).map_eq))
  have hc : Measure.map (Prod.map (id : ℝ → ℝ) coord.symm) (volume.prod volume) =
      volume.prod (Measure.map coord.symm volume) := by
    rw [← Measure.map_prod_map _ _ measurable_id coord.symm.continuous.measurable,
      Measure.map_id]
  have hecomp : e ∘ radialAngularLogMap K ∘ Prod.map (id : ℝ → ℝ) coord.symm = shear := by
    funext sx
    rw [Function.comp_apply, Function.comp_apply, er,
      weightedLogSum_radialAngularLogMap]
    apply Prod.ext
    · rfl
    funext w
    change sx.1 / (Module.finrank ℚ K : ℝ) +
        (coord.symm sx.2).val w.val = _
    have heval := congr_fun (coord.apply_symm_apply sx.2) w
    change (coord.symm sx.2).val w.val = sx.2 w at heval
    exact congrArg (_ + ·) heval
  apply e.measurableEmbedding.map_injective
  rw [hev]
  change Measure.map e (Measure.map (radialAngularLogMap K)
    (volume.prod (c • Measure.map coord.symm volume))) = _
  rw [Measure.prod_smul_right, Measure.map_smul c hr.aemeasurable,
    Measure.map_smul c e.measurable.aemeasurable]
  congr 1
  rw [← hc, Measure.map_map hr (measurable_id.prodMap coord.symm.continuous.measurable),
    Measure.map_map e.measurable (hr.comp (measurable_id.prodMap coord.symm.continuous.measurable)),
    hecomp, hs.map_eq]

def positiveRadialHaar : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun t => ENNReal.ofReal (t⁻¹))

private theorem map_log_positiveRadialHaar :
    Measure.map Real.log positiveRadialHaar = volume := by
  have himage : Real.log '' Set.Ioi (0 : ℝ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    exact ⟨Real.exp s, Real.exp_pos s, Real.log_exp s⟩
  have hj := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure ℝ) measurableSet_Ioi.nullMeasurableSet
    (f := Real.log) (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (t⁻¹))
    (fun t ht => (Real.hasDerivAt_log (ne_of_gt ht)).hasFDerivAt.hasFDerivWithinAt)
    (fun a ha b hb hab => Real.log_injOn_pos ha hb hab)
  rw [himage, Measure.restrict_univ] at hj
  convert hj using 1
  unfold positiveRadialHaar
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  congr 1
  have hd : (ContinuousLinearMap.toSpanSingleton ℝ (t⁻¹)).det = t⁻¹ := by
    have he : (ContinuousLinearMap.toSpanSingleton ℝ (t⁻¹)).toLinearMap =
        t⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
      ext x
      simp [mul_comm]
    rw [ContinuousLinearMap.det, he, LinearMap.det_smul]
    simp
  rw [hd, abs_of_pos (inv_pos.mpr ht)]

def positiveRadialAngularLogMap (th : ℝ × RayCoset.logHyperplane K) :
    InfinitePlace K → ℝ :=
  radialAngularLogMap K (Real.log th.1, th.2)

theorem map_positiveRadialHaar_prod_normalizedLogHaar :
    Measure.map (positiveRadialAngularLogMap K)
      (positiveRadialHaar.prod (normalizedLogHaar K)) = volume := by
  letI : SFinite positiveRadialHaar := by
    unfold positiveRadialHaar
    infer_instance
  have hm : Measurable (radialAngularLogMap K) := by
    apply measurable_pi_lambda
    intro v
    exact (measurable_fst.div_const _).add
      ((measurable_pi_apply v).comp (measurable_subtype_coe.comp measurable_snd))
  have hprod : Measure.map (Prod.map Real.log id)
      (positiveRadialHaar.prod (normalizedLogHaar K)) =
      volume.prod (normalizedLogHaar K) := by
    rw [← Measure.map_prod_map _ _ Real.measurable_log measurable_id,
      map_log_positiveRadialHaar, Measure.map_id]
  change Measure.map (radialAngularLogMap K ∘ Prod.map Real.log id) _ = volume
  rw [← Measure.map_map hm (Real.measurable_log.prodMap measurable_id), hprod]
  exact map_volume_prod_normalizedLogHaar_radialAngularLogMap K

end DedekindZetaZeroFree.AbelianQuotient.Theta

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable (K : Type) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)

def rayUnitRealLogBasis :
    Basis (Fin (NumberField.Units.rank K)) ℝ (logHyperplane K) := by
  letI := isZLattice_rayUnitLogLattice K m hm
  exact (rayUnitLogBasis K m hm).ofZLatticeBasis ℝ

def rayUnitHalfOpenDomain : Set (logHyperplane K) :=
  ZSpan.fundamentalDomain (rayUnitRealLogBasis K m hm)

theorem measurableSet_rayUnitHalfOpenDomain :
    MeasurableSet (rayUnitHalfOpenDomain K m hm) := by
  exact ZSpan.fundamentalDomain_measurableSet _

theorem isCompact_closure_rayUnitHalfOpenDomain :
    IsCompact (closure (rayUnitHalfOpenDomain K m hm)) := by
  exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure

theorem isAddFundamentalDomain_rayUnitHalfOpenDomain :
    IsAddFundamentalDomain (rayUnitLogLattice K m)
      (rayUnitHalfOpenDomain K m hm) (Theta.normalizedLogHaar K) := by
  letI := isZLattice_rayUnitLogLattice K m hm
  exact ZLattice.isAddFundamentalDomain (rayUnitLogBasis K m hm) _

def rayUnitDomainVolume : ℝ :=
  (Theta.normalizedLogHaar K).real (rayUnitHalfOpenDomain K m hm)

theorem measure_rayUnitHalfOpenDomain_lt_top :
    Theta.normalizedLogHaar K (rayUnitHalfOpenDomain K m hm) < ⊤ := by
  exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
