module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.WeightedScalarBallRestriction

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorBallRestriction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualSectorCoordinateNullEquivalence

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

open KPContActualCotangentPieceHilbertSum KPContActualCotangentChartRestriction
open KPContCotangentActualGenuineTwistIsotropy

namespace CoordinateConstruction
variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure α} {e : α → β}

omit [NormedSpace ℂ E] in
 theorem extendMem (he : MeasurableEmbedding e) (f : Lp E 2 μ) :
    MemLp (Function.extend e f 0) 2 (Measure.map e μ) := by
  rw [he.memLp_map_measure_iff]
  simpa only [Function.extend_comp he.injective] using Lp.memLp f

 def extendLinear (he : MeasurableEmbedding e) :
    Lp E 2 μ →ₗ[ℂ] Lp E 2 (Measure.map e μ) where
  toFun f := (extendMem he f).toLp (Function.extend e f 0)
  map_add' f g := by
    apply Lp.ext
    apply he.ae_map_iff.mpr
    have hp (f : Lp E 2 μ) : ∀ᵐ x ∂μ,
        (extendMem he f).toLp (Function.extend e f 0) (e x) = f x := by
      have hh := (extendMem he f).coeFn_toLp
      rw [Filter.EventuallyEq, he.ae_map_iff] at hh
      filter_upwards [hh] with x hx
      exact hx.trans (congrFun (Function.extend_comp he.injective f 0) x)
    have ha := Lp.coeFn_add ((extendMem he f).toLp _) ((extendMem he g).toLp _)
    rw [Filter.EventuallyEq, he.ae_map_iff] at ha
    filter_upwards [hp (f+g), hp f, hp g, ha, Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.add_apply, h2, h3, h5]
  map_smul' c f := by
    apply Lp.ext
    apply he.ae_map_iff.mpr
    have hp (f : Lp E 2 μ) : ∀ᵐ x ∂μ,
        (extendMem he f).toLp (Function.extend e f 0) (e x) = f x := by
      have hh := (extendMem he f).coeFn_toLp
      rw [Filter.EventuallyEq, he.ae_map_iff] at hh
      filter_upwards [hh] with x hx
      exact hx.trans (congrFun (Function.extend_comp he.injective f 0) x)
    have hs := Lp.coeFn_smul c ((extendMem he f).toLp _)
    rw [Filter.EventuallyEq, he.ae_map_iff] at hs
    filter_upwards [hp (c • f), hp f, hs, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h3, Pi.smul_apply, h2, h4]

 def extendCLM (he : MeasurableEmbedding e) :
    Lp E 2 μ →L[ℂ] Lp E 2 (Measure.map e μ) :=
  (extendLinear he).mkContinuous 1 (by
    intro f
    change ‖(extendMem he f).toLp _‖ ≤ 1 * ‖f‖
    rw [Lp.norm_toLp, he.eLpNorm_map_measure,
      Function.extend_comp he.injective, ← Lp.norm_def]
    simp)
end CoordinateConstruction

variable (a : ActualChart (U := U) (H := H))

 def emb (y : a.domain) := fromActual (ζ := ζ) (hζ := hζ) y.val
 def actualEquiv : EuclideanSpace ℝ (Fin (3 * d F)) ≃ᵐ
    KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := toActual (ζ := ζ) (hζ := hζ)
  invFun := fromActual (ζ := ζ) (hζ := hζ)
  left_inv x := by
    unfold fromActual toActual
    have hh : ∀ y : M F, labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) y) = y := by
      intro y; apply PiLp.ext; intro k; simp [labeledAInv, labeledA]
    rw [hh, LinearIsometryEquiv.apply_symm_apply]
  right_inv y := by
    simp only [toActual, fromActual, LinearIsometryEquiv.symm_apply_apply]
    funext k
    simp [labeledA, labeledAInv]
  measurable_toFun := by
    change Measurable (toActual (ζ := ζ) (hζ := hζ))
    apply Continuous.measurable
    unfold toActual labeledA
    fun_prop
  measurable_invFun := by
    change Measurable (fromActual (ζ := ζ) (hζ := hζ))
    apply Continuous.measurable
    unfold fromActual labeledAInv
    fun_prop
 theorem emb_meas : MeasurableEmbedding (emb a) :=
  (actualEquiv (ζ := ζ) (hζ := hζ)).symm.measurableEmbedding.comp
    (MeasurableEmbedding.subtype_coe a.domain_open.measurableSet)
 def flatLp : Lp (E F) 2 a.liftedMeasure →L[ℂ] Lp (E F) 2 (measure a) := by
  have hm : Measure.map (emb a) a.liftedMeasure = measure a :=
    lifted_measure_transport (a := a)
  exact hm ▸ CoordinateConstruction.extendCLM (emb_meas a)
private theorem flatLp_pull (f : Lp (E F) 2 a.liftedMeasure) :
    (fun y => flatLp a f (emb a y)) =ᵐ[a.liftedMeasure] f := by
  have hm := lifted_measure_transport (a := a)
  have hp : ∀ (ν : Measure (Space (3*d F))) (hm : Measure.map (emb a) a.liftedMeasure = ν),
      (fun y => (hm ▸ CoordinateConstruction.extendCLM (emb_meas a)) f (emb a y)) =ᵐ[a.liftedMeasure] f := by
    intro ν hm
    subst ν
    have h := (CoordinateConstruction.extendMem (emb_meas a) f).coeFn_toLp
    rw [Filter.EventuallyEq, (emb_meas a).ae_map_iff] at h
    filter_upwards [h] with y hy
    exact hy.trans (congrFun (Function.extend_comp (emb_meas a).injective f 0) y)
  exact hp _ hm
 def cotangentFlat : KPContActualSectorCotangentL2.V F ζ hζ U R P H →L[ℂ]
    Lp (E F) 2 (measure a) :=
  (flatLp a).comp ((Q a).subtypeL.comp
    (res (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H) a))
private theorem cotangentFlat_pull (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v) :
    (fun y => cotangentFlat a v (emb a y)) =ᵐ[a.liftedMeasure] localCoefficient a r.val := by
  have h := flatLp_pull a ((res (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H) a v).val)
  refine h.trans ?_
  apply res_represented
  symm
  change (KPContActualSectorCotangentL2.intrinsicClass F ζ hζ U R P H) v = toAeQuotient r
  rw [← hr]
  exact (KPContActualSectorCotangentL2.intrinsicClass F ζ hζ U R P H).apply_symm_apply _

 def decodeIndex (j : Fin (3*d F)) : Fin (d F) × Fin 3 :=
  let ik := (coefficientIndex (F := F)).symm j
  (ik.1, ![1,2,0] ik.2)
 def decodeFactor (j : Fin (3*d F)) (x : Space (3*d F)) : ℂ :=
  let ik := (coefficientIndex (F := F)).symm j
  if ik.2 = 2 then 1 else (Real.exp (-((baseReindex (F := F)).symm x) (ik.1,2)) : ℂ)
private theorem decode_cont (j : Fin (3*d F)) : Continuous (decodeFactor (F := F) j) := by
  unfold decodeFactor
  dsimp only
  split_ifs <;> fun_prop
private theorem decoder_eq (W : Family (U := U) (H := H)) (x : Space (3*d F)) (j : Fin (3*d F)) :
    coordinateW W a x j = decodeFactor j x *
      (liftExtension a (coefficient W a) ((baseReindex (F := F)).symm x)) (decodeIndex j) := by
  generalize hk : (coefficientIndex (F := F)).symm j = ik
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [coordinateW, decodeFactor, decodeIndex, hk]
 def coordFlat (j : Fin (3*d F)) : KPContActualSectorCotangentL2.V F ζ hζ U R P H →L[ℂ]
    Lp ℂ 2 (measure a) :=
  ((PiLp.proj 2 (fun _ : Fin (d F) × Fin 3 => ℂ) (decodeIndex (F := F) j)).compLpL 2 (measure a)).comp (cotangentFlat a)
private theorem coordFlat_ae (j : Fin (3*d F)) (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v) :
    (fun y => coordFlat a j v (emb a y)) =ᵐ[a.liftedMeasure]
      (fun y => localCoefficient a r.val y (decodeIndex j)) := by
  have hp := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin (d F) × Fin 3 => ℂ) (decodeIndex (F := F) j)).coeFn_compLpL (cotangentFlat a v)
  have hmap : Measure.map (emb a) a.liftedMeasure = measure a := lifted_measure_transport (a := a)
  have hp' : ∀ᵐ y ∂a.liftedMeasure, coordFlat a j v (emb a y) = cotangentFlat a v (emb a y) (decodeIndex j) := by
    have hh : ∀ᵐ x ∂Measure.map (emb a) a.liftedMeasure,
        coordFlat a j v x = cotangentFlat a v x (decodeIndex j) := by
      simpa only [emb, hmap, coordFlat, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
        Filter.EventuallyEq] using hp
    exact (emb_meas a).ae_map_iff.mp hh
  filter_upwards [hp', cotangentFlat_pull a v r hr] with y h1 h2
  rw [h1,h2]
 theorem factor_bound (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume.restrict B.carrier, ‖decodeFactor (F := F) j x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hB.1.bddAbove_image ((decode_cont j).norm.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
  exact (hC ⟨x, subset_closure hx, rfl⟩).trans (le_max_left _ _)

 theorem factorMem (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F))
    (f : BallL2 B) : MemLp (fun x => decodeFactor j x * f x) 2 (volume.restrict B.carrier) := by
  obtain ⟨C,hC,hb⟩ := factor_bound a B hB j
  have hm : AEStronglyMeasurable (decodeFactor (F := F) j) (volume.restrict B.carrier) :=
    (decode_cont (F := F) j).measurable.aestronglyMeasurable
  have htop := memLp_top_of_bound (hm : AEStronglyMeasurable _ (volume.restrict B.carrier)) C hb
  exact htop.mul (Lp.memLp f)
 def factorLinear (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F)) :
    BallL2 B →ₗ[ℂ] BallL2 B where
  toFun f := (factorMem a B hB j f).toLp (fun x => decodeFactor j x * f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(factorMem a B hB j (f+g)).coeFn_toLp,
      (factorMem a B hB j f).coeFn_toLp, (factorMem a B hB j g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((factorMem a B hB j f).toLp _) ((factorMem a B hB j g).toLp _)] with x h1 h2 h3 h4 h5
    simp only [h1,h5,Pi.add_apply,h2,h3,h4,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(factorMem a B hB j (c • f)).coeFn_toLp,
      (factorMem a B hB j f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((factorMem a B hB j f).toLp _)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,h1,h4,Pi.smul_apply,h2,h3,smul_eq_mul,mul_left_comm]
 def factorCLM (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F)) :
    BallL2 B →L[ℂ] BallL2 B := by
  let C := (factor_bound a B hB j).choose
  have hC := (factor_bound a B hB j).choose_spec.1
  have hb := (factor_bound a B hB j).choose_spec.2
  refine (factorLinear a B hB j).mkContinuous C ?_
  intro f
  change ‖(factorMem a B hB j f).toLp _‖ ≤ C * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  have hm := (factorMem a B hB j f).aestronglyMeasurable
  have hh : eLpNorm (fun x => decodeFactor j x * f x) 2 (volume.restrict B.carrier) ≤
      ENNReal.ofReal C * eLpNorm f 2 (volume.restrict B.carrier) := by
    calc _ ≤ eLpNorm (fun x => (C : ℂ) * f x) 2 (volume.restrict B.carrier) := by
           apply eLpNorm_mono_ae hm
           filter_upwards [hb] with x hx
           rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
           exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
         _ = _ := by
           change eLpNorm ((C : ℂ) • (fun x => f x)) 2 (volume.restrict B.carrier) = _
           rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real,
             Real.norm_eq_abs, abs_of_nonneg hC]
  have hfin := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C)) (Lp.memLp f).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono hfin hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ C from hC)] at hr
  exact hr
private theorem factorCLM_ae (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F))
    (f : BallL2 B) : factorCLM a B hB j f =ᵐ[volume.restrict B.carrier]
      (fun x => decodeFactor j x * f x) := by
  exact (factorMem a B hB j f).coeFn_toLp

 def completeBall (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F)) :
    KPContActualSectorCotangentL2.V F ζ hζ U R P H →L[ℂ] BallL2 B :=
  (factorCLM a B hB j).comp ((weightedBall a B hB).comp (coordFlat a j))
private theorem completeBall_ae (B : LocalBall (3*d F)) (hB : BallInside a B) (j : Fin (3*d F))
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v) :
    (fun x => completeBall a B hB j v x) =ᵐ[volume.restrict B.carrier]
      (fun x => coordinateW r.val a x j) := by
  have hc := coordFlat_ae a j v r hr
  have hg : ∀ᵐ x ∂measure a, decodeFactor j x * coordFlat a j v x = coordinateW r.val a x j := by
    have hm : Measure.map (emb a) a.liftedMeasure = measure a := lifted_measure_transport (a := a)
    apply Eq.mp (congrArg (fun μ => ∀ᵐ x ∂μ, decodeFactor j x * coordFlat a j v x = coordinateW r.val a x j) hm)
    apply (emb_meas a).ae_map_iff.mpr
    filter_upwards [hc] with y hy
    rw [hy, decoder_eq]
    have he : (baseReindex (F := F)).symm (emb a y) = (coordinates a y).val := by
      simp only [emb,fromActual,coordinates, LinearIsometryEquiv.symm_apply_apply]
    rw [he]
    simp only [liftExtension, dite_eq_left (coordinates a y).property, localCoefficient]
  obtain ⟨c,hc0,hdom⟩ := ball_measure_domination a B hB
  have habs : volume.restrict B.carrier ≪ measure a := Measure.absolutelyContinuous_of_le_smul hdom
  have hball := habs.ae_le hg
  have h1 := factorCLM_ae a B hB j (weightedBall a B hB (coordFlat a j v))
  have h2 := weightedBall_ae a B hB (coordFlat a j v)
  filter_upwards [h1,h2,hball] with x hx1 hx2 hx3
  change factorCLM a B hB j (weightedBall a B hB (coordFlat a j v)) x = _
  rw [hx1,hx2,hx3]

def coordinateBall (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) (j : Fin (3 * d F)) :
    KPContActualSectorCotangentL2.V F ζ hζ U R P H →L[ℂ] BallL2 B :=
  completeBall a B hB j

theorem coordinateBall_ae (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) (j : Fin (3 * d F))
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v) :
    (fun x => coordinateBall a B hB j v x) =ᵐ[volume.restrict B.carrier]
      (fun x => coordinateW r.val a x j) := by
  exact completeBall_ae a B hB j v r hr

end DedekindZetaZeroFree.KPContActualSectorBallRestriction

end
