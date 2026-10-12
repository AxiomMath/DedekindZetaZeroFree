module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.FlatTestsAndGraphCauchyBounds
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.CompactMultiplierWeakH1
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.CompactSupportSquareFiniteGradient
public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.InteriorBallLocality
public import DedekindZetaZeroFree.Analysis.Sobolev.EquivariantSections.WeightedH1Approximation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualCotangentChartRestriction
open KPContActualSectorChartEquivariantInputs KPContSectorLineL2Isometry
open KPContLocalNorm KPContSectorSmoothFramesSupport
open KPContActualCotangentCountableShrinking KPContCotangentActualGenuineTwistIsotropy
open KPContSectorPhaseComponentCharts KPContActualSectorFormWeakLocalization KPCompactInteriorH1
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
private theorem measurable_extension {V : Type*} [Zero V] [MeasurableSpace V]
    (a : ActualChart (U:=U) (H:=H)) (f : omega a → V) (hf : Measurable f) :
    Measurable (fun x : Space (3*d F) => liftExtension a f ((baseReindex (F:=F)).symm x)) := by
  classical
  have hg : Measurable (liftExtension a f) := by
    unfold liftExtension
    exact Measurable.dite hf measurable_const (KPContActualGlobalGreen.isOpen_omega_actual a).measurableSet
  exact hg.comp (baseReindex (F:=F)).symm.continuous.measurable

private theorem weakChartData_weakFirst
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U:=U) (H:=H))
    (hs : WeakChartData s W) (a : ActualChart (U:=U) (H:=H)) :
    WeakFirst (chartOpens (scalarData a))
      (fun x => WithLp.toLp 2 (fun _ : Fin 1 => scalarCoordinate s a x))
      (fun j x => WithLp.toLp 2 (fun _ : Fin 1 => covariantCoordinate W a x j)) := by
  have hd : 0 < d F := by
    have hp := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
    rw [show d F = Module.finrank ℚ F / 2 from rfl, ← hp.2.1]
    exact hp.2.2
  apply weakFirst_of_all_interior_balls (3*d F) (by omega)
  · apply measurable_extension
    have he : (sectionFields s.val a) = fun x => (s.val a.component).val
        (labeledA (placeEquiv F ζ hζ) x.val) := by
      funext x
      have hcoe : (isotropyChart a).coefficient s.val x.val =
          (KPCuspGenuineMonodromy.chi F ζ hζ ((isotropyChart a).splitting x.val) : ℂ) *
            (s.val a.component).val ((isotropyChart a).kind.representative •
              labeledA (isotropyChart a).places x.val) := rfl
      rw [sectionFields,hcoe]
      simp [isotropyChart,ChartKind.representative]
    rw [he]
    apply (s.property.1 a.component).comp
    have hc : Continuous (labeledA (placeEquiv F ζ hζ)) := by
      unfold labeledA
      fun_prop
    exact (hc.comp continuous_subtype_val).measurable
  · intro j
    have hm := measurable_extension a (coefficient W a) (W.property.1 a)
    unfold covariantCoordinate
    dsimp only
    rcases (coefficientIndex (F:=F)).symm j with ⟨i,k⟩
    have hcoef (k : Fin 3) : Measurable (fun x => (liftExtension a (coefficient W a)
        ((baseReindex (F:=F)).symm x)) (i,k)) :=
      (continuous_apply (i,k)).measurable.comp ((PiLp.continuous_ofLp 2 _).measurable.comp hm)
    have he : Measurable (fun x : Space (3*d F) => (Real.exp (-((baseReindex (F:=F)).symm x) (i,2)) : ℂ)) := by
      fun_prop
    fin_cases k
    · change Measurable ((fun x => (Real.exp (-((baseReindex (F:=F)).symm x) (i,2)) : ℂ)) *
        (fun x => liftExtension a (coefficient W a) ((baseReindex (F:=F)).symm x) (i,1)))
      exact he.mul (hcoef 1)
    · change Measurable ((fun x => (Real.exp (-((baseReindex (F:=F)).symm x) (i,2)) : ℂ)) *
        (fun x => liftExtension a (coefficient W a) ((baseReindex (F:=F)).symm x) (i,2)))
      exact he.mul (hcoef 2)
    · exact hcoef 0
  · intro B hB
    have hball : InteriorBall a B := ⟨by
        change IsCompact (closure (Metric.ball B.center B.radius))
        rw [closure_ball B.center B.radius_pos.ne']
        exact isCompact_closedBall _ _, hB⟩
    obtain ⟨h,hzero,hfirst⟩ := hs a B hball 1
    refine ⟨h,?_,?_⟩
    · simpa only [KPContLocalEnergy.value,KPContLocalEnergy.zeroIndex,zeroIndex,map_one,Units.val_one,one_mul] using hzero
    · intro j
      have hh := hfirst (KPContLocalEnergy.firstIndex j) j (by simp [KPContLocalEnergy.firstIndex])
      simpa only [KPContLocalEnergy.gradient,map_one,Units.val_one,one_mul] using hh
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContLocalNorm KPCompactInteriorH1
open KPContActualSectorChartEquivariantInputs KPContActualCotangentChartRestriction
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
 def actualInverseMetric (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H)) :
    InverseMetric (chartOpens (scalarData a)) where
  Q x := Matrix.diagonal (fun j =>
    let ik := (coefficientIndex (F:=F)).symm j
    if ik.2 = 2 then 1 else Real.exp (2 * ((baseReindex (F:=F)).symm x) (ik.1,2)))
  smooth j k := by
    by_cases hjk : j = k
    · subst k
      simp only [Matrix.diagonal_apply_eq]
      split_ifs <;> fun_prop
    · simp only [Matrix.diagonal_apply_ne _ hjk]
      exact contDiffOn_const
  symmetric x hx j k := by
    by_cases hjk : j = k
    · subst k; rfl
    · simp [Matrix.diagonal_apply_ne _ hjk, Matrix.diagonal_apply_ne _ (Ne.symm hjk)]
  positive_definite x hx := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro j
    dsimp only
    split_ifs
    · norm_num
    · exact Real.exp_pos _

 def actualZeroConnection (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H)) :
    Connection (r:=1) (chartOpens (scalarData a)) where
  A _ _ := 0
  smooth _ := contDiffOn_const
private theorem actualZeroConnection_unitary (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H)) :
    (actualZeroConnection a).IsUnitary := by
  intro x hx j
  simp [actualZeroConnection]

private theorem actualZeroConnection_compatible (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H)) :
    (actualZeroConnection a).IsCompatible (scalarData a) := by
  intro γ u hu x hx v
  simp only [smoothCovariantDerivative,actualZeroConnection,zero_apply,
    smul_zero,Finset.sum_const_zero,add_zero]
  let L := (scalarCocycle a γ 0).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hu' : DifferentiableAt ℝ u (action a γ x) :=
    hu.differentiableOn (by simp) (action a γ x)
      ((scalarData a).act_mem γ x hx) |>.differentiableAt
        ((scalarData a).open_chart.mem_nhds ((scalarData a).act_mem γ x hx))
  have ha : DifferentiableAt ℝ (action a γ) x :=
    (scalarData a).smooth_action γ |>.differentiableOn (by simp) x hx
      |>.differentiableAt ((scalarData a).open_chart.mem_nhds hx)
  have hf := L.hasFDerivAt.comp x (hu'.hasFDerivAt.comp x ha.hasFDerivAt)
  have hfe := hf.fderiv
  change fderiv ℝ (fun y => L (u (action a γ y))) x = _ at hfe
  rw [show (fun y => ((scalarData a).cocycle γ y).symm (u ((scalarData a).act γ y))) =
      (fun y => L (u (action a γ y))) from rfl, hfe]
  rfl
private theorem actualInverseMetric_quadratic
    (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (x : E (3*KPContCotangentActualOverlap.d F)) (v : Fin (3*KPContCotangentActualOverlap.d F) → V 1) :
    (actualInverseMetric a).quadratic x v =
      ∑ j, (if ((coefficientIndex (F:=F)).symm j).2 = 2 then 1 else
        Real.exp (2 * ((baseReindex (F:=F)).symm x) (((coefficientIndex (F:=F)).symm j).1,2))) *
        ‖v j‖ ^ 2 := by
  simp only [InverseMetric.quadratic,actualInverseMetric]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply_eq, inner_self_eq_norm_sq_to_K]
    norm_cast
  · intro k hk hjk
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hjk),zero_mul]
  · simp

open KPContActualCotangentMeasurableFamilies KPContActualSectorTestDifferentialDescent
open KPContActualSectorFormWeakLocalization
 def vec (z : ℂ) : V 1 := WithLp.toLp 2 (fun _ => z)
private theorem vec_norm (z : ℂ) : ‖vec z‖ = ‖z‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vec,Real.sqrt_sq (norm_nonneg _)]
private theorem actualInverseMetric_decode
    (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (W : Family (U:=U) (H:=H)) (x : E (3*KPContCotangentActualOverlap.d F)) :
    (actualInverseMetric a).quadratic x (fun j => vec (covariantCoordinate W a x j)) =
      ‖liftExtension a (coefficient W a) ((baseReindex (F:=F)).symm x)‖^2 := by
  rw [actualInverseMetric_quadratic]
  simp_rw [vec_norm]
  rw [← Equiv.sum_comp (coefficientIndex (F:=F)), Fintype.sum_prod_type,
    EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.sum_univ_three,Equiv.symm_apply_apply,covariantCoordinate,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    norm_mul, Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
  have he (t : ℝ) : Real.exp (2*t) * Real.exp (-t)^2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2 <;> ring
  simp only [Fin.reduceEq,ite_false,ite_true,one_mul]
  rw [← mul_assoc,← mul_assoc,he]
  simp only [Function.comp_apply,Fin.succ_zero_eq_one,Matrix.cons_val_one,Matrix.cons_val_zero]
  ring

open KPContSectorLineL2Isometry KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
private theorem sum_real_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℝ) :
    ∑ i, (L (b i)) ^ 2 = ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L‖ ^ 2 := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    b.sum_sq_inner_left ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L)
private theorem sum_complex_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b c : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℂ) :
    ∑ i, ‖L (b i)‖ ^ 2 = ∑ i, ‖L (c i)‖ ^ 2 := by
  have hRe := (sum_real_basis b (Complex.reCLM.comp L)).trans
    (sum_real_basis c (Complex.reCLM.comp L)).symm
  have hIm := (sum_real_basis b (Complex.imCLM.comp L)).trans
    (sum_real_basis c (Complex.imCLM.comp L)).symm
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hRe hIm
  simp only [Complex.sq_norm, Complex.normSq_apply, Finset.sum_add_distrib]
  simpa only [pow_two] using congrArg₂ (· + ·) hRe hIm
private theorem sum_vector_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b c : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] V 1) :
    ∑ i, ‖L (b i)‖ ^ 2 = ∑ i, ‖L (c i)‖ ^ 2 := by
  have hc := sum_complex_basis b c
    (scalarReindex.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ |>.comp L)
  change (∑ i, ‖scalarReindex.symm (L (b i))‖^2) = (∑ i, ‖scalarReindex.symm (L (c i))‖^2) at hc
  simpa only [LinearIsometryEquiv.norm_map] using hc
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem flat_frame_basis (x : Space (3*d F)) (i : Fin (d F)) (k : Fin 3) :
    baseReindex (CotangentLogCoframe.H (d F) ((baseReindex (F:=F)).symm x)
      (EuclideanSpace.basisFun _ ℝ (i,k))) =
      ![coordinateDirection ((coefficientIndex (F:=F)) (i,2)),
        Real.exp (((baseReindex (F:=F)).symm x) (i,2)) • coordinateDirection ((coefficientIndex (F:=F)) (i,0)),
        Real.exp (((baseReindex (F:=F)).symm x) (i,2)) • coordinateDirection ((coefficientIndex (F:=F)) (i,1))] k := by
  apply PiLp.ext
  intro j
  rcases (coefficientIndex (F:=F)).surjective j with ⟨⟨l,m⟩,rfl⟩
  fin_cases k <;> fin_cases m <;> simp [baseReindex,CotangentLogCoframe.H,CotangentLogCoframe.C,
    coordinateDirection,EuclideanSpace.basisFun_apply,PiLp.single_apply,eq_comm]
  all_goals split_ifs <;> simp_all

private theorem actualInverseMetric_frame
    (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (x : Space (3*d F)) (L : Space (3*d F) →L[ℝ] V 1) :
    (actualInverseMetric a).quadratic x (fun j => L (coordinateDirection j)) =
      ∑ k : Fin (d F) × Fin 3,
        ‖L (baseReindex (CotangentLogCoframe.H (d F) ((baseReindex (F:=F)).symm x)
          (EuclideanSpace.basisFun _ ℝ k)))‖^2 := by
  rw [actualInverseMetric_quadratic,← Equiv.sum_comp (coefficientIndex (F:=F)),
    Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.sum_univ_three,Equiv.symm_apply_apply,Fin.reduceEq,ite_true,ite_false,one_mul,
    flat_frame_basis,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,
    map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
  have he (t : ℝ) : Real.exp t ^ 2 = Real.exp (2*t) := by
    rw [← Real.exp_nat_mul]
    norm_num
  simp only [he]
  ring

private theorem actualInverseMetric_invariant
    (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H)) :
    (actualInverseMetric a).IsInvariant (scalarData a) := by
  intro γ x hx T
  let p := (baseReindex (F:=F)).symm x
  let ψ := isotropyArrow a γ
  have hp : p ∈ ψ.domain := by
    change p ∈ (isotropyChart a).omega
    exact a.closure_subset (subset_closure hx)
  let q := KPContCotangentActualGenuineTwistIsotropy.q ψ p hp
  let L : KPContCotangentActualGenuineTwistIsotropy.V F →L[ℝ] V 1 :=
    T.comp ((baseReindex (F:=F)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (CotangentLogCoframe.H (d F) (ψ.psi p)).toContinuousLinearMap)
  have he : ∀ v, fderiv ℝ ψ.psi p (CotangentLogCoframe.H (d F) p v) =
      CotangentLogCoframe.H (d F) (ψ.psi p) (q v) := by
    intro v
    apply (CotangentLogCoframe.C (d F) (ψ.psi p)).injective
    simp only [CotangentLogCoframe.H,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hsum := sum_vector_basis ((EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ).map q)
    (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ) L
  have ha : fderiv ℝ (action a γ) x =
      (baseReindex (F:=F)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ ψ.psi p).comp (baseReindex (F:=F)).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    have hd := (smooth_metric ψ).1.differentiableOn (by simp) p hp
    have hdo : IsOpen ψ.domain := ψ.isOpen_domain
    have hh := ((baseReindex (F:=F)).hasFDerivAt (x := ψ.psi p)).comp x
      ((hd.differentiableAt (hdo.mem_nhds hp)).hasFDerivAt.comp x
        ((baseReindex (F:=F)).symm.hasFDerivAt (x := x)))
    exact hh.fderiv
  rw [show (fun j => T (fderiv ℝ ((scalarData a).act γ) x (coordinateDirection j))) =
      (fun j => (T.comp (fderiv ℝ (action a γ) x)) (coordinateDirection j)) from rfl,
    actualInverseMetric_frame,actualInverseMetric_frame]
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro k _
    simp only [ContinuousLinearMap.comp_apply,ha,OrthonormalBasis.map_apply,L]
    change ‖T (baseReindex (fderiv ℝ ψ.psi p ((baseReindex (F:=F)).symm
      (baseReindex (CotangentLogCoframe.H (d F) p (EuclideanSpace.basisFun _ ℝ k))))))‖^2 = _
    rw [LinearIsometryEquiv.symm_apply_apply,he]
    rfl
  · apply Finset.sum_congr rfl
    intro k _
    change ‖T (baseReindex (CotangentLogCoframe.H (d F)
      ((baseReindex (F:=F)).symm (baseReindex (ψ.psi p))) (EuclideanSpace.basisFun _ ℝ k)))‖^2 = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl

private theorem actualFiniteHw
    (a : KPContActualSectorSmoothTestModules.ActualChart (U:=U) (H:=H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s)
    (r : SquareFiniteFamily (U:=U) (H:=H)) :
    FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => vec (scalarCoordinate s a x))
      (fun j x => vec (covariantCoordinate r.val a x j)) := by
  have hscalar : MemLp (scalarCoordinate s a) 2 (KPContActualSectorChartEquivariantInputs.measure a) :=
    MemLp.ae_eq (KPContActualSectorBallRestriction.scalarProducer_spec a u s hs)
      (Lp.memLp (KPContActualSectorBallRestriction.scalarProducer a u))
  have hsc : Continuous (vec : ℂ → V 1) := by
    unfold vec
    fun_prop
  refine ⟨hscalar.congr_norm (hsc.comp_aestronglyMeasurable hscalar.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (vec_norm _).symm), ?_⟩
  let G := fun x : Space (3*d F) =>
    ‖liftExtension a (coefficient r.val a) ((baseReindex (F:=F)).symm x)‖^2
  have hG : Measurable G := by
    exact (measurable_extension a (coefficient r.val a) (r.val.property.1 a)).norm.pow_const 2
  have hc := KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H a
  let emb := fun y : a.domain => fromActual (ζ:=ζ) (hζ:=hζ) y.val
  have hem : Measurable emb := by
    apply Continuous.measurable
    unfold emb fromActual labeledAInv
    exact (baseReindex (F:=F)).continuous.comp ((CotangentLogCoframe.A (d F)).symm.continuous.comp
      (continuous_pi fun k => (continuous_apply _).comp continuous_subtype_val))
  have hmap : Measure.map emb a.liftedMeasure = KPContActualSectorChartEquivariantInputs.measure a :=
    lifted_measure_transport (a:=a)
  have hGi : Integrable G (KPContActualSectorChartEquivariantInputs.measure a) := by
    rw [← hmap]
    apply (integrable_map_measure hG.aestronglyMeasurable hem.aemeasurable).mpr
    have hlp := localCoefficient_memLp a r
    have hi := (memLp_two_iff_integrable_sq_norm hlp.aestronglyMeasurable).mp hlp
    convert hi using 1
    funext y
    have hy := (KPContActualCotangentPieceHilbertSum.coordinates a y).property
    change ‖liftExtension a (coefficient r.val a) ((baseReindex (F:=F)).symm (emb y))‖^2 =
      ‖localCoefficient a r.val y‖^2
    have hy' : labeledAInv (placeEquiv F ζ hζ) y.val ∈ KPContCotangentOverlapRationalBranches.omega a := hy
    simp only [emb, fromActual,LinearIsometryEquiv.symm_apply_apply,liftExtension,
      localCoefficient,KPContActualCotangentPieceHilbertSum.coordinates]
    rw [dif_pos hy']
  have hw : AEMeasurable (fun x => ENNReal.ofReal (weight a x)) (volume.restrict (chart a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((scalarData a).smooth_weight.continuousOn.aemeasurable (scalarData a).open_chart.measurableSet)
  have hweighted := (integrable_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (weight a x)) from by
      unfold weight KPArch.volumeDensity KPArch.height toActual labeledA
      fun_prop) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hGi
  apply hweighted.congr
  filter_upwards [ae_restrict_mem (scalarData a).open_chart.measurableSet] with x hx
  simp only [covariantFirst,actualZeroConnection,zero_apply,add_zero]
  rw [actualInverseMetric_decode,
    ENNReal.toReal_ofReal (show 0 ≤ weight a x from ((scalarData a).positive_weight x hx).le)]
  exact mul_comm _ _

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContLocalNorm KPCompactInteriorH1
 def scalarVector (f : ℂ) : V 1 := WithLp.toLp 2 (fun _ => f)
private theorem scalarVector_norm (f : ℂ) : ‖scalarVector f‖ = ‖f‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [scalarVector, Real.sqrt_sq (norm_nonneg _)]
 def oneIndex {n : ℕ} (j : Fin n) : MultiIndex n 1 :=
  ⟨fun i => if i = j then ⟨1,by omega⟩ else ⟨0,by omega⟩,by
    simp only [apply_ite Fin.val]
    simp⟩
private theorem one_dirs {n : ℕ} (j : Fin n) : (oneIndex j).directions = [j] := by
  classical
  simp only [MultiIndex.directions, oneIndex, apply_ite Fin.val, Fin.val_one, Fin.val_zero,
    List.replicate_one, List.replicate_zero]
  have hh : ∀ l : List (Fin n), l.flatMap (fun i => if i = j then [i] else []) = l.filter (· = j) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => by_cases hij : i = j <;> simp [hij,ih]
  have hrep (i : Fin n) : List.replicate (if i = j then 1 else 0) i = if i = j then [i] else [] := by
    split_ifs <;> simp
  simp_rw [hrep]
  rw [hh,List.filter_eq]
  simp
private theorem sobolev_weakFirst_on_ball {n : ℕ} (B : LocalBall n) (h : IntegerSobolev B 1) :
    WeakFirst B.toOpens (fun x => scalarVector (h.derivatives ⟨fun _ => 0,by simp⟩ x))
      (fun j x => scalarVector (h.derivatives (oneIndex j) x)) := by
  have localLp (u : BallL2 B) : LocallyL2 B.toOpens (fun x => scalarVector (u x)) := by
    have hm : MemLp (fun x => scalarVector (u x)) 2 (volume.restrict B.carrier) :=
      (Lp.memLp u).congr_norm (by
        have hc : Continuous scalarVector := by
          unfold scalarVector
          fun_prop
        exact hc.comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => (scalarVector_norm (u x)).symm)
    exact ⟨hm.aestronglyMeasurable, fun L hL hLB => hm.mono_measure (Measure.restrict_mono hLB le_rfl)⟩
  refine ⟨localLp _,fun j => localLp _,?_⟩
  intro j ψ a
  have hw := h.weak_derivatives (oneIndex j) ψ
  have hd : (oneIndex j).degree = 1 := by
    simp only [MultiIndex.degree,oneIndex,apply_ite Fin.val,Fin.val_one,Fin.val_zero]
    simp
  simpa only [scalarVector,PiLp.toLp_apply, coordinatePartial, coordinateDirection,
    coordinateDerivative,one_dirs,coordinateDerivativeList,hd,pow_one,neg_mul,one_mul]
    using (show (∫ x in (B.toOpens : Set (E n)), (h.derivatives ⟨fun _ => 0,by simp⟩) x *
      coordinateDerivative (oneIndex j) (fun y => ψ y) x) =
      (-1 : ℂ) ^ (oneIndex j).degree * (∫ x in (B.toOpens : Set (E n)),
        (h.derivatives (oneIndex j)) x * ψ x) from hw)
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
open KPContActualSectorFormWeakLocalization KPContActualCotangentPieceHilbertSum
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ} {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ} {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem fields_apply (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U:=U) (H:=H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ ((isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((isotropyChart a).kind.representative • labeledA (isotropyChart a).places x.val) := rfl
  rw [sectionFields, hcoe]
  simp [isotropyChart, KPContCotangentActualOverlap.ChartKind.representative]
private theorem norm_toBase (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U:=U) (H:=H)) (y : a.domain) :
    sectionNorm F ζ hζ U R P H s (a.toBase y) = ‖(s a.component).val y.val‖ := by
  rw [show a.toBase y = (H.atlas U).components ⟨a.component, Quotient.mk _ y.val⟩ from
    ((H.atlas U).components_formula a.component _).symm, sectionNorm_component]

private theorem chart_fields_eq_imp_mk_eq
    (s t : BorelL2Sections F ζ hζ U R P H)
    (hfields : ∀ a : ActualChart (U:=U) (H:=H),
      (fun y : a.domain => sectionFields s.val a (coordinates a y)) =ᵐ[a.liftedMeasure]
      (fun y => sectionFields t.val a (coordinates a y))) :
    mk F ζ hζ U R P H s = mk F ζ hζ U R P H t := by
  apply (mk_eq_mk_iff F ζ hζ U R P H s t).mpr
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hchart (n : ℕ) : squaredNorm F ζ hζ U R P H (s.val-t.val)
      =ᵐ[(KPContActualSectorCotangentL2.muU F ζ hζ U R P).restrict (cover.chart n).baseDomain] 0 := by
    let a := cover.chart n
    have hcoef : (fun y : a.domain => (s.val a.component).val y.val) =ᵐ[a.liftedMeasure]
        (fun y => (t.val a.component).val y.val) := by
      have he := hfields a
      filter_upwards [he] with y hy
      have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
        funext k
        simp [labeledA, labeledAInv]
      simpa only [fields_apply, coordinates, hi] using hy
    have hnorm : ∀ᵐ y ∂a.liftedMeasure,
        squaredNorm F ζ hζ U R P H (s.val-t.val) (a.toBase y) = 0 := by
      filter_upwards [hcoef] with y hy
      unfold squaredNorm
      rw [norm_toBase]
      simp [hy]
    rw [← (cover.properties n).exact_pushforward]
    apply (ae_map_iff (cover.properties n).measurable.aemeasurable ?_).mpr hnorm
    exact measurableSet_eq_fun (squaredNorm_measurable F ζ hζ U R P H (s.val-t.val)
      (fun i => by simpa using (s.property.1 i).sub (t.property.1 i))) measurable_const
  have he := (ae_restrict_iUnion_iff (fun n => (cover.chart n).baseDomain)
    (fun x => squaredNorm F ζ hζ U R P H (s.val-t.val) x = 0)).mpr hchart
  rwa [cover.covers, Measure.restrict_univ] at he
private theorem chart_fields_ae_of_mk_eq
    (s t : BorelL2Sections F ζ hζ U R P H)
    (heq : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t)
    (a : ActualChart (U:=U) (H:=H)) :
    (fun y : a.domain => sectionFields s.val a (coordinates a y)) =ᵐ[a.liftedMeasure]
      (fun y => sectionFields t.val a (coordinates a y)) := by
  have hnorm := (mk_eq_mk_iff F ζ hζ U R P H s t).mp heq
  have hc := KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H a
  have hlocal := ae_mono (Measure.restrict_le_self (s:=a.baseDomain)) hnorm
  rw [← hc.exact_pushforward] at hlocal
  have hme : MeasurableSet {x | squaredNorm F ζ hζ U R P H (s.val-t.val) x = 0} :=
    measurableSet_eq_fun (squaredNorm_measurable F ζ hζ U R P H (s.val-t.val)
      (fun i => by simpa using (s.property.1 i).sub (t.property.1 i))) measurable_const
  have hlift := (ae_map_iff hc.measurable.aemeasurable hme).mp hlocal
  filter_upwards [hlift] with y hy
  unfold squaredNorm at hy
  rw [norm_toBase] at hy
  have hval : (s.val a.component).val y.val = (t.val a.component).val y.val := by
    simp only [ENNReal.ofReal_eq_zero, sq_nonpos_iff] at hy
    have hh : (s.val a.component).val y.val - (t.val a.component).val y.val = 0 := by
      apply norm_eq_zero.mp
      simpa using hy
    exact sub_eq_zero.mp hh
  have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k
    simp [labeledA,labeledAInv]
  simpa only [fields_apply,coordinates,hi] using hval

private theorem actualProduct_unique (η : CompactMultiplier (U:=U) (H:=H))
    (u v w : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hv : IsActualProduct η u v) (hw : IsActualProduct η u w) : v = w := by
  obtain ⟨s,t,hs,ht,he⟩ := hv
  obtain ⟨s',t',hs',ht',he'⟩ := hw
  apply (sectorLineIsometry F ζ hζ U R P H).injective
  rw [ht,ht']
  apply chart_fields_eq_imp_mk_eq
  intro a
  have hss := chart_fields_ae_of_mk_eq s s' (hs.symm.trans hs') a
  filter_upwards [he a, he' a, hss] with y h1 h2 h3
  rw [h1,h2,h3]

private theorem compact_multiplier_of_converse
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (hc : ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)),
      IsCompact K → SupportedAE (H:=H) u K → ActualWeakH1Loc (H:=H) u →
      u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain)
    (η : CompactMultiplier (U:=U) (H:=H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (hu : ActualWeakH1Loc (H:=H) u) :
    ∃! v : KPContActualSectorFriedrichsSynthesis.formDomain F ζ hζ U R P H μG hμG hR realization,
      IsActualProduct η u v.val := by
  obtain ⟨v,hprod,hweak,K,hK,hsupp⟩ := compactMultiplier_product_weakH1 η u hu
  refine ⟨⟨v,hc v K hK hsupp hweak⟩,hprod,?_⟩
  intro w hw
  apply Subtype.ext
  exact actualProduct_unique η u w.val v hw hprod

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualSectorFormWeakLocalization

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

variable (F ζ hζ) (U R P H)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "A" => KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
local notation "Q" => KPContActualSectorFriedrichsSynthesis.formDomain F ζ hζ U R P H μG hμG hR realization

structure Properties : Prop where

  compact_converse : ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)),
    IsCompact K → SupportedAE (H := H) u K → ActualWeakH1Loc (H := H) u →
    ∃ hu : u ∈ (A).closure.domain,
      IsActualWeakGradient (H := H) u ((A).closure ⟨u, hu⟩) ∧
      ∃ φ : ℕ → S_U F ζ hζ U R P H,
        Filter.Tendsto (fun n => iota (φ n)) Filter.atTop (nhds u) ∧
        Filter.Tendsto (fun n => j (D_U (φ n))) Filter.atTop
          (nhds ((A).closure ⟨u, hu⟩))

  compact_multiplier : ∀ (η : CompactMultiplier (U := U) (H := H))
      (u : KPContSectorClosedLpSubspace.H F ζ hζ R U),
    ActualWeakH1Loc (H := H) u →
    ∃! v : Q, IsActualProduct η u (v : KPContSectorClosedLpSubspace.H F ζ hζ R U)

  form_weak_local : ∀ u : Q,
    ActualWeakH1Loc (H := H) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ∧
    IsActualWeakGradient (H := H)
      (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ((A).closure u)

theorem form_weak_local_of_formDomain (u : Q) :
    ActualWeakH1Loc (H := H) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) ∧
    IsActualWeakGradient (H := H) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      ((A).closure u) :=
  let P' := kp_cont_actual_sector_form_weak_localization F ζ hζ μG hμG U R hR P H realization
  ⟨P'.weak_local u, P'.closed_gradient u⟩

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

namespace DedekindZetaZeroFree

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualSectorFormWeakLocalization KPContActualSectorCompactWeakFormConverse

theorem formDomain_of_smoothTest_limit
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (φ : ℕ → S_U F ζ hζ U R P H)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (G : KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (hlim : Filter.Tendsto (fun n => iota (φ n)) Filter.atTop (nhds u))
    (hg : Filter.Tendsto (fun n => j (D_U (φ n))) Filter.atTop (nhds G)) :
    ∃ hu : u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
        realization).closure.domain,
      (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
        realization).closure ⟨u, hu⟩ = G := by
  let A := KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
  have hclosable : A.IsClosable :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H
      realization).gradient_closable
  have hs : ∀ n, iota (φ n) ∈ A.domain := fun n => LinearMap.mem_range_self iota (φ n)
  let s : ℕ → A.domain := fun n => ⟨iota (φ n), hs n⟩
  have hlim' : Filter.Tendsto
      (fun n => (s n : KPContSectorClosedLpSubspace.H F ζ hζ R U))
      Filter.atTop (nhds u) := hlim
  have hcauchy : CauchySeq (fun n => A (s n)) := by
    simpa only [s, A, KPContActualSectorFriedrichsSynthesis.A_U,
      KPTestOperator.descend_image] using hg.cauchySeq
  obtain ⟨hu, hgrad, _⟩ :=
    closedGradientForm_closure_characterization A hclosable s u hlim' hcauchy
  have hgrad' : Filter.Tendsto (fun n => j (D_U (φ n))) Filter.atTop
      (nhds (A.closure ⟨u, hu⟩)) := by
    simpa only [s, A, KPContActualSectorFriedrichsSynthesis.A_U,
      KPTestOperator.descend_image] using hgrad
  exact ⟨hu, tendsto_nhds_unique hgrad' hg⟩

end DedekindZetaZeroFree

namespace DedekindZetaZeroFree

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualSectorFormWeakLocalization KPContActualSectorCompactWeakFormConverse
open KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem compact_converse_of_approximation
    (approx : ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
        (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
        (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U := U) (H := H)),
      IsCompact K →
      sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
      SupportedAE (H := H) u K → WeakChartData s r.val →
      ∃ φ : ℕ → S_U F ζ hζ U R P H,
        Filter.Tendsto (fun n => iota (φ n)) Filter.atTop (nhds u) ∧
        Filter.Tendsto (fun n => j (D_U (φ n))) Filter.atTop
          (nhds (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r)))
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (hsupp : SupportedAE (H := H) u K) (hweak : ActualWeakH1Loc (H := H) u) :
    ∃ hu : u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
        realization).closure.domain,
      IsActualWeakGradient (H := H) u
        ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
          realization).closure ⟨u, hu⟩) ∧
      ∃ φ : ℕ → S_U F ζ hζ U R P H,
        Filter.Tendsto (fun n => iota (φ n)) Filter.atTop (nhds u) ∧
        Filter.Tendsto (fun n => j (D_U (φ n))) Filter.atTop
          (nhds ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR
            realization).closure ⟨u, hu⟩)) := by
  obtain ⟨s, r, hs, hW⟩ :=
    KPContActualSectorCompactWeakFormConverse.actualWeakH1Loc_compactSupport_squareFinite
      u K hK hsupp hweak
  obtain ⟨φ, hlim, hgrad⟩ := approx u K s r hK hs hsupp hW
  obtain ⟨hu, hG⟩ := formDomain_of_smoothTest_limit F ζ hζ μG hμG U R hR P H realization
    φ u (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r) hlim hgrad
  exact ⟨hu, by rw [hG]; exact ⟨s, r, hs, rfl, hW⟩, φ, hlim, by rw [hG]; exact hgrad⟩

end DedekindZetaZeroFree

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPCompactInteriorH1
private theorem invariant_window {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (K : Set (E n)) (hK : IsCompact K)
    (hKD : K ⊆ D.chart) (hKin : ∀ γ, ∀ x ∈ K, D.act γ x ∈ K) :
    ∃ O : TopologicalSpace.Opens (E n), K ⊆ O ∧ IsCompact (closure (O : Set (E n))) ∧
      closure (O : Set (E n)) ⊆ D.chart ∧
      ∀ γ, ∀ x ∈ (O : Set (E n)), D.act γ x ∈ O := by
  obtain ⟨W,hWo,hKW,hWsub,hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK D.open_chart hKD
  let V : Set (E n) := ⋂ γ : Γ, D.chart ∩ D.act γ ⁻¹' W
  have hVo : IsOpen V := isOpen_iInter_of_finite (fun γ =>
    (D.smooth_action γ).continuousOn.isOpen_inter_preimage D.open_chart hWo)
  have hKV : K ⊆ V := by
    intro x hx
    exact Set.mem_iInter.mpr fun γ => ⟨hKD hx, hKW (hKin γ x hx)⟩
  have hVW : V ⊆ W := by
    intro x hx
    have hh := Set.mem_iInter.mp hx (1 : Γ)
    have h := hh.2
    change D.act 1 x ∈ W at h
    simpa only [D.act_one x hh.1] using h
  have hVclose : IsCompact (closure V) := hWcompact.of_isClosed_subset isClosed_closure (closure_mono hVW)
  have hVchart : closure V ⊆ D.chart := (closure_mono hVW).trans hWsub
  refine ⟨⟨V,hVo⟩,hKV,hVclose,hVchart,?_⟩
  intro γ x hx
  change D.act γ x ∈ V
  refine Set.mem_iInter.mpr fun δ => ⟨D.act_mem γ x (Set.mem_iInter.mp hx 1).1, ?_⟩
  change D.act δ (D.act γ x) ∈ W
  rw [← D.act_mul δ γ x (Set.mem_iInter.mp hx 1).1]
  exact (Set.mem_iInter.mp hx (δ*γ)).2
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

open scoped Classical NumberField ContDiff
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContCotangentOverlapRationalBranches
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContActualSectorChartEquivariantInputs KPContLocalNorm KPCompactInteriorH1
open KPContActualSectorFormWeakLocalization KPContSectorPhaseComponentCharts
open KPContActualSectorTestDifferentialDescent KPContActualCotangentChartRestriction KPContActualCotangentMeasurableFamilies KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem flat_smooth_to_localTest (a : ActualChart (U:=U) (H:=H))
    (h : KPCompactInteriorH1.E (3*d F) → V 1) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ chart a)
    (he : ∀ γ x, x ∈ chart a → h (action a γ x) = scalarCocycle a γ x (h x)) :
    ∃ f : localScalarTests a,
      (∀ x : omega a, f.val x = scalarReindex.symm (h (baseReindex x.val))) ∧
      (∀ x : KPCompactInteriorH1.E (3*d F), liftExtension a f.val (baseReindex.symm x) = scalarReindex.symm (h x)) := by
  let g : M F → ℂ := fun x => scalarReindex.symm (h (baseReindex x))
  let f : omega a → ℂ := fun x => g x.val
  have hscalar : ContDiff ℝ ∞ (fun z : V 1 => scalarReindex.symm z) := by
    change ContDiff ℝ ∞ (fun z : V 1 => z 0)
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℂ) 0).contDiff
  have hg : ContDiff ℝ ∞ g := hscalar.comp
      (hh.comp baseReindex.toContinuousLinearEquiv.contDiff)
  have hext : ∀ x : M F, liftExtension a f x = g x := by
    intro x
    by_cases hx : x ∈ omega a
    · simp [liftExtension, hx, f]
    · have hz : h (baseReindex x) = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (by
        have ht := hs hh
        simpa [chart, toActual, omega] using ht))
      simp [liftExtension, hx, g, hz]
  let L : Set (M F) := baseReindex.symm '' tsupport h
  have hL : IsCompact L := hc.image baseReindex.symm.continuous
  have hLω : L ⊆ omega a := by
    rintro x ⟨y,hy,rfl⟩
    simpa [chart, toActual, omega] using hs hy
  have hq : Continuous (q a) := by
    unfold KPContCotangentOverlapRationalBranches.q KPFiniteCuspAtlas.componentMap KPCuspSiegel.projection
    apply continuous_quotient_mk'.comp
    apply Continuous.prodMk _ continuous_const
    unfold labeledA
    fun_prop
  have hlocal : localSupport a f ⊆ q a '' L := by
    apply closure_minimal _ (hL.image hq).isClosed
    rintro y ⟨x,⟨hx,hfx⟩,rfl⟩
    refine ⟨x,?_,rfl⟩
    refine ⟨baseReindex x,subset_tsupport _ ?_,by simp⟩
    intro hz
    exact hfx (by simp [f,g,hz])
  have hbase : q a '' L ⊆ a.baseDomain := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨⟨labeledA (placeEquiv F ζ hζ) x,hLω hx⟩,rfl⟩
  refine ⟨⟨f,⟨⟨g,hg.contDiffOn,fun _ => rfl⟩,?_,
    (hL.image hq).of_isClosed_subset isClosed_closure hlocal,hlocal.trans hbase⟩⟩,
    fun _ => rfl,?_⟩
  · intro γ x hx
    have ht := he γ (baseReindex x) (by simpa [chart,toActual,omega] using hx)
    have hs' := congrArg scalarReindex.symm ht
    simpa [f,g,action,scalarCocycle,scalarPhase,isotropyArrow,isotropyChart,Arrow.phase,ChartKind.representative] using hs'
  · intro x
    rw [hext]
    simp [g]
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches
open KPContActualCotangentPieceHilbertSum KPContActualSectorFiniteSupportPartition
open KPContCotangentActualOverlap KPContActualSectorTestDifferentialDescent
open scoped BigOperators
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem partition_products_reconstruct {n : ℕ}
    (C : Fin n → ActualChart (U:=U) (H:=H))
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (Q : FinitePartition F ζ hζ U R P H C K O)
    (η : Fin n → CompactMultiplier (U:=U) (H:=H))
    (hη : ∀ i, (η i).val.val = Q.multiplier i)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : Fin n → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hv : ∀ i, IsActualProduct (η i) u (v i))
    (hsupp : SupportedAE (H:=H) u K) : ∑ i, v i = u := by
  obtain ⟨s,hs,hzero⟩ := hsupp
  choose si ti hsi hti hprod using hv
  apply (sectorLineIsometry F ζ hζ U R P H).injective
  rw [map_sum,hs]
  have ht : (∑ i, (sectorLineIsometry F ζ hζ U R P H) (v i)) =
      mk F ζ hζ U R P H (∑ i, ti i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hti i
  rw [ht]
  apply chart_fields_eq_imp_mk_eq
  intro a
  have hp := every_shrunkChart_properties F ζ hζ U R P H a
  have hz : ∀ᵐ y ∂a.liftedMeasure, a.toBase y ∉ K →
      sectionFields s.val a (coordinates a y) = 0 := by
    have hh : ∀ᵐ y ∂a.liftedMeasure, a.toBase y ∉ K →
        squaredNorm F ζ hζ U R P H s.val (a.toBase y) = 0 :=
      ae_of_ae_map hp.measurable.aemeasurable (by
        rw [hp.exact_pushforward]
        exact hzero.filter_mono (ae_mono Measure.restrict_le_self))
    filter_upwards [hh] with y hy hnot
    have hn := hy hnot
    simp only [squaredNorm,norm_toBase,ENNReal.ofReal_eq_zero,sq_nonpos_iff] at hn
    have he := norm_eq_zero.mp hn
    have hi : labeledA (placeEquiv F ζ hζ)
        (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
      funext k; simp [labeledA,labeledAInv]
    simpa [fields_apply,coordinates,hi] using he
  have he : ∀ i, ∀ᵐ y ∂a.liftedMeasure,
      sectionFields (ti i).val a (coordinates a y) =
        ((η i).val.val (a.toBase y) : ℂ) * sectionFields s.val a (coordinates a y) := by
    intro i
    have hh := chart_fields_ae_of_mk_eq (si i) s ((hsi i).symm.trans hs) a
    filter_upwards [hprod i a,hh] with y hy hh
    rw [hh] at hy
    have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
      funext k; simp [labeledA,labeledAInv]
    simpa only [cutoffLift,coordinates,q,hi,ShrunkChart.toBase] using hy
  have heall := (ae_all_iff).mpr he
  filter_upwards [heall,hz] with y hy hz
  have hsum : sectionFields (∑ i, ti i).val a (coordinates a y) =
      ∑ i, sectionFields (ti i).val a (coordinates a y) := by
    simp [fields_apply, Submodule.coe_sum, Finset.sum_apply]
  rw [hsum]
  simp_rw [hy, hη]
  rw [← Finset.sum_mul]
  by_cases hmem : a.toBase y ∈ K
  · have hh : (∑ i, (Q.multiplier i (a.toBase y) : ℂ)) = 1 := by
      exact_mod_cast Q.partition _ (Q.contains_compact hmem)
    rw [hh,one_mul]
  · rw [hz hmem,mul_zero]
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualSectorFiniteSupportPartition
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
 def partitionMultiplier {n : ℕ}
    (C : Fin n → ActualChart (U:=U) (H:=H))
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (Q : FinitePartition F ζ hζ U R P H C K O) (i : Fin n) :
    CompactMultiplier (U:=U) (H:=H) :=
  ⟨⟨Q.multiplier i, by
    intro a
    refine ⟨fun x => Q.multiplier i (q a x), ?_, fun _ => rfl⟩
    have hh := Q.smooth i ((H.atlas U).representative a.component)
    have hl : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
      exact KPContActualGlobalGreen.contDiff_labeledA
    exact (hh.comp hl).contDiffOn⟩, Q.compact_support i⟩
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPCompactInteriorH1
private theorem compact_invariant_saturation {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (L : Set (E n)) (hL : IsCompact L)
    (hLD : L ⊆ D.chart) :
    ∃ K : Set (E n), IsCompact K ∧ L ⊆ K ∧ K ⊆ D.chart ∧
      ∀ γ, ∀ x ∈ K, D.act γ x ∈ K := by
  let K : Set (E n) := ⋃ γ : Γ, D.act γ '' L
  have hK : IsCompact K := isCompact_iUnion (fun γ =>
    hL.image_of_continuousOn ((D.smooth_action γ).continuousOn.mono hLD))
  have hLK : L ⊆ K := by
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨1,x,hx,?_⟩
    exact D.act_one x (hLD hx)
  have hKD : K ⊆ D.chart := by
    intro x hx
    obtain ⟨γ,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    exact D.act_mem γ y (hLD hy)
  refine ⟨K,hK,hLK,hKD,?_⟩
  intro δ x hx
  obtain ⟨γ,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  exact ⟨δ*γ,y,hy,D.act_mul δ γ y (hLD hy)⟩
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContActualSectorFiniteSupportPartition
open KPContActualSectorChartEquivariantInputs KPContLocalNorm KPCompactInteriorH1
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem partition_flat_window {n : ℕ}
    (C : Fin n → ActualChart (U:=U) (H:=H))
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (Q : FinitePartition F ζ hζ U R P H C K O) (i : Fin n) :
    ∃ L : Set (KPCompactInteriorH1.E (3*d F)), IsCompact L ∧ L ⊆ chart (C i) ∧
      (∀ γ, ∀ x ∈ L, action (C i) γ x ∈ L) ∧
      (∀ x ∈ chart (C i), x ∉ L → Q.multiplier i (q (C i) (baseReindex.symm x)) = 0) ∧
      ∃ N : TopologicalSpace.Opens (KPCompactInteriorH1.E (3*d F)), L ⊆ N ∧
        IsCompact (closure (N : Set (KPCompactInteriorH1.E (3*d F)))) ∧
        closure (N : Set (KPCompactInteriorH1.E (3*d F))) ⊆ chart (C i) ∧
        ∀ γ, ∀ x ∈ (N : Set (KPCompactInteriorH1.E (3*d F))), action (C i) γ x ∈ N := by
  let L₀ : Set (KPCompactInteriorH1.E (3*d F)) :=
    fromActual (ζ:=ζ) (hζ:=hζ) '' tsupport (Q.lift i)
  have hfrom : Continuous (fromActual (F:=F) (ζ:=ζ) (hζ:=hζ)) := by
    unfold fromActual labeledAInv
    fun_prop
  have hcompact : IsCompact L₀ := (Q.lift_compact_support i).image hfrom
  have hLchart : L₀ ⊆ chart (C i) := by
    rintro x ⟨y,hy,rfl⟩
    change toActual (fromActual (ζ:=ζ) (hζ:=hζ) y) ∈ (C i).domain
    have hh : toActual (ζ:=ζ) (hζ:=hζ) (fromActual (ζ:=ζ) (hζ:=hζ) y) = y := by
      simp only [toActual,fromActual,LinearIsometryEquiv.symm_apply_apply]
      funext k; simp [labeledA,labeledAInv]
    rw [hh]
    exact Q.lift_support_subset i hy
  obtain ⟨L,hL,hL₀L,hLD,hLi⟩ := compact_invariant_saturation (scalarData (C i)) L₀ hcompact hLchart
  obtain ⟨N,hLN,hNc,hND,hNi⟩ := invariant_window (scalarData (C i)) L hL hLD hLi
  refine ⟨L,hL,hLD,hLi,?_,N,hLN,hNc,hND,hNi⟩
  intro x hx hxL
  have hxL₀ : x ∉ L₀ := fun hh => hxL (hL₀L hh)
  have ht : toActual (ζ:=ζ) (hζ:=hζ) x ∉ tsupport (Q.lift i) := by
    intro hh
    apply hxL₀
    refine ⟨toActual (ζ:=ζ) (hζ:=hζ) x,hh,?_⟩
    simp only [fromActual,toActual]
    have hh : labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) (baseReindex.symm x)) =
        baseReindex.symm x := by
      apply PiLp.ext; intro k; simp [labeledA,labeledAInv]
    rw [hh,LinearIsometryEquiv.apply_symm_apply]
  have hz := image_eq_zero_of_notMem_tsupport ht
  have hr := Q.lift_restriction i ⟨toActual (ζ:=ζ) (hζ:=hζ) x,hx⟩
  exact hr.symm.trans hz
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContSectorLineL2Isometry
open KPContActualCotangentPieceHilbertSum KPContActualSectorChartEquivariantInputs
open KPContLocalNorm KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
private theorem chart_scalar_fromActual (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U:=U) (H:=H)) (y : a.domain) :
    scalarCoordinate s a (fromActual (ζ:=ζ) (hζ:=hζ) y.val) = sectionFields s.val a (coordinates a y) := by
  have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k; simp [labeledA,labeledAInv]
  simp [scalarCoordinate,fromActual,liftExtension,omega,hi,coordinates]
private theorem scalarCoordinate_measurable (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U:=U) (H:=H)) : Measurable (scalarCoordinate s a) := by
  apply measurable_extension
  have he : sectionFields s.val a = fun x => (s.val a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
    funext x; exact fields_apply _ _ _
  rw [he]
  apply (s.property.1 a.component).comp
  exact (KPContActualGlobalGreen.contDiff_labeledA.continuous.comp continuous_subtype_val).measurable
private theorem scalarCoordinate_of_product
    (η : CompactMultiplier (U:=U) (H:=H)) (hη : Measurable η.val.val)
    (u v : KPContSectorClosedLpSubspace.H F ζ hζ R U) (hv : IsActualProduct η u v)
    (s t : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s)
    (ht : sectorLineIsometry F ζ hζ U R P H v = mk F ζ hζ U R P H t)
    (a : ActualChart (U:=U) (H:=H)) :
    scalarCoordinate t a =ᵐ[measure a]
      fun x => (η.val.val (KPContCotangentOverlapRationalBranches.q a (baseReindex.symm x)) : ℂ) * scalarCoordinate s a x := by
  obtain ⟨s',t',hs',ht',hprod⟩ := hv
  have hst := chart_fields_ae_of_mk_eq s' s (hs'.symm.trans hs) a
  have htt := chart_fields_ae_of_mk_eq t' t (ht'.symm.trans ht) a
  have hq : Measurable (fun x : KPContLocalNorm.Space (3*d F) =>
      KPContCotangentOverlapRationalBranches.q a (baseReindex.symm x)) := by
    apply Continuous.measurable
    unfold KPContCotangentOverlapRationalBranches.q KPFiniteCuspAtlas.componentMap KPCuspSiegel.projection
    apply continuous_quotient_mk'.comp
    apply Continuous.prodMk _ continuous_const
    exact KPContActualGlobalGreen.contDiff_labeledA.continuous.comp baseReindex.symm.continuous
  unfold KPContActualSectorChartEquivariantInputs.measure
  rw [← lifted_measure_transport (a:=a)]
  apply (ae_map_iff (by
      apply Continuous.aemeasurable
      have hf : Continuous (fromActual (F:=F) (ζ:=ζ) (hζ:=hζ)) := by
        unfold fromActual labeledAInv
        fun_prop
      exact hf.comp continuous_subtype_val : AEMeasurable (fun y : a.domain => fromActual (ζ:=ζ) (hζ:=hζ) y.val) a.liftedMeasure)
    (measurableSet_eq_fun (scalarCoordinate_measurable t a)
      ((Complex.measurable_ofReal.comp (hη.comp hq)).mul (scalarCoordinate_measurable s a)))).mpr
  filter_upwards [hprod a,hst,htt] with y hy h1 h2
  change scalarCoordinate t a (fromActual y.val) =
    (η.val.val (KPContCotangentOverlapRationalBranches.q a (baseReindex.symm (fromActual y.val))) : ℂ) *
      scalarCoordinate s a (fromActual y.val)
  rw [chart_scalar_fromActual,chart_scalar_fromActual]
  rw [← h2,hy,h1]
  simp only [cutoffLift,coordinates,fromActual,LinearIsometryEquiv.symm_apply_apply]
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContSectorLineL2Isometry
open KPContActualCotangentPieceHilbertSum KPContActualSectorChartEquivariantInputs
open KPContLocalNorm KPContCotangentActualGenuineTwistIsotropy KPCompactInteriorH1
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem scalarCoordinate_equivariant (s : BorelL2Sections F ζ hζ U R P H)
    (a : ActualChart (U:=U) (H:=H)) (γ : Gamma a) (x : Space (3*d F)) (hx : x ∈ chart a) :
    scalarReindex (scalarCoordinate s a (action a γ x)) =
      scalarCocycle a γ x (scalarReindex (scalarCoordinate s a x)) := by
  have hp : baseReindex.symm x ∈ omega a := hx
  have ha : (isotropyArrow a γ).psi (baseReindex.symm x) ∈ omega a := KPContActualCotangentMeasurableFamilies.isotropy_mem a γ _ hp
  have he := (unitary_phase (isotropyArrow a γ)).2.2.2 s.val (baseReindex.symm x)
    (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hp)
  have hphase : (isotropyArrow a γ).phase (baseReindex.symm x) =
      (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) := by
    simp [Arrow.phase,isotropyArrow,isotropyChart]
  simp only [scalarCoordinate,action,LinearIsometryEquiv.symm_apply_apply,liftExtension,dif_pos hp,dif_pos ha]
  change scalarReindex ((isotropyChart a).coefficient s.val _) = _
  rw [he,hphase]
  simp [scalarCocycle,scalarPhase,sectionFields]
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContSectorLineL2Isometry KPContActualSectorFiniteSupportPartition
open KPContActualCotangentPieceHilbertSum KPContActualSectorChartEquivariantInputs
open KPContLocalNorm KPCompactInteriorH1 KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem partition_localized_weak_data {n : ℕ}
    (C : Fin n → ActualChart (U:=U) (H:=H))
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (Q : FinitePartition F ζ hζ U R P H C K O) (i : Fin n)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (hu : ActualWeakH1Loc (H:=H) u) :
    ∃ (v : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (t : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U:=U) (H:=H))
      (L : Set (KPCompactInteriorH1.E (3*d F)))
      (N : TopologicalSpace.Opens (KPCompactInteriorH1.E (3*d F))),
      IsActualProduct (partitionMultiplier C K O Q i) u v ∧
      sectorLineIsometry F ζ hζ U R P H v = mk F ζ hζ U R P H t ∧
      WeakChartData t r.val ∧
      IsCompact L ∧ L ⊆ N ∧ IsCompact (closure (N : Set (KPCompactInteriorH1.E (3*d F)))) ∧
      closure (N : Set (KPCompactInteriorH1.E (3*d F))) ⊆ chart (C i) ∧
      (∀ γ, ∀ x ∈ L, action (C i) γ x ∈ L) ∧
      (∀ γ, ∀ x ∈ (N : Set (KPCompactInteriorH1.E (3*d F))), action (C i) γ x ∈ N) ∧
      (∀ᵐ x ∂volume.restrict (chart (C i)), x ∉ L → scalarCoordinate t (C i) x = 0) ∧
      WeakFirst (chartOpens (scalarData (C i)))
        (fun x => scalarReindex (scalarCoordinate t (C i) x))
        (fun j x => scalarReindex (covariantCoordinate r.val (C i) x j)) ∧
      FiniteHw (chart (C i)) (weight (C i)) (actualInverseMetric (C i)) (actualZeroConnection (C i))
        (fun x => scalarReindex (scalarCoordinate t (C i) x))
        (fun j x => scalarReindex (covariantCoordinate r.val (C i) x j)) := by
  obtain ⟨v,hprod,hv,B,hB,hsupp⟩ := compactMultiplier_product_weakH1 (partitionMultiplier C K O Q i) u hu
  obtain ⟨t,r,ht,hw⟩ := actualWeakH1Loc_compactSupport_squareFinite v B hB hsupp hv
  obtain ⟨L,hL,hLD,hLi,hzero,N,hLN,hNc,hND,hNi⟩ := partition_flat_window C K O Q i
  obtain ⟨s,W,hs,hW⟩ := hu
  have he := scalarCoordinate_of_product (partitionMultiplier C K O Q i) (Q.continuous i).measurable u v hprod s t hs ht (C i)
  have he' := he.filter_mono (weightedMeasure_mutually_absolutelyContinuous
    (chartOpens (scalarData (C i))) (weight (C i)) (scalarData (C i)).smooth_weight
    (scalarData (C i)).positive_weight).2.ae_le
  have hz : ∀ᵐ x ∂volume.restrict (chart (C i)), x ∉ L → scalarCoordinate t (C i) x = 0 := by
    filter_upwards [he',ae_restrict_mem (scalarData (C i)).open_chart.measurableSet] with x hx hxD hxL
    rw [hx]
    change (Q.multiplier i _ : ℂ) * _ = 0
    rw [hzero x hxD hxL]
    simp
  exact ⟨v,t,r,L,N,hprod,ht,hw,hL,hLN,hNc,hND,hLi,hNi,hz,
    weakChartData_weakFirst t r.val hw (C i), actualFiniteHw (C i) v t ht r⟩

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContActualSectorSmoothTestModules KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualSectorChartEquivariantInputs KPContActualSectorCoordinateNullEquivalence
open KPContActualSectorBallRestriction KPContActualCotangentCountableShrinking

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem lp_norm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ).toReal := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow]
  congr 1
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal))
    (by norm_num) hf.aestronglyMeasurable
  norm_num at h
  rw [h]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

private theorem scalarProducer_norm_of_supported (a : ActualChart (U:=U) (H:=H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hu : SupportedAE (H:=H) u a.baseDomain) : ‖scalarProducer a u‖ = ‖u‖ := by
  obtain ⟨s, hs, hzero⟩ := hu
  have he : scalarProducer a u = (scalar_memLp a s).toLp (scalar s a) := by
    apply Lp.ext
    exact (scalarProducer_spec a u s hs).trans (scalar_memLp a s).coeFn_toLp.symm
  have hm := squaredNorm_measurable F ζ hζ U R P H s.val s.property.1
  have hi : (∫⁻ x, ENNReal.ofReal (‖scalar s a x‖^2) ∂measure a) =
      normIntegral F ζ hζ U R P H s.val := by
    change (∫⁻ x, ENNReal.ofReal (‖scalar s a x‖^2) ∂KPChartL2.weightedMeasure (3*KPContCotangentActualOverlap.d F) (chart a) (weight a)) = _
    rw [← lifted_measure_transport (a:=a)]
    change (∫⁻ x, ENNReal.ofReal (‖scalar s a x‖^2) ∂Measure.map (ActualScalarTransport.emb a) a.liftedMeasure) = _
    rw [(ActualScalarTransport.emb_meas a).lintegral_map]
    have hp : ∀ y : a.domain, ENNReal.ofReal (‖scalar s a (ActualScalarTransport.emb a y)‖^2) =
        squaredNorm F ζ hζ U R P H s.val (a.toBase y) := by
      intro y
      rw [ActualScalarTransport.scalar_pull, squaredNorm,
        ActualScalarTransport.coefficient_norm]
    change (∫⁻ y, ENNReal.ofReal (‖scalar s a (ActualScalarTransport.emb a y)‖^2) ∂a.liftedMeasure) = _
    simp_rw [hp]
    rw [← lintegral_map' hm.aemeasurable (every_shrunkChart_properties F ζ hζ U R P H a).measurable.aemeasurable,
      (every_shrunkChart_properties F ζ hζ U R P H a).exact_pushforward]
    rw [← lintegral_indicator (every_shrunkChart_properties F ζ hζ U R P H a).base_open.measurableSet]
    apply lintegral_congr_ae
    filter_upwards [hzero] with x hx
    by_cases h : x ∈ a.baseDomain
    · simp [h]
    · simp [h, hx h]
  have hn : ‖scalarProducer a u‖^2 = ‖u‖^2 := by
    rw [he, lp_norm_sq, hi]
    rw [← (sectorLineIsometry F ζ hζ U R P H).norm_map u, hs, norm_sq]
  nlinarith [norm_nonneg (scalarProducer a u), norm_nonneg u]

private theorem squaredNorm_sub_zero (s t : Sections F ζ hζ U R P H)
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U)
    (hs : squaredNorm F ζ hζ U R P H s x = 0)
    (ht : squaredNorm F ζ hζ U R P H t x = 0) :
    squaredNorm F ζ hζ U R P H (s-t) x = 0 := by
  change ENNReal.ofReal (sectionNorm F ζ hζ U R P H s x ^ 2) = 0 at hs
  change ENNReal.ofReal (sectionNorm F ζ hζ U R P H t x ^ 2) = 0 at ht
  have hs0 : sectionNorm F ζ hζ U R P H s x = 0 :=
    sq_eq_zero_iff.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hs) (sq_nonneg _))
  have ht0 : sectionNorm F ζ hζ U R P H t x = 0 :=
    sq_eq_zero_iff.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (sq_nonneg _))
  simp only [sectionNorm] at hs0 ht0
  unfold squaredNorm sectionNorm
  generalize hy : (H.atlas U).components.symm x = y at *
  rcases y with ⟨i,y⟩
  induction y using Quotient.inductionOn with
  | h y =>
    simp only [componentNorm, Quotient.lift_mk] at hs0 ht0 ⊢
    have hs' := norm_eq_zero.mp hs0
    have ht' := norm_eq_zero.mp ht0
    simp [hs', ht']

private theorem supportedAE_sub (a : ActualChart (U:=U) (H:=H))
    (u v : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hu : SupportedAE (H:=H) u a.baseDomain)
    (hv : SupportedAE (H:=H) v a.baseDomain) :
    SupportedAE (H:=H) (u-v) a.baseDomain := by
  obtain ⟨s,hs,hzero⟩ := hu
  obtain ⟨t,ht,hzero'⟩ := hv
  refine ⟨s-t, ?_, ?_⟩
  · rw [map_sub, hs, ht, ← map_sub]
  · filter_upwards [hzero,hzero'] with x hx hx'
    intro h
    exact squaredNorm_sub_zero s.val t.val x (hx h) (hx' h)

private theorem scalarProducer_tendsto_of_supported (a : ActualChart (U:=U) (H:=H))
    (f : ℕ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hf : ∀ n, SupportedAE (H:=H) (f n) a.baseDomain)
    (hu : SupportedAE (H:=H) u a.baseDomain)
    (hlim : Filter.Tendsto (fun n => scalarProducer a (f n)) Filter.atTop
      (nhds (scalarProducer a u))) :
    Filter.Tendsto f Filter.atTop (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  convert hlim using 1
  funext n
  rw [← map_sub]
  exact (scalarProducer_norm_of_supported a (f n-u) (supportedAE_sub a (f n) u (hf n) hu)).symm

open KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
private theorem scalarZeroExtension_supportedAE
    (a : ActualChart (U:=U) (H:=H)) (f : localScalarTests a)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    SupportedAE (H:=H) (iota (scalarZeroExtension a f)) a.baseDomain := by
  let g := scalarZeroExtension a f
  have ps := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar R.adelic_isHaar
    U R rfl P H realization
  have hspec := (Classical.choose_spec (scalar_gluing g)).1
  have hcont : Continuous (scalarCovered g).val :=
    (continuous_iff F ζ hζ U R P H (scalarSections g)).mp
      (fun i => (hspec.1 i).continuous)
  let b : BorelL2Scalars F ζ hζ U R :=
    ⟨scalarCovered g, hcont.measurable, scalar_memLp g⟩
  have hb := sectorLineIsometry_representative F ζ hζ U R P H (iota g) b (by rfl)
  have hval : (borelS F ζ hζ U R P H b).val = scalarSections g := by
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarCovered g) = _
    exact ps.covered_realization g
  refine ⟨borelS F ζ hζ U R P H b, hb, Filter.Eventually.of_forall fun x hx => ?_⟩
  rw [hval, squaredNorm]
  have hs : tsupport (sectionNorm F ζ hζ U R P H (scalarSections g)) ⊆ a.baseDomain := by
    rw [← ps.scalar_support, ps.scalar_extension_support]
    exact f.property.2.2.2
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))]
  simp

private theorem scalarZeroExtension_tendsto_of_scalarProducer
    (a : ActualChart (U:=U) (H:=H)) (f : ℕ → localScalarTests a)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (hu : SupportedAE (H:=H) u a.baseDomain)
    (hlim : Filter.Tendsto (fun n => scalarProducer a (iota (scalarZeroExtension a (f n))))
      Filter.atTop (nhds (scalarProducer a u))) :
    Filter.Tendsto (fun n => iota (scalarZeroExtension a (f n))) Filter.atTop (nhds u) := by
  exact scalarProducer_tendsto_of_supported a _ u
    (fun n => scalarZeroExtension_supportedAE a (f n) realization) hu hlim

private theorem scalarProducer_zeroExtension_ae
    (a : ActualChart (U:=U) (H:=H)) (f : localScalarTests a)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    scalarProducer a (iota (scalarZeroExtension a f)) =ᵐ[measure a]
      (fun x => liftExtension a f.val ((baseReindex (F:=F)).symm x)) := by
  let g := scalarZeroExtension a f
  have ps := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar R.adelic_isHaar
    U R rfl P H realization
  have hspec := (Classical.choose_spec (scalar_gluing g)).1
  have hcont : Continuous (scalarCovered g).val :=
    (continuous_iff F ζ hζ U R P H (scalarSections g)).mp
      (fun i => (hspec.1 i).continuous)
  let b : BorelL2Scalars F ζ hζ U R :=
    ⟨scalarCovered g, hcont.measurable, scalar_memLp g⟩
  have hb := sectorLineIsometry_representative F ζ hζ U R P H (iota g) b (by rfl)
  have hval : (borelS F ζ hζ U R P H b).val = scalarSections g := by
    change KPContSectorScalarLineAlgebra.S F ζ hζ U R P H (scalarCovered g) = _
    exact ps.covered_realization g
  have hfields : sectionFields (scalarSections g) = g.val := ps.scalar_represented g
  have h := scalarProducer_spec a (iota g) (borelS F ζ hζ U R P H b) hb
  have hg : g.val a = f.val := ps.scalar_restriction_extension a f
  simpa only [scalar, hval, hfields, hg] using h

private theorem scalarZeroExtension_tendsto_of_chartL2
    (a : ActualChart (U:=U) (H:=H)) (f : ℕ → localScalarTests a)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (hu : SupportedAE (H:=H) u a.baseDomain)
    (hmem : ∀ n, MemLp (fun x => liftExtension a (f n).val ((baseReindex (F:=F)).symm x)) 2 (measure a))
    (hlim : Filter.Tendsto (fun n => (hmem n).toLp
      (fun x => liftExtension a (f n).val ((baseReindex (F:=F)).symm x)))
      Filter.atTop (nhds ((scalar_memLp a s).toLp (scalar s a)))) :
    Filter.Tendsto (fun n => iota (scalarZeroExtension a (f n))) Filter.atTop (nhds u) := by
  apply scalarZeroExtension_tendsto_of_scalarProducer a f u realization hu
  have ht : scalarProducer a u = (scalar_memLp a s).toLp (scalar s a) := by
    apply Lp.ext
    exact (scalarProducer_spec a u s hs).trans (scalar_memLp a s).coeFn_toLp.symm
  have hf : ∀ n, scalarProducer a (iota (scalarZeroExtension a (f n))) =
      (hmem n).toLp (fun x => liftExtension a (f n).val ((baseReindex (F:=F)).symm x)) := by
    intro n
    apply Lp.ext
    exact (scalarProducer_zeroExtension_ae a (f n) realization).trans (hmem n).coeFn_toLp.symm
  simpa only [hf, ht] using hlim

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContSectorLineL2Isometry KPContActualSectorFiniteSupportPartition
open KPContActualSectorChartEquivariantInputs KPContLocalNorm KPCompactInteriorH1
open KPContActualCotangentMeasurableFamilies KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem actual_chart_approximation
    (a : ActualChart (U:=U) (H:=H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U:=U) (H:=H))
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s)
    (hw : WeakChartData s r.val)
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLi : ∀ γ, ∀ x ∈ L, action a γ x ∈ L)
    (N : TopologicalSpace.Opens (Space (3*d F))) (hLN : L ⊆ N)
    (hNc : IsCompact (closure (N : Set (Space (3*d F)))))
    (hND : closure (N : Set (Space (3*d F))) ⊆ chart a)
    (hNi : ∀ γ, ∀ x ∈ (N : Set (Space (3*d F))), action a γ x ∈ N)
    (hz : ∀ᵐ x ∂volume.restrict (chart a), x ∉ L → scalarCoordinate s a x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (h : Space (3*d F) → KPCompactInteriorH1.V 1)
      (herror : FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
        (fun x => scalarReindex (scalarCoordinate s a x) - h x)
        (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ h x (coordinateDirection j)))
      (τ : localScalarTests a),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ N ∧
      (∀ x, liftExtension a τ.val (baseReindex.symm x) = (h x) 0) ∧
      Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
        (fun x => scalarReindex (scalarCoordinate s a x) - h x)
        (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ h x (coordinateDirection j)) herror < ε := by
  have hd : 0 < d F := by
    have hp := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
    rw [show d F = Module.finrank ℚ F / 2 from rfl, ← hp.2.1]
    exact hp.2.2
  obtain ⟨h,he,hsm,hc,ht,heq,hb⟩ := kp_cont_compact_interior_equivariant_h1_approximation
    (3*d F) 1 (by omega) (by omega) (Gamma a) (scalarData a)
    (actualInverseMetric a) (actualZeroConnection a) (actualInverseMetric_invariant a)
    (actualZeroConnection_unitary a) (actualZeroConnection_compatible a)
    L hL hLi N hLN hNc hND hNi
    (fun x => scalarReindex (scalarCoordinate s a x))
    (fun j x => scalarReindex (covariantCoordinate r.val a x j))
    (weakChartData_weakFirst s r.val hw a)
    (by filter_upwards [hz] with x hx hxL; rw [hx hxL]; exact map_zero _)
    (by intro γ; filter_upwards [ae_restrict_mem (scalarData a).open_chart.measurableSet |>.filter_mono
          (withDensity_absolutelyContinuous (volume.restrict (chart a))
            (fun x => ENNReal.ofReal (weight a x))).ae_le] with x hx
        exact scalarCoordinate_equivariant s a γ x hx)
    (actualFiniteHw a u s hs r) ε hε
  obtain ⟨τ,hτ,hflat,hτc,hτs⟩ := smoothChartTest_of_flat a h hsm hc
    (ht.trans (fun x hx => hND (subset_closure hx))) heq
  exact ⟨h,he,τ,hsm,hc,ht,hflat,hb⟩
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem actual_form_mem_outputs
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hu : u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain) :
    IsActualWeakGradient (H:=H) u
      ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure ⟨u,hu⟩) ∧
    ∃ φ : ℕ → S_U F ζ hζ U R P H,
      Filter.Tendsto (fun n => iota (φ n)) Filter.atTop (nhds u) ∧
      Filter.Tendsto (fun n => j (D_U (φ n))) Filter.atTop
        (nhds ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure ⟨u,hu⟩)) := by
  have hw := (kp_cont_actual_sector_form_weak_localization F ζ hζ μG hμG U R hR P H realization).closed_gradient ⟨u,hu⟩
  obtain ⟨φ,hφ,hD,hE⟩ := (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization).form_core ⟨u,hu⟩
  exact ⟨hw,φ,hφ,hD⟩
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualCotangentPieceHilbertSum KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
attribute [local instance 2000] KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

private theorem product_supportedAE_9669
    (η : CompactMultiplier (U:=U) (H:=H))
    (u v : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hv : IsActualProduct η u v)
    (B : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hB : tsupport η.val.val ⊆ B) (hBm : MeasurableSet B) : SupportedAE (H:=H) v B := by
  obtain ⟨s,t,hs,ht,hprod⟩ := hv
  refine ⟨t,ht,?_⟩
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hchart (n : ℕ) : ∀ᵐ b ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P).restrict
      (cover.chart n).baseDomain,
      b ∉ B → squaredNorm F ζ hζ U R P H t.val b = 0 := by
    let a := cover.chart n
    have hlocal : ∀ᵐ y ∂a.liftedMeasure,
        a.toBase y ∉ B → squaredNorm F ζ hζ U R P H t.val (a.toBase y) = 0 := by
      filter_upwards [hprod a] with y hy hnot
      have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
        funext k; simp [labeledA,labeledAInv]
      have hz : η.val.val (a.toBase y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx => hnot (hB hx))
      have hfields : (t.val a.component).val y.val = 0 := by
        change η.val.val (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) (KPCuspSiegel.projection F _ y.val)) = 0 at hz
        simpa only [fields_apply,coordinates,cutoffLift,hi,KPContCotangentOverlapRationalBranches.q,
          KPContActualCotangentCountableShrinking.ShrunkChart.toBase,hz,
          Complex.ofReal_zero,zero_mul] using hy
      unfold squaredNorm
      rw [norm_toBase,hfields]
      simp
    rw [← (cover.properties n).exact_pushforward]
    apply (ae_map_iff (cover.properties n).measurable.aemeasurable ?_).mpr hlocal
    have hm := squaredNorm_measurable F ζ hζ U R P H t.val t.property.1
    convert hBm.union (measurableSet_eq_fun hm measurable_const) using 1
    ext x
    simp only [Set.mem_union,Set.mem_setOf_eq]
    tauto
  have he := (ae_restrict_iUnion_iff (fun n => (cover.chart n).baseDomain)
    (fun x => x ∉ B → squaredNorm F ζ hζ U R P H t.val x = 0)).mpr hchart
  rwa [cover.covers,Measure.restrict_univ] at he

private theorem form_mem_of_limit_cauchy_9669
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (φ : ℕ → S_U F ζ hζ U R P H)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hlim : Filter.Tendsto (fun n => iota (φ n)) Filter.atTop (nhds u))
    (hC : CauchySeq (fun n => j (D_U (φ n)))) :
    u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain := by
  let A := KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
  have hclosable : A.IsClosable :=
    (kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization).gradient_closable
  let s : ℕ → A.domain := fun n => ⟨iota (φ n), LinearMap.mem_range_self iota (φ n)⟩
  have hC' : CauchySeq (fun n => A (s n)) := by
    simpa only [s,A,KPContActualSectorFriedrichsSynthesis.A_U,KPTestOperator.descend_image] using hC
  exact (closedGradientForm_closure_characterization A hclosable s u hlim hC').choose
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPContActualCotangentMeasurableFamilies
open KPContCotangentActualOverlap KPCompactInteriorH1 KPContLocalNorm
open KPContActualSectorChartEquivariantInputs KPContActualSectorFiniteSupportPartition
open KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem finite_partition_form_mem_9669
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    {n : ℕ} (C : Fin n → ActualChart (U:=U) (H:=H))
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (Q : FinitePartition F ζ hζ U R P H C K O)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hsupp : SupportedAE (H:=H) u K)
    (v : Fin n → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hv : ∀ i, IsActualProduct (partitionMultiplier C K O Q i) u (v i))
    (hmem : ∀ i, v i ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain) :
    u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain := by
  have heq : ∑ i, v i = u := partition_products_reconstruct C K O Q
    (partitionMultiplier C K O Q) (fun _ => rfl) u v hv hsupp
  rw [← heq]
  exact Submodule.sum_mem _ (fun i _ => hmem i)
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPCompactInteriorH1 KPContLocalNorm
open KPContCotangentActualOverlap KPContActualSectorChartEquivariantInputs
open KPContActualSectorTestDifferentialDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

open KPContActualSectorBallRestriction KPContActualSectorCoordinateNullEquivalence
private theorem norm_toLp_l2_9669 {X Y : Type*} [MeasurableSpace X]
    [NormedAddCommGroup Y] (μ : Measure X) (f : X → Y) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ) := by
  have h := lpNorm_eq_integral_norm_rpow_toReal (μ:=μ) (f:=f)
    (p:=2) (by norm_num) (by norm_num) hf.aestronglyMeasurable
  rw [Lp.norm_toLp,toReal_eLpNorm,h]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [Real.rpow_ofNat])

private theorem scalar_limit_of_Hw_errors_9669
    (a : ActualChart (U:=U) (H:=H))
    (s : BorelL2Sections F ζ hζ U R P H)
    (r : KPContActualCotangentMeasurableFamilies.SquareFiniteFamily (U:=U) (H:=H))
    (τ : ℕ → localScalarTests a) (h : ℕ → Space (3*d F) → V 1)
    (hext : ∀ n x, liftExtension a (τ n).val (baseReindex.symm x) = (h n x) 0)
    (herr : ∀ n, FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
      (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)))
    (hsmall : Filter.Tendsto (fun n => Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
      (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)) (herr n))
      Filter.atTop (nhds 0)) :
    ∃ hmem : ∀ n, MemLp (fun x => liftExtension a (τ n).val (baseReindex.symm x)) 2 (measure a),
      Filter.Tendsto (fun n => (hmem n).toLp (fun x => liftExtension a (τ n).val (baseReindex.symm x)))
        Filter.atTop (nhds ((scalar_memLp a s).toLp (scalar s a))) := by
  let e : ℕ → Space (3*d F) → ℂ := fun n x => scalar s a x - liftExtension a (τ n).val (baseReindex.symm x)
  have he : ∀ n x, e n x = scalarReindex.symm (scalarReindex (scalarCoordinate s a x) - h n x) := by
    intro n x
    rw [map_sub,LinearIsometryEquiv.symm_apply_apply]
    rw [show scalarReindex.symm (h n x) = (h n x) 0 from rfl]
    exact congrArg (fun z => scalar s a x - z) (hext n x)
  have heLp : ∀ n, MemLp (e n) 2 (measure a) := by
    intro n
    have hh := (herr n).1.continuousLinearMap_comp
      scalarReindex.symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact hh.ae_eq (Filter.Eventually.of_forall (fun x => (he n x).symm))
  have hmem : ∀ n, MemLp (fun x => liftExtension a (τ n).val (baseReindex.symm x)) 2 (measure a) := by
    intro n
    convert (scalar_memLp a s).sub (heLp n) using 1
    funext x
    dsimp [e]
    abel
  refine ⟨hmem,?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖(hmem n).toLp (fun x => liftExtension a (τ n).val (baseReindex.symm x)) -
      (scalar_memLp a s).toLp (scalar s a)‖ =
      l2Norm (measure a) (fun x => scalarReindex (scalarCoordinate s a x) - h n x) (herr n).1 := by
    intro n
    rw [← MemLp.toLp_sub]
    rw [norm_toLp_l2_9669,l2Norm]
    congr 1
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun x => ?_)
    change ‖liftExtension a (τ n).val (baseReindex.symm x) - scalar s a x‖^2 = _
    rw [norm_sub_rev]
    change ‖e n x‖^2 = _
    rw [he,LinearIsometryEquiv.norm_map]
  simp_rw [hnorm]
  apply squeeze_zero (fun n => Real.sqrt_nonneg _) _ hsmall
  intro n
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPCompactInteriorH1 KPContLocalNorm
open KPContCotangentActualOverlap KPContActualSectorChartEquivariantInputs
open KPContActualSectorTestDifferentialDescent KPContActualSectorTestEmbeddings
open KPContActualCotangentMeasurableFamilies
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem actual_Hw_nonneg_9669 (a : ActualChart (U:=U) (H:=H))
    (f : Space (3*d F) → V 1) (g : Fin (3*d F) → Space (3*d F) → V 1)
    (hf : FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a) f g) :
    0 ≤ Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a) f g hf :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem chart_form_mem_from_Hw_sequence_9669
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (a : ActualChart (U:=U) (H:=H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U:=U) (H:=H))
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s)
    (hsupp : SupportedAE (H:=H) u a.baseDomain)
    (τ : ℕ → localScalarTests a) (h : ℕ → Space (3*d F) → V 1)
    (hext : ∀ n x, liftExtension a (τ n).val (baseReindex.symm x) = (h n x) 0)
    (herr : ∀ n, FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
      (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)))
    (hsmall : Filter.Tendsto (fun n => Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
      (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)) (herr n))
      Filter.atTop (nhds 0))
    (hC : CauchySeq (fun n => j (D_U (scalarZeroExtension a (τ n))))) :
    u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain := by
  obtain ⟨hmem,hlim⟩ := scalar_limit_of_Hw_errors_9669 a s r τ h hext herr hsmall
  have hscalar := scalarZeroExtension_tendsto_of_chartL2 a τ u s hs realization hsupp hmem hlim
  exact form_mem_of_limit_cauchy_9669 μG hμG hR realization (fun n => scalarZeroExtension a (τ n)) u hscalar hC
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPCompactInteriorH1 KPContLocalNorm
open KPContCotangentActualOverlap KPContActualSectorChartEquivariantInputs
open KPContActualSectorTestDifferentialDescent KPContActualSectorTestEmbeddings
open KPContActualCotangentMeasurableFamilies
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem actual_chart_Hw_sequence_9669
    (a : ActualChart (U:=U) (H:=H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U:=U) (H:=H))
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s)
    (hw : WeakChartData s r.val)
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLi : ∀ γ, ∀ x ∈ L, action a γ x ∈ L)
    (N : TopologicalSpace.Opens (Space (3*d F))) (hLN : L ⊆ N)
    (hNc : IsCompact (closure (N : Set (Space (3*d F)))))
    (hND : closure (N : Set (Space (3*d F))) ⊆ chart a)
    (hNi : ∀ γ, ∀ x ∈ (N : Set (Space (3*d F))), action a γ x ∈ N)
    (hz : ∀ᵐ x ∂volume.restrict (chart a), x ∉ L → scalarCoordinate s a x = 0) :
    ∃ (h : ℕ → Space (3*d F) → V 1) (τ : ℕ → localScalarTests a)
      (herr : ∀ n, FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
        (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
        (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j))),
      (∀ n, ContDiff ℝ ∞ (h n)) ∧ (∀ n, HasCompactSupport (h n)) ∧
      (∀ n, tsupport (h n) ⊆ N) ∧
      (∀ n x, liftExtension a (τ n).val (baseReindex.symm x) = (h n x) 0) ∧
      Filter.Tendsto (fun n => Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
        (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
        (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)) (herr n))
        Filter.atTop (nhds 0) := by
  have hex (n : ℕ) := actual_chart_approximation a u s r hs hw L hL hLi N hLN hNc hND hNi hz
    (1 / (n+1:ℝ)) (by positivity)
  choose h herr τ hsm hcomp hsub hext hb using hex
  refine ⟨h,τ,herr,hsm,hcomp,hsub,hext,?_⟩
  exact squeeze_zero (fun n => actual_Hw_nonneg_9669 a _ _ (herr n))
    (fun n => (hb n).le) tendsto_one_div_add_atTop_nhds_zero_nat
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPCompactInteriorH1 KPContLocalNorm
open KPContCotangentActualOverlap KPContActualSectorChartEquivariantInputs
open KPContActualSectorTestDifferentialDescent KPContActualSectorTestEmbeddings
open KPContActualCotangentMeasurableFamilies KPContActualSectorFiniteSupportPartition
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem compact_form_mem_from_local_9669
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (hlocal : ∀ (a : ActualChart (U:=U) (H:=H))
      (v : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U:=U) (H:=H)),
      sectorLineIsometry F ζ hζ U R P H v = mk F ζ hζ U R P H s →
      WeakChartData s r.val → SupportedAE (H:=H) v a.baseDomain →
      ∀ (L : Set (Space (3*d F))), IsCompact L →
      (∀ γ, ∀ x ∈ L, action a γ x ∈ L) →
      ∀ (N : TopologicalSpace.Opens (Space (3*d F))), L ⊆ N →
      IsCompact (closure (N : Set (Space (3*d F)))) →
      closure (N : Set (Space (3*d F))) ⊆ chart a →
      (∀ γ, ∀ x ∈ (N : Set (Space (3*d F))), action a γ x ∈ N) →
      (∀ᵐ x ∂volume.restrict (chart a), x ∉ L → scalarCoordinate s a x = 0) →
      v ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (hsupp : SupportedAE (H:=H) u K) (hw : ActualWeakH1Loc (H:=H) u) :
    u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain := by
  obtain ⟨n,C,hn,hcover,⟨Q⟩⟩ := kp_cont_actual_sector_finite_support_partition
    F ζ hζ U R P H K Set.univ hK isOpen_univ (Set.subset_univ _)
  have hdata := fun i => partition_localized_weak_data C K Set.univ Q i u hw
  choose v s r L N hprod hs hweak hL hLN hNc hND hLi hNi hz hfirst hfin using hdata
  apply finite_partition_form_mem_9669 μG hμG hR realization C K Set.univ Q u hsupp v hprod
  intro i
  have hvSupport : SupportedAE (H:=H) (v i) (C i).baseDomain :=
    product_supportedAE_9669 (partitionMultiplier C K Set.univ Q i) u (v i) (hprod i)
      (C i).baseDomain (fun x hx => (Q.support_subset i hx).1)
      (KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H (C i)).base_open.measurableSet
  exact hlocal (C i) (v i) (s i) (r i) (hs i) (hweak i) hvSupport (L i) (hL i)
    (hLi i) (N i) (hLN i) (hNc i) (hND i) (hNi i) (hz i)
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

noncomputable section
open scoped Classical NumberField ContDiff ContDiff
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualCotangentMeasurableFamilies KPContActualCotangentPieceHilbertSum
open KPContActualSectorChartEquivariantInputs KPContActualCotangentChartRestriction
open KPContCotangentActualGenuineTwistIsotropy KPContLocalNorm KPCompactInteriorH1
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem port_lp_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖^2 ∂μ) = ‖hf.toLp f‖^2 := by
  have h := L2.inner_def (𝕜:=ℂ) (hf.toLp f) (hf.toLp f)
  have hc : inner ℂ (hf.toLp f) (hf.toLp f) = ((‖hf.toLp f‖^2 : ℝ) : ℂ) := by
    convert (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (hf.toLp f)) using 1 <;> norm_cast
  rw [hc] at h
  have he : (∫ x, inner ℂ (hf.toLp f x) (hf.toLp f x) ∂μ) =
      ((∫ x, ‖f x‖^2 ∂μ : ℝ) : ℂ) := by
    calc
      _ = ∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        simp [hx, inner_self_eq_norm_sq_to_K]
      _ = _ := integral_ofReal
  rw [he] at h
  have hh := congrArg Complex.re h
  simpa only [Complex.ofReal_re] using hh.symm
private theorem scalarZeroExtension_cauchy_of_chartH1
    (a : ActualChart (U:=U) (H:=H)) (f : ℕ → localScalarTests a)
    (L : Set (Space (3*d F))) (hL : IsCompact L) (hLD : L ⊆ chart a)
    (hsm : ∀ n, ContDiff ℝ ∞ (fun x => liftExtension a (f n).val (baseReindex.symm x)))
    (hsupp : ∀ n, tsupport (fun x => liftExtension a (f n).val (baseReindex.symm x)) ⊆ L)
    (hm : ∀ n, MemLp (fun x => liftExtension a (f n).val (baseReindex.symm x)) 2 (measure a))
    (hdm : ∀ n j, MemLp (coordinatePartial j (fun x => liftExtension a (f n).val (baseReindex.symm x))) 2 (measure a))
    (hc : CauchySeq (fun n => (hm n).toLp (fun x => liftExtension a (f n).val (baseReindex.symm x))))
    (hcd : ∀ j, CauchySeq (fun n => (hdm n j).toLp (coordinatePartial j (fun x => liftExtension a (f n).val (baseReindex.symm x))))) :
    CauchySeq (fun n => j (D_U (scalarZeroExtension a (f n)))) := by
  let g : ℕ → Space (3*d F) → ℂ := fun n x => liftExtension a (f n).val (baseReindex.symm x)
  obtain ⟨C,hC,hbound⟩ := scalarZeroExtension_firstJet_bound a L hL hLD
  have hflat (m n : ℕ) : (fun x => liftExtension a (f m-f n).val (baseReindex.symm x)) = g m - g n := by
    funext x
    simp only [g, Pi.sub_apply, liftExtension, Submodule.coe_sub]
    split_ifs <;> simp
  have hsubsupp (m n : ℕ) : tsupport (g m-g n) ⊆ L := by
    rw [sub_eq_add_neg]
    exact (tsupport_add (g m) (-g n)).trans (Set.union_subset (hsupp m) (by simpa using hsupp n))
  have hpartial (m n : ℕ) (k : Fin (3*d F)) :
      coordinatePartial k (g m-g n) = coordinatePartial k (g m)-coordinatePartial k (g n) := by
    funext x
    unfold coordinatePartial
    rw [fderiv_sub ((hsm m).differentiable (by simp) x) ((hsm n).differentiable (by simp) x)]
    rfl
  have hi (m n : ℕ) : Integrable (fun x => ‖(g m-g n) x‖^2 + ∑ k, ‖coordinatePartial k (g m-g n) x‖^2) (measure a) := by
    apply ((hm m).sub (hm n)).integrable_norm_pow (by norm_num) |>.add
    apply integrable_finsetSum
    intro k _
    rw [hpartial]
    exact ((hdm m k).sub (hdm n k)).integrable_norm_pow (by norm_num)
  have he (m n : ℕ) : (∫ x in L, (‖(g m-g n) x‖^2 + ∑ k, ‖coordinatePartial k (g m-g n) x‖^2) ∂measure a) =
      ‖(hm m).toLp (g m)-(hm n).toLp (g n)‖^2 + ∑ k, ‖(hdm m k).toLp (coordinatePartial k (g m))-(hdm n k).toLp (coordinatePartial k (g n))‖^2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
    · rw [integral_add (((hm m).sub (hm n)).integrable_norm_pow (by norm_num)) (by
        apply integrable_finsetSum
        intro k _
        rw [hpartial]
        exact ((hdm m k).sub (hdm n k)).integrable_norm_pow (by norm_num))]
      rw [port_lp_integral (measure a) (g m-g n) ((hm m).sub (hm n)), (hm m).toLp_sub (hm n)]
      congr 1
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [hpartial, port_lp_integral (measure a) _ ((hdm m k).sub (hdm n k)), (hdm m k).toLp_sub (hdm n k)]
      · intro k _
        rw [hpartial]
        exact ((hdm m k).sub (hdm n k)).integrable_norm_pow (by norm_num)
    · have hz : (g m-g n) x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hsubsupp m n ht))
      have hd : ∀ k, coordinatePartial k (g m-g n) x = 0 := by
        intro k
        apply image_eq_zero_of_notMem_tsupport
        intro ht
        exact hx (hsubsupp m n (tsupport_fderiv_apply_subset ℝ (coordinateDirection k) ht))
      simp [hz, hd]
  have hb (m n : ℕ) : ‖j (D_U (scalarZeroExtension a (f m)))-j (D_U (scalarZeroExtension a (f n)))‖^2 ≤
      C * (‖(hm m).toLp (g m)-(hm n).toLp (g n)‖^2 + ∑ k, ‖(hdm m k).toLp (coordinatePartial k (g m))-(hdm n k).toLp (coordinatePartial k (g n))‖^2) := by
    have h := hbound (f m-f n) (by rw [hflat]; exact hsubsupp m n)
    simp only [show ∀ x, liftExtension a (f m-f n).val (baseReindex.symm x) = (g m-g n) x from congrFun (hflat m n)] at h
    change _ ≤ C * (∫ x in L, (‖(g m-g n) x‖^2 + ∑ k, ‖coordinatePartial k (g m-g n) x‖^2) ∂measure a) at h
    rw [he] at h
    simp only [map_sub] at h
    nlinarith [sq_nonneg ‖iota (scalarZeroExtension a (f m-f n))‖]
  rw [cauchySeq_iff_tendsto_dist_atTop_0] at hc
  simp only [dist_eq_norm] at hc
  have hdlim : ∀ k, Filter.Tendsto (fun p : ℕ × ℕ => ‖(hdm p.1 k).toLp (coordinatePartial k (g p.1))-(hdm p.2 k).toLp (coordinatePartial k (g p.2))‖^2) Filter.atTop (nhds 0) := by
    intro k
    have ht := cauchySeq_iff_tendsto_dist_atTop_0.mp (hcd k)
    simpa only [dist_eq_norm, zero_pow (by norm_num : 2 ≠ 0)] using ht.pow 2
  have hlim := (hc.pow 2).add (tendsto_finsetSum Finset.univ (fun k _ => hdlim k)) |>.const_mul C
  simp only [zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, add_zero, mul_zero] at hlim
  have hs := squeeze_zero (fun p : ℕ × ℕ => sq_nonneg ‖j (D_U (scalarZeroExtension a (f p.1)))-j (D_U (scalarZeroExtension a (f p.2)))‖) (fun p => hb p.1 p.2) hlim
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  rw [Real.sqrt_zero] at ht
  convert ht using 1
  funext p
  rw [dist_eq_norm]
  exact (Real.sqrt_sq (norm_nonneg _)).symm
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse
open KPContActualSectorSmoothTestModules KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPCompactInteriorH1 KPContLocalNorm
open KPContCotangentActualOverlap KPContActualSectorChartEquivariantInputs
open KPContActualSectorTestDifferentialDescent KPContActualSectorTestEmbeddings
open KPContActualCotangentMeasurableFamilies
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem compact_actual_derivatives_memLp
    (a : ActualChart (U:=U) (H:=H)) (C : Set (Space (3*d F)))
    (hC : IsCompact C) (hCD : C ⊆ chart a)
    (f : Space (3*d F) → V 1) (g : Fin (3*d F) → Space (3*d F) → V 1)
    (hw : WeakFirst (chartOpens (scalarData a)) f g)
    (hz : ∀ᵐ x ∂volume.restrict (chart a), x ∉ C → f x = 0) :
    ∀ j, MemLp (g j) 2 (measure a) := by
  have hz' : ∀ᵐ x ∂volume.restrict (chart a), x ∈ chart a \ C → f x = 0 :=
    hz.mono (fun x hx h => hx h.2)
  obtain ⟨hf,hg,_,_,_,_,_,_,he,he'⟩ := compactZeroExtension_properties hC hCD hw hz'
  have h0 : FiniteH0 (chart a) f g :=
    ⟨(hf.mono_measure Measure.restrict_le_self).ae_eq he,
      fun j => ((hg j).mono_measure Measure.restrict_le_self).ae_eq (he' j)⟩
  have hgz : ∀ j, ∀ᵐ x ∂volume.restrict (chart a), x ∉ C → g j x = 0 := by
    intro j
    filter_upwards [weakFirst_zero_off_compact hC hCD hw hz' j,
      ae_restrict_mem (scalarData a).open_chart.measurableSet] with x hx hxD hxC
    exact hx ⟨hxD,hxC⟩
  have ht := (compact_finiteH0_iff_weighted_covariant_memLp (chartOpens (scalarData a))
    C hC hCD (weight a) (scalarData a).smooth_weight (scalarData a).positive_weight
    (actualZeroConnection a) f g h0.1.aestronglyMeasurable
    (fun j => (h0.2 j).aestronglyMeasurable) hz hgz).mp h0
  intro j
  have hh := ht.2 j
  change MemLp (fun x => g j x + (0 : V 1 →L[ℂ] V 1) (f x)) 2 (measure a) at hh
  simpa only [zero_apply,add_zero] using hh

set_option maxHeartbeats 1600000 in
private theorem chart_weighted_derivative_cauchy_from_Hw
    (a : ActualChart (U:=U) (H:=H))
    (s : BorelL2Sections F ζ hζ U R P H) (r : SquareFiniteFamily (U:=U) (H:=H))
    (hw : WeakChartData s r.val)
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (N : TopologicalSpace.Opens (Space (3*d F))) (hLN : L ⊆ N)
    (hNc : IsCompact (closure (N : Set (Space (3*d F)))))
    (hND : closure (N : Set (Space (3*d F))) ⊆ chart a)
    (hz : ∀ᵐ x ∂volume.restrict (chart a), x ∉ L → scalarCoordinate s a x = 0)
    (τ : ℕ → localScalarTests a) (h : ℕ → Space (3*d F) → V 1)
    (hsm : ∀ n, ContDiff ℝ ∞ (h n)) (hcomp : ∀ n, HasCompactSupport (h n))
    (hsub : ∀ n, tsupport (h n) ⊆ N)
    (hext : ∀ n x, liftExtension a (τ n).val (baseReindex.symm x) = (h n x) 0)
    (herr : ∀ n, FiniteHw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
      (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)))
    (hsmall : Filter.Tendsto (fun n => Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
      (fun x => scalarReindex (scalarCoordinate s a x) - h n x)
      (fun j x => scalarReindex (covariantCoordinate r.val a x j) - fderiv ℝ (h n) x (coordinateDirection j)) (herr n))
      Filter.atTop (nhds 0)) :
    ∃ hdm : ∀ n j, MemLp (coordinatePartial j (fun x => liftExtension a (τ n).val (baseReindex.symm x))) 2 (measure a),
      ∀ j, CauchySeq (fun n => (hdm n j).toLp (coordinatePartial j (fun x => liftExtension a (τ n).val (baseReindex.symm x)))) := by
  let f := fun x => scalarReindex (scalarCoordinate s a x)
  let g := fun j x => scalarReindex (covariantCoordinate r.val a x j)
  let dh := fun n j x => fderiv ℝ (h n) x (coordinateDirection j)
  let C := closure (N : Set (Space (3*d F)))
  have hLD : L ⊆ chart a := hLN.trans (subset_closure.trans hND)
  have hw' : WeakFirst (chartOpens (scalarData a)) f g := weakChartData_weakFirst s r.val hw a
  have hfz : ∀ᵐ x ∂volume.restrict (chart a), x ∉ L → f x = 0 := by
    filter_upwards [hz] with x hx hxL
    simp only [f,hx hxL,map_zero]
  have gm := compact_actual_derivatives_memLp a L hL hLD f g hw' hfz
  have hm : ∀ n j, MemLp (dh n j) 2 (measure a) := by
    intro n
    apply compact_actual_derivatives_memLp a C hNc hND (h n) (dh n)
    · exact weakFirst_smooth_compactSupport (chartOpens (scalarData a)) (h n) (hsm n) (hcomp n)
        ((hsub n).trans (subset_closure.trans hND))
    · exact Filter.Eventually.of_forall (fun x hx => image_eq_zero_of_notMem_tsupport
        (fun ht => hx (subset_closure (hsub n ht))))
  have hgz := weakFirst_zero_off_compact hL hLD hw' (hfz.mono (fun x hx h => hx h.2))
  obtain ⟨cw,Cw,κ,Λ,M,hcw,hCw,hκ,hΛ,hM,hbounds⟩ :=
    exists_compact_metric_bounds (chartOpens (scalarData a)) C hNc hND (weight a)
      (scalarData a).smooth_weight (scalarData a).positive_weight (actualInverseMetric a) (actualZeroConnection a)
  have hb (n : ℕ) (j : Fin (3*d F)) :
      κ * ‖(gm j).toLp (g j) - (hm n j).toLp (dh n j)‖^2 ≤
      (Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
        (fun x => f x-h n x) (fun j x => g j x-dh n j x) (herr n))^2 := by
    have hi := ((gm j).sub (hm n j)).integrable_norm_pow (by norm_num)
    have he : (∫ x, ‖g j x-dh n j x‖^2 ∂measure a) = ‖(gm j).toLp (g j)-(hm n j).toLp (dh n j)‖^2 := by
      rw [← MemLp.toLp_sub, norm_toLp_l2_9669]
      exact (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))).symm
    have hwm : AEMeasurable (fun x => ENNReal.ofReal (weight a x)) (volume.restrict (chart a)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((scalarData a).smooth_weight.continuousOn.aemeasurable (scalarData a).open_chart.measurableSet)
    have he' : (∫ x, ‖g j x-dh n j x‖^2 ∂measure a) =
        ∫ x in chart a, weight a x * ‖g j x-dh n j x‖^2 := by
      rw [KPContActualSectorChartEquivariantInputs.measure, KPChartL2.weightedMeasure,
        integral_withDensity_eq_integral_toReal_smul₀ hwm (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (scalarData a).open_chart.measurableSet] with x hx
      rw [ENNReal.toReal_ofReal (show 0 ≤ weight a x from ((scalarData a).positive_weight x hx).le)]
      simp only [smul_eq_mul]
    have hi' : Integrable (fun x => weight a x * ‖g j x-dh n j x‖^2) (volume.restrict (chart a)) := by
      have hmweight : Measurable (fun x => ENNReal.ofReal (weight a x)) := by
        unfold weight KPArch.volumeDensity KPArch.height toActual labeledA
        fun_prop
      have hh := (integrable_withDensity_iff hmweight (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hi
      apply hh.congr
      filter_upwards [ae_restrict_mem (scalarData a).open_chart.measurableSet] with x hx
      rw [ENNReal.toReal_ofReal (show 0 ≤ weight a x from ((scalarData a).positive_weight x hx).le)]
      simp only [Pi.sub_apply]
      ring
    let E := ∫ x in chart a, weight a x * (actualInverseMetric a).quadratic x (fun j => g j x-dh n j x)
    have henergy : Integrable (fun x => weight a x * (actualInverseMetric a).quadratic x (fun j => g j x-dh n j x))
        (volume.restrict (chart a)) := by
      simpa only [covariantFirst,actualZeroConnection,zero_apply,add_zero] using (herr n).2
    have hle : κ * (∫ x, ‖g j x-dh n j x‖^2 ∂measure a) ≤ E := by
      rw [he', ← integral_const_mul]
      apply integral_mono_ae (hi'.const_mul κ) henergy
      filter_upwards [hgz j,ae_restrict_mem (scalarData a).open_chart.measurableSet] with x hx hxD
      have hwpos : 0 ≤ weight a x := ((scalarData a).positive_weight x hxD).le
      by_cases hxC : x ∈ C
      · have hsum : ‖g j x-dh n j x‖^2 ≤ ∑ k, ‖g k x-dh n k x‖^2 :=
          Finset.single_le_sum (f:=fun k => ‖g k x-dh n k x‖^2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
        have hh := (hbounds x hxC).2.1 (fun k => g k x-dh n k x)
        have hh' := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hsum hκ.le).trans hh.1) hwpos
        nlinarith
      · have hxL : x ∉ L := fun ht => hxC (subset_closure (hLN ht))
        have hzG := hx ⟨hxD,hxL⟩
        have hdh : dh n j x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro ht
          exact hxC (subset_closure (hsub n (tsupport_fderiv_apply_subset ℝ (coordinateDirection j) ht)))
        have hp := (actualInverseMetric a).positive_definite x hxD
        have hn := show 0 ≤ (actualInverseMetric a).quadratic x (fun k => g k x-dh n k x) from by
          rw [actualInverseMetric_quadratic]
          apply Finset.sum_nonneg
          intro k _
          apply mul_nonneg _ (sq_nonneg _)
          split_ifs <;> positivity
        simp only [hzG,hdh,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero]
        exact mul_nonneg hwpos hn
    have hEn : 0 ≤ E := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem (scalarData a).open_chart.measurableSet] with x hx
      exact mul_nonneg ((scalarData a).positive_weight x hx).le
        (by rw [actualInverseMetric_quadratic]; apply Finset.sum_nonneg; intro k _
            apply mul_nonneg _ (sq_nonneg _); split_ifs <;> positivity)
    have heHw : Hw (chart a) (weight a) (actualInverseMetric a) (actualZeroConnection a)
        (fun x => f x-h n x) (fun j x => g j x-dh n j x) (herr n) =
        l2Norm (measure a) (fun x => f x-h n x) (herr n).1 + Real.sqrt E := by
      simp only [Hw,covariantFirst,actualZeroConnection,zero_apply,add_zero,E]
    rw [he] at hle
    rw [heHw]
    nlinarith [Real.sqrt_nonneg E,Real.sq_sqrt hEn,
      show 0 ≤ l2Norm (measure a) (fun x => f x-h n x) (herr n).1 from Real.sqrt_nonneg _]
  have ht (j : Fin (3*d F)) : Filter.Tendsto (fun n => (hm n j).toLp (dh n j)) Filter.atTop
      (nhds ((gm j).toLp (g j))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht0 := (hsmall.pow 2).div_const κ
    simp only [zero_pow (by norm_num : 2 ≠ 0),zero_div] at ht0
    have hsq := squeeze_zero (fun n => sq_nonneg ‖(gm j).toLp (g j)-(hm n j).toLp (dh n j)‖)
      (fun n => (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hb n j)) ht0
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Real.sqrt_zero] at ht
    convert ht using 1
    funext n
    change ‖(hm n j).toLp (dh n j)-(gm j).toLp (g j)‖ =
      Real.sqrt (‖(gm j).toLp (g j)-(hm n j).toLp (dh n j)‖^2)
    exact (norm_sub_rev _ _).trans (Real.sqrt_sq (norm_nonneg _)).symm
  have hdEq (n : ℕ) (j : Fin (3*d F)) :
      coordinatePartial j (fun x => liftExtension a (τ n).val (baseReindex.symm x)) =
      fun x => scalarReindex.symm (dh n j x) := by
    have he : (fun x => liftExtension a (τ n).val (baseReindex.symm x)) =
        fun x => scalarReindex.symm (h n x) := funext (hext n)
    rw [he]
    funext x
    unfold coordinatePartial dh
    let T := scalarReindex.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
    exact congrArg (fun D : Space (3*d F) →L[ℝ] ℂ => D (coordinateDirection j))
      ((T.hasFDerivAt.comp x ((hsm n).differentiable (by simp) x).hasFDerivAt).fderiv)
  have hdm : ∀ n j, MemLp (coordinatePartial j (fun x => liftExtension a (τ n).val (baseReindex.symm x))) 2 (measure a) := by
    intro n j
    rw [hdEq]
    exact (hm n j).continuousLinearMap_comp scalarReindex.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨hdm,fun j => ?_⟩
  have hm' := (gm j).continuousLinearMap_comp scalarReindex.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let T := scalarReindex.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hlim := ((T.compLpL 2 (measure a)).continuous.tendsto _).comp (ht j)
  have he (n : ℕ) : (hdm n j).toLp _ =
      (T.compLpL 2 (measure a)) ((hm n j).toLp (dh n j)) := by
    apply Lp.ext
    filter_upwards [(hdm n j).coeFn_toLp, T.coeFn_compLpL ((hm n j).toLp (dh n j)), (hm n j).coeFn_toLp] with x hx hy hz
    rw [hx,hy,hz,hdEq]
    rfl
  have hc := hlim.cauchySeq
  have heq : (fun n => (hdm n j).toLp _) =
      (T.compLpL 2 (measure a)) ∘ (fun n => (hm n j).toLp (dh n j)) := funext he
  rw [heq]
  exact hc
end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree
open KPContActualSectorCompactWeakFormConverse

theorem kp_cont_actual_sector_compact_weak_form_converse
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorCompactWeakFormConverse.Properties F ζ hζ U R P H μG hμG hR realization := by
  have hc : ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)),
      IsCompact K → KPContActualSectorCompactWeakFormConverse.SupportedAE (H:=H) u K →
      KPContActualSectorFormWeakLocalization.ActualWeakH1Loc (H:=H) u →
      ∃ hu : u ∈ (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure.domain,
        KPContActualSectorFormWeakLocalization.IsActualWeakGradient (H:=H) u
          ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure ⟨u,hu⟩) ∧
        ∃ φ : ℕ → KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H,
          Filter.Tendsto (fun n => KPContActualSectorTestEmbeddings.iota (φ n)) Filter.atTop (nhds u) ∧
          Filter.Tendsto (fun n => KPContActualSectorTestEmbeddings.j
            (KPContActualSectorTestDifferentialDescent.D_U (φ n))) Filter.atTop
            (nhds ((KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure ⟨u,hu⟩)) := by
    intro u K hK hsupp hweak
    have hu := compact_form_mem_from_local_9669 μG hμG hR realization
      (fun a v s r hs hw hv L hL hLi N hLN hNc hND hNi hz => by
        obtain ⟨h, τ, herr, hsm, hcomp, hsub, hext, hsmall⟩ :=
          actual_chart_Hw_sequence_9669 a v s r hs hw L hL hLi N hLN hNc hND hNi hz
        apply chart_form_mem_from_Hw_sequence_9669 μG hμG hR realization
          a v s r hs hv τ h hext herr hsmall
        obtain ⟨hmem, hlim⟩ := scalar_limit_of_Hw_errors_9669 a s r τ h hext herr hsmall
        have hsm' : ∀ n, ContDiff ℝ ∞ (fun x =>
            KPContActualSectorTestDifferentialDescent.liftExtension a (τ n).val
              (KPContActualSectorChartEquivariantInputs.baseReindex.symm x)) := by
          intro n
          simp_rw [hext]
          exact (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).restrictScalars ℝ).contDiff).comp (hsm n)
        have hsub' : ∀ n, tsupport (fun x =>
            KPContActualSectorTestDifferentialDescent.liftExtension a (τ n).val
              (KPContActualSectorChartEquivariantInputs.baseReindex.symm x)) ⊆
              closure (N : Set (KPContLocalNorm.Space (3 * KPContCotangentActualOverlap.d F))) := by
          intro n
          simp_rw [hext]
          exact (tsupport_comp_subset (g := fun z : KPCompactInteriorH1.V 1 => z 0)
            (by simp) (h n)).trans ((hsub n).trans subset_closure)
        obtain ⟨hdm, hcd⟩ := chart_weighted_derivative_cauchy_from_Hw
          a s r hw L hL N hLN hNc hND hz τ h hsm hcomp hsub hext herr hsmall
        exact scalarZeroExtension_cauchy_of_chartH1 a τ
          (closure (N : Set (KPContLocalNorm.Space (3 * KPContCotangentActualOverlap.d F))))
          hNc hND hsm' hsub' hmem hdm hlim.cauchySeq hcd) u K hK hsupp hweak
    exact ⟨hu, actual_form_mem_outputs μG hμG hR realization u hu⟩
  refine ⟨hc, ?_, KPContActualSectorCompactWeakFormConverse.form_weak_local_of_formDomain
    F ζ hζ U R P H μG hμG hR realization⟩
  intro η u hweak
  exact KPContActualSectorCompactWeakFormConverse.compact_multiplier_of_converse
    μG hμG hR realization (fun v K hK hs hv => (hc v K hK hs hv).choose) η u hweak

end DedekindZetaZeroFree

end
end
end
