module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GradientForms.LocalCutoffCoefficient
public import DedekindZetaZeroFree.Analysis.Sobolev.Cubes.GraphRellichCompactness
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.CutoffGraphApproximation

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualFormLocalRestrictionCompact
attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU
open KPContActualFixedHaarCoreLocalizers KPContSectorLineL2Isometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
variable (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)

theorem actual_cutoff_value_bound (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count) (x : KPCoreChartLocalizers.E (A.chart i).n) :
    ‖A.cutoff i x‖ ≤ A.derivativeBound i 0 := by
  by_cases hx : x ∈ tsupport (A.cutoff i)
  · simpa only [norm_iteratedFDeriv_zero] using A.derivative_bounds i 0 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact A.nonnegative_derivativeBound i 0

theorem actual_cutoff_firstDerivative_bound (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count) (r : Fin (A.chart i).n)
    (x : KPCoreChartLocalizers.E (A.chart i).n) :
    ‖fderiv ℝ (A.cutoff i) x (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r)‖ ≤
      A.derivativeBound i 1 := by
  by_cases hx : x ∈ tsupport (A.cutoff i)
  · have hb : ‖fderiv ℝ (A.cutoff i) x‖ ≤ A.derivativeBound i 1 := by
      simpa only [norm_iteratedFDeriv_one] using A.derivative_bounds i 1 x hx
    calc
      _ ≤ ‖fderiv ℝ (A.cutoff i) x‖ *
          ‖EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (A.cutoff i) x‖ := by
        rw [(EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ).orthonormal.norm_eq_one r,
          mul_one]
      _ ≤ _ := hb
  · simp only [fderiv_of_notMem_tsupport ℝ hx, zero_apply, norm_zero]
    exact A.nonnegative_derivativeBound i 1

include μG hμG hR realization in

theorem actual_coefficient_coordinateDerivative (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (r : Fin (A.chart i).n) (x : KPCoreChartLocalizers.E (A.chart i).n) :
    KPCubeAverage.coordinateDerivative (A.chart i).n
      (actualLocalCoefficient F ζ hζ U R P H K hK A i f) r x =
      (A.cutoff i x : ℂ) * KPCubeAverage.coordinateDerivative (A.chart i).n
        (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y))
        r x + (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x) *
          (fderiv ℝ (A.cutoff i) x
            (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r) : ℂ) := by
  have hs := (kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization).scalar_smooth f
  have hc := (A.smooth_cutoff i).differentiable (by simp)
  have hcast : fderiv ℝ (fun y => (A.cutoff i y : ℂ)) x =
      Complex.ofRealCLM.comp (fderiv ℝ (A.cutoff i) x) := by
    simpa only [ContinuousLinearMap.fderiv, Function.comp_def, Complex.ofRealCLM_apply] using
      fderiv_comp x Complex.ofRealCLM.differentiableAt (hc x)
  by_cases hx : x ∈ tsupport (A.cutoff i)
  · have he : x ∈ (A.chart i).extendedDomain :=
      (A.chart i).closed_ball_in_extension (subset_closure (A.support_cutoff i hx))
    have hcoord := (A.chart i).smooth_coordinates.contDiffAt
      ((A.chart i).open_extendedDomain.mem_nhds he)
    have hs' := (hs (A.chart i).component).contDiffAt.comp x hcoord
    unfold KPCubeAverage.coordinateDerivative actualLocalCoefficient
    have hc' : DifferentiableAt ℝ (fun y => (A.cutoff i y : ℂ)) x := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        (Complex.ofRealCLM.differentiable.comp hc) x
    have hs'' : DifferentiableAt ℝ
        (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) x := by
      simpa only [Function.comp_def] using hs'.differentiableAt (by simp)
    have hfun : ((fun y => (A.cutoff i y : ℂ)) *
        (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y))) =
        (fun y => (A.cutoff i y : ℂ) * (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) := by
      funext y
      rfl
    have hp := congrArg (fun L => L (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r))
      (fderiv_mul hc' hs'')
    rw [hfun] at hp
    simpa only [Pi.mul_apply, hcast, add_apply,
      smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul] using hp
  · have hz : x ∉ tsupport (actualLocalCoefficient F ζ hζ U R P H K hK A i f) := by
      intro h
      apply hx
      have hsub : Function.support (actualLocalCoefficient F ζ hζ U R P H K hK A i f) ⊆
          Function.support (A.cutoff i) := by
        intro y hy
        contrapose! hy
        simp only [Function.mem_support, not_not] at hy ⊢
        simp [actualLocalCoefficient, hy]
      exact closure_mono hsub h
    simp only [KPCubeAverage.coordinateDerivative, fderiv_of_notMem_tsupport ℝ hz,
      zero_apply, image_eq_zero_of_notMem_tsupport hx,
      Complex.ofReal_zero, zero_mul, fderiv_of_notMem_tsupport ℝ hx, mul_zero, add_zero]

include μG hμG hR realization in

theorem actual_coefficient_coordinateDerivative_sq_le (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (r : Fin (A.chart i).n) (x : KPCoreChartLocalizers.E (A.chart i).n) :
    ‖KPCubeAverage.coordinateDerivative (A.chart i).n
      (actualLocalCoefficient F ζ hζ U R P H K hK A i f) r x‖ ^ 2 ≤
      2 * (A.derivativeBound i 0 ^ 2 *
        ‖KPCubeAverage.coordinateDerivative (A.chart i).n
          (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y))
          r x‖ ^ 2 + A.derivativeBound i 1 ^ 2 *
        ‖(KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x)‖ ^ 2) := by
  rw [actual_coefficient_coordinateDerivative F ζ hζ U R P H μG hμG hR realization K hK A i f r x]
  have hvalue := actual_cutoff_value_bound F ζ hζ U R P H K hK A i x
  have hderiv := actual_cutoff_firstDerivative_bound F ζ hζ U R P H K hK A i r x
  have hvalue2 := pow_le_pow_left₀ (norm_nonneg _) hvalue 2
  have hderiv2 := pow_le_pow_left₀ (norm_nonneg _) hderiv 2
  have ha := norm_add_le
    ((A.cutoff i x : ℂ) * KPCubeAverage.coordinateDerivative (A.chart i).n
      (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) r x)
    ((KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x) *
      (fderiv ℝ (A.cutoff i) x (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r) : ℂ))
  calc
    _ ≤ (‖(A.cutoff i x : ℂ) * KPCubeAverage.coordinateDerivative (A.chart i).n
          (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) r x‖ +
        ‖(KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x) *
          (fderiv ℝ (A.cutoff i) x (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r) : ℂ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ha 2
    _ ≤ 2 * (‖(A.cutoff i x : ℂ) * KPCubeAverage.coordinateDerivative (A.chart i).n
          (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) r x‖ ^ 2 +
        ‖(KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x) *
          (fderiv ℝ (A.cutoff i) x (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r) : ℂ)‖ ^ 2) :=
      add_sq_le
    _ ≤ _ := by
      simp only [norm_mul, Complex.norm_real, mul_pow]
      have hb0 := mul_le_mul_of_nonneg_right hvalue2
        (sq_nonneg (‖KPCubeAverage.coordinateDerivative (A.chart i).n
          (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) r x‖))
      have hb1 := mul_le_mul_of_nonneg_left hderiv2
        (sq_nonneg (‖(KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x)‖))
      nlinarith

include μG hμG hR realization in

theorem actual_coefficient_energy_bound (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (x : KPCoreChartLocalizers.E (A.chart i).n) :
    ‖actualLocalCoefficient F ζ hζ U R P H K hK A i f x‖ ^ 2 +
      ∑ r : Fin (A.chart i).n, ‖KPCubeAverage.coordinateDerivative (A.chart i).n
        (actualLocalCoefficient F ζ hζ U R P H K hK A i f) r x‖ ^ 2 ≤
      (A.derivativeBound i 0 ^ 2 + 2 * (A.chart i).n * A.derivativeBound i 1 ^ 2) *
        ‖(KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x)‖ ^ 2 +
      2 * A.derivativeBound i 0 ^ 2 *
        ∑ r : Fin (A.chart i).n, ‖KPCubeAverage.coordinateDerivative (A.chart i).n
          (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y))
          r x‖ ^ 2 := by
  have hv : ‖actualLocalCoefficient F ζ hζ U R P H K hK A i f x‖ ^ 2 ≤
      A.derivativeBound i 0 ^ 2 *
        ‖(KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates x)‖ ^ 2 := by
    simp only [actualLocalCoefficient, norm_mul, Complex.norm_real, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (actual_cutoff_value_bound F ζ hζ U R P H K hK A i x) 2)
      (sq_nonneg _)
  have hg := Finset.sum_le_sum (s := Finset.univ)
    (fun r _ => actual_coefficient_coordinateDerivative_sq_le F ζ hζ U R P H μG hμG hR realization K hK A i f r x)
  have ht := add_le_add hv hg
  calc
    _ ≤ _ := ht
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem actual_chart_complex_ellipticity (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (x : KPCoreChartLocalizers.E (A.chart i).n)
    (hx : x ∈ tsupport (A.cutoff i))
    (η : Fin (A.chart i).n → ℂ) :
    A.ellipticity i * (∑ j, ‖η j‖ ^ 2) ≤
      ∑ j, ∑ k, (A.chart i).energyMatrix F ζ hζ H.totallyComplex U x j k *
        ((η j).re * (η k).re + (η j).im * (η k).im) := by
  have hr := (A.metric_bounds i x hx (WithLp.toLp 2 (fun j => (η j).re))).1
  have hi := (A.metric_bounds i x hx (WithLp.toLp 2 (fun j => (η j).im))).1
  rw [EuclideanSpace.real_norm_sq_eq] at hr hi
  simp only [WithLp.ofLp_toLp] at hr hi
  calc
    _ = A.ellipticity i * (∑ j, (η j).re ^ 2) +
        A.ellipticity i * (∑ j, (η j).im ^ 2) := by
      simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        ← sq, Finset.sum_add_distrib, mul_add]
    _ ≤ _ := add_le_add hr hi
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_assoc]
include μG hμG hR realization in
theorem actual_chart_coordinateDerivative_chain_rule (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (r : Fin (A.chart i).n) (x : KPCoreChartLocalizers.E (A.chart i).n)
    (hx : x ∈ (A.chart i).extendedDomain) :
    KPCubeAverage.coordinateDerivative (A.chart i).n
      (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) r x =
      fderiv ℝ (fun z => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val z)
        ((A.chart i).coordinates x)
        (fderiv ℝ (A.chart i).coordinates x
          (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r)) := by
  have hs := (kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization).scalar_smooth f
  have hcoord := ((A.chart i).smooth_coordinates.contDiffAt
    ((A.chart i).open_extendedDomain.mem_nhds hx)).differentiableAt (by simp)
  exact congrArg (fun L : KPCoreChartLocalizers.E (A.chart i).n →L[ℝ] ℂ =>
    L (EuclideanSpace.basisFun (Fin (A.chart i).n) ℝ r))
    (fderiv_comp x ((hs (A.chart i).component).differentiable (by simp) _)
      hcoord)

theorem actual_chart_coordinate_derivative_injective (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
    (x : KPCoreChartLocalizers.E (A.chart i).n)
    (hx : x ∈ (A.chart i).extendedDomain) :
    Function.Injective (fderiv ℝ (A.chart i).coordinates x) := by
  obtain ⟨inv, hinv, hleft⟩ := (A.chart i).smooth_inverse
  have hcoord := ((A.chart i).smooth_coordinates.contDiffAt
    ((A.chart i).open_extendedDomain.mem_nhds hx)).differentiableAt (by simp)
  have hinvd := (hinv.contDiffAt ((A.chart i).coordinates_open.mem_nhds
    ⟨x, hx, rfl⟩)).differentiableAt (by simp)
  have heq : (inv ∘ (A.chart i).coordinates) =ᶠ[nhds x] id := by
    filter_upwards [(A.chart i).open_extendedDomain.mem_nhds hx] with y hy
    exact hleft y hy
  have hd : (fderiv ℝ inv ((A.chart i).coordinates x)).comp
      (fderiv ℝ (A.chart i).coordinates x) = ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp x hinvd hcoord, heq.fderiv_eq, fderiv_id]
  intro a b hab
  have hh := congrArg (fderiv ℝ inv ((A.chart i).coordinates x)) hab
  have ha := congrArg (fun L : KPCoreChartLocalizers.E (A.chart i).n →L[ℝ]
    KPCoreChartLocalizers.E (A.chart i).n => L a) hd
  have hb := congrArg (fun L : KPCoreChartLocalizers.E (A.chart i).n →L[ℝ]
    KPCoreChartLocalizers.E (A.chart i).n => L b) hd
  exact ha.symm.trans (hh.trans hb)

namespace ActualChartEnergyGeometry
open HyperbolicChart Matrix
open scoped Matrix
 def arch (d : ℕ) (p : Space d) : KPArch.Space d :=
  fun i => (⟨p (i,0), p (i,1)⟩, p (i,2))
 def real (d : ℕ) (p : KPArch.Space d) : Space d :=
  WithLp.toLp 2 (fun ik => ![(p ik.1).1.re, (p ik.1).1.im, (p ik.1).2] ik.2)
 def archL (d : ℕ) : Space d →L[ℝ] KPArch.Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := arch d
    map_add' := by intro x y; ext i <;> simp [arch, Complex.add_re, Complex.add_im]; rfl
    map_smul' := by intro a x; ext i : 1; apply Prod.ext <;> simp [arch, Complex.real_smul]; apply Complex.ext <;> simp }
 def realL (d : ℕ) : KPArch.Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := real d
    map_add' := by
      intro x y; ext ⟨i,k⟩; fin_cases k <;> simp [real]
    map_smul' := by
      intro a x; ext ⟨i,k⟩; fin_cases k <;> simp [real, Complex.real_smul] }

private lemma arch_real' (d : ℕ) (x : KPArch.Space d) : arch d (real d x) = x := by
  ext i <;> simp [real, arch]
 def scaleL (d : ℕ) (w : Fin d × Fin 3 → ℝ) : Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun j => w j * x j)
    map_add' := by intro x y; ext j; simp [mul_add]
    map_smul' := by intro a x; ext j; simp; ring }
private lemma scaleL_apply (d : ℕ) (w : Fin d × Fin 3 → ℝ) (z : Space d) (j) :
    scaleL d w z j = w j * z j := rfl
 def frame (d : ℕ) (x : Space d) : Space d →L[ℝ] Space d :=
  scaleL d (fun j => if j.2 = 2 then 1 else Real.exp (x (j.1, 2)))
 def unframe (d : ℕ) (x : Space d) : Space d →L[ℝ] Space d :=
  scaleL d (fun j => if j.2 = 2 then 1 else (Real.exp (x (j.1, 2)))⁻¹)
private lemma frame_unframe (d : ℕ) (x z : Space d) : frame d x (unframe d x z) = z := by
  ext j
  simp only [frame, unframe, scaleL_apply]
  split_ifs <;> simp [Real.exp_ne_zero, ← mul_assoc]
private lemma metric_frame (d : ℕ) (x z : Space d) :
    KPArch.metric d (arch d x) (arch d (frame d x z)) = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp only [KPArch.metric, KPArch.height, arch, frame, scaleL_apply,
    Fin.sum_univ_three, Fin.reduceEq, ite_true, ite_false, one_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  field_simp
private lemma metric_unframe (d : ℕ) (x z : Space d) :
    ‖unframe d x z‖ ^ 2 = KPArch.metric d (arch d x) (arch d z) := by
  rw [← metric_frame d x (unframe d x z), frame_unframe]
private lemma frame_basis (d : ℕ) (x : Space d) (i : Fin d) (k : Fin 3) :
    frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ (i,k)) =
      (if k = 2 then 1 else Real.exp (x (i,2))) • coordinateVector d i k := by
  ext j
  simp only [frame, scaleL_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply, coordinateVector, PiLp.smul_apply,
    WithLp.ofLp_toLp, smul_eq_mul]
  by_cases h : j = (i,k)
  · subst j; simp
  · simp [h, Ne.symm h]
private theorem differential_sum (d : ℕ) (g : Space d → ℂ) (x : Space d) :
    (∑ i, ∑ k, ‖differential d g x i k‖ ^ 2) =
      ∑ j, ‖fderiv ℝ g x (frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.sum_univ_three, differential, frame_basis, Fin.reduceEq,
    ite_true, ite_false, one_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, coordinateDerivative, map_smul,
    Complex.real_smul, Complex.ofReal_one, one_mul]
  simp
  ring

private theorem pullback_metric (d n : ℕ) (y : Space d)
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] KPArch.Space d) :
    let T := (unframe d y).comp ((realL d).comp J)
    let B : Matrix (Fin d × Fin 3) (Fin n) ℝ :=
      fun k r => T (EuclideanSpace.basisFun (Fin n) ℝ r) k
    (fun j k => (KPArch.metric d (arch d y) (J (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)) -
      KPArch.metric d (arch d y) (J (EuclideanSpace.single j 1)) -
      KPArch.metric d (arch d y) (J (EuclideanSpace.single k 1))) / 2) = B.transpose * B := by
  dsimp
  ext j k
  have hm (z : KPArch.Space d) : KPArch.metric d (arch d y) z =
      ‖unframe d y (real d z)‖ ^ 2 := by
    rw [metric_unframe, arch_real']
  simp only [hm]
  change (‖(unframe d y) ((realL d) (J (_ + _)))‖ ^ 2 -
    ‖(unframe d y) ((realL d) (J _))‖ ^ 2 -
    ‖(unframe d y) ((realL d) (J _))‖ ^ 2) / 2 = _
  simp only [map_add]
  rw [norm_add_sq_real]
  simp only [mul_apply, transpose_apply, ContinuousLinearMap.comp_apply,
    EuclideanSpace.basisFun_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  change (_ + 2 * (∑ z : Fin d × Fin 3,
    ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z) + _ - _ - _) / 2 =
    ∑ z : Fin d × Fin 3,
    ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z
  rw [show (∑ z, ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z) =
    ∑ z, ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z by
      apply Finset.sum_congr rfl; intro z hz; ring]
  ring

private theorem unframe_injective (d : ℕ) (y : Space d) : Function.Injective (unframe d y) := by
  intro a b hab
  have hh := congrArg (frame d y) hab
  simpa only [frame_unframe] using hh
private theorem realL_injective (d : ℕ) : Function.Injective (realL d) := by
  intro a b hab
  change real d a = real d b at hab
  have hh := congrArg (arch d) hab
  simpa only [arch_real'] using hh

set_option maxHeartbeats 1600000 in
 include μG hμG hR realization in
set_option maxHeartbeats 1600000 in
theorem actual_chart_derivative_pointwise_bound (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count)
      (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
      (x : KPCoreChartLocalizers.E (A.chart i).n)
      (hx : x ∈ tsupport (A.cutoff i)) :
    A.ellipticity i * (∑ r : Fin (A.chart i).n,
        ‖KPCubeAverage.coordinateDerivative (A.chart i).n
          (fun y => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val ((A.chart i).coordinates y)) r x‖ ^ 2) ≤
        ∑ ik : Fin (KPCuspLogShape.dimension F) × Fin 3,
          ‖differential (KPCuspLogShape.dimension F)
            (fun p => (KPContActualSectorSmoothTestModules.scalarSections f (A.chart i).component).val (KPCuspCutoffGraph.toArch F p))
            (KPCuspCutoffGraph.fromArch F ((A.chart i).coordinates x)) ik.1 ik.2‖ ^ 2 := by
  have hs := (kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization).scalar_smooth f
  let C := A.chart i
  let d := KPCuspLogShape.dimension F
  let z := C.coordinates x
  let y := real d z
  let J := fderiv ℝ C.coordinates x
  let T := (unframe d y).comp ((realL d).comp J)
  let L := (fderiv ℝ (fun z => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val z) z).comp
    ((archL d).comp (frame d y))
  let B : Matrix (Fin d × Fin 3) (Fin C.n) ℝ := fun k r => T (EuclideanSpace.basisFun (Fin C.n) ℝ r) k
  have hT : Function.Injective T :=
    (unframe_injective d y).comp ((realL_injective d).comp
      (actual_chart_coordinate_derivative_injective F ζ hζ U R P H K hK A i x (C.closed_ball_in_extension (subset_closure (A.support_cutoff i hx)))))
  have hM : C.metricMatrix F ζ hζ H.totallyComplex U x = B.transpose * B := by
    have hh := pullback_metric d C.n y J
    dsimp only at hh
    rw [arch_real'] at hh
    exact hh
  have hchain (r : Fin C.n) :
      KPCubeAverage.coordinateDerivative C.n
        (fun y => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val (C.coordinates y)) r x =
        L (T (EuclideanSpace.basisFun (Fin C.n) ℝ r)) := by
    rw [actual_chart_coordinateDerivative_chain_rule F ζ hζ U R P H μG hμG hR realization K hK A i f r x (C.closed_ball_in_extension (subset_closure (A.support_cutoff i hx)))]
    change _ = fderiv ℝ _ z (arch d (frame d y (unframe d y (real d (J _)))))
    rw [frame_unframe, arch_real']
  have he := actual_chart_complex_ellipticity F ζ hζ U R P H K hK A i x hx
    (fun r => L (T (EuclideanSpace.basisFun (Fin C.n) ℝ r)))
  simp_rw [← hchain] at he
  refine he.trans ?_
  simp_rw [hchain, ← Complex.reCLM_apply, ← Complex.imCLM_apply, ← ContinuousLinearMap.comp_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  have hb1 := KPLocalizedFormGraph.ChartEnergyGeometry.jacobian_bound T hT (Complex.reCLM.comp L)
  have hb2 := KPLocalizedFormGraph.ChartEnergyGeometry.jacobian_bound T hT (Complex.imCLM.comp L)
  have hb := add_le_add hb1 hb2
  have hsum : (∑ r, ((Complex.reCLM.comp L) (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ r)) ^ 2) +
      (∑ r, ((Complex.imCLM.comp L) (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ r)) ^ 2) =
      ∑ r, ‖L (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ r)‖ ^ 2 := by
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, Finset.sum_add_distrib]
  rw [hsum] at hb
  have hdf : fderiv ℝ (fun p : Space d => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val (arch d p)) y =
      (fderiv ℝ (fun z => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val z) z).comp (archL d) := by
    have hh := ((hs C.component).differentiable (by simp) z).hasFDerivAt.comp y (archL d).hasFDerivAt
    change HasFDerivAt (fun p : Space d => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val (arch d p))
      ((fderiv ℝ (fun z => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val z) (arch d y)).comp (archL d)) y at hh
    simpa only [arch_real', y, z] using hh.fderiv
  rw [show (∑ ik : Fin d × Fin 3,
      ‖differential d (fun p => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val (KPCuspCutoffGraph.toArch F p))
        (KPCuspCutoffGraph.fromArch F z) ik.1 ik.2‖ ^ 2) =
      ∑ r, ‖L (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ r)‖ ^ 2 by
    rw [Fintype.sum_prod_type]
    change (∑ i, ∑ k, ‖differential d (fun p => (KPContActualSectorSmoothTestModules.scalarSections f C.component).val (arch d p)) y i k‖ ^ 2) = _
    rw [differential_sum, hdf]
    rfl]
  dsimp only at hb
  have hM' : (A.chart i).metricMatrix F ζ hζ H.totallyComplex U x = B.transpose * B := hM
  simp only [KPCoreChartLocalizers.Chart.energyMatrix, hM', ContinuousLinearMap.comp_apply]
  simp only [dotProduct, mulVec, Finset.mul_sum] at hb
  convert hb using 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
    apply Finset.sum_congr rfl <;> intro k hk <;>
    simp only [ContinuousLinearMap.comp_apply, B] <;> ring

end ActualChartEnergyGeometry

namespace ActualChartCotangentBinding
open KPContActualCotangentCountableShrinking KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches KPContCotangentActualGenuineTwistIsotropy
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem bounds_shrink_at (i : Fin (H.atlas U).componentCount) (p : KPCuspGenuineMonodromy.SymmetricSpace F) :
    ∃ C : ShrunkChart F ζ hζ U R P H, C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (orbifoldChart_exists F ζ hζ U R P H i p)
  let : Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) p) :=
    chart_stabilizer_finite F ζ hζ U R P H i p O
  let := Fintype.ofFinite (MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  obtain ⟨W,hWo,hpW,hWsub,hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer (Component F ζ hζ U R P H i) p,
    (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i,p,O,V,hopen,hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub,?_⟩,rfl,rfl,hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h*g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x,?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h*g⁻¹)

theorem actual_pairing_at_arch (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    (∑ j : Fin (d F), ∑ k : Fin 3,
      ‖HyperbolicChart.differential (d F)
        (fun x => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) x))
        (labeledAInv (placeEquiv F ζ hζ) y) j k‖ ^ 2) =
    (∑ j : Fin (d F), KPContActualSectorFriedrichsSynthesis.placePair (D_U f) (D_U f) j
      ((H.atlas U).components ⟨i, Quotient.mk _ y⟩)).re := by
  obtain ⟨a, hi, hcenter, hy⟩ := bounds_shrink_at (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i y
  let x := labeledAInv (placeEquiv F ζ hζ) y
  have hA : labeledA (placeEquiv F ζ hζ) x = y := by
    funext k
    simp [x, labeledA, labeledAInv]
  have hx : x ∈ omega a := by
    change labeledA (placeEquiv F ζ hζ) x ∈ a.domain
    rw [hA]; exact hy
  have hq : q a x = (H.atlas U).components ⟨i, Quotient.mk _ y⟩ := by
    rw [(H.atlas U).components_formula]
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x)) = _
    rw [hA, hi]
  have hopen : IsOpen (omega a) := by
    apply a.domain_open.preimage
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  have hsec : sectionFields (scalarSections f) = f.val :=
    (Classical.choose_spec (scalar_gluing f)).1.2.2
  have hgerm : liftExtension a (f.val a) =ᶠ[𝓝 x]
      (fun z => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) z)) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [liftExtension, dite_eq_left hz, ← hsec]
    simp only [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative,
      map_one, Units.val_one, one_mul, one_smul]
    rw [hi]
  have hcoeff : ∀ j k, coefficient (D_U f).val a ⟨x, hx⟩ (j,k) =
      HyperbolicChart.differential (d F)
        (fun z => (scalarSections f i).val (labeledA (placeEquiv F ζ hζ) z)) x j k := by
    intro j k
    change (CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a (f.val a)) x)) (j,k) = _
    rw [CotangentLogCoframe.j_apply]
    fin_cases k <;> simp only [HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, hgerm.fderiv_eq]
  rw [← hq]
  simp only [KPContActualSectorFriedrichsSynthesis.placePair_chart F ζ hζ U R P H
    (D_U f) (D_U f) _ a ⟨x,hx⟩, hcoeff, inner_self_eq_norm_sq_to_K]
  simp [x, ← Complex.ofReal_pow]

end ActualChartCotangentBinding

private theorem actual_chart_base_measurable (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count) : AEMeasurable ((A.chart i).toBase F ζ hζ H.totallyComplex U)
    (volume.restrict (Metric.ball 0 (A.chart i).radius)) := by
  letI : BorelSpace (KPCoreChartLocalizers.X F ζ hζ U) := ⟨rfl⟩
  apply aemeasurable_restrict_of_measurable_subtype measurableSet_ball
  apply Continuous.measurable
  have hc := (A.chart i).smooth_coordinates.continuousOn.mono
    (Set.Subset.trans subset_closure (A.chart i).closed_ball_in_extension)
  have hcc := continuousOn_iff_continuous_restrict.mp hc
  have hq : Continuous (fun z : KPFiniteCuspAtlas.SymmetricSpace F =>
      (Quotient.mk _ (z, (H.atlas U).representative (A.chart i).component) : KPCoreChartLocalizers.X F ζ hζ U)) :=
    continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)
  convert hq.comp hcc using 1
  rfl
private theorem actual_chart_weight_measurable (A : Localizers F ζ hζ U R P H K hK) (i : Fin A.count) : AEMeasurable (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H (A.chart i) x))
    (volume.restrict (Metric.ball 0 (A.chart i).radius)) := by
  apply aemeasurable_restrict_of_measurable_subtype measurableSet_ball
  exact (ENNReal.continuous_ofReal.comp
    (continuousOn_iff_continuous_restrict.mp (continuousOn_const.mul ((A.chart i).smooth_weight.continuousOn.mono
      (Set.Subset.trans subset_closure (A.chart i).closed_ball_in_extension))))).measurable

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem actual_chart_energy_transport (A : Localizers F ζ hζ U R P H K hK)
    (i : Fin A.count) (e : X_U F ζ hζ U → ℝ≥0∞)
    (he : AEMeasurable e (muU F ζ hζ U R P)) :
    (∫⁻ x, e ((A.chart i).toBase F ζ hζ H.totallyComplex U x)
      ∂volume.restrict (Metric.ball 0 (A.chart i).radius)) ≤
      ENNReal.ofReal ((Fintype.card ((A.chart i).G F ζ hζ H.totallyComplex U) : ℝ) / A.lower i) *
        ∫⁻ x, e x ∂muU F ζ hζ U R P := by
  let C := A.chart i
  let ν := volume.restrict (Metric.ball (0 : KPCoreChartLocalizers.E C.n) C.radius)
  let w := fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x)
  let b := C.toBase F ζ hζ H.totallyComplex U
  let N : ℝ≥0∞ := Fintype.card (C.G F ζ hζ H.totallyComplex U)
  have hN : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
  have hNt : N ≠ ∞ := by simp [N]
  have hw : AEMeasurable w ν := actual_chart_weight_measurable F ζ hζ U R P H K hK A i
  have hb : AEMeasurable b ν := actual_chart_base_measurable F ζ hζ U R P H K hK A i
  have hb' := hb.mono_ac (withDensity_absolutelyContinuous ν w)
  have hpos : ∀ᵐ x ∂ν, w x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (ENNReal.ofReal_pos.mpr ((A.positive_lower i).trans_le
      (A.density_bounds i x (subset_closure hx)).1)).ne'
  have hac : ν ≪ ν.withDensity w := withDensity_absolutelyContinuous' hw hpos
  have hm : Measure.map b (ν.withDensity w) = N • (muU F ζ hζ U R P).restrict
      (C.O F ζ hζ H.totallyComplex U) := by
    rw [← A.chart_measure i, Measure.map_smul _ hb', smul_smul,
      ENNReal.mul_inv_cancel hN hNt, one_smul]
  have hem : AEMeasurable e (Measure.map b (ν.withDensity w)) := by
    rw [hm]
    exact he.restrict.mono_ac Measure.smul_absolutelyContinuous
  have heb' : AEMeasurable (fun x => e (b x)) (ν.withDensity w) :=
    hem.comp_aemeasurable hb'
  have heb : AEMeasurable (fun x => e (b x)) ν := heb'.mono_ac hac
  have hweighted : (∫⁻ x, w x * e (b x) ∂ν) ≤ N * ∫⁻ x, e x ∂muU F ζ hζ U R P := by
    change (∫⁻ x, (w * (fun x => e (b x))) x ∂ν) ≤ _
    rw [← lintegral_withDensity_eq_lintegral_mul₀' hw heb', ← lintegral_map' hem hb',
      hm, lintegral_smul_measure]
    exact mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) N
  have hl : ENNReal.ofReal (A.lower i) ≠ 0 := (ENNReal.ofReal_pos.mpr (A.positive_lower i)).ne'
  have hbound : (∫⁻ x, e (b x) ∂ν) ≤ (ENNReal.ofReal (A.lower i))⁻¹ *
      (N * ∫⁻ x, e x ∂muU F ζ hζ U R P) := by
    calc
      _ ≤ ∫⁻ x, (ENNReal.ofReal (A.lower i))⁻¹ * (w x * e (b x)) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        have hlow : ENNReal.ofReal (A.lower i) ≤ w x := ENNReal.ofReal_le_ofReal
          (A.density_bounds i x (subset_closure hx)).1
        calc
          _ = ((ENNReal.ofReal (A.lower i))⁻¹ * ENNReal.ofReal (A.lower i)) * e (b x) := by
            rw [ENNReal.inv_mul_cancel hl ENNReal.ofReal_ne_top, one_mul]
          _ ≤ _ := by simpa only [mul_assoc] using
            mul_le_mul_left (mul_le_mul_right hlow (ENNReal.ofReal (A.lower i))⁻¹) (e (b x))
      _ = (ENNReal.ofReal (A.lower i))⁻¹ * ∫⁻ x, w x * e (b x) ∂ν :=
        lintegral_const_mul'' _ (hw.mul heb)
      _ ≤ _ := mul_le_mul_right hweighted _
  have hconstant : (ENNReal.ofReal (A.lower i))⁻¹ * N =
      ENNReal.ofReal ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ) / A.lower i) := by
    rw [ENNReal.ofReal_div_of_pos (A.positive_lower i), ENNReal.ofReal_natCast, div_eq_mul_inv]
    exact mul_comm _ _
  rw [← mul_assoc, hconstant] at hbound
  exact hbound

namespace ActualChartCotangentBinding
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap KPContActualCotangentMeasurableFamilies
open KPContActualSectorTestEmbeddings KPContActualSectorSmoothTestModules
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches

private theorem exists_actual_lift (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  let C := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hB := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H C
  have hx : x ∈ ⋃ n, KPContActualCotangentBorelRefinement.basePiece C n := by
    rw [hB.covers]
    exact Set.mem_univ x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := Set.mem_range.mp (hB.base_subset n hn)
  refine ⟨C.chart n, KPContActualCotangentPieceHilbertSum.coordinates (C.chart n) y, ?_⟩
  have hi : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y.val) = y.val := by
    funext k
    simp [labeledA, labeledAInv]
  simpa only [q, KPContActualCotangentCountableShrinking.ShrunkChart.toBase,
    KPContActualCotangentPieceHilbertSum.coordinates, Subtype.coe_mk, hi] using hy

theorem actual_place_sum_normSquare (W : T_U F ζ hζ U R P H) (x : X_U F ζ hζ U) :
    (∑ i : Fin (d F), KPContActualSectorFriedrichsSynthesis.placePair W W i x).re =
      (normSquare W.val x : ℝ) := by
  obtain ⟨a, y, rfl⟩ := exists_actual_lift F ζ hζ U R P H x
  simp only [KPContActualSectorFriedrichsSynthesis.placePair_chart F ζ hζ U R P H,
    normSquare_chart, inner_self_eq_norm_sq_to_K, PiLp.norm_sq_eq_of_L2]
  simp only [map_sum, Complex.ofReal_pow, Complex.ofReal_re, NNReal.coe_pow, coe_nnnorm]
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp [← Complex.ofReal_pow]

private theorem coframe_reindex (m n : ℕ) (h : m = n) (g : KPArch.Space n → ℂ)
    (y : KPArch.Space n) :
    (∑ j : Fin m, ∑ k : Fin 3, ‖HyperbolicChart.differential m
      (fun x => g (fun r => CotangentLogCoframe.A m x ((finCongr h).symm r)))
      ((CotangentLogCoframe.A m).symm (fun r => y (finCongr h r))) j k‖ ^ 2) =
    ∑ j : Fin n, ∑ k : Fin 3, ‖HyperbolicChart.differential n
      (fun x => g (fun r => (⟨x (r,0), x (r,1)⟩, x (r,2))))
      (WithLp.toLp 2 (fun r => ![(y r.1).1.re, (y r.1).1.im, (y r.1).2] r.2)) j k‖ ^ 2 := by
  subst n
  have hA : (fun x : HyperbolicChart.Space m => fun r => CotangentLogCoframe.A m x r) =
      (fun x => fun r => (⟨x (r,0), x (r,1)⟩, x (r,2))) := by
    funext x r
    simp [CotangentLogCoframe.A_apply, Complex.mk_eq_add_mul_I, mul_comm]
  simp only [finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  have hAg : (fun x : HyperbolicChart.Space m => g (fun r => CotangentLogCoframe.A m x r)) =
      (fun x => g (fun r => (⟨x (r,0), x (r,1)⟩, x (r,2)))) := by
    funext x
    exact congrArg g (congrFun hA x)
  rw [hAg]
  rfl

theorem actual_normal_coframe_normSquare (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    (∑ j : Fin (KPCuspLogShape.dimension F), ∑ k : Fin 3,
      ‖HyperbolicChart.differential (KPCuspLogShape.dimension F)
        (fun x => (scalarSections f i).val (KPCuspCutoffGraph.toArch F x))
        (KPCuspCutoffGraph.fromArch F y) j k‖ ^ 2) =
      (normSquare (D_U f).val ((H.atlas U).components ⟨i, Quotient.mk _ y⟩) : ℝ) := by
  rw [← actual_place_sum_normSquare]
  have hp := actual_pairing_at_arch f i y
  have hr := coframe_reindex (d F) (KPCuspLogShape.dimension F)
    (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm
    (scalarSections f i).val y
  exact hr.symm.trans hp

include μG hμG hR realization in

theorem actual_test_gradient_norm_sq (f : S_U F ζ hζ U R P H) :
    ‖j (D_U f)‖ ^ 2 = ∫ x, (normSquare (D_U f).val x : ℝ) ∂muU F ζ hζ U R P := by
  have hV := kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization
  have h := hV.norm_integral (j (D_U f)) (cotangentSquareFamily (D_U f)) rfl
  simpa [cotangentSquareFamily] using h

end ActualChartCotangentBinding

namespace ActualChartCotangentBinding
open KPContCotangentActualOverlap KPContActualSectorSmoothTestModules
open KPContActualSectorTestEmbeddings KPContActualSectorTestDifferentialDescent
open KPContSectorSmoothFramesSupport KPContCotangentOverlapRationalBranches
open KPContActualCotangentMeasurableFamilies KPContActualCotangentCountableShrinking

theorem actual_scalar_pair_at_arch (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    (scalarPair f f ((H.atlas U).components ⟨i, Quotient.mk _ y⟩)).re =
      ‖(scalarSections f i).val y‖ ^ 2 := by
  obtain ⟨a, hi, hcenter, hy⟩ := bounds_shrink_at (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i y
  let x := labeledAInv (placeEquiv F ζ hζ) y
  have hA : labeledA (placeEquiv F ζ hζ) x = y := by
    funext k
    simp [x, labeledA, labeledAInv]
  have hx : x ∈ omega a := by
    change labeledA (placeEquiv F ζ hζ) x ∈ a.domain
    rw [hA]; exact hy
  have hq : q a x = (H.atlas U).components ⟨i, Quotient.mk _ y⟩ := by
    rw [(H.atlas U).components_formula]
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x)) = _
    rw [hA, hi]
  have hsec : sectionFields (scalarSections f) = f.val :=
    (Classical.choose_spec (scalar_gluing f)).1.2.2
  rw [← hq, scalar_pair_chart f f a ⟨x,hx⟩]
  have hf : f.val a ⟨x,hx⟩ = (scalarSections f i).val y := by
    rw [← hsec]
    simp only [sectionFields, LiftedChart.coefficient, KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative, map_one, Units.val_one, one_mul, one_smul]
    change (scalarSections f a.component).val (labeledA (placeEquiv F ζ hζ) x) = _
    rw [hA, hi]
  rw [hf]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

include μG hμG hR realization in

theorem actual_test_scalar_norm_sq (f : S_U F ζ hζ U R P H) :
    ‖iota f‖ ^ 2 = ∫ x, (scalarPair f f x).re ∂muU F ζ hζ U R P := by
  have hE := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have hint := hE.scalar_pair_integrable f f
  have hstep : (∫ x, (scalarPair f f x).re ∂muU F ζ hζ U R P) =
      ∫ x, Complex.reCLM (scalarPair f f x) ∂muU F ζ hζ U R P := by
    simp [Complex.reCLM_apply]
  rw [hstep, ContinuousLinearMap.integral_comp_comm Complex.reCLM hint,
    ← hE.scalar_inner f f, Complex.reCLM_apply]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

end ActualChartCotangentBinding

include μG hμG hR realization in

theorem actual_coefficient_intrinsic_energy_bound (A : Localizers F ζ hζ U R P H K hK)
    (i : Fin A.count) (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H)
    (x : KPCoreChartLocalizers.E (A.chart i).n) :
    ‖actualLocalCoefficient F ζ hζ U R P H K hK A i f x‖ ^ 2 +
      ∑ r : Fin (A.chart i).n, ‖KPCubeAverage.coordinateDerivative (A.chart i).n
        (actualLocalCoefficient F ζ hζ U R P H K hK A i f) r x‖ ^ 2 ≤
    (A.derivativeBound i 0 ^ 2 + 2 * (A.chart i).n * A.derivativeBound i 1 ^ 2) *
      (KPContActualSectorTestEmbeddings.scalarPair f f
        ((A.chart i).toBase F ζ hζ H.totallyComplex U x)).re +
    (2 * A.derivativeBound i 0 ^ 2 / A.ellipticity i) *
      (KPContActualCotangentMeasurableFamilies.normSquare
        (KPContActualSectorTestDifferentialDescent.D_U f).val
        ((A.chart i).toBase F ζ hζ H.totallyComplex U x) : ℝ) := by
  have hbase : (A.chart i).toBase F ζ hζ H.totallyComplex U x =
      (H.atlas U).components ⟨(A.chart i).component, Quotient.mk _ ((A.chart i).coordinates x)⟩ := by
    rw [(H.atlas U).components_formula]
    rfl
  have hv := ActualChartCotangentBinding.actual_scalar_pair_at_arch F ζ hζ U R P H f
    (A.chart i).component ((A.chart i).coordinates x)
  rw [← hbase] at hv
  by_cases hx : x ∈ tsupport (A.cutoff i)
  · have hg := ActualChartEnergyGeometry.actual_chart_derivative_pointwise_bound
      F ζ hζ U R P H μG hμG hR realization K hK A i f x hx
    rw [Fintype.sum_prod_type, ActualChartCotangentBinding.actual_normal_coframe_normSquare
      F ζ hζ U R P H f (A.chart i).component ((A.chart i).coordinates x), ← hbase] at hg
    have hgd := (div_le_div_of_nonneg_right hg (A.positive_ellipticity i).le)
    rw [mul_div_cancel_left₀ _ (A.positive_ellipticity i).ne'] at hgd
    have hp := actual_coefficient_energy_bound F ζ hζ U R P H μG hμG hR realization K hK A i f x
    rw [hv]
    apply hp.trans
    apply add_le_add_right
    calc
      _ ≤ (2 * A.derivativeBound i 0 ^ 2) * (_ / A.ellipticity i) :=
        mul_le_mul_of_nonneg_left hgd (by positivity)
      _ = _ := by ring
  · have hl : x ∉ tsupport (actualLocalCoefficient F ζ hζ U R P H K hK A i f) := by
      intro h
      apply hx
      apply closure_mono (show Function.support (actualLocalCoefficient F ζ hζ U R P H K hK A i f) ⊆
        Function.support (A.cutoff i) from ?_) h
      intro y hy
      contrapose! hy
      simp only [Function.mem_support, not_not] at hy ⊢
      simp [actualLocalCoefficient, hy]
    simp only [image_eq_zero_of_notMem_tsupport hl, norm_zero, zero_pow (by decide : 2 ≠ 0),
      KPCubeAverage.coordinateDerivative, fderiv_of_notMem_tsupport ℝ hl, zero_apply,
      Finset.sum_const_zero, add_zero]
    rw [hv]
    exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (mul_nonneg (div_nonneg (by positivity) (A.positive_ellipticity i).le)
        (NNReal.coe_nonneg _))

include μG hμG hR realization in

theorem actual_graph_test_norm_sq (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H) :
    ‖KPContActualFormCutoffClosedProduct.graphTestLinear F ζ hζ U R P H μG hμG hR realization f‖ ^ 2 =
      ‖KPContActualSectorTestEmbeddings.iota f‖ ^ 2 +
        ‖KPContActualSectorTestEmbeddings.j (KPContActualSectorTestDifferentialDescent.D_U f)‖ ^ 2 := by
  change ‖WithLp.toLp 2 (KPContActualSectorTestEmbeddings.iota f,
    KPContActualSectorTestEmbeddings.j (KPContActualSectorTestDifferentialDescent.D_U f))‖ ^ 2 = _
  exact WithLp.prod_norm_sq_eq_of_L2 _

theorem actual_smoothJet_norm_sq (n : ℕ) (a : ℝ) (g : KPCoreChartLocalizers.E n → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ‖KPCubeGraphRellich.smoothJet n a g hg‖ ^ 2 =
      ∫ x, (‖g x‖ ^ 2 + ∑ r : Fin n, ‖KPCubeAverage.coordinateDerivative n g r x‖ ^ 2)
        ∂KPCubeAverage.cubeMeasure n a := by
  rw [WithLp.prod_norm_sq_eq_of_L2, KPCubeGraphRellich.smoothJet_gradient_norm_sq]
  have hv : ‖(KPCubeGraphRellich.smoothJet n a g hg).fst‖ ^ 2 =
      ∫ x, ‖g x‖ ^ 2 ∂KPCubeAverage.cubeMeasure n a := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), MeasureTheory.L2.inner_def]
    rw [← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (KPCubeGraphRellich.smoothJet n a g hg).fst (KPCubeGraphRellich.smoothJet n a g hg).fst)]
    apply integral_congr_ae
    filter_upwards [(KPCubeAverage.smooth_memLp n a g hg).coeFn_toLp] with x hx
    simp [KPCubeGraphRellich.smoothJet, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  rw [hv, integral_add]
  · rfl
  · exact ((KPCubeAverage.smooth_memLp n a g hg).norm).integrable_sq
  · exact integrable_finset_sum _ (fun r _ =>
      ((KPCubeGraphRellich.smooth_coordinate_memLp n a g hg r).norm).integrable_sq)

set_option maxHeartbeats 2000000 in

theorem actual_smooth_jet_bound (A : Localizers F ζ hζ U R P H K hK) :
    ∃ C : Fin A.count → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ i f,
      ‖KPCubeGraphRellich.smoothJet (A.chart i).n (A.chart i).a
        (actualLocalCoefficient F ζ hζ U R P H K hK A i f)
        (actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f)‖ ≤
          C i * ‖KPContActualFormCutoffClosedProduct.graphTestLinear
            F ζ hζ U R P H μG hμG hR realization f‖ := by
  let q (i : Fin A.count) : ℝ := (Fintype.card ((A.chart i).G F ζ hζ H.totallyComplex U) : ℝ) / A.lower i
  let c (i : Fin A.count) : ℝ := A.derivativeBound i 0 ^ 2 + 2 * (A.chart i).n * A.derivativeBound i 1 ^ 2
  let d (i : Fin A.count) : ℝ := 2 * A.derivativeBound i 0 ^ 2 / A.ellipticity i
  refine ⟨fun i => Real.sqrt (q i * (c i + d i)), fun i => Real.sqrt_nonneg _, ?_⟩
  intro i f
  let l := actualLocalCoefficient F ζ hζ U R P H K hK A i f
  let B := Metric.ball (0 : KPCoreChartLocalizers.E (A.chart i).n) (A.chart i).radius
  let E := fun x => ‖l x‖ ^ 2 + ∑ r : Fin (A.chart i).n, ‖KPCubeAverage.coordinateDerivative (A.chart i).n l r x‖ ^ 2
  let e := fun x => c i * (KPContActualSectorTestEmbeddings.scalarPair f f x).re +
    d i * (KPContActualCotangentMeasurableFamilies.normSquare (KPContActualSectorTestDifferentialDescent.D_U f).val x : ℝ)
  have hscalar (x : X_U F ζ hζ U) : 0 ≤ (KPContActualSectorTestEmbeddings.scalarPair f f x).re := by
    obtain ⟨a, y, rfl⟩ := ActualChartCotangentBinding.exists_actual_lift F ζ hζ U R P H x
    rw [KPContActualSectorTestEmbeddings.scalar_pair_chart]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  have hc : 0 ≤ c i := by dsimp [c]; positivity
  have hd : 0 ≤ d i := div_nonneg (by positivity) (A.positive_ellipticity i).le
  have hq : 0 ≤ q i := div_nonneg (Nat.cast_nonneg _) (A.positive_lower i).le
  have he0 (x) : 0 ≤ e x := add_nonneg (mul_nonneg hc (hscalar x)) (mul_nonneg hd (NNReal.coe_nonneg _))
  have hei : Integrable e (muU F ζ hζ U R P) :=
    ((KPContActualSectorTestEmbeddings.scalar_pair_integrable f f).re.const_mul (c i)).add
      ((KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
        (KPContActualSectorTestEmbeddings.cotangentSquareFamily (KPContActualSectorTestDifferentialDescent.D_U f))).const_mul (d i))
  have hEnon (x) : 0 ≤ E x := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hEsmooth := actualLocalCoefficient_smooth F ζ hζ U R P H μG hμG hR realization K hK A i f
  have hEcont : Continuous E := hEsmooth.continuous.norm.pow 2 |>.add
    (continuous_finset_sum _ fun r _ =>
      ((hEsmooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hzero (x) (hx : x ∉ B) : E x = 0 := by
    have hcut : x ∉ tsupport (A.cutoff i) := fun h => hx (A.support_cutoff i h)
    have hl : x ∉ tsupport l := by
      intro h
      apply hcut
      apply closure_mono (show Function.support l ⊆ Function.support (A.cutoff i) from ?_) h
      intro y hy
      contrapose! hy
      simp only [Function.mem_support, not_not] at hy ⊢
      simp [l, actualLocalCoefficient, hy]
    simp [E, image_eq_zero_of_notMem_tsupport hl, KPCubeAverage.coordinateDerivative, fderiv_of_notMem_tsupport ℝ hl]
  have hsub : B ⊆ KPCubeAverage.cube (A.chart i).n (A.chart i).a :=
    fun x hx => interior_subset ((A.chart i).closed_ball_in_cube (subset_closure hx))
  have heq : (∫ x, E x ∂KPCubeAverage.cubeMeasure (A.chart i).n (A.chart i).a) = ∫ x in B, E x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (KPCubeAverage.cube_isCompact (A.chart i).n (A.chart i).a).measurableSet hsub
    intro x hx
    exact hzero x hx.2
  have ht := actual_chart_energy_transport F ζ hζ U R P H K hK A i
    (fun x => ENNReal.ofReal (e x)) hei.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hbound : (∫⁻ x in B, ENNReal.ofReal (E x)) ≤ ENNReal.ofReal (q i * ∫ x, e x ∂muU F ζ hζ U R P) := by
    apply le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (actual_coefficient_intrinsic_energy_bound F ζ hζ U R P H μG hμG hR realization K hK A i f x))
    rw [← ofReal_integral_eq_lintegral_ofReal hei (Filter.Eventually.of_forall he0), ← ENNReal.ofReal_mul hq] at ht
    exact ht
  have hreal : (∫ x in B, E x) ≤ q i * ∫ x, e x ∂muU F ζ hζ U R P := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hEnon) hEcont.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hq (integral_nonneg he0)) hbound
  have heint : (∫ x, e x ∂muU F ζ hζ U R P) = c i * ‖KPContActualSectorTestEmbeddings.iota f‖ ^ 2 +
      d i * ‖KPContActualSectorTestEmbeddings.j (KPContActualSectorTestDifferentialDescent.D_U f)‖ ^ 2 := by
    rw [integral_add, integral_const_mul, integral_const_mul,
      ← ActualChartCotangentBinding.actual_test_scalar_norm_sq F ζ hζ U R P H μG hμG hR realization,
      ← ActualChartCotangentBinding.actual_test_gradient_norm_sq F ζ hζ U R P H μG hμG hR realization]
    · exact (KPContActualSectorTestEmbeddings.scalar_pair_integrable f f).re.const_mul _
    · exact (KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
        (KPContActualSectorTestEmbeddings.cotangentSquareFamily (KPContActualSectorTestDifferentialDescent.D_U f))).const_mul _
  have hgraph := actual_graph_test_norm_sq F ζ hζ U R P H μG hμG hR realization f
  have hs := actual_smoothJet_norm_sq (A.chart i).n (A.chart i).a l hEsmooth
  rw [heq] at hs
  rw [heint] at hreal
  have hsum : c i * ‖KPContActualSectorTestEmbeddings.iota f‖ ^ 2 +
      d i * ‖KPContActualSectorTestEmbeddings.j (KPContActualSectorTestDifferentialDescent.D_U f)‖ ^ 2 ≤
      (c i + d i) * ‖KPContActualFormCutoffClosedProduct.graphTestLinear F ζ hζ U R P H μG hμG hR realization f‖ ^ 2 := by
    rw [hgraph]
    nlinarith [mul_nonneg hc (sq_nonneg ‖KPContActualSectorTestEmbeddings.j (KPContActualSectorTestDifferentialDescent.D_U f)‖), mul_nonneg hd (sq_nonneg ‖KPContActualSectorTestEmbeddings.iota f‖)]
  have hsq := hreal.trans (mul_le_mul_of_nonneg_left hsum hq)
  rw [← hs] at hsq
  have hroot := Real.sq_sqrt (mul_nonneg hq (add_nonneg hc hd))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, hroot]
  simpa [mul_assoc] using hsq

end DedekindZetaZeroFree.KPContActualFormLocalRestrictionCompact

end
