module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerSmoothness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerChartEstimates
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypeMultiplicity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerHarmonicIntegrals

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

theorem positive_intertwiner_infinityCoordinate_contDiff (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  have hweyl (y : ℂ) : weyl * upperUnipotent y * weyl = lowerUnipotent y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  have hchart :
      infinityCoordinate (fun g : ComplexGL2 =>
        ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) =
      openCoordinate (fun g : ComplexGL2 =>
        ∫ x : ℂ, rightTranslate positiveParameter weyl f
          (weyl * upperUnipotent x * g) ∂characterHaar β) := by
    funext y
    change (∫ x : ℂ, f (weyl * upperUnipotent x * lowerUnipotent y)
        ∂characterHaar β) =
      ∫ x : ℂ, f ((weyl * upperUnipotent x * (weyl * upperUnipotent y)) * weyl)
        ∂characterHaar β
    simp only [mul_assoc, hweyl]
  rw [hchart]
  exact positive_intertwiner_openCoordinate_contDiff β
    (rightTranslate positiveParameter weyl f)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped NNReal

private theorem weyl_upper_weyl (u : ℂ) :
    weyl * upperUnipotent u * weyl = lowerUnipotent u := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem lower_weyl (u : ℂ) :
    lowerUnipotent u * weyl = weyl * upperUnipotent u := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem weyl_translate_chartSeminorm (s : ℝ) (n : ℕ)
    (f : PrincipalSeries s) :
    chartSeminorm s n (rightTranslate s weyl f) = chartSeminorm s n f := by
  have hO : openCoordinate (rightTranslate s weyl f) = infinityCoordinate f := by
    funext u
    change f (weyl * upperUnipotent u * weyl) = f (lowerUnipotent u)
    rw [weyl_upper_weyl]
  have hI : infinityCoordinate (rightTranslate s weyl f) = openCoordinate f := by
    funext u
    change f (lowerUnipotent u * weyl) = f (weyl * upperUnipotent u)
    rw [lower_weyl]
  change chartSeminormValue s n (rightTranslate s weyl f) = chartSeminormValue s n f
  simp only [chartSeminormValue, hO, hI, max_comm]

theorem positive_intertwiner_infinity_chart_bounds (β : ℂˣ)
    (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2),
      T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) :
    ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries positiveParameter) (u : ℂ),
        u ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) u‖ ≤
            (C • orders.sup (chartSeminorm positiveParameter)) f := by
  intro n
  obtain ⟨orders, C, hbound⟩ := positive_intertwiner_open_chart_bounds β T hT n
  refine ⟨orders, C, ?_⟩
  intro f u hu
  have hcharts : infinityCoordinate (T f) =
      openCoordinate (T (rightTranslate positiveParameter weyl f)) := by
    funext v
    change T f (lowerUnipotent v) =
      T (rightTranslate positiveParameter weyl f) (weyl * upperUnipotent v)
    rw [hT, hT]
    apply integral_congr_ae
    filter_upwards [] with x
    change f (weyl * upperUnipotent x * lowerUnipotent v) =
      f ((weyl * upperUnipotent x * (weyl * upperUnipotent v)) * weyl)
    rw [mul_assoc (weyl * upperUnipotent x) (weyl * upperUnipotent v) weyl,
      weyl_upper_weyl]
  have hsup : orders.sup (chartSeminorm positiveParameter)
      (rightTranslate positiveParameter weyl f) =
      orders.sup (chartSeminorm positiveParameter) f := by
    classical
    clear hbound
    induction orders using Finset.induction_on with
    | empty => simp
    | @insert a orders ha ih =>
      simp only [Finset.sup_insert, Seminorm.sup_apply, weyl_translate_chartSeminorm, ih]
  rw [hcharts]
  have h := hbound (rightTranslate positiveParameter weyl f) u hu
  simpa only [Seminorm.smul_apply, hsup] using h

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxPrincipalSeriesCharts
open scoped NNReal

private theorem sSup_closedBall_le {F : ℂ → ℝ} {M : ℝ}
    (h : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, F x ≤ M) :
    sSup (F '' Metric.closedBall (0 : ℂ) 1) ≤ M := by
  refine csSup_le ⟨F 0, 0, Metric.mem_closedBall_self (by norm_num), rfl⟩ ?_
  rintro y ⟨x, hx, rfl⟩
  exact h x hx

theorem linearMap_isBounded_of_two_chart_derivative_bounds (s t : ℝ)
    (T : PrincipalSeries s →ₗ[ℂ] PrincipalSeries t)
    (hopen : ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries s) (x : ℂ),
        x ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (openCoordinate (T f)) x‖ ≤
            (C • orders.sup (chartSeminorm s)) f)
    (hinfinity : ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries s) (u : ℂ),
        u ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) u‖ ≤
            (C • orders.sup (chartSeminorm s)) f) :
    Seminorm.IsBounded (chartSeminorm s) (chartSeminorm t) T := by
  rw [Seminorm.IsBounded]
  intro n
  obtain ⟨ordersO, CO, hO⟩ := hopen n
  obtain ⟨ordersI, CI, hI⟩ := hinfinity n
  refine ⟨ordersO ∪ ordersI, max CO CI, ?_⟩
  rw [Seminorm.le_def]
  intro f
  set S : ℝ := ((ordersO ∪ ordersI).sup (chartSeminorm s)) f with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact apply_nonneg _ _
  have hsupO : (ordersO.sup (chartSeminorm s)) f ≤ S := by
    rw [hS]
    exact (Seminorm.le_def.mp (Finset.sup_mono (f := chartSeminorm s)
      (Finset.subset_union_left : ordersO ⊆ ordersO ∪ ordersI))) f
  have hsupI : (ordersI.sup (chartSeminorm s)) f ≤ S := by
    rw [hS]
    exact (Seminorm.le_def.mp (Finset.sup_mono (f := chartSeminorm s)
      (Finset.subset_union_right : ordersI ⊆ ordersO ∪ ordersI))) f
  have hCO : (CO : ℝ) ≤ (max CO CI : ℝ) := by
    exact_mod_cast le_max_left CO CI
  have hCI : (CI : ℝ) ≤ (max CO CI : ℝ) := by
    exact_mod_cast le_max_right CO CI
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (openCoordinate (T f)) x‖ ≤ (max CO CI : ℝ) * S := by
    intro x hx
    have h1 := hO f x hx
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans ?_
    calc (CO : ℝ) * (ordersO.sup (chartSeminorm s)) f
        ≤ (CO : ℝ) * S := mul_le_mul_of_nonneg_left hsupO (by positivity)
      _ ≤ (max CO CI : ℝ) * S := mul_le_mul_of_nonneg_right hCO hSnn
  have hbound' : ∀ x ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) x‖ ≤ (max CO CI : ℝ) * S := by
    intro x hx
    have h1 := hI f x hx
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans ?_
    calc (CI : ℝ) * (ordersI.sup (chartSeminorm s)) f
        ≤ (CI : ℝ) * S := mul_le_mul_of_nonneg_left hsupI (by positivity)
      _ ≤ (max CO CI : ℝ) * S := mul_le_mul_of_nonneg_right hCI hSnn
  have hA := sSup_closedBall_le
    (F := fun x : ℂ => ‖iteratedFDeriv ℝ n (openCoordinate (T f)) x‖) hbound
  have hB := sSup_closedBall_le
    (F := fun x : ℂ => ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) x‖) hbound'
  rw [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  change chartSeminormValue t n (T f) ≤ (max CO CI : ℝ) * S
  rw [chartSeminormValue]
  exact max_le hA hB

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators Matrix

private lemma complex_integral_mul (F : ℂ → ℂ) (c : ℂ) (hc : c ≠ 0) :
    (∫ x : ℂ, F (c * x)) = (‖c‖ ^ 2)⁻¹ • ∫ x : ℂ, F x := by
  let u : Circle := ⟨c / (‖c‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [norm_div, Complex.norm_real, abs_of_nonneg (norm_nonneg _), hc]⟩
  have hcx (x : ℂ) : c * x = ‖c‖ • (rotation u x) := by
    change c * x = (‖c‖ : ℂ) * ((c / (‖c‖ : ℂ)) * x)
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)]
  simp_rw [hcx]
  rw [MeasureTheory.integral_comp (rotation u) (fun y => F (‖c‖ • y))]
  simpa only [Complex.finrank_real_complex] using
    Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ) F ‖c‖
      (hR := norm_nonneg _)

lemma character_integral_mul (β : ℂˣ) (F : ℂ → ℂ) (c : ℂ) (hc : c ≠ 0) :
    (∫ x : ℂ, F (c * x) ∂characterHaar β) =
      (‖c‖ ^ 2)⁻¹ • ∫ x : ℂ, F x ∂characterHaar β := by
  unfold characterHaar
  rw [integral_smul_measure, integral_smul_measure]
  change _ • (∫ x : ℂ, F (c * x)) = (‖c‖ ^ 2)⁻¹ • _ • (∫ x : ℂ, F x)
  rw [complex_integral_mul F c hc, smul_comm]
private lemma positive_intertwiner_triangular_identity (a d : ℂˣ) (b x : ℂ) :
    weyl * upperUnipotent x * upperTriangular a d b =
      upperTriangular d a 0 * (weyl * upperUnipotent ((b + x * (d : ℂ)) / (a : ℂ))) := by
  apply Units.ext
  have h1 : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  have h2 : (upperTriangular d a 0 : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(d : ℂ), 0; 0, (a : ℂ)] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, h1, h2,
      mul_assoc, mul_comm, mul_left_comm, a.ne_zero]
  all_goals field_simp
private lemma positive_intertwiner_weight (a d : ℂˣ) :
    inductionWeight positiveParameter d a * (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ =
      inductionWeight negativeParameter a d := by
  have hpos : 0 < ‖(d : ℂ) / (a : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (div_ne_zero d.ne_zero a.ne_zero)) 2
  have hinv : ‖(a : ℂ) / (d : ℂ)‖ ^ 2 = (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ := by
    rw [← inv_div, norm_inv, inv_pow]
  simp only [inductionWeight, complexAbs, positiveParameter, negativeParameter, hinv]
  simp only [Real.rpow_eq_pow]
  have hneg : (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ =
      (‖(d : ℂ) / (a : ℂ)‖ ^ 2) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_one]
  rw [← Real.rpow_neg_eq_inv_rpow]
  conv_lhs => arg 2; rw [hneg]
  rw [← Real.rpow_add hpos]
  congr 1
  norm_num

lemma positive_intertwiner_covariance (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    HasCovariance negativeParameter (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) := by
  intro a d b g
  letI : (characterHaar β).IsAddHaarMeasure := characterHaar_isAddHaarMeasure β
  have hf := f.property.1
  change HasCovariance positiveParameter (f : ComplexGL2 → ℂ) at hf
  simp_rw [← mul_assoc, positive_intertwiner_triangular_identity, mul_assoc,
    hf d a 0]
  rw [integral_const_mul]
  have heq (x : ℂ) : (b + x * (d : ℂ)) / (a : ℂ) =
      (d : ℂ) / (a : ℂ) * x + b / (a : ℂ) := by ring
  simp_rw [heq, ← mul_assoc]
  rw [character_integral_mul β (fun x => f (weyl * upperUnipotent (x + b / (a : ℂ)) * g))
    ((d : ℂ) / (a : ℂ)) (div_ne_zero d.ne_zero a.ne_zero)]
  rw [integral_add_right_eq_self (fun x => f (weyl * upperUnipotent x * g)) (b / (a : ℂ)),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, positive_intertwiner_weight]

theorem positive_intertwiner_section (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) ∈
      principalSeriesSubmodule negativeParameter := by
  exact ⟨positive_intertwiner_covariance β f,
    positive_intertwiner_openCoordinate_contDiff β f,
    positive_intertwiner_infinityCoordinate_contDiff β f⟩

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators NNReal

theorem positive_intertwiner_seminorm_bounds (β : ℂˣ)
    (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2),
      T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) :
    Seminorm.IsBounded (chartSeminorm positiveParameter)
      (chartSeminorm negativeParameter) T := by
  exact linearMap_isBounded_of_two_chart_derivative_bounds
    positiveParameter negativeParameter T
    (positive_intertwiner_open_chart_bounds β T hT)
    (positive_intertwiner_infinity_chart_bounds β T hT)

theorem positive_intertwiner_continuous (β : ℂˣ)
    (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2),
      T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) :
    Continuous T := by
  have hp : WithSeminorms (chartSeminorm positiveParameter) := ⟨rfl⟩
  have hq : WithSeminorms (chartSeminorm negativeParameter) := ⟨rfl⟩
  exact WithSeminorms.continuous_of_isBounded hp hq T
    (positive_intertwiner_seminorm_bounds β T hT)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section

namespace DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

noncomputable def compactSphereCoordinate (k : ComplexSU2) : Fin 3 → ℂ :=
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  ![(2 * (m 1 0 * star (m 1 1)).re : ℝ),
    (2 * (m 1 0 * star (m 1 1)).im : ℝ),
    (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ)]

noncomputable def polynomialLaplacian :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] MvPolynomial (Fin 3) ℂ :=
  ∑ i : Fin 3, (MvPolynomial.pderiv i).toLinearMap.comp
    (MvPolynomial.pderiv i).toLinearMap

noncomputable def harmonicPolynomials (ℓ : ℕ) : Submodule ℂ (MvPolynomial (Fin 3) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ ⊓ polynomialLaplacian.ker

noncomputable def compactRestriction (s : ℝ) : PrincipalSeries s →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun f k := f (complexSU2Embedding k)
  map_add' f h := rfl
  map_smul' c f := rfl

noncomputable def polynomialCompactRestriction :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun p k := MvPolynomial.eval (compactSphereCoordinate k) p
  map_add' p q := by ext k; simp
  map_smul' c p := by ext k; simp

noncomputable def harmonicKType (s : ℝ) (ℓ : ℕ) : Submodule ℂ (PrincipalSeries s) :=
  ((harmonicPolynomials ℓ).map polynomialCompactRestriction).comap (compactRestriction s)

def IsKInvariant (s : ℝ) (U : Submodule ℂ (PrincipalSeries s)) : Prop :=
  ∀ (k : compactSubgroup) (f : PrincipalSeries s), f ∈ U → pi s k f ∈ U

def KEquivalent (s : ℝ) (U V : Submodule ℂ (PrincipalSeries s)) : Prop :=
  ∃ e : U ≃ₗ[ℂ] V, ∀ (k : compactSubgroup) (u v : U),
    (v : PrincipalSeries s) = pi s k u →
      (e v : PrincipalSeries s) = pi s k (e u)

theorem harmonicKType_multiplicity_one (s : ℝ) (ℓ : ℕ) :
    IsKInvariant s (harmonicKType s ℓ) ∧
    Module.finrank ℂ (harmonicKType s ℓ) = 2 * ℓ + 1 ∧
    (∀ U : Submodule ℂ (PrincipalSeries s), U ≤ harmonicKType s ℓ →
      IsKInvariant s U → U = ⊥ ∨ U = harmonicKType s ℓ) ∧
    (∀ U : Submodule ℂ (PrincipalSeries s), IsKInvariant s U →
      KEquivalent s U (harmonicKType s ℓ) → U = harmonicKType s ℓ) := by
  have hs := KPCplxHarmonicIntertwinerSpectrum.harmonicKType_structure s ℓ
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  intro U hU he
  exact KPCplxHarmonicIntertwinerSpectrum.harmonicKType_unique_copy s ℓ U hU he

noncomputable def intertwinerIntegral (β : ℂˣ) (f : PrincipalSeries positiveParameter)
    (g : ComplexGL2) : ℂ :=
  ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β

theorem intertwinerIntegral_exists (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    (∀ g : ComplexGL2, Integrable
      (fun x : ℂ => f (weyl * upperUnipotent x * g)) (characterHaar β)) ∧
    intertwinerIntegral β f ∈ principalSeriesSubmodule negativeParameter := by
  exact ⟨fun g => KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_integrable β f g,
    KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_section β f⟩

noncomputable def intertwinerLinearMap (β : ℂˣ) :
    PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter where
  toFun f := ⟨intertwinerIntegral β f, (intertwinerIntegral_exists β f).2⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    exact integral_add ((intertwinerIntegral_exists β f).1 g)
      ((intertwinerIntegral_exists β h).1 g)
  map_smul' c f := by
    apply Subtype.ext
    funext g
    exact integral_smul c (fun x : ℂ => f (weyl * upperUnipotent x * g))

theorem intertwinerLinearMap_continuous (β : ℂˣ) :
    Continuous (intertwinerLinearMap β) := by
  exact KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_continuous β
    (intertwinerLinearMap β) (fun _ _ => rfl)

noncomputable def standardIntertwiner (β : ℂˣ) :
    PrincipalSeries positiveParameter →L[ℂ] PrincipalSeries negativeParameter :=
  ⟨intertwinerLinearMap β, intertwinerLinearMap_continuous β⟩

theorem standardIntertwiner_apply (β : ℂˣ) (f : PrincipalSeries positiveParameter)
    (g : ComplexGL2) :
    standardIntertwiner β f g =
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β := rfl

theorem standardIntertwiner_equivariant (β : ℂˣ) (g : ComplexPGL2)
    (f : PrincipalSeries positiveParameter) :
    standardIntertwiner β (pi positiveParameter g f) =
      pi negativeParameter g (standardIntertwiner β f) := by
  induction g using Quotient.inductionOn with
  | h g =>
    change standardIntertwiner β (pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f) =
      pi negativeParameter (Matrix.ProjGenLinGroup.mk g) (standardIntertwiner β f)
    rw [pi_mk, pi_mk]
    apply Subtype.ext
    funext h
    change (∫ x : ℂ, f ((weyl * upperUnipotent x * h) * g) ∂characterHaar β) =
      ∫ x : ℂ, f (weyl * upperUnipotent x * (h * g)) ∂characterHaar β
    simp only [mul_assoc]

noncomputable def eigenvalue (β : ℂˣ) (ℓ : ℕ) : ℝ :=
  (3 * characterScale β / 2) *
    ∏ j ∈ Finset.Icc 1 ℓ, (((j : ℝ) - 1 / 3) / ((j : ℝ) + 1 / 3))

lemma su2_matrix (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) :
    (!![star b, -star a; a, b] : Matrix (Fin 2) (Fin 2) ℂ) ∈ ComplexSU2 := by
  have hc : a * star a + b * star b = 1 := by
    rw [show a * star a = (Complex.normSq a : ℂ) from Complex.mul_conj a,
      show b * star b = (Complex.normSq b : ℂ) from Complex.mul_conj b,
      ← Complex.ofReal_add, h, Complex.ofReal_one]
  change a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1 at hc
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · convert hc using 1 <;> ring
    · ring
    · ring
    · exact hc
  · simp [Matrix.det_fin_two]
    convert hc using 1 <;> ring
noncomputable def openSU2 (x : ℂ) : ComplexSU2 := by
  let r : ℝ := Real.sqrt (1 + Complex.normSq x)
  have hn := Complex.normSq_nonneg x
  have hr : r ^ 2 = 1 + Complex.normSq x := Real.sq_sqrt (by linarith)
  refine ⟨!![(star x) / r, -(1 / r); 1 / r, x / r], ?_⟩
  convert su2_matrix (1 / (r : ℂ)) (x / (r : ℂ)) ?_ using 1
  · simp [map_div₀]
  · simp only [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
    rw [← pow_two, hr]
    field_simp [show 1 + Complex.normSq x ≠ 0 by linarith]

private lemma openSU2_factor (x : ℂ) :
    ∃ (a d : ℂˣ) (b : ℂ), weyl * upperUnipotent x =
      upperTriangular a d b * complexSU2Embedding (openSU2 x) := by
  let r : ℝ := Real.sqrt (1 + Complex.normSq x)
  have hn := Complex.normSq_nonneg x
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hn := Complex.normSq_nonneg x
  have hr : r ^ 2 = 1 + Complex.normSq x := Real.sq_sqrt (by linarith)
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have hrc : (r : ℂ) ^ 2 = 1 + x * (starRingEnd ℂ) x := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_add, ← hr,
      Complex.ofReal_pow]
  refine ⟨Units.mk0 (-(1 / (r : ℂ))) (by simp [hrne]),
    Units.mk0 (r : ℂ) hrne, (star x) / r, ?_⟩
  apply Units.ext
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, x; 0, 1] =
    !![-(1 / (r : ℂ)), star x / r; 0, (r : ℂ)] *
      !![star x / r, -(1 / (r : ℂ)); 1 / (r : ℂ), x / r]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
    ring
  · change (1 : ℂ) = (r : ℂ)⁻¹ * (r : ℂ)⁻¹ + (starRingEnd ℂ) x / r * (x / r)
    field_simp
    linear_combination hrc
  · change (1 : ℂ) = (r : ℂ) * (r : ℂ)⁻¹
    simp [hrne]
  · change x = (r : ℂ) * (x / r)
    field_simp

theorem compactRestriction_injective (s : ℝ) : Function.Injective (compactRestriction s) := by
  intro f h hfh
  apply openCoordinate_injective s
  funext x
  obtain ⟨a, d, b, hx⟩ := openSU2_factor x
  change f (weyl * upperUnipotent x) = h (weyl * upperUnipotent x)
  rw [hx, f.property.1, h.property.1]
  congr 1
  exact congrFun hfh (openSU2 x)
private lemma spherical_compact (s : ℝ) (k : ComplexSU2) :
    sphericalSection s (complexSU2Embedding k) = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have hrow := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => (B 1 1).re)
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hrow
  change (((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
    (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 *
    (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1))).re = 1 at hrow
  simp only [Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re] at hrow
  change (Real.rpow (‖(k : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
    (‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) (1 + 2 * s) : ℂ) = 1
  rw [hd, hrow]
  simp

lemma inductionWeight_product (s u : ℝ) (a d : ℂˣ) :
    inductionWeight s a d * inductionWeight u a d = inductionWeight (s + u + 1 / 2) a d := by
  have hn : 0 < complexAbs ((a : ℂ) / (d : ℂ)) := by
    unfold complexAbs
    exact pow_pos (norm_pos_iff.mpr (div_ne_zero a.ne_zero d.ne_zero)) _
  unfold inductionWeight
  rw [show 1 / 2 + (s + u + 1 / 2) = (1 / 2 + s) + (1 / 2 + u) by ring]
  exact (Real.rpow_add hn (1 / 2 + s) (1 / 2 + u)).symm

noncomputable def changeParameter (s t : ℝ) (f : PrincipalSeries s) : PrincipalSeries t := by
  let h := sphericalSection (t - s - 1 / 2)
  refine ⟨fun g => f g * h g, ?_⟩
  change HasCovariance t (fun g => f g * h g) ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro a d b g
    dsimp only
    rw [f.property.1, h.property.1]
    have hw := inductionWeight_product s (t - s - 1 / 2) a d
    have he : s + (t - s - 1 / 2) + 1 / 2 = t := by ring
    rw [he] at hw
    push_cast
    rw [← hw]
    push_cast
    ring
  · exact f.property.2.1.mul h.property.2.1
  · exact f.property.2.2.mul h.property.2.2

private lemma changeParameter_restriction (s t : ℝ) (f : PrincipalSeries s) :
    compactRestriction t (changeParameter s t f) = compactRestriction s f := by
  ext k
  change f (complexSU2Embedding k) * sphericalSection _ (complexSU2Embedding k) = _
  rw [spherical_compact, mul_one]
  rfl

theorem harmonicKType_compact_identification (s t : ℝ) (ℓ : ℕ) :
    Function.Injective (compactRestriction s) ∧
    (harmonicKType s ℓ).map (compactRestriction s) =
      (harmonicKType t ℓ).map (compactRestriction t) := by
  refine ⟨compactRestriction_injective s, ?_⟩
  apply le_antisymm
  · rintro u ⟨f, hf, rfl⟩
    refine ⟨changeParameter s t f, ?_, changeParameter_restriction s t f⟩
    change compactRestriction t (changeParameter s t f) ∈ (harmonicPolynomials ℓ).map polynomialCompactRestriction
    rw [changeParameter_restriction]
    exact hf
  · rintro u ⟨f, hf, rfl⟩
    refine ⟨changeParameter t s f, ?_, changeParameter_restriction t s f⟩
    change compactRestriction s (changeParameter t s f) ∈ (harmonicPolynomials ℓ).map polynomialCompactRestriction
    rw [changeParameter_restriction]
    exact hf

theorem standardIntertwiner_harmonic_eigenvalue (β : ℂˣ) (ℓ : ℕ)
    (f : PrincipalSeries positiveParameter) (hf : f ∈ harmonicKType positiveParameter ℓ) :
    standardIntertwiner β f ∈ harmonicKType negativeParameter ℓ ∧
    compactRestriction negativeParameter (standardIntertwiner β f) =
      (eigenvalue β ℓ : ℂ) • compactRestriction positiveParameter f := by
  have hcompact : compactRestriction positiveParameter f ∈
      (harmonicPolynomials ℓ).map polynomialCompactRestriction := hf
  obtain ⟨p, hp, hpf⟩ := hcompact
  have hscalar : compactRestriction negativeParameter (standardIntertwiner β f) =
      (eigenvalue β ℓ : ℂ) • compactRestriction positiveParameter f := by
    ext k
    change (∫ x : ℂ, f (weyl * upperUnipotent x * complexSU2Embedding k) ∂characterHaar β) =
      (eigenvalue β ℓ : ℂ) * f (complexSU2Embedding k)
    have hfk : ∀ k : ComplexSU2, f (complexSU2Embedding k) =
        MvPolynomial.eval (compactSphereCoordinate k) p :=
      fun k => (congrFun hpf k).symm
    rw [hfk k]
    exact KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_harmonic_integral
      β ℓ p hp f hfk k
  refine ⟨?_, hscalar⟩
  change compactRestriction negativeParameter (standardIntertwiner β f) ∈
    (harmonicPolynomials ℓ).map polynomialCompactRestriction
  rw [hscalar]
  exact Submodule.smul_mem _ _ hf

private lemma characterScale_pos' (β : ℂˣ) : 0 < characterScale β := by
  rw [characterScale]
  exact norm_pos_iff.mpr (Units.ne_zero β)

private lemma eigenvalue_pos (β : ℂˣ) (ℓ : ℕ) : 0 < eigenvalue β ℓ := by
  have hc := characterScale_pos' β
  rw [eigenvalue]
  apply mul_pos
  · positivity
  · apply Finset.prod_pos
    intro j hj
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    apply div_pos <;> linarith

theorem eigenvalue_zero (β : ℂˣ) :
    eigenvalue β 0 = 3 * characterScale β / 2 ∧ 0 < eigenvalue β 0 := by
  constructor
  · rw [eigenvalue]; simp
  · exact eigenvalue_pos β 0

theorem eigenvalue_ne_zero (β : ℂˣ) (ℓ : ℕ) : eigenvalue β ℓ ≠ 0 :=
  ne_of_gt (eigenvalue_pos β ℓ)

private lemma one_harmonic : (1 : MvPolynomial (Fin 3) ℂ) ∈ harmonicPolynomials 0 := by
  constructor
  · exact MvPolynomial.isHomogeneous_one (Fin 3) ℂ
  · simp [LinearMap.mem_ker, polynomialLaplacian, LinearMap.sum_apply,
      LinearMap.comp_apply]

private lemma spherical_harmonic_zero (s : ℝ) :
    sphericalSection s ∈ harmonicKType s 0 := by
  change compactRestriction s (sphericalSection s) ∈
    (harmonicPolynomials 0).map polynomialCompactRestriction
  refine ⟨1, one_harmonic, ?_⟩
  ext k
  change MvPolynomial.eval (compactSphereCoordinate k) 1 =
    sphericalSection s (complexSU2Embedding k)
  rw [spherical_compact]; simp

theorem standardIntertwiner_spherical (β : ℂˣ) :
    standardIntertwiner β (sphericalSection positiveParameter) =
      (3 * characterScale β / 2 : ℂ) • sphericalSection negativeParameter := by
  apply (harmonicKType_compact_identification negativeParameter negativeParameter 0).1
  rw [map_smul]
  have he := (standardIntertwiner_harmonic_eigenvalue β 0
    (sphericalSection positiveParameter) (spherical_harmonic_zero positiveParameter)).2
  rw [(eigenvalue_zero β).1] at he
  rw [he]
  congr 1
  · push_cast; rfl
  · funext k
    exact (spherical_compact positiveParameter k).trans (spherical_compact negativeParameter k).symm

end DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

end

section

namespace DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

theorem harmonicKType_zero_scalar (s : ℝ) (f : PrincipalSeries s) (hf : f ∈ harmonicKType s 0) :
    f = (f 1) • sphericalSection s := by
  obtain ⟨p, hp, he⟩ := hf
  have hp0 : p.IsHomogeneous 0 := hp.1
  have hc : p = MvPolynomial.C (p.coeff 0) := by
    rw [← MvPolynomial.homogeneousComponent_zero p]
    exact (MvPolynomial.homogeneousComponent_eq_self hp0).symm
  apply compactRestriction_injective s
  ext k
  have hek := congrFun he k
  change MvPolynomial.eval (compactSphereCoordinate k) p = f (complexSU2Embedding k) at hek
  rw [hc, MvPolynomial.eval_C] at hek
  have hek1 := congrFun he 1
  change MvPolynomial.eval (compactSphereCoordinate 1) p = f (complexSU2Embedding 1) at hek1
  rw [hc, MvPolynomial.eval_C, map_one] at hek1
  change f (complexSU2Embedding k) = f 1 * sphericalSection s (complexSU2Embedding k)
  rw [← hek, ← hek1]
  rw [spherical_compact, mul_one]

theorem harmonicKType_zero_eq_span (s : ℝ) :
    harmonicKType s 0 = Submodule.span ℂ {sphericalSection s} := by
  apply le_antisymm
  · intro f hf
    rw [harmonicKType_zero_scalar s f hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    change compactRestriction s (sphericalSection s) ∈
      (harmonicPolynomials 0).map polynomialCompactRestriction
    refine ⟨1, ?_, ?_⟩
    · constructor
      · exact MvPolynomial.isHomogeneous_one (Fin 3) ℂ
      · simp [LinearMap.mem_ker, polynomialLaplacian, LinearMap.sum_apply,
          LinearMap.comp_apply]
    · ext k
      change MvPolynomial.eval (compactSphereCoordinate k) 1 =
        sphericalSection s (complexSU2Embedding k)
      rw [spherical_compact]; simp

end DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

end
