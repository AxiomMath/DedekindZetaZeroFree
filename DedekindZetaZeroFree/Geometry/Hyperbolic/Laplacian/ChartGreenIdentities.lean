module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Star

@[expose] public section

noncomputable section

open scoped ContDiff
open MeasureTheory

namespace DedekindZetaZeroFree
namespace HyperbolicChart

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin 3)

abbrev Cotangent (d : ℕ) := Fin d → Fin 3 → ℂ

def coordinateVector (d : ℕ) (i : Fin d) (k : Fin 3) : Space d :=
  WithLp.toLp 2 (fun j => if j = (i, k) then 1 else 0)

def coordinateDerivative (d : ℕ) (i : Fin d) (k : Fin 3) (f : Space d → ℂ)
    (p : Space d) : ℂ := fderiv ℝ f p (coordinateVector d i k)

def metric (d : ℕ) (p v w : Space d) : ℝ :=
  ∑ i : Fin d, (v (i, 2) * w (i, 2) + Real.exp (-2 * p (i, 2)) *
    (v (i, 0) * w (i, 0) + v (i, 1) * w (i, 1)))

def density (d : ℕ) (p : Space d) : ℝ :=
  Real.exp (-2 * ∑ i : Fin d, p (i, 2))

def measure (d : ℕ) : MeasureTheory.Measure (Space d) :=
  MeasureTheory.volume.withDensity (fun p => ENNReal.ofReal (density d p))

def chartMeasure (d : ℕ) (c : ℝ) (m : ℕ) : MeasureTheory.Measure (Space d) :=
  ENNReal.ofReal (c / (m : ℝ)) • measure d

def differential (d : ℕ) (f : Space d → ℂ) (p : Space d) : Cotangent d :=
  fun i => ![coordinateDerivative d i 2 f p,
    (Real.exp (p (i, 2)) : ℂ) * coordinateDerivative d i 0 f p,
    (Real.exp (p (i, 2)) : ℂ) * coordinateDerivative d i 1 f p]

def codifferential (d : ℕ) (W : Space d → Cotangent d) (p : Space d) : ℂ :=
  ∑ i : Fin d, (-coordinateDerivative d i 2 (fun q => W q i 0) p + 2 * W p i 0 -
    (Real.exp (p (i, 2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) p -
    (Real.exp (p (i, 2)) : ℂ) * coordinateDerivative d i 1 (fun q => W q i 2) p)

def laplacian (d : ℕ) (f : Space d → ℂ) (p : Space d) : ℂ :=
  ∑ i : Fin d, (-coordinateDerivative d i 2 (coordinateDerivative d i 2 f) p + 2 * coordinateDerivative d i 2 f p -
    (Real.exp (2 * p (i, 2)) : ℂ) *
      (coordinateDerivative d i 0 (coordinateDerivative d i 0 f) p + coordinateDerivative d i 1 (coordinateDerivative d i 1 f) p))

def pairing (d : ℕ) (U W : Cotangent d) : ℂ :=
  ∑ i : Fin d, ∑ k : Fin 3, star (U i k) * W i k

def IsTestFunction (d : ℕ) (Ω : Set (Space d)) (f : Space d → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω

def IsTestField (d : ℕ) (Ω : Set (Space d)) (W : Space d → Cotangent d) : Prop :=
  ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ Ω

private theorem smooth_coordinateDerivative (d : ℕ) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (i : Fin d) (k : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative d i k f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem coordinateDerivative_exp_mul (d : ℕ) (i : Fin d) (k : Fin 3)
    (hk : k ≠ 2) (f : Space d → ℂ) (hf : Differentiable ℝ f) (p : Space d) :
    coordinateDerivative d i k (fun q => (Real.exp (q (i, 2)) : ℂ) * f q) p =
      (Real.exp (p (i, 2)) : ℂ) * coordinateDerivative d i k f p := by
  have he : HasFDerivAt (fun q : Space d => (Real.exp (q (i, 2)) : ℂ))
      (Complex.ofRealCLM.comp (Real.exp (p (i, 2)) • EuclideanSpace.proj (i, 2))) p := by
    simpa only [Function.comp_def, PiLp.proj_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp p
        ((EuclideanSpace.proj (i, 2)).hasFDerivAt.exp))
  have hh := congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
    (he.mul (hf p).hasFDerivAt).fderiv
  simpa [coordinateDerivative, coordinateVector, hk, Ne.symm hk, Pi.mul_def] using hh

private theorem smooth_star (d : ℕ) (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) :
 ContDiff ℝ ∞ (fun p => star (f p)) := by
 exact (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hf

private theorem deriv_mul (d : ℕ) (i : Fin d) (k : Fin 3) (f g : Space d → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (p : Space d) :
 coordinateDerivative d i k (fun q => f q * g q) p =
  f p * coordinateDerivative d i k g p + g p * coordinateDerivative d i k f p := by
 simpa [coordinateDerivative, Pi.mul_def] using congrArg
  (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k)) ((hf p).hasFDerivAt.mul (hg p).hasFDerivAt).fderiv

private theorem deriv_star (d : ℕ) (i : Fin d) (k : Fin 3) (f : Space d → ℂ) (p : Space d) :
 coordinateDerivative d i k (fun q => star (f q)) p = star (coordinateDerivative d i k f p) := by
 unfold coordinateDerivative
 rw [fderiv_star]
 rfl

private theorem compact_star (d : ℕ) (f : Space d → ℂ) (hf : HasCompactSupport f) :
 HasCompactSupport (fun p => star (f p)) :=
 hf.comp_left (g := star) (by simp)

private theorem smooth_density (d : ℕ) : ContDiff ℝ ∞ (density d) := by
 unfold density
 apply ContDiff.exp
 apply ContDiff.mul contDiff_const
 apply ContDiff.sum
 intro i hi
 convert (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d × Fin 3 => ℝ) (i, 2)).contDiff (n := ∞) using 1
 rfl

private theorem deriv_density (d : ℕ) (i : Fin d) (k : Fin 3) (p : Space d) :
 coordinateDerivative d i k (fun q => (density d q : ℂ)) p =
 (if k = 2 then -2 else 0) * (density d p : ℂ) := by
 have hs : HasFDerivAt (fun q : Space d => ∑ j : Fin d, q (j,2))
  (∑ j : Fin d, EuclideanSpace.proj (𝕜 := ℝ) (j,(2 : Fin 3))) p := by
  apply HasFDerivAt.fun_sum
  intro j hj
  convert (EuclideanSpace.proj (𝕜 := ℝ) (j,(2 : Fin 3))).hasFDerivAt (x := p) using 1
  rfl
 have hh := Complex.ofRealCLM.hasFDerivAt.comp p (hs.const_mul (-2)).exp
 have hhe := congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k)) hh.fderiv
 by_cases hk : k = 2
 · subst k
   simpa [coordinateDerivative, density, PiLp.proj_apply, Function.comp_def, coordinateVector,
    Finset.sum_apply, Pi.mul_def, Finset.sum_ite, mul_comm, mul_left_comm] using hhe
 · simpa [coordinateDerivative, density, PiLp.proj_apply, Function.comp_def, coordinateVector,
    Finset.sum_apply, Pi.mul_def, Finset.sum_ite, mul_comm, mul_left_comm, hk, Ne.symm hk] using hhe

private theorem smooth_exp (d : ℕ) (i : Fin d) :
    ContDiff ℝ ∞ (fun p : Space d => (Real.exp (p (i, 2)) : ℂ)) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.exp
  convert (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff (n := ∞) using 1
  rfl

private theorem smooth_density_complex (d : ℕ) :
    ContDiff ℝ ∞ (fun p => (density d p : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (smooth_density d)

private theorem smooth_differential (d : ℕ) (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (differential d f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro k
  fin_cases k
  · simpa [differential] using smooth_coordinateDerivative d f hf i 2
  · simpa [differential] using (smooth_exp d i).mul (smooth_coordinateDerivative d f hf i 0)
  · simpa [differential] using (smooth_exp d i).mul (smooth_coordinateDerivative d f hf i 1)

private theorem differential_zero_off (d : ℕ) (f : Space d → ℂ) (p : Space d)
    (hp : p ∉ tsupport f) : differential d f p = 0 := by
  funext i k
  fin_cases k <;> simp [differential, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hp]

private theorem compact_differential (d : ℕ) (f : Space d → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (differential d f) := by
  apply HasCompactSupport.of_support_subset_isCompact hf
  intro p hp
  by_contra hn
  exact hp (differential_zero_off d f p hn)

private theorem continuous_codifferential (d : ℕ) (W : Space d → Cotangent d)
    (hW : ContDiff ℝ ∞ W) : Continuous (codifferential d W) := by
  apply continuous_finset_sum
  intro i hi
  have h (k : Fin 3) : ContDiff ℝ ∞ (fun p => W p i k) :=
    contDiff_pi.mp (contDiff_pi.mp hW i) k
  exact ((((smooth_coordinateDerivative d _ (h 0) i 2).continuous.neg.add
    (continuous_const.mul (h 0).continuous)).sub
    ((smooth_exp d i).continuous.mul (smooth_coordinateDerivative d _ (h 1) i 0).continuous)).sub
    ((smooth_exp d i).continuous.mul (smooth_coordinateDerivative d _ (h 2) i 1).continuous))

private theorem continuous_pairing (d : ℕ) (U W : Space d → Cotangent d)
    (hU : Continuous U) (hW : Continuous W) : Continuous (fun p => pairing d (U p) (W p)) := by
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro k hk
  exact ((continuous_apply k).comp ((continuous_apply i).comp hU)).star.mul
    ((continuous_apply k).comp ((continuous_apply i).comp hW))

private theorem integrable_measure (d : ℕ) (F : Space d → ℂ)
    (hF : Continuous F) (hc : HasCompactSupport F) : Integrable F (measure d) := by
  unfold measure
  rw [integrable_withDensity_iff_integrable_smul'
    ((smooth_density d).continuous.measurable.ennreal_ofReal) (Filter.Eventually.of_forall (fun p => ENNReal.ofReal_lt_top))]
  have hi : Integrable (fun p => density d p • F p) volume :=
    ((smooth_density d).continuous.smul hF).integrable_of_hasCompactSupport
      (μ := volume) hc.smul_left
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ density d _ from le_of_lt (Real.exp_pos _))] using hi

private theorem integral_measure (d : ℕ) (F : Space d → ℂ) :
    (∫ p, F p ∂measure d) = ∫ p, (density d p : ℂ) * F p := by
  unfold measure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((smooth_density d).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun p => ENNReal.ofReal_lt_top))]
  congr 1
  funext p
  rw [ENNReal.toReal_ofReal (show 0 ≤ density d p from le_of_lt (Real.exp_pos _))]
  exact Complex.real_smul

private theorem weighted_parts (d : ℕ) (i : Fin d) (k : Fin 3)
 (f g w : Space d → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
 (hw : ContDiff ℝ ∞ w) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
 (∫ p, w p * star (coordinateDerivative d i k f p) * g p) =
 (∫ p, star (f p) * (-w p * coordinateDerivative d i k g p - coordinateDerivative d i k w p * g p)) := by
 have hd : ∀ h : Space d → ℂ, ContDiff ℝ ∞ h → Differentiable ℝ h := fun h hh => hh.differentiable (by simp)
 have h1 := ((hw.mul ((smooth_star d f hf))).mul (smooth_coordinateDerivative d g hg i k)).continuous.integrable_of_hasCompactSupport (μ := volume)
  ((compact_star d f hfc).mul_left.mul_right)
 have h2 := (((smooth_coordinateDerivative d (fun p => w p * star (f p)) (hw.mul (smooth_star d f hf)) i k)).mul hg).continuous.integrable_of_hasCompactSupport (μ := volume)
  (hgc.mul_left)
 have h3 := ((hw.mul (smooth_star d f hf)).mul hg).continuous.integrable_of_hasCompactSupport (μ := volume) (hgc.mul_left)
 have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  (μ := volume) (v := coordinateVector d i k) h2 h1 h3
  (fun p hp => hd _ (hw.mul (smooth_star d f hf)) p) (fun p hp => hd _ hg p)
 have eq : (fun p => coordinateDerivative d i k (fun q => w q * star (f q)) p * g p) =
  (fun p => w p * star (coordinateDerivative d i k f p) * g p +
   star (f p) * coordinateDerivative d i k w p * g p) := by
  funext p
  rw [deriv_mul d i k w (fun q => star (f q)) (hd _ hw) (hd _ (smooth_star d f hf)), deriv_star]
  ring
 have ha := ((hw.mul (smooth_star d (coordinateDerivative d i k f) (smooth_coordinateDerivative d f hf i k))).mul hg).continuous.integrable_of_hasCompactSupport (μ := volume) (hgc.mul_left)
 have hb := (((smooth_star d f hf).mul (smooth_coordinateDerivative d w hw i k)).mul hg).continuous.integrable_of_hasCompactSupport (μ := volume) (hgc.mul_left)
 change (∫ p, w p * star (f p) * coordinateDerivative d i k g p) =
  -(∫ p, coordinateDerivative d i k (fun q => w q * star (f q)) p * g p) at ibp
 rw [eq, integral_add ha hb] at ibp
 have hr : (fun p => star (f p) * (-w p * coordinateDerivative d i k g p - coordinateDerivative d i k w p * g p)) =
   (fun p => -(w p * star (f p) * coordinateDerivative d i k g p) - star (f p) * coordinateDerivative d i k w p * g p) := by
  funext p; ring
 rw [hr]
 rw [integral_sub (show Integrable (fun p => -(w p * star (f p) * coordinateDerivative d i k g p)) volume from h1.neg) hb, integral_neg]
 linear_combination ibp

private theorem component_parts (d : ℕ) (i : Fin d) (k : Fin 3)
    (f g : Space d → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ p, (if k = 2 then (1 : ℂ) else (Real.exp (p (i, 2)) : ℂ)) *
        star (coordinateDerivative d i k f p) * g p ∂measure d) =
      ∫ p, star (f p) *
        (-(if k = 2 then (1 : ℂ) else (Real.exp (p (i, 2)) : ℂ)) *
          coordinateDerivative d i k g p + (if k = 2 then 2 else 0) * g p) ∂measure d := by
  rw [integral_measure, integral_measure]
  by_cases hk : k = 2
  · subst k
    have ibp := weighted_parts d i 2 f g (fun p => (density d p : ℂ)) hf hg
      (smooth_density_complex d) hfc hgc
    simp only [ite_true, one_mul]
    calc
      _ = ∫ p, (density d p : ℂ) * star (coordinateDerivative d i 2 f p) * g p := by
        congr 1; funext p; ring
      _ = _ := ibp
      _ = _ := by
        congr 1; funext p
        rw [deriv_density]
        simp only [ite_true]
        ring
  · have hw := (smooth_exp d i).mul (smooth_density_complex d)
    have hder (p : Space d) :
        coordinateDerivative d i k (fun q => (Real.exp (q (i,2)) : ℂ) * (density d q : ℂ)) p = 0 := by
      rw [coordinateDerivative_exp_mul d i k hk _ ((smooth_density_complex d).differentiable (by simp)),
        deriv_density]
      simp [hk]
    have ibp := weighted_parts d i k f g
      (fun p => (Real.exp (p (i,2)) : ℂ) * (density d p : ℂ)) hf hg hw hfc hgc
    simp only [hder, zero_mul, sub_zero] at ibp
    simp only [hk, ite_false, zero_mul, add_zero]
    calc
      _ = ∫ p, ((Real.exp (p (i,2)) : ℂ) * (density d p : ℂ)) *
          star (coordinateDerivative d i k f p) * g p := by
        congr 1; funext p; ring
      _ = _ := ibp
      _ = _ := by congr 1; funext p; ring

private theorem compact_pairing_right (d : ℕ) (U W : Space d → Cotangent d)
    (hW : HasCompactSupport W) : HasCompactSupport (fun p => pairing d (U p) (W p)) := by
  apply hW.mono
  intro p hp hn
  apply hp
  simp [pairing, hn]

 theorem first_order_green (d : ℕ) (f : Space d → ℂ) (W : Space d → Cotangent d)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    Integrable (fun p => pairing d (differential d f p) (W p)) (measure d) ∧
    Integrable (fun p => star (f p) * codifferential d W p) (measure d) ∧
    (∫ p, pairing d (differential d f p) (W p) ∂measure d) =
      ∫ p, star (f p) * codifferential d W p ∂measure d := by
  have hs (i : Fin d) (k : Fin 3) : ContDiff ℝ ∞ (fun p => W p i k) :=
    contDiff_pi.mp (contDiff_pi.mp hW i) k
  have hcs (i : Fin d) (k : Fin 3) : HasCompactSupport (fun p => W p i k) :=
    hWc.comp_left (g := fun a : Cotangent d => a i k) (by simp)
  have hleft := integrable_measure d _
    (continuous_pairing d _ W (smooth_differential d f hf).continuous hW.continuous)
    (compact_pairing_right d _ W hWc)
  have hright := integrable_measure d _
    ((smooth_star d f hf).continuous.mul (continuous_codifferential d W hW))
    (compact_star d f hfc).mul_right
  refine ⟨hleft, hright, ?_⟩
  let A (i : Fin d) (k : Fin 3) (p : Space d) :=
    star (differential d f p i k) * W p i k
  let B (i : Fin d) (p : Space d) := star (f p) *
    (-coordinateDerivative d i 2 (fun q => W q i 0) p + 2 * W p i 0 -
      (Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) p -
      (Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 1 (fun q => W q i 2) p)
  have hA (i : Fin d) (k : Fin 3) : Integrable (A i k) (measure d) := by
    apply integrable_measure d
    · exact ((smooth_star d _ (contDiff_pi.mp (contDiff_pi.mp (smooth_differential d f hf) i) k)).continuous.mul (hs i k).continuous)
    · exact (hcs i k).mul_left
  have hB (i : Fin d) : Integrable (B i) (measure d) := by
    apply integrable_measure d
    · exact (smooth_star d f hf).continuous.mul
        (((((smooth_coordinateDerivative d _ (hs i 0) i 2).continuous.neg.add
          (continuous_const.mul (hs i 0).continuous)).sub
          ((smooth_exp d i).continuous.mul (smooth_coordinateDerivative d _ (hs i 1) i 0).continuous)).sub
          ((smooth_exp d i).continuous.mul (smooth_coordinateDerivative d _ (hs i 2) i 1).continuous)))
    · exact (compact_star d f hfc).mul_right
  have hAB (i : Fin d) : (∫ p, ∑ k : Fin 3, A i k p ∂measure d) =
      ∫ p, B i p ∂measure d := by
    rw [integral_finset_sum _ (fun k hk => hA i k)]
    simp only [Fin.sum_univ_three]
    have ht := component_parts d i 2 f (fun p => W p i 0) hf (hs i 0) hfc (hcs i 0)
    have hx := component_parts d i 0 f (fun p => W p i 1) hf (hs i 1) hfc (hcs i 1)
    have hy := component_parts d i 1 f (fun p => W p i 2) hf (hs i 2) hfc (hcs i 2)
    simp only [ite_true, one_mul] at ht
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      ite_false, zero_mul, add_zero] at hx hy
    have hAe : ∀ k : Fin 3, A i k = fun p =>
      (if k = 0 then star (coordinateDerivative d i 2 f p) * W p i 0
       else if k = 1 then (Real.exp (p (i,2)) : ℂ) * star (coordinateDerivative d i 0 f p) * W p i 1
       else (Real.exp (p (i,2)) : ℂ) * star (coordinateDerivative d i 1 f p) * W p i 2) := by
      intro k; funext p
      have he : star (Real.exp (p (i,2)) : ℂ) = (Real.exp (p (i,2)) : ℂ) := by
        apply Complex.ext <;> simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero]
      fin_cases k
      · change A i 0 p = _
        simp [A, differential]
      · change A i 1 p = _
        change star ((Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 0 f p) * W p i 1 =
          (Real.exp (p (i,2)) : ℂ) * star (coordinateDerivative d i 0 f p) * W p i 1
        rw [star_mul, he]
        ring
      · change A i 2 p = _
        change star ((Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 1 f p) * W p i 2 =
          (Real.exp (p (i,2)) : ℂ) * star (coordinateDerivative d i 1 f p) * W p i 2
        rw [star_mul, he]
        ring
    rw [hAe 0, hAe 1, hAe 2]
    simp only [ite_true, ite_false, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide]
    rw [ht, hx, hy]
    have hrt : Integrable (fun p => star (f p) * (-1 * coordinateDerivative d i 2 (fun q => W q i 0) p + 2 * W p i 0)) (measure d) := by
      apply integrable_measure d _ _ (compact_star d f hfc).mul_right
      exact (smooth_star d f hf).continuous.mul
        ((continuous_const.mul (smooth_coordinateDerivative d _ (hs i 0) i 2).continuous).add
          (continuous_const.mul (hs i 0).continuous))
    have hrx : Integrable (fun p => star (f p) * (-(Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) p)) (measure d) := by
      apply integrable_measure d _ _ (compact_star d f hfc).mul_right
      exact (smooth_star d f hf).continuous.mul ((smooth_exp d i).continuous.neg.mul (smooth_coordinateDerivative d _ (hs i 1) i 0).continuous)
    have hry : Integrable (fun p => star (f p) * (-(Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 1 (fun q => W q i 2) p)) (measure d) := by
      apply integrable_measure d _ _ (compact_star d f hfc).mul_right
      exact (smooth_star d f hf).continuous.mul ((smooth_exp d i).continuous.neg.mul (smooth_coordinateDerivative d _ (hs i 2) i 1).continuous)
    rw [← integral_add hrt hrx]
    have htxy : Integrable (fun p =>
        star (f p) * (-1 * coordinateDerivative d i 2 (fun q => W q i 0) p + 2 * W p i 0) +
        star (f p) * (-(Real.exp (p (i,2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) p)) (measure d) := hrt.add hrx
    rw [← integral_add htxy hry]
    congr 1; funext p; dsimp [B]; ring
  change (∫ p, ∑ i : Fin d, ∑ k : Fin 3, A i k p ∂measure d) = _
  rw [integral_finset_sum _ (fun i hi => integrable_finset_sum _ (fun k hk => hA i k))]
  have hBe : (fun p => star (f p) * codifferential d W p) = fun p => ∑ i : Fin d, B i p := by
    funext p; simp only [codifferential, Finset.mul_sum]; rfl
  rw [hBe, integral_finset_sum _ (fun i hi => hB i)]
  exact Finset.sum_congr rfl (fun i hi => hAB i)

theorem codifferential_differential (d : ℕ) (hd : 1 ≤ d)
    (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) :
    codifferential d (differential d f) = laplacian d f := by
  funext p
  unfold codifferential laplacian
  apply Finset.sum_congr rfl
  intro i hi
  simp only [differential, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_def,
    Fin.succ_zero_eq_one]
  rw [coordinateDerivative_exp_mul d i 0 (by decide)
      (coordinateDerivative d i 0 f) ((smooth_coordinateDerivative d f hf i 0).differentiable (by simp)),
    coordinateDerivative_exp_mul d i 1 (by decide)
      (coordinateDerivative d i 1 f) ((smooth_coordinateDerivative d f hf i 1).differentiable (by simp))]
  rw [show (Real.exp (2 * p (i, 2)) : ℂ) =
      (Real.exp (p (i, 2)) : ℂ) * (Real.exp (p (i, 2)) : ℂ) by
    rw [two_mul, Real.exp_add, Complex.ofReal_mul]]
  ring

end HyperbolicChart

open MeasureTheory HyperbolicChart

theorem kp_cont_hyperbolic_chart_green (d : ℕ) (hd : 1 ≤ d)
    (Ω : Set (HyperbolicChart.Space d)) (hΩ : IsOpen Ω)
    (f g : HyperbolicChart.Space d → ℂ)
    (W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    (hf : HyperbolicChart.IsTestFunction d Ω f)
    (hg : HyperbolicChart.IsTestFunction d Ω g)
    (hW : HyperbolicChart.IsTestField d Ω W)
    (c : ℝ) (hc : 0 < c) (m : ℕ) (hm : 1 ≤ m) :
    let μ := HyperbolicChart.chartMeasure d c m
    IntegrableOn (fun p => pairing d (differential d f p) (W p)) Ω μ ∧
    IntegrableOn (fun p => star (f p) * codifferential d W p) Ω μ ∧
    IntegrableOn (fun p => star (f p) * laplacian d g p) Ω μ ∧
    IntegrableOn (fun p => pairing d (differential d f p) (differential d g p)) Ω μ ∧
    (∫ p in Ω, pairing d (differential d f p) (W p) ∂μ) =
      (∫ p in Ω, star (f p) * codifferential d W p ∂μ) ∧
    (∫ p in Ω, star (f p) * laplacian d g p ∂μ) =
      (∫ p in Ω, pairing d (differential d f p) (differential d g p) ∂μ) := by
  dsimp only
  obtain ⟨hf, hfc, hfs⟩ := hf
  obtain ⟨hg, hgc, hgs⟩ := hg
  obtain ⟨hW, hWc, hWs⟩ := hW
  have hfg := HyperbolicChart.first_order_green d f (differential d g) hf hfc
    (HyperbolicChart.smooth_differential d g hg) (HyperbolicChart.compact_differential d g hgc)
  have hfW := HyperbolicChart.first_order_green d f W hf hfc hW hWc
  rw [codifferential_differential d hd g hg] at hfg
  have int (F : Space d → ℂ) (hF : Integrable F (measure d)) :
      IntegrableOn F Ω (chartMeasure d c m) :=
    (hF.smul_measure ENNReal.ofReal_ne_top).integrableOn
  have eq (F : Space d → ℂ) (hF : ∀ p ∉ Ω, F p = 0) :
      (∫ p in Ω, F p ∂chartMeasure d c m) =
        (ENNReal.ofReal (c / (m : ℝ))).toReal • ∫ p, F p ∂measure d := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hF]
    exact integral_smul_measure _ _
  have fzero (p : Space d) (hp : p ∉ Ω) : f p = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => hp (hfs hs)
  have dzero (p : Space d) (hp : p ∉ Ω) : differential d f p = 0 :=
    HyperbolicChart.differential_zero_off d f p (fun hs => hp (hfs hs))
  have pzero (U : Space d → Cotangent d) (p : Space d) (hp : p ∉ Ω) :
      pairing d (differential d f p) (U p) = 0 := by
    simp [dzero p hp, pairing]
  have szero (F : Space d → ℂ) (p : Space d) (hp : p ∉ Ω) : star (f p) * F p = 0 := by
    rw [fzero p hp, star_zero, zero_mul]
  refine ⟨int _ hfW.1, int _ hfW.2.1, int _ hfg.2.1, int _ hfg.1, ?_, ?_⟩
  · rw [eq _ (pzero W), eq _ (szero (codifferential d W)), hfW.2.2]
  · rw [eq _ (szero (laplacian d g)), eq _ (pzero (differential d g)), hfg.2.2]

end DedekindZetaZeroFree

end
