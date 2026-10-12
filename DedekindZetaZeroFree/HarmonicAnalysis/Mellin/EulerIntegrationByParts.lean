module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicEndpointIntegrability

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ContDiff Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor
namespace LogMellinPhysical

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}

private theorem contDiffOn_eulerIter {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0)) :
    ∀ j : ℕ, ContDiffOn ℝ ∞ (EulerIter j f) (Set.Ioi 0) := by
  intro j
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    have hderiv : ContDiffOn ℝ ∞ (deriv (EulerIter j f)) (Set.Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp ih).2
    have hmul : ContDiffOn ℝ ∞ (fun x : ℝ => (x : ℂ) * deriv (EulerIter j f) x)
        (Set.Ioi 0) :=
      (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).contDiffOn.mul hderiv
    exact hmul.congr (fun x hx => EulerIter_succ_of_pos j f x hx)

private theorem cpow_sub_one_mul (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have h1 : (x : ℂ) ^ s = (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by
    rw [← Complex.cpow_add (s - 1) 1 hx0, show s - 1 + 1 = s by ring]
  rw [h1, Complex.cpow_one]

theorem euler_succ_mellin_eq (h : LogMellinPhysical f δ P) (j : ℕ)
    (s : ℂ) (hs : 0 < s.re) :
    mellin (EulerIter (j + 1) f) s = -s * mellin (EulerIter j f) s := by
  have hsne : s ≠ 0 := by rintro rfl; simp at hs
  have hg : ContDiffOn ℝ ∞ (EulerIter j f) (Set.Ioi 0) := contDiffOn_eulerIter h.contDiffOn j
  have hgd : DifferentiableOn ℝ (EulerIter j f) (Set.Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hg).1
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (EulerIter j f) (deriv (EulerIter j f) x) x :=
    fun x hx => (hgd.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x :=
    fun x hx => hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hsne
  have hpt : ∀ x : ℝ, 0 < x →
      (x : ℂ) ^ (s - 1) * EulerIter (j + 1) f x = (x : ℂ) ^ s * deriv (EulerIter j f) x := by
    intro x hx
    rw [EulerIter_succ_of_pos j f x hx, ← mul_assoc, cpow_sub_one_mul s hx]
  have hconv : MellinConvergent (EulerIter (j + 1) f) s := euler_mellinConvergent h (j + 1) s hs
  have huv' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv (EulerIter j f) x)
      (Set.Ioi 0) := by
    rw [MellinConvergent] at hconv
    refine hconv.congr_fun (fun x hx => ?_) measurableSet_Ioi
    show (x : ℂ) ^ (s - 1) * EulerIter (j + 1) f x = _
    exact hpt x hx
  have hu'v : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * EulerIter j f x)
      (Set.Ioi 0) := by
    have h0 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * EulerIter j f x)
        (Set.Ioi 0) := by
      have := euler_mellinConvergent h j s hs
      simpa only [MellinConvergent, smul_eq_mul] using this
    have h1 : Integrable (fun x : ℝ => s * ((x : ℂ) ^ (s - 1) * EulerIter j f x))
        (volume.restrict (Set.Ioi 0)) := h0.const_mul s
    simpa only [mul_assoc, IntegrableOn] using h1
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
    (u := fun x : ℝ => (x : ℂ) ^ s) (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (v := EulerIter j f) (v' := deriv (EulerIter j f)) (a' := 0) (b' := 0)
    hu hv huv' hu'v (euler_cpow_tendsto_origin h j s hs) (euler_cpow_tendsto_atTop h j s hs)
  have hcongr : (∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * EulerIter (j + 1) f x)
      = ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ s * deriv (EulerIter j f) x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact hpt x hx
  have hkey2 : (∫ x in Set.Ioi (0 : ℝ), (s * (x : ℂ) ^ (s - 1)) * EulerIter j f x)
      = s * ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * EulerIter j f x := by
    simp only [mul_assoc]
    rw [integral_const_mul]
  simp only [mellin, smul_eq_mul]
  rw [hcongr, key, hkey2]
  ring

theorem euler_mellin_eq (h : LogMellinPhysical f δ P) (n : ℕ)
    (s : ℂ) (hs : 0 < s.re) :
    mellin (EulerIter n f) s = (-s) ^ n * mellin f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [euler_succ_mellin_eq h n s hs, ih, pow_succ]
    ring

end LogMellinPhysical
end DedekindZetaZeroFree.LargeSieve.Vendor

end
