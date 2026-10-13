module

public import DedekindZetaZeroFree.Moments.Principal.Contour.RightKernelBound
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelHolomorphy

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalIntegratedXiControls

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.EulerDomain
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions Set Filter Complex
open MeasureTheory
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma nested_norm_le (K : ℝ → ℝ → ℂ) (f : ℝ × ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : Integrable f) (hK : ∀ s t, ‖K s t‖ ≤ c * f (s, t)) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, K s t‖ ≤
      ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * c) * ∫ p, f p := by
  have hg : Integrable (fun t : ℝ => ∫ s : ℝ, f (s, t)) := hf.integral_prod_right
  have hslice : ∀ᵐ t ∂(volume : Measure ℝ), Integrable (fun s : ℝ => f (s, t)) :=
    hf.prod_left_ae
  have hIz : ∀ᵐ t ∂(volume : Measure ℝ), ‖∫ s : ℝ, K s t‖ ≤ c * ∫ s : ℝ, f (s, t) := by
    filter_upwards [hslice] with t ht
    calc ‖∫ s : ℝ, K s t‖ ≤ ∫ s : ℝ, ‖K s t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ, c * f (s, t) :=
          integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _)
            (ht.const_mul c) (Eventually.of_forall fun s => hK s t)
      _ = c * ∫ s : ℝ, f (s, t) := integral_const_mul _ _
  set a : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖ with ha
  have h1 : ‖∫ t : ℝ, (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, K s t‖ ≤
      ∫ t : ℝ, a * (c * ∫ s : ℝ, f (s, t)) := by
    calc ‖∫ t : ℝ, (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, K s t‖
        ≤ ∫ t : ℝ, ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, K s t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, a * (c * ∫ s : ℝ, f (s, t)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            ((hg.const_mul c).const_mul a) ?_
          filter_upwards [hIz] with t ht
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have hsym : ∫ p, f p = ∫ t : ℝ, ∫ s : ℝ, f (s, t) := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_symm f hf
  calc ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, K s t‖
      = a * ‖∫ t : ℝ, (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, K s t‖ := norm_mul _ _
    _ ≤ a * ∫ t : ℝ, a * (c * ∫ s : ℝ, f (s, t)) :=
        mul_le_mul_of_nonneg_left (h1) (norm_nonneg _)
    _ = a * (a * c) * ∫ p, f p := by
        rw [integral_const_mul, integral_const_mul, hsym]
        ring

private def holoSet : Set Coordinates :=
  {p | Scales.rightLine - Scales.contourOffset / 2 < p.1.re ∧ 1 + Scales.contourOffset / 2 < p.2.1.re ∧
    1 / 6 + Scales.contourOffset / 2 < p.2.2.re}

private def holoV : Set ℂ :=
  {ξ : ℂ | Scales.rightLine - Scales.contourOffset / 2 < ξ.re ∧ ξ.re < 5}

set_option maxHeartbeats 1000000 in

theorem Iwz_xi_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    DifferentiableOn ℂ (fun ξ => Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ξ)
      (comparisonClosedStrip Scales.rightLine 4) := by
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hpad : pad = 1 / 1000000 := rfl
  have hδpos : 0 < Scales.contourOffset := by rw [hd]; norm_num
  have hvpos : (0 : ℝ) < 1 / 6 + Scales.contourOffset := by linarith
  have hV : IsOpen holoV :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hO : IsOpen holoSet :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_fst.comp continuous_snd))).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_snd.comp continuous_snd))))
  have hOsub : holoSet ⊆ (paddedBox₂ ∩ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re} ∩
      {p : Coordinates | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}) \ {p : Coordinates | p.2.1 = 1} := by
    rintro p ⟨h1, h2, h3⟩
    refine Set.mem_diff_of_mem (Set.mem_inter (Set.mem_inter ?_ h1) h3) ?_
    · simp only [paddedBox₂, box, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
    · intro h
      have h' : p.2.1.re = 1 := by
        simp only [Set.mem_setOf_eq] at h
        rw [h]; simp
      linarith
  have hdiffO : DifferentiableOn ℂ (fun p : Coordinates => kern D u Z p.1 p.2.1 p.2.2) holoSet :=
    (DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31.kern_differentiableOn D u hu Z (by linarith)).mono hOsub
  have hwre : ∀ s : ℝ, (((Scales.rightLine : ℝ) : ℂ) + (s : ℂ) * Complex.I).re = Scales.rightLine :=
    fun s => by simp
  have hzre : ∀ t : ℝ, (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * Complex.I).re
      = 1 / 6 + Scales.contourOffset := fun t => by simp
  have memO : ∀ ξ ∈ holoV, ∀ s t : ℝ,
      (ξ, ((Scales.rightLine : ℝ) : ℂ) + (s : ℂ) * Complex.I,
        ((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈ holoSet := by
    intro ξ hξ s t
    have hξ' : Scales.rightLine - Scales.contourOffset / 2 < ξ.re := hξ.1
    show Scales.rightLine - Scales.contourOffset / 2 < ξ.re ∧
      1 + Scales.contourOffset / 2 < (((Scales.rightLine : ℝ) : ℂ) + (s : ℂ) * Complex.I).re ∧
      1 / 6 + Scales.contourOffset / 2 < (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * Complex.I).re
    rw [hwre, hzre]
    exact ⟨hξ', by linarith, by linarith⟩
  have hdiffPt : ∀ ξ ∈ holoV, ∀ s t : ℝ, DifferentiableAt ℂ
      (fun x : ℂ => kern D u Z x (((Scales.rightLine : ℝ) : ℂ) + (s : ℂ) * Complex.I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ξ := by
    intro ξ hξ s t
    have hnhds := hO.mem_nhds (memO ξ hξ s t)
    have hf := hdiffO.differentiableAt hnhds
    have hg : DifferentiableAt ℂ (fun x : ℂ => ((x, (((Scales.rightLine : ℝ) : ℂ) + (s : ℂ) * Complex.I,
        ((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * Complex.I)) : Coordinates)) ξ := by
      fun_prop
    exact hf.comp ξ hg
  have hcont : ∀ ξ ∈ holoV, Continuous (fun p : ℝ × ℝ =>
      kern D u Z ξ (((Scales.rightLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I)) := by
    intro ξ hξ
    have hc : ContinuousOn (fun p : Coordinates => kern D u Z p.1 p.2.1 p.2.2) holoSet :=
      hdiffO.continuousOn
    have hmap : Continuous (fun p : ℝ × ℝ => ((ξ, ((Scales.rightLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I,
        ((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I) : Coordinates)) := by
      fun_prop
    have hcomp := hc.comp_continuous hmap (fun p => memO ξ hξ p.2 p.1)
    exact hcomp
  have hmaj : ∀ ξ₀ ∈ holoV, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ holoV ∧ ∃ C k : ℝ,
      0 ≤ C ∧ 0 ≤ k ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖kern D u Z ξ (((Scales.rightLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)
            (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
          C * WeightConvolution.weightModulus D ξ (1 / 6 + Scales.contourOffset) Scales.rightLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
    intro ξ₀ hξ₀
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV ξ₀ hξ₀
    obtain ⟨Cc, hCc, k, hk, hbd⟩ := DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31.kernel_weight_bound D u hu Z hZ
    refine ⟨r, hr, hball, Cc, k, hCc, hk, fun ξ hξ p => ?_⟩
    have hξV : ξ ∈ holoV := hball hξ
    exact hbd ξ hξV.1.le hξV.2.le p.1 p.2
  have key := RowKernelHolomorphy.differentiableOn_nested_integral D holoV hV
    (fun ξ w z => kern D u Z ξ w z) Scales.rightLine (1 / 6 + Scales.contourOffset) hvpos hdiffPt hcont hmaj
  have hsub : comparisonClosedStrip Scales.rightLine 4 ⊆ holoV := by
    intro ξ hξ
    simp only [comparisonClosedStrip, Set.mem_setOf_eq] at hξ
    show Scales.rightLine - Scales.contourOffset / 2 < ξ.re ∧ ξ.re < 5
    constructor <;> linarith [hξ.1, hξ.2]
  exact key.mono hsub

set_option maxHeartbeats 1000000 in

theorem Iwz_xi_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    DecayOn (fun ξ => Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ξ) Scales.rightLine 4 := by
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hδpos : 0 < Scales.contourOffset := by rw [hd]; norm_num
  have hvpos : (0 : ℝ) < 1 / 6 + Scales.contourOffset := by linarith
  intro B hB
  obtain ⟨C0, hC0, k, hk, hbd⟩ := DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31.kernel_weight_bound D u hu Z hZ
  obtain ⟨Cw, hCw0, hw⟩ := WeightConvolution.weight_kernel_decay D (1 / 6 + Scales.contourOffset)
    (1 / 6 + Scales.contourOffset) Scales.rightLine Scales.rightLine (Scales.rightLine - Scales.contourOffset / 2) 5 hvpos le_rfl le_rfl
    (by linarith) B k hB hk
  refine ⟨‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * C0) * Cw, 0, ?_⟩
  intro x hx y _
  have hxre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have hξ0 : Scales.rightLine - Scales.contourOffset / 2 ≤ ((x : ℂ) + (y : ℂ) * Complex.I).re := by
    rw [hxre]; linarith [hx.1]
  have hξ1 : ((x : ℂ) + (y : ℂ) * Complex.I).re ≤ 5 := by
    rw [hxre]; linarith [hx.2]
  obtain ⟨hint, hwb⟩ := hw ((x : ℂ) + (y : ℂ) * Complex.I) hξ0 hξ1 (1 / 6 + Scales.contourOffset)
    Scales.rightLine le_rfl le_rfl le_rfl le_rfl
  have hnorm := nested_norm_le
    (fun s t => kern D u Z ((x : ℂ) + (y : ℂ) * Complex.I) (((Scales.rightLine : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (s : ℂ) * Complex.I))
    (fun p => WeightConvolution.weightModulus D ((x : ℂ) + (y : ℂ) * Complex.I)
      (1 / 6 + Scales.contourOffset) Scales.rightLine p * (2 + |p.1| + |p.2| + |((x : ℂ) + (y : ℂ) * Complex.I).im|) ^ k)
    C0 hC0 hint (fun s t => by
      have := hbd ((x : ℂ) + (y : ℂ) * Complex.I) hξ0 hξ1 s t
      simpa only [mul_assoc] using this)
  have hnorm' : ‖Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * C0) *
        ∫ p : ℝ × ℝ, WeightConvolution.weightModulus D ((x : ℂ) + (y : ℂ) * Complex.I)
          (1 / 6 + Scales.contourOffset) Scales.rightLine p * (2 + |p.1| + |p.2| + |((x : ℂ) + (y : ℂ) * Complex.I).im|) ^ k :=
    hnorm
  have hpos : 0 ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * C0) := by positivity
  show ‖Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ _
  calc ‖Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * C0) *
          (Cw * (1 + |((x : ℂ) + (y : ℂ) * Complex.I).im|) ^ (-B)) :=
        hnorm'.trans (mul_le_mul_of_nonneg_left hwb hpos)
    _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * C0) * Cw * (1 + |y|) ^ (-B) := by
        rw [him]; ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalIntegratedXiControls
