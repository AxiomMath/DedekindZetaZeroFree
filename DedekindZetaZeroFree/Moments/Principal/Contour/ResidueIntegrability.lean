module

public import DedekindZetaZeroFree.Moments.Principal.Contour.KernelMajorants
public import DedekindZetaZeroFree.Analysis.Integration.NormalizedFubiniMajorant

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalResidueIntegrability

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem consequences (Fn : ℝ → ℝ × ℝ → ℂ) (E : ℝ)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g) (hg0 : ∀ p, 0 ≤ g p)
    (hc : ∀ Z : ℝ, 2 ≤ Z → Continuous (Fn Z))
    (hb : ∀ Z : ℝ, 2 ≤ Z → ∀ p, ‖Fn Z p‖ ≤ Z ^ E * g p) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Integrable (Fn Z) ∧
      Integrable (fun t : ℝ => NormalizedFubiniMajorant.c * ∫ s : ℝ, Fn Z (t, s)) ∧
      ‖NormalizedFubiniMajorant.c * ∫ t : ℝ, NormalizedFubiniMajorant.c * ∫ s : ℝ, Fn Z (t, s)‖
        ≤ C * Z ^ E := by
  refine ⟨((2 * Real.pi)⁻¹) ^ 2 * (∫ p, g p) + 1, ?_, ?_⟩
  · have : 0 ≤ ∫ p, g p := integral_nonneg hg0
    positivity
  intro Z hZ
  have hZ0 : 0 ≤ Z ^ E := Real.rpow_nonneg (by linarith) _
  have hb' : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn Z p‖ ≤ Z ^ E * g p :=
    Filter.Eventually.of_forall (hb Z hZ)
  refine ⟨NormalizedFubiniMajorant.integrable_of_majorant2_continuous _ (hc Z hZ) g hg _
    (hb Z hZ), NormalizedFubiniMajorant.outer_integrable2 _ (hc Z hZ).aestronglyMeasurable g hg _
    hb', ?_⟩
  refine (NormalizedFubiniMajorant.norm_double_le _ (hc Z hZ).aestronglyMeasurable g hg _ hZ0
    hb').trans ?_
  have : 0 ≤ ∫ p, g p := integral_nonneg hg0
  have h2 : 0 ≤ ((2 * Real.pi)⁻¹) ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg h2 this) hZ0]

private def bodyR (u : D.Row) (ξ z : ℂ) (Z : ℝ) : ℂ :=
  (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
    Complex.exp ((ξ + z - 1) ^ 2) * D.M z *
      (D.zetaSCont (6 * z) * EulerDomain.Hu D u ξ 1 z / D.Llam u ξ)

private theorem wResidue_eq_bodyR (u : D.Row) (hu : u.u = 1) (ξ z : ℂ) (Z : ℝ) (hZ : 2 ≤ Z)
    (hξ : 1 < ξ.re) (hz : 1 / 20 - EulerDomain.pad ≤ z.re) (hz6 : 6 * z ≠ 1) :
    wResidueLocal D u ξ z Z = Spectral.RS D * D.W1Hat 1 * bodyR D u ξ z Z := by
  rw [PrincipalResidueFormulas.wResidue_eq D u hu ξ z Z (by linarith) hξ hz hz6,
    PrincipalResidueFormulas.remainingKernel_principal D u hu]
  rfl

private theorem abstract_slice (H : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ)
    (hd : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2) (ξ, 1, z)) :
    ContinuousAt (fun p : ℂ × ℂ => H p.1 1 p.2) (ξ, z) := by
  have hc : ContinuousAt (fun p : ℂ × ℂ => ((p.1, (1 : ℂ), p.2) : ℂ × ℂ × ℂ)) (ξ, z) := by
    fun_prop
  exact ContinuousAt.comp (g := fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2)
    (f := fun p : ℂ × ℂ => ((p.1, (1 : ℂ), p.2) : ℂ × ℂ × ℂ)) hd.continuousAt hc

private theorem abstract_comp {α : Type*} [TopologicalSpace α] (G : ℂ × ℂ → ℂ) (g : α → ℂ × ℂ)
    (a : α) (hG : ContinuousAt G (g a)) (hg : ContinuousAt g a) : ContinuousAt (fun t => G (g t)) a :=
  ContinuousAt.comp hG hg

set_option maxHeartbeats 1000000 in
private theorem bodyR_continuousAt (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z)
    (ξ z : ℂ) (hξ : 1 < ξ.re) (hz : 1 / 20 - EulerDomain.pad ≤ z.re) (hz0 : 0 < z.re)
    (hz6 : 6 * z ≠ 1) :
    ContinuousAt (fun p : ℂ × ℂ => bodyR D u p.1 p.2 Z) (ξ, z) := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, Complex.one_re]
    simp only [EulerDomain.pad] at hz
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have h1 : ContinuousAt (fun p : ℂ × ℂ =>
      (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + p.1 - 1 + (Scales.smoothingExponent : ℂ) * p.2)) (ξ, z) :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl hZc)
  have h2 : ContinuousAt (fun p : ℂ × ℂ => Complex.exp ((p.1 + p.2 - 1) ^ 2)) (ξ, z) :=
    (by fun_prop : Continuous fun p : ℂ × ℂ => Complex.exp ((p.1 + p.2 - 1) ^ 2)).continuousAt
  have hM : ContinuousAt D.M z :=
    (D.M_differentiableOn.differentiableAt (hMopen.mem_nhds hz0)).continuousAt
  have h3 : ContinuousAt (fun p : ℂ × ℂ => D.M p.2) (ξ, z) := hM.comp_of_eq continuousAt_snd rfl
  have h6z : (6 * z) ∈ ({s : ℂ | (0 : ℝ) < s.re} \ {(1 : ℂ)}) :=
    ⟨by
      have hre : (6 * z).re = 6 * z.re := by simp
      show (0 : ℝ) < (6 * z).re
      rw [hre]; linarith, fun h => hz6 h⟩
  have hζA : ContinuousAt D.zetaSCont (6 * z) :=
    (PrincipalResidueFormulas.zetaSCont_analytic D (6 * z) h6z).continuousAt
  have h6 : ContinuousAt (fun p : ℂ × ℂ => 6 * p.2) (ξ, z) := continuousAt_const.mul continuousAt_snd
  have h4 : ContinuousAt (fun p : ℂ × ℂ => D.zetaSCont (6 * p.2)) (ξ, z) :=
    hζA.comp_of_eq h6 rfl
  have hHc : ContinuousAt (fun p : ℂ × ℂ => EulerDomain.Hu D u p.1 1 p.2) (ξ, z) := by
    have hd : DifferentiableAt ℂ
        (fun p : ℂ × ℂ × ℂ => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, 1, z) :=
      (EulerDomain.Hu_normal_convergence D u).2.2.1.differentiableAt
        (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    exact abstract_slice (EulerDomain.Hu D u) ξ z hd
  have hLne : D.Llam u ξ ≠ 0 := RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ hξ
  have hL : ContinuousAt (fun p : ℂ × ℂ => D.Llam u p.1) (ξ, z) := by
    have hξA : ξ ∈ ({s : ℂ | (0 : ℝ) < s.re} \ {(1 : ℂ)}) :=
      ⟨by show (0 : ℝ) < ξ.re; linarith, fun h => by
        have h' : ξ = 1 := h
        rw [h'] at hξ; norm_num at hξ⟩
    have hcz : ContinuousAt (fun p : ℂ × ℂ => D.zetaSCont p.1) (ξ, z) :=
      (PrincipalResidueFormulas.zetaSCont_analytic D ξ hξA).continuousAt.comp_of_eq continuousAt_fst rfl
    refine hcz.congr ?_
    have hopen : IsOpen {p : ℂ × ℂ | 1 < p.1.re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
    filter_upwards [hopen.mem_nhds hξ] with q hq
    have hq' : 1 < q.1.re := hq
    show D.zetaSCont q.1 = D.Llam u q.1
    exact (PrincipalResidueFormulas.Llam_principal_eq D u hu q.1 (by linarith)
      (by intro h; rw [h] at hq'; norm_num at hq')).symm
  have hdiv : ContinuousAt (fun p : ℂ × ℂ =>
      D.zetaSCont (6 * p.2) * EulerDomain.Hu D u p.1 1 p.2 / D.Llam u p.1) (ξ, z) :=
    (h4.mul hHc).div hL hLne
  exact ((h1.mul h2).mul h3).mul hdiv

set_option maxHeartbeats 1000000 in

private theorem wResidue_line_continuous (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z)
    (c : ℝ) (hc : 1 / 20 - EulerDomain.pad ≤ c) (hc0 : 0 < c) (hc6 : 6 * c ≠ 1) :
    Continuous (fun t : ℝ × ℝ =>
      wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) := by
  have hξ : ∀ t : ℝ × ℝ, 1 < ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I).re := by
    intro t
    norm_num [Scales.rightLine, Scales.contourOffset]
  have hz : ∀ t : ℝ × ℝ, 1 / 20 - EulerDomain.pad ≤ (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I).re := by
    intro t
    simpa using hc
  have hz0 : ∀ t : ℝ × ℝ, 0 < (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I).re := by
    intro t
    simpa using hc0
  have hz6 : ∀ t : ℝ × ℝ, 6 * (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    norm_num at this
    apply hc6
    linarith
  have hc' : Continuous (fun t : ℝ × ℝ =>
      (((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I), (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I))) := by
    fun_prop
  have hf : Continuous (fun t : ℝ × ℝ => Spectral.RS D * D.W1Hat 1 *
      bodyR D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) := by
    refine continuous_iff_continuousAt.2 fun t => ContinuousAt.mul continuousAt_const ?_
    exact abstract_comp (fun p : ℂ × ℂ => bodyR D u p.1 p.2 Z)
      (fun t : ℝ × ℝ => (((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I),
        (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I))) t
      (bodyR_continuousAt D u hu Z hZ ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        (((c : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) (hξ t) (hz t) (hz0 t) (hz6 t))
      hc'.continuousAt
  exact hf.congr (fun t => (wResidue_eq_bodyR D u hu _ _ Z hZ (hξ t) (hz t) (hz6 t)).symm)

theorem wResidue_continuous_z (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    Continuous (fun t : ℝ × ℝ =>
      wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        (((1 / 20 : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) :=
  wResidue_line_continuous D u hu Z hZ (1 / 20) (by norm_num [EulerDomain.pad])
    (by norm_num) (by norm_num)

theorem wResidue_continuous_w (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    Continuous (fun t : ℝ × ℝ =>
      wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) :=
  wResidue_line_continuous D u hu Z hZ (1 / 6 + Scales.contourOffset)
    (by norm_num [EulerDomain.pad, Scales.contourOffset]) (by norm_num [Scales.contourOffset])
    (by norm_num [Scales.contourOffset])

theorem residue_integrability_z (u : D.Row) (hu : u.u = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Continuous (fun t : ℝ × ℝ =>
        wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          (((1 / 20 : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) ∧
      Integrable (fun t : ℝ × ℝ =>
        wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          (((1 / 20 : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) ∧
      Integrable (fun t : ℝ =>
        comparisonVerticalIntegral (1 / 20)
          (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) z Z)) ∧
      ‖comparisonVerticalIntegral Scales.rightLine (fun ξ =>
          comparisonVerticalIntegral (1 / 20) (fun z => wResidueLocal D u ξ z Z))‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine 1 (1 / 20)) := by
  obtain ⟨g, hg, hg0, hb⟩ := PrincipalKernelMajorants.wResidue_majorant_z D u hu
  obtain ⟨C, hC, h⟩ := consequences
    (fun Z t => wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
      (((1 / 20 : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) _ g hg hg0
    (fun Z hZ => wResidue_continuous_z D u hu Z hZ) (fun Z hZ p => hb Z hZ p)
  refine ⟨C, hC, fun Z hZ => ⟨wResidue_continuous_z D u hu Z hZ, ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := h Z hZ
  exact ⟨h1, h2, h3⟩

theorem residue_integrability_w (u : D.Row) (hu : u.u = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      Continuous (fun t : ℝ × ℝ =>
        wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) ∧
      Integrable (fun t : ℝ × ℝ =>
        wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) ∧
      Integrable (fun t : ℝ =>
        comparisonVerticalIntegral (1 / 6 + Scales.contourOffset)
          (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) z Z)) ∧
      ‖comparisonVerticalIntegral Scales.rightLine (fun ξ =>
          comparisonVerticalIntegral (1 / 6 + Scales.contourOffset)
            (fun z => wResidueLocal D u ξ z Z))‖ ≤
        C * Z ^ (Scales.kernelExponent Scales.rightLine 1 (1 / 6 + Scales.contourOffset)) := by
  obtain ⟨g, hg, hg0, hb⟩ := PrincipalKernelMajorants.wResidue_majorant_w D u hu
  obtain ⟨C, hC, h⟩ := consequences
    (fun Z t => wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
      (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) _ g hg hg0
    (fun Z hZ => wResidue_continuous_w D u hu Z hZ) (fun Z hZ p => hb Z hZ p)
  refine ⟨C, hC, fun Z hZ => ⟨wResidue_continuous_w D u hu Z hZ, ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := h Z hZ
  exact ⟨h1, h2, h3⟩

end

end DedekindZetaZeroFree.Quantitative.PrincipalResidueIntegrability
