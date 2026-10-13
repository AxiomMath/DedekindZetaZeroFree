module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralRegularity
public import DedekindZetaZeroFree.Moments.Principal.Contour.PointwiseDecay
public import DedekindZetaZeroFree.Moments.Principal.Contour.IntegratedWControls
public import DedekindZetaZeroFree.Moments.Principal.Contour.IntegratedXiControls

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalStripControls

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions Set Filter Complex
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def DecayOn (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C T0 : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-B)

def kern (u : D.Row) (Z : ℝ) (ξ w z : ℂ) : ℂ := kernelWith D (rowContLocal D) u ξ w z Z

def Iz (u : D.Row) (Z v : ℝ) (ξ w : ℂ) : ℂ :=
  comparisonVerticalIntegral v (fun z => kern D u Z ξ w z)

def Iwz (u : D.Row) (Z y v : ℝ) (ξ : ℂ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u Z v ξ w)

def wResidueExplicit (u : D.Row) (ξ z : ℂ) (Z : ℝ) : ℂ :=
  Spectral.RS D * D.W1Hat 1 * PrincipalResidueFormulas.remainingKernel D u ξ z Z

def zResidueExplicit (ξ : ℂ) (Z : ℝ) : ℂ :=
  Spectral.c₀ D * (Z : ℂ) ^ (ξ - 61 / 100) * Spectral.G D ξ

theorem one_lt_x₁ : (1 : ℝ) < Scales.rightLine := by
  unfold Scales.rightLine Scales.contourOffset; norm_num

theorem strip_re_one_lt {a b : ℝ} (ha : Scales.rightLine ≤ a) {s : ℂ}
    (hs : s ∈ comparisonClosedStrip a b) : 1 < s.re :=
  lt_of_lt_of_le one_lt_x₁ (ha.trans hs.1)

theorem re_x₁_line (s : ℝ) : (((Scales.rightLine : ℂ) + (s : ℂ) * I)).re = Scales.rightLine := by
  simp

theorem re_z_line (t : ℝ) :
    ((((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)).re = 1 / 6 + Scales.contourOffset := by
  simp

theorem six_mul_ne_one_of_re {z : ℂ} (h : z.re ≠ 1 / 6) : 6 * z ≠ 1 := by
  intro h1
  apply h
  have h2 := congrArg Complex.re h1
  have h3 : (6 * z).re = 6 * z.re := by simp
  rw [h3] at h2
  simp at h2
  linarith

variable {D} in

theorem kern_w_tendsto (u : D.Row) (hu : u.u = 1) (ξ z : ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hξ : 1 < ξ.re) (hz : 1 / 20 - EulerDomain.pad ≤ z.re) (hz6 : 6 * z ≠ 1) :
    Tendsto (fun w : ℂ => (w - 1) * kernelWith D (rowContLocal D) u ξ w z Z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (Spectral.RS D * D.W1Hat 1 * PrincipalResidueFormulas.remainingKernel D u ξ z Z)) := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hmem : ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, Complex.one_re]
    simp only [EulerDomain.pad] at hz
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hHu : ContinuousAt (fun w : ℂ => EulerDomain.Hu D u ξ w z) 1 := by
    have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
    have hat : DifferentiableAt ℂ
        (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, 1, z) :=
      hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    have hc : Continuous fun w : ℂ => ((ξ, w, z) : EulerDomain.Coordinates) := by fun_prop
    exact ContinuousAt.comp (f := fun w : ℂ => ((ξ, w, z) : EulerDomain.Coordinates)) (x := 1)
      hat.continuousAt hc.continuousAt
  have hW : Continuous D.W1Hat :=
    (ProbeSheet.MellinProof.realWeight_mellin_differentiable D.recipe.probe.W1).continuous
  have hpow : ContinuousAt (fun w : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))) 1 :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl hZc)
  have hQ := (hpow.mul hW.continuousAt).mul hHu
  have hlim := ((Spectral.RS_spec D).mul (hQ.tendsto.mono_left nhdsWithin_le_nhds)).mul_const
    (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * (D.q u : ℂ) ^ (-z) *
      (D.zetaSCont (6 * z) / D.Llam u ξ))
  have hev : ∀ᶠ w in nhdsWithin (1 : ℂ) {1}ᶜ,
      ((w - 1) * D.zetaSCont w * ((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
          (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) * D.W1Hat w *
          EulerDomain.Hu D u ξ w z)) *
        (Complex.exp ((ξ + z - 1) ^ 2) * D.M z * (D.q u : ℂ) ^ (-z) *
          (D.zetaSCont (6 * z) / D.Llam u ξ)) =
      (w - 1) * kernelWith D (rowContLocal D) u ξ w z Z := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hpos : ∀ᶠ w in nhdsWithin (1 : ℂ) {1}ᶜ, 0 < w.re :=
      eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds (by simp))
    filter_upwards [hpos, self_mem_nhdsWithin] with w hw hw1
    have hw1' : w ≠ 1 := hw1
    unfold kernelWith rowContLocal
    rw [PrincipalResidueFormulas.Lpsi_principal_eq D u hu w hw hw1']
    ring
  have hfin := Filter.Tendsto.congr' hev hlim
  convert hfin using 2
  unfold PrincipalResidueFormulas.remainingKernel
  first
    | (simp only [Pi.mul_apply, sub_self, mul_zero, add_zero]; ring)
    | (beta_reduce; ring_nf)
    | (simp; ring)

variable {D} in

theorem wResidue_tendsto (u : D.Row) (hu : u.u = 1) (ξ : ℂ) (hξ : 1 < ξ.re) (Z : ℝ)
    (hZ : 0 < Z) :
    Tendsto (fun z : ℂ => (z - 1 / 6) * wResidueLocal D u ξ z Z)
      (𝓝[≠] (1 / 6 : ℂ))
      (𝓝 (Spectral.c₀ D * (Z : ℂ) ^ (ξ - 61 / 100) * Spectral.G D ξ)) := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hne1 : ξ ≠ 1 := fun h => by rw [h] at hξ; simp at hξ
  have h16 : (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) := by
    first | norm_num | simp | (push_cast; ring)
  have h16re : ((1 / 6 : ℂ)).re = 1 / 6 := by rw [h16, Complex.ofReal_re]
  have hmem : ((ξ, (1 : ℂ), (1 / 6 : ℂ)) : EulerDomain.Coordinates) ∈
      EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, Complex.one_re, h16re]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hHuz : ContinuousAt (fun z : ℂ => EulerDomain.Hu D u ξ 1 z) (1 / 6) := by
    have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
    have hat : DifferentiableAt ℂ
        (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2)
        (ξ, 1, 1 / 6) :=
      hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    have hc : Continuous fun z : ℂ => ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) := by
      fun_prop
    exact ContinuousAt.comp
      (f := fun z : ℂ => ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates)) (x := 1 / 6)
      hat.continuousAt hc.continuousAt
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hM : ContinuousAt D.M (1 / 6) :=
    (D.M_differentiableOn.differentiableAt
      (hMopen.mem_nhds (by show (0 : ℝ) < ((1 / 6 : ℂ)).re; rw [h16re]; norm_num))).continuousAt
  have hpow : ContinuousAt (fun z : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z)) (1 / 6) :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl hZc)
  have hexp : ContinuousAt (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) (1 / 6) :=
    (Complex.continuous_exp.comp
      (by fun_prop : Continuous fun z : ℂ => (ξ + z - 1) ^ 2)).continuousAt
  have hT : ContinuousAt (fun z : ℂ => (Spectral.RS D * D.W1Hat 1) *
      (((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
        Complex.exp ((ξ + z - 1) ^ 2) * D.M z * EulerDomain.Hu D u ξ 1 z) / D.Llam u ξ))
      (1 / 6) :=
    ((((hpow.mul hexp).mul hM).mul hHuz).div_const _).const_mul _
  have hlim := (PrincipalResidueFormulas.zetaSCont_six_residue D).mul
    (hT.tendsto.mono_left nhdsWithin_le_nhds)
  have hre : ∀ᶠ z in nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ, 1 / 20 - EulerDomain.pad < z.re := by
    have hopen : IsOpen {z : ℂ | 1 / 20 - EulerDomain.pad < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hm : ∀ᶠ z in nhds (1 / 6 : ℂ), 1 / 20 - EulerDomain.pad < z.re :=
      hopen.mem_nhds (by
        show 1 / 20 - EulerDomain.pad < ((1 / 6 : ℂ)).re
        rw [h16re]; simp only [EulerDomain.pad]; norm_num)
    exact eventually_nhdsWithin_of_eventually_nhds hm
  have hev : ∀ᶠ z in nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ,
      (z - 1 / 6) * D.zetaSCont (6 * z) * ((Spectral.RS D * D.W1Hat 1) *
      (((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
        Complex.exp ((ξ + z - 1) ^ 2) * D.M z * EulerDomain.Hu D u ξ 1 z) / D.Llam u ξ)) =
      (z - 1 / 6) * wResidueLocal D u ξ z Z := by
    filter_upwards [hre, self_mem_nhdsWithin] with z hz hz1
    have hz1' : z ≠ 1 / 6 := hz1
    have h6 : 6 * z ≠ 1 := by
      intro h
      apply hz1'
      linear_combination h / 6
    rw [PrincipalResidueFormulas.wResidue_eq D u hu ξ z Z hZ hξ hz.le h6,
      PrincipalResidueFormulas.remainingKernel_principal D u hu]
    ring
  have hfin := Filter.Tendsto.congr' hev hlim
  have hE : (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * (1 / 6)) =
      (Z : ℂ) ^ (ξ - 61 / 100) := by
    congr 1
    simp only [Scales.xExponent, Scales.smoothingExponent]
    push_cast
    ring
  have hex : Complex.exp ((ξ + 1 / 6 - 1) ^ 2) = Complex.exp ((ξ - 5 / 6) ^ 2) := by
    congr 1
    ring
  convert hfin using 2
  beta_reduce
  rw [hE, hex, PrincipalResidueFormulas.Hu_slice_eq_H D u hu ξ hξ,
    PrincipalResidueFormulas.Llam_principal_eq D u hu ξ (by linarith) hne1]
  unfold Spectral.c₀ Spectral.G
  ring

set_option maxHeartbeats 1000000 in
theorem zetaSCont_six_diffAt (z : ℂ) (h0 : 0 < z.re) (hz6 : 6 * z ≠ 1) :
    DifferentiableAt ℂ (fun z : ℂ => D.zetaSCont (6 * z)) z := by
  have hm : (6 * z) ∈ ({s : ℂ | (0 : ℝ) < s.re} \ {(1 : ℂ)}) := by
    refine ⟨?_, hz6⟩
    show (0 : ℝ) < (6 * z).re
    have : (6 * z).re = 6 * z.re := by simp
    rw [this]; linarith
  have h1 := (PrincipalResidueFormulas.zetaSCont_analytic D (6 * z) hm).differentiableAt
  have h2 : DifferentiableAt ℂ (fun z : ℂ => 6 * z) z :=
    (differentiableAt_id.const_mul (6 : ℂ))
  have h3 : DifferentiableAt ℂ (D.zetaSCont ∘ (fun z : ℂ => 6 * z)) z :=
    DifferentiableAt.comp z h1 h2
  exact h3

set_option maxHeartbeats 1000000 in
theorem Hu_diffAt_w (u : D.Row) (ξ w z : ℂ)
    (hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar) :
    DifferentiableAt ℂ (fun w : ℂ => EulerDomain.Hu D u ξ w z) w := by
  have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
  have h1 : DifferentiableAt ℂ
      (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, w, z) :=
    hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => ((ξ, w, z) : EulerDomain.Coordinates)) w :=
    (differentiableAt_const _).prodMk (differentiableAt_id.prodMk (differentiableAt_const _))
  have h3 : DifferentiableAt ℂ ((fun p : EulerDomain.Coordinates =>
      EulerDomain.Hu D u p.1 p.2.1 p.2.2) ∘
      (fun w : ℂ => ((ξ, w, z) : EulerDomain.Coordinates))) w :=
    DifferentiableAt.comp w h1 h2
  exact h3

set_option maxHeartbeats 1000000 in
theorem kern_diffAt_w (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ)
    (hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar)
    (hw0 : 0 < w.re) (hw1 : w ≠ 1) :
    DifferentiableAt ℂ (fun w => kern D u Z ξ w z) w := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hW : Differentiable ℂ D.W1Hat :=
    ProbeSheet.MellinProof.realWeight_mellin_differentiable D.recipe.probe.W1
  have hL : DifferentiableAt ℂ (D.Lpsi u) w := (D.Lpsi_analyticOnNhd u w ⟨hw0, hw1⟩).differentiableAt
  have hHu := Hu_diffAt_w D u ξ w z hmem
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))) w :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZc)
  unfold kern kernelWith rowContLocal
  exact ((((hpow.mul (differentiableAt_const _)).mul (differentiableAt_const _)).mul
    (hW w)).mul (differentiableAt_const _)).mul
    ((((differentiableAt_const _).mul hL).mul hHu).div_const _)

set_option maxHeartbeats 1000000 in
theorem kern_diffAt_z (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ)
    (hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar)
    (hz0 : 0 < z.re) (hz6 : 6 * z ≠ 1) :
    DifferentiableAt ℂ (fun z => kern D u Z ξ w z) z := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hq0 : (D.q u : ℂ) ≠ 0 := by
    rw [PrincipalResidueFormulas.q_principal D u hu]; simp
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hM : DifferentiableAt ℂ D.M z :=
    D.M_differentiableOn.differentiableAt (hMopen.mem_nhds hz0)
  have hζ := zetaSCont_six_diffAt D z hz0 hz6
  have hHu : DifferentiableAt ℂ (fun z : ℂ => EulerDomain.Hu D u ξ w z) z := by
    have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
    have h1 : DifferentiableAt ℂ
        (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, w, z) :=
      hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => ((ξ, w, z) : EulerDomain.Coordinates)) z :=
      (differentiableAt_const _).prodMk ((differentiableAt_const _).prodMk differentiableAt_id)
    have h3 : DifferentiableAt ℂ ((fun p : EulerDomain.Coordinates =>
        EulerDomain.Hu D u p.1 p.2.1 p.2.2) ∘
        (fun z : ℂ => ((ξ, w, z) : EulerDomain.Coordinates))) z :=
      DifferentiableAt.comp z h1 h2
    exact h3
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))) z :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZc)
  have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) z :=
    DifferentiableAt.cexp (by fun_prop)
  have hqz : DifferentiableAt ℂ (fun z : ℂ => (D.q u : ℂ) ^ (-z)) z :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hq0)
  unfold kern kernelWith rowContLocal
  exact ((((hpow.mul hexp).mul hM).mul (differentiableAt_const _)).mul hqz).mul
    (((hζ.mul (differentiableAt_const _)).mul hHu).div_const _)

theorem kern_z_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) (hw : w.re ∈ Icc Scales.rightLine 4) :
    DifferentiableOn ℂ (fun z => kern D u Z ξ w z)
      (comparisonClosedStrip (1 / 6 + Scales.contourOffset) 2) := by
  have hZpos : 0 < Z := by linarith
  have hx1 := one_lt_x₁
  have hξ1 : Scales.rightLine ≤ ξ.re := hξ.1
  have hw1 : Scales.rightLine ≤ w.re := hw.1
  intro z hz
  have hz1 : 1 / 6 + Scales.contourOffset ≤ z.re := hz.1
  have hδ : (0 : ℝ) < Scales.contourOffset := by unfold Scales.contourOffset; norm_num
  have hz6 : 6 * z ≠ 1 := by
    apply six_mul_ne_one_of_re
    intro h; linarith
  have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  exact (kern_diffAt_z D u hu Z hZpos ξ w z hmem (by linarith) hz6).differentiableWithinAt

theorem kern_z_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) (hw : w.re ∈ Icc Scales.rightLine 4) :
    DecayOn (fun z => kern D u Z ξ w z) (1 / 6 + Scales.contourOffset) 2 :=
  DedekindZetaZeroFree.Quantitative.PrincipalPointwiseDecay.kern_z_decay D u hu Z hZ ξ w hξ hw

theorem Iz_w_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) :
    DifferentiableOn ℂ (fun w => Iz D u Z (1 / 6 + Scales.contourOffset) ξ w)
      (comparisonClosedStrip Scales.rightLine 4) :=
  DedekindZetaZeroFree.Quantitative.PrincipalIntegratedWControls.Iz_w_holo D u hu Z hZ ξ hξ

theorem Iz_w_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) :
    DecayOn (fun w => Iz D u Z (1 / 6 + Scales.contourOffset) ξ w) Scales.rightLine 4 :=
  DedekindZetaZeroFree.Quantitative.PrincipalIntegratedWControls.Iz_w_decay D u hu Z hZ ξ hξ

theorem Iwz_xi_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    DifferentiableOn ℂ (fun ξ => Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ξ)
      (comparisonClosedStrip Scales.rightLine 4) :=
  DedekindZetaZeroFree.Quantitative.PrincipalIntegratedXiControls.Iwz_xi_holo D u hu Z hZ

theorem Iwz_xi_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    DecayOn (fun ξ => Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ξ) Scales.rightLine 4 :=
  DedekindZetaZeroFree.Quantitative.PrincipalIntegratedXiControls.Iwz_xi_decay D u hu Z hZ

theorem kern_w_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s t : ℝ) :
    DifferentiableOn ℂ
      (fun w => kern D u Z ((Scales.rightLine : ℂ) + (s : ℂ) * I) w
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I))
      (comparisonClosedStrip (9 / 10) Scales.rightLine \ {1}) := by
  have hZpos : 0 < Z := by linarith
  have hx1 := one_lt_x₁
  have hδ : (0 : ℝ) < Scales.contourOffset := by unfold Scales.contourOffset; norm_num
  have hξre := re_x₁_line s
  have hzre := re_z_line t
  intro w hw
  have hw1 : 9 / 10 ≤ w.re := hw.1.1
  have hw0 : w ≠ 1 := hw.2
  have hmem : ((((Scales.rightLine : ℂ) + (s : ℂ) * I), w,
      (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) : EulerDomain.Coordinates) ∈
      EulerDomain.OmegaStar := by
    simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, hξre, hzre]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  exact (kern_diffAt_w D u Z hZpos _ w _ hmem (by linarith) hw0).differentiableWithinAt

theorem kern_w_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s t : ℝ) :
    DecayOn
      (fun w => kern D u Z ((Scales.rightLine : ℂ) + (s : ℂ) * I) w
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) (9 / 10) Scales.rightLine :=
  DedekindZetaZeroFree.Quantitative.PrincipalPointwiseDecay.kern_w_decay D u hu Z hZ s t

theorem kern_w_residue (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s t : ℝ) :
    Tendsto (fun w : ℂ => (w - 1) *
        kern D u Z ((Scales.rightLine : ℂ) + (s : ℂ) * I) w
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I))
      (𝓝[≠] (1 : ℂ))
      (𝓝 (wResidueExplicit D u ((Scales.rightLine : ℂ) + (s : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) Z)) := by
  have hz6 : 6 * (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
    apply six_mul_ne_one_of_re
    rw [re_z_line]
    unfold Scales.contourOffset
    norm_num
  exact kern_w_tendsto u hu _ _ Z (by linarith) (by rw [re_x₁_line]; exact one_lt_x₁)
    (by rw [re_z_line]; unfold EulerDomain.pad Scales.contourOffset; norm_num) hz6

set_option maxHeartbeats 1000000 in
theorem Hu_diffAt_z (u : D.Row) (ξ z : ℂ)
    (hmem : ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar) :
    DifferentiableAt ℂ (fun z : ℂ => EulerDomain.Hu D u ξ 1 z) z := by
  have hd := (EulerDomain.Hu_normal_convergence D u).2.2.1
  have h1 : DifferentiableAt ℂ
      (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, 1, z) :=
    hd.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates)) z :=
    (differentiableAt_const _).prodMk ((differentiableAt_const _).prodMk differentiableAt_id)
  have h3 : DifferentiableAt ℂ ((fun p : EulerDomain.Coordinates =>
      EulerDomain.Hu D u p.1 p.2.1 p.2.2) ∘
      (fun z : ℂ => ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates))) z :=
    DifferentiableAt.comp z h1 h2
  exact h3

set_option maxHeartbeats 1000000 in
theorem wResidueExplicit_diffAt (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (ξ z : ℂ)
    (hmem : ((ξ, (1 : ℂ), z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar)
    (hz0 : 0 < z.re) (hz6 : 6 * z ≠ 1) :
    DifferentiableAt ℂ (fun z => Spectral.RS D * D.W1Hat 1 *
        ((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z) *
          Complex.exp ((ξ + z - 1) ^ 2) * D.M z *
            (D.zetaSCont (6 * z) * EulerDomain.Hu D u ξ 1 z / D.Llam u ξ))) z := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hHu := Hu_diffAt_z D u ξ z hmem
  have hM : DifferentiableAt ℂ D.M z :=
    D.M_differentiableOn.differentiableAt (hMopen.mem_nhds hz0)
  have hζ := zetaSCont_six_diffAt D z hz0 hz6
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
      (Scales.smoothingExponent : ℂ) * z)) z :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZc)
  have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) z :=
    DifferentiableAt.cexp (by fun_prop)
  exact (((hpow.mul hexp).mul hM).mul ((hζ.mul hHu).div_const _)).const_mul _

set_option maxHeartbeats 1000000 in
theorem wResidue_z_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s : ℝ) :
    DifferentiableOn ℂ
      (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) z Z)
      (comparisonClosedStrip (1 / 20) (1 / 6 + Scales.contourOffset) \ {1 / 6}) := by
  have hZpos : 0 < Z := by linarith
  have hξre := re_x₁_line s
  have hx1 := one_lt_x₁
  have hat : ∀ z ∈ comparisonClosedStrip (1 / 20) (1 / 6 + Scales.contourOffset) \ {1 / 6},
      DifferentiableAt ℂ (fun z => Spectral.RS D * D.W1Hat 1 *
        ((Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ((Scales.rightLine : ℂ) + (s : ℂ) * I) - 1 +
            (Scales.smoothingExponent : ℂ) * z) *
          Complex.exp ((((Scales.rightLine : ℂ) + (s : ℂ) * I) + z - 1) ^ 2) * D.M z *
            (D.zetaSCont (6 * z) * EulerDomain.Hu D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) 1 z /
              D.Llam u ((Scales.rightLine : ℂ) + (s : ℂ) * I)))) z := by
    intro z hz
    have hz1 : 1 / 20 ≤ z.re := hz.1.1
    have hz6 : 6 * z ≠ 1 := by
      intro h
      apply hz.2
      show z = 1 / 6
      linear_combination h / 6
    have hmem : ((((Scales.rightLine : ℂ) + (s : ℂ) * I), (1 : ℂ), z) : EulerDomain.Coordinates) ∈
        EulerDomain.OmegaStar := by
      simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq, Complex.one_re, hξre]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    exact wResidueExplicit_diffAt D u Z hZpos _ z hmem (by linarith) hz6
  refine DifferentiableOn.congr (fun z hz => (hat z hz).differentiableWithinAt) ?_
  intro z hz
  have hz6 : 6 * z ≠ 1 := by
    intro h
    apply hz.2
    show z = 1 / 6
    linear_combination h / 6
  have h20 : 1 / 20 - EulerDomain.pad ≤ z.re := by
    have := hz.1.1
    unfold EulerDomain.pad; linarith
  rw [PrincipalResidueFormulas.wResidue_eq D u hu _ z Z hZpos (by rw [hξre]; exact hx1) h20 hz6,
    PrincipalResidueFormulas.remainingKernel_principal D u hu]

theorem wResidue_z_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s : ℝ) :
    DecayOn (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) z Z)
      (1 / 20) (1 / 6 + Scales.contourOffset) :=
  DedekindZetaZeroFree.Quantitative.PrincipalPointwiseDecay.wResidue_z_decay D u hu Z hZ s

theorem wResidue_z_residue (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s : ℝ) :
    Tendsto (fun z : ℂ => (z - 1 / 6) *
        wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) z Z)
      (𝓝[≠] (1 / 6 : ℂ))
      (𝓝 (zResidueExplicit D ((Scales.rightLine : ℂ) + (s : ℂ) * I) Z)) :=
  wResidue_tendsto u hu _ (by rw [re_x₁_line]; exact one_lt_x₁) Z (by linarith)

theorem zResidue_xi_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    DifferentiableOn ℂ (fun ξ => zResidueLocal D u ξ Z)
      (comparisonClosedStrip Scales.rightLine 2) := by
  have hZpos : 0 < Z := by linarith
  have hZ0 : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
  have hsub : comparisonClosedStrip Scales.rightLine 2 ⊆ {s : ℂ | 1 < s.re} :=
    fun s hs => strip_re_one_lt le_rfl hs
  have hG : DifferentiableOn ℂ (Spectral.G D) {s : ℂ | 1 < s.re} :=
    SpectralData.G_differentiableOn D
  have hpow : Differentiable ℂ (fun ξ : ℂ => (Z : ℂ) ^ (ξ - 61 / 100)) := fun ξ =>
    (differentiableAt_id.sub_const _).const_cpow (Or.inl hZ0)
  have hex : DifferentiableOn ℂ (fun ξ => zResidueExplicit D ξ Z)
      (comparisonClosedStrip Scales.rightLine 2) :=
    ((differentiableOn_const _).mul hpow.differentiableOn).mul (hG.mono hsub)
  exact hex.congr fun ξ hξ =>
    PrincipalResidueFormulas.zResidue_eq D u hu ξ (strip_re_one_lt le_rfl hξ) Z hZpos

theorem zResidue_xi_gaussian_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ C : ℝ, ∀ x ∈ Icc Scales.rightLine 2, ∀ y : ℝ,
      ‖zResidueLocal D u ((x : ℂ) + (y : ℂ) * I) Z‖ ≤ C * Real.exp (-(y ^ 2) / 2) := by
  have hZpos : 0 < Z := by linarith
  have hx1 := one_lt_x₁
  obtain ⟨CH, hCH, hH⟩ := EulerSubpower.Hu_subpower D (1 / 10) (by norm_num) 1 (by norm_num)
  obtain ⟨Cz, hCz, hz⟩ := RightHeckeBounds.zetaSCont_inv_norm_le_right D Scales.rightLine hx1
  have h16 : (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) := by
    first | norm_num | simp | (push_cast; ring)
  have h16re : ((1 / 6 : ℂ)).re = 1 / 6 := by rw [h16, Complex.ofReal_re]
  refine ⟨‖Spectral.c₀ D‖ * (Z ^ (139 / 100 : ℝ) * (Real.exp 2 * (CH * Cz))), fun x hx y => ?_⟩
  have hxx1 : Scales.rightLine ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hξ1 : 1 < ((x : ℂ) + (y : ℂ) * I).re := by rw [hre]; linarith
  rw [PrincipalResidueFormulas.zResidue_eq D u hu _ hξ1 Z hZpos]
  have hHb : ‖Spectral.H D ((x : ℂ) + (y : ℂ) * I)‖ ≤ CH := by
    rw [← PrincipalResidueFormulas.Hu_slice_eq_H D u hu _ hξ1]
    have hmem : ((((x : ℂ) + (y : ℂ) * I), (1 : ℂ), (1 / 6 : ℂ)) : EulerDomain.Coordinates) ∈
        EulerDomain.OmegaStarMargin (1 / 10) := by
      simp only [EulerDomain.OmegaStarMargin, Set.mem_setOf_eq, Complex.one_re, h16re, hre]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    have h := (hH u _ hmem).2
    rw [PrincipalResidueFormulas.q_principal D u hu, Real.one_rpow, mul_one] at h
    exact h
  have hζb : ‖(D.zetaSCont ((x : ℂ) + (y : ℂ) * I))⁻¹‖ ≤ Cz := hz _ (by rw [hre]; exact hxx1)
  have hsq : ((((x : ℂ) + (y : ℂ) * I) - 5 / 6) ^ 2).re = (x - 5 / 6) ^ 2 - y ^ 2 := by
    have : ((x : ℂ) + (y : ℂ) * I) - 5 / 6 = ((x - 5 / 6 : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [this, pow_two]
    simp [Complex.mul_re]
    ring
  have hGb : ‖Spectral.G D ((x : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp 2 * (CH * Cz) * Real.exp (-(y ^ 2) / 2) := by
    unfold Spectral.G
    rw [div_eq_mul_inv, norm_mul, norm_mul, Complex.norm_exp, hsq]
    have hE : Real.exp ((x - 5 / 6) ^ 2 - y ^ 2) ≤ Real.exp 2 * Real.exp (-(y ^ 2) / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg y]
    have h1 : Real.exp ((x - 5 / 6) ^ 2 - y ^ 2) * ‖Spectral.H D ((x : ℂ) + (y : ℂ) * I)‖ ≤
        (Real.exp 2 * Real.exp (-(y ^ 2) / 2)) * CH :=
      mul_le_mul hE hHb (norm_nonneg _) (by positivity)
    calc Real.exp ((x - 5 / 6) ^ 2 - y ^ 2) * ‖Spectral.H D ((x : ℂ) + (y : ℂ) * I)‖ *
          ‖(D.zetaSCont ((x : ℂ) + (y : ℂ) * I))⁻¹‖
        ≤ ((Real.exp 2 * Real.exp (-(y ^ 2) / 2)) * CH) * Cz :=
          mul_le_mul h1 hζb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hZn : ‖(Z : ℂ) ^ (((x : ℂ) + (y : ℂ) * I) - 61 / 100)‖ ≤ Z ^ (139 / 100 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos]
    have : (((x : ℂ) + (y : ℂ) * I) - 61 / 100).re = x - 61 / 100 := by
      have h61 : (61 / 100 : ℂ) = ((61 / 100 : ℝ) : ℂ) := by push_cast; ring
      rw [h61]; simp
    rw [this]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  rw [norm_mul, norm_mul]
  calc ‖Spectral.c₀ D‖ * ‖(Z : ℂ) ^ (((x : ℂ) + (y : ℂ) * I) - 61 / 100)‖ *
        ‖Spectral.G D ((x : ℂ) + (y : ℂ) * I)‖
      ≤ ‖Spectral.c₀ D‖ * Z ^ (139 / 100 : ℝ) *
        (Real.exp 2 * (CH * Cz) * Real.exp (-(y ^ 2) / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hZn (norm_nonneg _)) hGb (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalStripControls
