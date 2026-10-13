module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift
public import DedekindZetaZeroFree.Moments.Principal.Contour.StripControls

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalContourDeformation

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions DedekindZetaZeroFree.Quantitative.EulerDomain MeasureTheory Set Filter Complex
open scoped Classical Topology

theorem verticalIntegral_eq_of_decay {a b : ℝ} {f : ℂ → ℂ} (hab : a < b)
    (hf : DifferentiableOn ℂ f (comparisonClosedStrip a b)) (C T0 : ℝ)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ)) :
    comparisonVerticalIntegral b f = comparisonVerticalIntegral a f := by
  set m : ℝ := (a + b) / 2 with hm
  have ham : a < ((m : ℂ)).re := by simp [hm]; linarith
  have hmb : ((m : ℂ)).re < b := by simp [hm]; linarith
  have hnb : comparisonClosedStrip a b ∈ 𝓝 (m : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a < (m : ℂ).re ∧ (m : ℂ).re < b from ⟨ham, hmb⟩))
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hcont : ContinuousAt f (m : ℂ) := (hf.differentiableAt hnb).continuousAt
  have hres : Tendsto (fun z : ℂ => (z - (m : ℂ)) * f z) (𝓝[≠] (m : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => (z - (m : ℂ)) * f z) (𝓝 (m : ℂ)) (𝓝 ((m - m : ℂ) * f m)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hcont).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have := SimplePoleVerticalShift.verticalIntegral_sub_eq_residue_of_decay ham hmb
    (hf.mono diff_subset) hres C T0 hbound
  linear_combination this

private theorem decay_two {f : ℂ → ℂ} {a b : ℝ}
    (h : PrincipalStripControls.DecayOn f a b) :
    ∃ C T0 : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ) :=
  h 2 (by norm_num)

private theorem re_eq (x s : ℝ) : ((x : ℂ) + (s : ℂ) * I).re = x := by simp

private theorem gauss_le (y : ℝ) : Real.exp (-(y ^ 2) / 2) ≤ 4 * (1 + |y|) ^ (-2 : ℝ) := by
  have h1 : (1 : ℝ) + y ^ 2 / 2 ≤ Real.exp (y ^ 2 / 2) := by
    have := Real.add_one_le_exp (y ^ 2 / 2); linarith
  have hpos : 0 < 1 + y ^ 2 / 2 := by positivity
  have hexp : Real.exp (-(y ^ 2) / 2) = (Real.exp (y ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have h2 : (Real.exp (y ^ 2 / 2))⁻¹ ≤ (1 + y ^ 2 / 2)⁻¹ := inv_anti₀ hpos h1
  have h3 : (1 + |y|) ^ (-2 : ℝ) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [hexp, h3]
  refine h2.trans ?_
  have hab : 0 < (1 + |y|) ^ 2 := by positivity
  have h4 : (1 + |y|) ^ 2 ≤ 4 * (1 + y ^ 2 / 2) := by
    have : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [sq_nonneg (|y| - 1), abs_nonneg y]
  calc (1 + y ^ 2 / 2)⁻¹ = 4 / (4 * (1 + y ^ 2 / 2)) := by field_simp
    _ ≤ 4 / (1 + |y|) ^ 2 := by gcongr
    _ = 4 * ((1 + |y|) ^ 2)⁻¹ := by rw [div_eq_mul_inv]

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def kern (u : D.Row) (Z : ℝ) (ξ w z : ℂ) : ℂ := kernelWith D (rowContLocal D) u ξ w z Z

def Iz (u : D.Row) (Z v : ℝ) (ξ w : ℂ) : ℂ :=
  comparisonVerticalIntegral v (fun z => kern D u Z ξ w z)

def Iwz (u : D.Row) (Z y v : ℝ) (ξ : ℂ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u Z v ξ w)

theorem initial_z_shift (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z)
    (x y : ℝ) (hx : x ∈ Icc Scales.rightLine 4) (hy : y ∈ Icc Scales.rightLine 4) (s t : ℝ) :
    Iz D u Z 2 ((x : ℂ) + (s : ℂ) * I) ((y : ℂ) + (t : ℂ) * I) =
      Iz D u Z (1 / 6 + Scales.contourOffset) ((x : ℂ) + (s : ℂ) * I) ((y : ℂ) + (t : ℂ) * I) := by
  have hξ : ((x : ℂ) + (s : ℂ) * I).re ∈ Icc Scales.rightLine 4 := by rw [re_eq]; exact hx
  have hw : ((y : ℂ) + (t : ℂ) * I).re ∈ Icc Scales.rightLine 4 := by rw [re_eq]; exact hy
  have hlt : (1 / 6 + Scales.contourOffset : ℝ) < 2 := by unfold Scales.contourOffset; norm_num
  obtain ⟨C, T0, hb⟩ := decay_two
    (PrincipalStripControls.kern_z_decay D u hu Z hZ _ _ hξ hw)
  unfold Iz
  exact verticalIntegral_eq_of_decay hlt
    (PrincipalStripControls.kern_z_holo D u hu Z hZ _ _ hξ hw) C T0 hb

theorem initial_w_shift (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z)
    (x : ℝ) (hx : x ∈ Icc Scales.rightLine 4) (s : ℝ) :
    Iwz D u Z 4 (1 / 6 + Scales.contourOffset) ((x : ℂ) + (s : ℂ) * I) =
      Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ((x : ℂ) + (s : ℂ) * I) := by
  have hξ : ((x : ℂ) + (s : ℂ) * I).re ∈ Icc Scales.rightLine 4 := by rw [re_eq]; exact hx
  have hlt : Scales.rightLine < 4 := by unfold Scales.rightLine Scales.contourOffset; norm_num
  obtain ⟨C, T0, hb⟩ := decay_two (PrincipalStripControls.Iz_w_decay D u hu Z hZ _ hξ)
  unfold Iwz
  exact verticalIntegral_eq_of_decay hlt
    (PrincipalStripControls.Iz_w_holo D u hu Z hZ _ hξ) C T0 hb

theorem initial_xi_shift (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    comparisonVerticalIntegral 4 (fun ξ => Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ξ) =
      comparisonVerticalIntegral Scales.rightLine
        (fun ξ => Iwz D u Z Scales.rightLine (1 / 6 + Scales.contourOffset) ξ) := by
  have hlt : Scales.rightLine < 4 := by unfold Scales.rightLine Scales.contourOffset; norm_num
  obtain ⟨C, T0, hb⟩ := decay_two (PrincipalStripControls.Iwz_xi_decay D u hu Z hZ)
  exact verticalIntegral_eq_of_decay hlt
    (PrincipalStripControls.Iwz_xi_holo D u hu Z hZ) C T0 hb

theorem w_shift_across_one (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s t : ℝ) :
    comparisonVerticalIntegral Scales.rightLine
        (fun w => kern D u Z ((Scales.rightLine : ℂ) + (s : ℂ) * I) w
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) -
      comparisonVerticalIntegral (9 / 10)
        (fun w => kern D u Z ((Scales.rightLine : ℂ) + (s : ℂ) * I) w
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) =
      wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) Z := by
  have hres := PrincipalStripControls.kern_w_residue D u hu Z hZ s t
  have hlim : wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) Z =
      PrincipalStripControls.wResidueExplicit D u ((Scales.rightLine : ℂ) + (s : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) Z := by
    unfold wResidueLocal
    exact hres.limUnder_eq
  rw [hlim]
  obtain ⟨C, T0, hb⟩ := decay_two (PrincipalStripControls.kern_w_decay D u hu Z hZ s t)
  have hap : (9 / 10 : ℝ) < (1 : ℂ).re := by rw [Complex.one_re]; norm_num
  have hpb : (1 : ℂ).re < Scales.rightLine := by
    rw [Complex.one_re]; unfold Scales.rightLine Scales.contourOffset; norm_num
  exact SimplePoleVerticalShift.verticalIntegral_sub_eq_residue_of_decay hap hpb
    (PrincipalStripControls.kern_w_holo D u hu Z hZ s t) hres C T0 hb

theorem wResidue_z_shift_across (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s : ℝ) :
    comparisonVerticalIntegral (1 / 6 + Scales.contourOffset)
        (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) z Z) -
      comparisonVerticalIntegral (1 / 20)
        (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) z Z) =
      zResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) Z := by
  have hres := PrincipalStripControls.wResidue_z_residue D u hu Z hZ s
  have hlim : zResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) Z =
      PrincipalStripControls.zResidueExplicit D ((Scales.rightLine : ℂ) + (s : ℂ) * I) Z := by
    unfold zResidueLocal
    exact hres.limUnder_eq
  rw [hlim]
  obtain ⟨C, T0, hb⟩ := decay_two (PrincipalStripControls.wResidue_z_decay D u hu Z hZ s)
  have hp : (1 / 6 : ℂ).re = 1 / 6 := by simp
  have hap : (1 / 20 : ℝ) < (1 / 6 : ℂ).re := by rw [hp]; norm_num
  have hpb : (1 / 6 : ℂ).re < 1 / 6 + Scales.contourOffset := by
    rw [hp]; unfold Scales.contourOffset; norm_num
  exact SimplePoleVerticalShift.verticalIntegral_sub_eq_residue_of_decay hap hpb
    (PrincipalStripControls.wResidue_z_holo D u hu Z hZ s) hres C T0 hb

theorem zResidue_xi_shift (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    comparisonVerticalIntegral Scales.rightLine (fun ξ => zResidueLocal D u ξ Z) =
      Spectral.c₀ D * Spectral.f D Z := by
  have hZ0 : 0 < Z := by linarith
  have hlt : Scales.rightLine < 2 := by unfold Scales.rightLine Scales.contourOffset; norm_num
  obtain ⟨C, hC⟩ := PrincipalStripControls.zResidue_xi_gaussian_decay D u hu Z hZ
  have hshift : comparisonVerticalIntegral 2 (fun ξ => zResidueLocal D u ξ Z) =
      comparisonVerticalIntegral Scales.rightLine (fun ξ => zResidueLocal D u ξ Z) := by
    refine verticalIntegral_eq_of_decay hlt
      (PrincipalStripControls.zResidue_xi_holo D u hu Z hZ) (4 * |C|) 0 ?_
    intro x hx y _
    refine (hC x hx y).trans ?_
    calc C * Real.exp (-(y ^ 2) / 2) ≤ |C| * Real.exp (-(y ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * (4 * (1 + |y|) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (gauss_le y) (abs_nonneg C)
      _ = 4 * |C| * (1 + |y|) ^ (-2 : ℝ) := by ring
  rw [← hshift]
  have hfun : ∀ t : ℝ, zResidueLocal D u (((2 : ℝ) : ℂ) + (t : ℂ) * I) Z =
      Spectral.c₀ D * (((Z : ℂ)) ^ ((((2 : ℝ) : ℂ) + (t : ℂ) * I) - 61 / 100) *
        Spectral.G D (((2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    intro t
    rw [PrincipalResidueFormulas.zResidue_eq D u hu (((2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp) Z hZ0]
    ring
  have hcongr : comparisonVerticalIntegral 2 (fun ξ => zResidueLocal D u ξ Z) =
      comparisonVerticalIntegral 2 (fun s => Spectral.c₀ D *
        ((Z : ℂ) ^ (s - 61 / 100) * Spectral.G D s)) := by
    simp only [comparisonVerticalIntegral, hfun]
  rw [hcongr]
  unfold Spectral.f
  rw [if_pos hZ0]
  simp only [comparisonVerticalIntegral]
  rw [MeasureTheory.integral_const_mul]
  ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalContourDeformation
