module

public import DedekindZetaZeroFree.Moments.Principal.Contour.StripDefinitions
public import DedekindZetaZeroFree.Moments.Principal.Contour.ZetaStripGrowth
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.SubpowerBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalPointwiseDecay

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions Set Filter Complex
  DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem decay_main (f h ζ : ℂ → ℂ) (a b T K C' k : ℝ) (hk : 0 ≤ k) (hC' : 0 ≤ C') (hK : 0 ≤ K)
    (hh : ∀ m : ℕ, ∃ C, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| →
      (1 + |z.im|) ^ m * ‖h z‖ ≤ C)
    (hz : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| → ‖ζ z‖ ≤ C' * (1 + |z.im|) ^ k)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ |z.im| → ‖f z‖ ≤ K * (‖h z‖ * ‖ζ z‖)) :
    DecayOn f a b := by
  intro B hB
  set N : ℕ := ⌈k⌉₊ with hN
  set M : ℕ := ⌈B⌉₊ with hM
  obtain ⟨C0, hC0⟩ := hh (M + N)
  refine ⟨max (K * C' * C0) 0, T, fun x hx y hy => ?_⟩
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have h1 := hf _ (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2) (by rw [him]; exact hy)
  have h2 := hz _ (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2) (by rw [him]; exact hy)
  have h3 := hC0 _ (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2) (by rw [him]; exact hy)
  rw [him] at h2 h3
  set z := (x : ℂ) + (y : ℂ) * I
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hpos : 0 < 1 + |y| := by linarith
  have hkN : (1 + |y|) ^ k ≤ (1 + |y|) ^ (N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil k)
  rw [Real.rpow_natCast] at hkN
  have hBM : (1 + |y|) ^ (-B) ≥ ((1 + |y|) ^ M)⁻¹ := by
    rw [Real.rpow_neg hpos.le, ge_iff_le]
    apply inv_anti₀ (by positivity)
    calc (1 + |y|) ^ B ≤ (1 + |y|) ^ (M : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil B)
      _ = (1 + |y|) ^ M := Real.rpow_natCast _ _

  have h4 : (1 + |y|) ^ M * ‖f z‖ ≤ K * C' * C0 := by
    have e1 : (1 + |y|) ^ M * ‖f z‖ ≤ (1 + |y|) ^ M * (K * (‖h z‖ * (C' * (1 + |y|) ^ N))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left (hkN) hC')) (norm_nonneg _)
    refine e1.trans ?_
    have : (1 + |y|) ^ M * (K * (‖h z‖ * (C' * (1 + |y|) ^ N))) =
        K * C' * ((1 + |y|) ^ (M + N) * ‖h z‖) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : ‖f z‖ ≤ max (K * C' * C0) 0 * ((1 + |y|) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖f z‖ * (1 + |y|) ^ M = (1 + |y|) ^ M * ‖f z‖ := by ring
      _ ≤ K * C' * C0 := h4
      _ ≤ _ := le_max_left _ _
  exact h5.trans (mul_le_mul_of_nonneg_left hBM (le_max_right _ _))

theorem Hu_bound (u : D.Row) : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ ξ w z : ℂ,
    ((Scales.rightLine ≤ ξ.re ∧ 9 / 10 ≤ w.re ∧ 1 / 6 + Scales.contourOffset ≤ z.re) ∨
      (Scales.rightLine ≤ ξ.re ∧ 1 ≤ w.re ∧ 1 / 20 ≤ z.re)) →
    ‖EulerDomain.Hu D u ξ w z‖ ≤ CH := by
  obtain ⟨C, _, h⟩ := EulerSubpower.Hu_subpower_boxes D 1 one_pos
  refine ⟨max (C * D.q u ^ (1 : ℝ)) 0, le_max_right _ _, fun ξ w z hp => ?_⟩
  have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.boxes := by
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl (Or.inr (by
        simp only [EulerDomain.box₂, EulerDomain.box, Set.mem_setOf_eq]
        exact ⟨h1, h2, h3⟩))
    · exact Or.inr (by
        simp only [EulerDomain.box₃, EulerDomain.box, Set.mem_setOf_eq]
        exact ⟨h1, h2, h3⟩)
  exact ((h u _ hmem).2).trans (le_max_left _ _)

theorem kern_norm_eq (u : D.Row) (hu : u.u = 1) (Z : ℝ) (ξ w z : ℂ) :
    ‖kern D u Z ξ w z‖ =
      ‖(Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))‖ *
        Real.exp (((ξ + z - 1) ^ 2).re) * ‖D.M z‖ * ‖D.W1Hat w‖ *
        (‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖EulerDomain.Hu D u ξ w z‖ / ‖D.Llam u ξ‖) := by
  have hq := PrincipalResidueFormulas.q_principal D u hu
  simp only [kern, kernelWith, rowContLocal, norm_mul, norm_div, hq, Complex.ofReal_one,
    Complex.one_cpow, norm_one, mul_one, Complex.norm_exp] <;> ring

theorem rem_norm_eq (u : D.Row) (hu : u.u = 1) (Z : ℝ) (ξ z : ℂ) :
    ‖PrincipalResidueFormulas.remainingKernel D u ξ z Z‖ =
      ‖(Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z)‖ *
        Real.exp (((ξ + z - 1) ^ 2).re) * ‖D.M z‖ *
        (‖D.zetaSCont (6 * z)‖ * ‖EulerDomain.Hu D u ξ 1 z‖ / ‖D.Llam u ξ‖) := by
  rw [PrincipalResidueFormulas.remainingKernel_principal D u hu]
  simp only [norm_mul, norm_div, Complex.norm_exp]

theorem zpow_norm_le (Z : ℝ) (hZ : 2 ≤ Z) (c : ℂ) (hc : c.re ≤ 12) :
    ‖(Z : ℂ) ^ c‖ ≤ Z ^ (12 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) hc

theorem sq_re_eq (c : ℂ) : (c ^ 2).re = c.re ^ 2 - c.im ^ 2 := by
  simp only [pow_two, Complex.mul_re]

theorem exp_sq_le (c : ℂ) (h1 : c.re ≤ 5) (h2 : -5 ≤ c.re) :
    Real.exp ((c ^ 2).re) ≤ Real.exp 25 := by
  rw [sq_re_eq]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg c.im]

theorem real_bound1 (P E m W zz Lp Hn Ll P' E' H' : ℝ) (hP : 0 ≤ P) (hP' : P ≤ P')
    (hE : 0 ≤ E) (hE' : E ≤ E') (hHn : 0 ≤ Hn) (hH : Hn ≤ H') (hm : 0 ≤ m) (hW : 0 ≤ W)
    (hzz : 0 ≤ zz) (hLp : 0 ≤ Lp) (hLl : 0 ≤ Ll) :
    P * E * m * W * (zz * Lp * Hn / Ll) ≤ (P' * E' * H') * (W * Lp / Ll) * (m * zz) := by
  have e : P * E * m * W * (zz * Lp * Hn / Ll) = (P * E * Hn) * (W * Lp / Ll) * (m * zz) := by
    ring
  rw [e]
  have h1 : P * E * Hn ≤ P' * E' * H' :=
    mul_le_mul (mul_le_mul hP' hE' hE (hP.trans hP')) hH hHn
      (mul_nonneg (hP.trans hP') (hE.trans hE'))
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hm hzz)
  apply mul_le_mul_of_nonneg_right h1 (by positivity)

theorem real_bound2 (P E m W zz Lp Hn Ll P' H' : ℝ) (hP : 0 ≤ P) (hP' : P ≤ P')
    (hE : 0 ≤ E) (hHn : 0 ≤ Hn) (hH : Hn ≤ H') (hm : 0 ≤ m) (hW : 0 ≤ W)
    (hzz : 0 ≤ zz) (hLp : 0 ≤ Lp) (hLl : 0 ≤ Ll) :
    P * E * m * W * (zz * Lp * Hn / Ll) ≤ (P' * H') * (E * m * zz / Ll) * (W * Lp) := by
  have e : P * E * m * W * (zz * Lp * Hn / Ll) = (P * Hn) * (E * m * zz / Ll) * (W * Lp) := by
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hW hLp)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul hP' hH hHn (hP.trans hP')

theorem real_bound3 (P E m zz Hn Ll P' E' H' : ℝ) (hP : 0 ≤ P) (hP' : P ≤ P')
    (hE : 0 ≤ E) (hE' : E ≤ E') (hHn : 0 ≤ Hn) (hH : Hn ≤ H') (hm : 0 ≤ m)
    (hzz : 0 ≤ zz) (hLl : 0 ≤ Ll) :
    P * E * m * (zz * Hn / Ll) ≤ ((P' * E' * H') / Ll) * (m * zz) := by
  have e : P * E * m * (zz * Hn / Ll) = ((P * E * Hn) / Ll) * (m * zz) := by ring
  rw [e]
  have h1 : P * E * Hn ≤ P' * E' * H' :=
    mul_le_mul (mul_le_mul hP' hE' hE (hP.trans hP')) hH hHn
      (mul_nonneg (hP.trans hP') (hE.trans hE'))
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hm hzz)
  exact div_le_div_of_nonneg_right h1 hLl

theorem zeta6_bound : ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧ ∀ z : ℂ, 1 / 20 ≤ z.re → z.re ≤ 2 →
    1 / 6 ≤ |z.im| → ‖D.zetaSCont (6 * z)‖ ≤ C * (1 + |z.im|) ^ k := by
  obtain ⟨C, k, hC, hk, h⟩ :=
    PrincipalZetaStripGrowth.zetaSCont_high_height_bound D (3 / 10) 12 (by norm_num)
      (by norm_num)
  refine ⟨C * 6 ^ k, k, by positivity, hk, fun z h1 h2 h3 => ?_⟩
  have hre : (6 * z).re = 6 * z.re := by simp
  have him : (6 * z).im = 6 * z.im := by simp
  have hb := h (6 * z) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]; linarith)
  rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
    Real.mul_rpow (by norm_num) (abs_nonneg _)] at hb
  have h4 : |z.im| ^ k ≤ (1 + |z.im|) ^ k :=
    Real.rpow_le_rpow (abs_nonneg _) (by linarith) hk
  calc ‖D.zetaSCont (6 * z)‖ ≤ C * (6 ^ k * |z.im| ^ k) := hb
    _ ≤ C * (6 ^ k * (1 + |z.im|) ^ k) := by gcongr
    _ = C * 6 ^ k * (1 + |z.im|) ^ k := by ring

theorem zeta1_bound : ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧ ∀ w : ℂ, 9 / 10 ≤ w.re → w.re ≤ 2 →
    1 ≤ |w.im| → ‖D.zetaSCont w‖ ≤ C * (1 + |w.im|) ^ k := by
  obtain ⟨C, k, hC, hk, h⟩ :=
    PrincipalZetaStripGrowth.zetaSCont_high_height_bound D (9 / 10) 2 (by norm_num)
      (by norm_num)
  refine ⟨C, k, hC.le, hk, fun w h1 h2 h3 => ?_⟩
  have hb := h w h1 h2 h3
  have h4 : |w.im| ^ k ≤ (1 + |w.im|) ^ k :=
    Real.rpow_le_rpow (abs_nonneg _) (by linarith) hk
  exact hb.trans (mul_le_mul_of_nonneg_left h4 hC.le)

theorem Scales_facts : (0 : ℝ) < Scales.contourOffset ∧ Scales.contourOffset ≤ 1 / 100 ∧ Scales.rightLine = 1 + Scales.contourOffset := by
  refine ⟨?_, ?_, rfl⟩ <;> norm_num [Scales.contourOffset]

theorem kern_z_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) (hw : w.re ∈ Icc Scales.rightLine 4) :
    DecayOn (fun z => kern D u Z ξ w z) (1 / 6 + Scales.contourOffset) 2 := by
  obtain ⟨hδ0, hδ1, hx1⟩ := Scales_facts
  have hZ0 : (0 : ℝ) < Z := by linarith
  obtain ⟨CH, hCH0, hCH⟩ := Hu_bound D u
  obtain ⟨Cz, kz, hCz, hkz, hz⟩ := zeta6_bound D
  have hξ1 := hξ.1
  have hξ2 := hξ.2
  have hw1 := hw.1
  have hw2 := hw.2
  refine decay_main (fun z => kern D u Z ξ w z) (fun z => D.M z) (fun z => D.zetaSCont (6 * z))
    (1 / 6 + Scales.contourOffset) 2 (1 / 6)
    (Z ^ (12 : ℝ) * Real.exp 25 * CH * (‖D.W1Hat w‖ * ‖D.Lpsi u w‖ / ‖D.Llam u ξ‖))
    Cz kz hkz hCz
    (by positivity) ?_ ?_ ?_
  · intro m
    obtain ⟨C, hC⟩ := D.M_vertical_decay (1 / 6 + Scales.contourOffset) 2 (by linarith) (by linarith) m
    exact ⟨C, fun z h1 h2 _ => hC z h1 h2⟩
  · intro z h1 h2 h3
    exact hz z (by linarith) h2 h3
  · intro z h1 h2 h3
    show ‖kern D u Z ξ w z‖ ≤ _
    rw [kern_norm_eq D u hu Z ξ w z]
    have hHu := hCH ξ w z (Or.inl ⟨by linarith, by linarith, h1⟩)
    have hc : (((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))).re ≤ 12 := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.sub_im]
      simp only [Scales.xExponent, Scales.smoothingExponent, Scales.yExponent]
      linarith
    have hP := zpow_norm_le Z hZ _ hc
    have hE := exp_sq_le (ξ + z - 1) (by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith) (by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith)
    exact real_bound1 _ _ _ _ _ _ _ _ _ _ _ (norm_nonneg _) hP (Real.exp_nonneg _) hE
      (norm_nonneg _) hHu (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _)

theorem kern_w_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s t : ℝ) :
    DecayOn
      (fun w => kern D u Z ((Scales.rightLine : ℂ) + (s : ℂ) * I) w
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) (9 / 10) Scales.rightLine := by
  obtain ⟨hδ0, hδ1, hx1⟩ := Scales_facts
  have hZ0 : (0 : ℝ) < Z := by linarith
  obtain ⟨CH, hCH0, hCH⟩ := Hu_bound D u
  obtain ⟨Cw, kw, hCw, hkw, hw⟩ := zeta1_bound D
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℂ, ξ = (Scales.rightLine : ℂ) + (s : ℂ) * I := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = (((1 / 6 + Scales.contourOffset : ℝ) : ℂ)) + (t : ℂ) * I := ⟨_, rfl⟩
  rw [← hξdef, ← hzdef]
  have hξre : ξ.re = Scales.rightLine := by simp [hξdef]
  have hzre : z.re = 1 / 6 + Scales.contourOffset := by simp [hzdef]
  have hcre : (ξ + z - 1).re ≤ 5 ∧ -5 ≤ (ξ + z - 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    constructor <;> linarith
  refine decay_main (fun w => kern D u Z ξ w z) (fun w => D.W1Hat w) (fun w => D.zetaSCont w)
    (9 / 10) Scales.rightLine 1
    ((Z ^ (12 : ℝ) * CH) * (Real.exp (((ξ + z - 1) ^ 2).re) * ‖D.M z‖ *
      ‖D.zetaSCont (6 * z)‖ / ‖D.Llam u ξ‖))
    Cw kw hkw hCw (by positivity) ?_ ?_ ?_
  · intro m
    obtain ⟨C, hC⟩ := D.W1Hat_vertical_decay (9 / 10) Scales.rightLine (by linarith) m
    exact ⟨C, fun w h1 h2 _ => hC w h1 h2⟩
  · intro w h1 h2 h3
    exact hw w h1 (by linarith) h3
  · intro w h1 h2 h3
    show ‖kern D u Z ξ w z‖ ≤ _
    have hw1 : w ≠ 1 := by
      intro h
      have : w.im = 0 := by rw [h]; simp
      rw [this] at h3
      norm_num at h3
    have hL : D.Lpsi u w = D.zetaSCont w :=
      PrincipalResidueFormulas.Lpsi_principal_eq D u hu w (by linarith) hw1
    rw [kern_norm_eq D u hu Z ξ w z, hL]
    have hHu := hCH ξ w z (Or.inl ⟨hξre.ge, h1, hzre.ge⟩)
    have hc : (((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1))).re ≤ 12 := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.sub_im]
      simp only [Scales.xExponent, Scales.smoothingExponent, Scales.yExponent]
      linarith
    have hP := zpow_norm_le Z hZ _ hc
    exact real_bound2 _ _ _ _ _ _ _ _ _ _ (norm_nonneg _) hP (Real.exp_nonneg _)
      (norm_nonneg _) hHu (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _)

theorem wResidue_z_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (s : ℝ) :
    DecayOn (fun z => wResidueLocal D u ((Scales.rightLine : ℂ) + (s : ℂ) * I) z Z)
      (1 / 20) (1 / 6 + Scales.contourOffset) := by
  obtain ⟨hδ0, hδ1, hx1⟩ := Scales_facts
  have hZ0 : (0 : ℝ) < Z := by linarith
  obtain ⟨CH, hCH0, hCH⟩ := Hu_bound D u
  obtain ⟨Cz, kz, hCz, hkz, hz⟩ := zeta6_bound D
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℂ, ξ = (Scales.rightLine : ℂ) + (s : ℂ) * I := ⟨_, rfl⟩
  rw [← hξdef]
  have hξre : ξ.re = Scales.rightLine := by simp [hξdef]
  refine decay_main (fun z => wResidueLocal D u ξ z Z) (fun z => D.M z)
    (fun z => D.zetaSCont (6 * z)) (1 / 20) (1 / 6 + Scales.contourOffset) (1 / 6)
    (‖Spectral.RS D‖ * ‖D.W1Hat 1‖ * ((Z ^ (12 : ℝ) * Real.exp 25 * CH) / ‖D.Llam u ξ‖))
    Cz kz hkz hCz (by positivity) ?_ ?_ ?_
  · intro m
    obtain ⟨C, hC⟩ := D.M_vertical_decay (1 / 20) (1 / 6 + Scales.contourOffset) (by norm_num)
      (by linarith) m
    exact ⟨C, fun z h1 h2 _ => hC z h1 h2⟩
  · intro z h1 h2 h3
    exact hz z h1 (by linarith) h3
  · intro z h1 h2 h3
    show ‖wResidueLocal D u ξ z Z‖ ≤ _
    have h6 : 6 * z ≠ 1 := by
      intro h
      have h0 : z.im = 0 := by
        have := congrArg Complex.im h
        simp at this
        linarith
      rw [h0] at h3
      norm_num at h3
    rw [PrincipalResidueFormulas.wResidue_eq D u hu ξ z Z hZ0 (by linarith)
      (by simp only [EulerDomain.pad]; linarith) h6, norm_mul, norm_mul,
      rem_norm_eq D u hu Z ξ z]
    have hHu := hCH ξ 1 z (Or.inr ⟨hξre.ge, by simp, h1⟩)
    have hc : (((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z)).re ≤ 12 := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.sub_im]
      simp only [Scales.xExponent, Scales.smoothingExponent]
      linarith
    have hP := zpow_norm_le Z hZ _ hc
    have hE := exp_sq_le (ξ + z - 1) (by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith) (by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith)
    have key := real_bound3 _ _ _ _ _ _ _ _ _ (norm_nonneg _) hP (Real.exp_nonneg _) hE
      (norm_nonneg _) hHu (norm_nonneg (D.M z)) (norm_nonneg (D.zetaSCont (6 * z)))
      (norm_nonneg (D.Llam u ξ))
    calc _ ≤ ‖Spectral.RS D‖ * ‖D.W1Hat 1‖ * (((Z ^ (12 : ℝ) * Real.exp 25 * CH) / ‖D.Llam u ξ‖) *
          (‖D.M z‖ * ‖D.zetaSCont (6 * z)‖)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalPointwiseDecay
