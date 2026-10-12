module

public import DedekindZetaZeroFree.Moments.Principal.MellinContourDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section

open MeasureTheory Complex

private lemma one_div_six_cast : ((((1 : ℝ) / 6 : ℝ)) : ℂ) = (1 / 6 : ℂ) := by norm_num

private theorem clearedKernel_at_pole
    (Z : ℝ) (hZ : 1 ≤ Z)
    (M W L R Hη : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) (ξ : ℂ)
    (hcorrection : H ξ 1 (1 / 6) = Hη ξ) :
    PrincipalZShift.clearedKernel Z M W L R H ξ (1 / 6) =
      (R 1 / 6 * M (1 / 6) * W 1) * PrincipalZShift.transformKernel Z L Hη ξ := by
  have hpos : 0 < Z := by linarith
  have hpower : comparisonRealPower (comparisonX Z) (1 / 2 - (1 / 6 : ℂ)) *
      comparisonRealPower Z (ξ + 1 / 6 - 1) =
        comparisonRealPower Z (comparisonC ξ) := by
    unfold comparisonRealPower comparisonX comparisonC
    rw [Real.log_rpow hpos, Complex.ofReal_mul, ← Complex.exp_add]
    congr 1
    norm_num [comparisonA]
    ring
  unfold PrincipalZShift.clearedKernel PrincipalZShift.transformKernel
  rw [hcorrection, hpower]
  norm_num
  have hexp : ξ + (1 / 6 : ℂ) - 1 = ξ - 5 / 6 := by ring
  rw [hexp]
  ring

private theorem residueKernel_slice_integrable
    (Z : ℝ) (M W ζ L R Hη : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (hcontour : PrincipalZShift.ZContourConditions Z M W ζ L R Hη H)
    (ξ : ℂ) (hξ : ξ.re = comparisonSigma₁) {σz : ℝ}
    (hσz : σz ∈ ({PrincipalZShift.zLine, comparisonZeta₁} : Set ℝ)) :
    Integrable (fun t : ℝ =>
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((σz : ℂ) + (t : ℂ) * I)) := by
  have hmem : σz ∈ Set.Icc PrincipalZShift.zLine comparisonZeta₁ := by
    rcases hσz with h | h
    · rw [h]; exact ⟨le_refl _, by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta]⟩
    · rw [h]; exact ⟨by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta], le_refl _⟩
  have hσp : σz ≠ (1 : ℝ) / 6 := by
    rcases hσz with h | h
    · rw [h]; norm_num [PrincipalZShift.zLine]
    · rw [h]; norm_num [comparisonZeta₁, comparisonDelta]
  have hline (t : ℝ) :
      ((σz : ℂ) + (t : ℂ) * I) ∈ comparisonClosedStrip PrincipalZShift.zLine comparisonZeta₁ := by
    show PrincipalZShift.zLine ≤ (((σz : ℂ) + (t : ℂ) * I)).re ∧
      (((σz : ℂ) + (t : ℂ) * I)).re ≤ comparisonZeta₁
    rw [show (((σz : ℂ) + (t : ℂ) * I)).re = σz by simp]
    exact hmem
  have hU (t : ℝ) : ((σz : ℂ) + (t : ℂ) * I) ∈ hcontour.U :=
    hcontour.strip (hline t)
  have hne (t : ℝ) : ((σz : ℂ) + (t : ℂ) * I) ≠ ((((1 : ℝ) / 6 : ℝ)) : ℂ) := by
    intro h
    exact hσp (by simpa using congrArg Complex.re h)
  have hne' (t : ℝ) : ((σz : ℂ) + (t : ℂ) * I) ≠ (1 / 6 : ℂ) := by
    rw [← one_div_six_cast]; exact hne t
  have hpt (t : ℝ) :
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((σz : ℂ) + (t : ℂ) * I) =
        PrincipalZShift.clearedKernel Z M W L R H ξ ((σz : ℂ) + (t : ℂ) * I) /
          (((σz : ℂ) + (t : ℂ) * I) - 1 / 6) := by
    have h := PrincipalZShift.clearedKernel_off_pole Z M W ζ L R H ξ ((σz : ℂ) + (t : ℂ) * I) (hne' t)
      (hcontour.regularization _ (hU t) (hne' t))
    exact eq_div_of_mul_eq (sub_ne_zero.mpr (hne' t)) (by rw [h]; ring)
  have hcont : Continuous (fun t : ℝ =>
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((σz : ℂ) + (t : ℂ) * I)) := by
    simp_rw [hpt]
    exact Continuous.div
      ((hcontour.holomorphic ξ hξ).continuousOn.comp_continuous (by fun_prop) hU)
      (by fun_prop) (fun t => sub_ne_zero.mpr (hne' t))
  refine ComparisonShiftProof.integrable_tail _ (hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ))
    hcont ?_
  intro t ht
  have him : (((σz : ℂ) + (t : ℂ) * I)).im = t := by simp
  have hd := hcontour.decay ξ ((σz : ℂ) + (t : ℂ) * I) hξ (hline t) (by rw [him]; exact ht)
  rw [him] at hd
  calc ‖PrincipalWShift.residueKernel Z M W ζ L H ξ ((σz : ℂ) + (t : ℂ) * I)‖
      ≤ hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |t|) ^ (-2 : ℝ) := hd
    _ = (hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ)) * (1 + |t|) ^ (-2 : ℝ) := by ring

private theorem zShift_one
    (Z : ℝ) (hZ : 1 ≤ Z)
    (M W ζ L R Hη : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (hcorrection : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ → H ξ 1 (1 / 6) = Hη ξ)
    (hcontour : PrincipalZShift.ZContourConditions Z M W ζ L R Hη H)
    (ξ : ℂ) (hξ : ξ.re = comparisonSigma₁) :
    comparisonVerticalIntegral comparisonZeta₁
        (PrincipalWShift.residueKernel Z M W ζ L H ξ) =
      comparisonVerticalIntegral PrincipalZShift.zLine
        (PrincipalWShift.residueKernel Z M W ζ L H ξ) +
        (R 1 / 6 * M (1 / 6) * W 1) * PrincipalZShift.transformKernel Z L Hη ξ := by
  have hap : PrincipalZShift.zLine < (1 : ℝ) / 6 := by norm_num [PrincipalZShift.zLine]
  have hpb : (1 : ℝ) / 6 < comparisonZeta₁ := by norm_num [comparisonZeta₁, comparisonDelta]
  have hle : PrincipalZShift.zLine ≤ comparisonZeta₁ := hap.le.trans hpb.le
  have hA : DifferentiableOn ℂ (fun z => PrincipalZShift.clearedKernel Z M W L R H ξ z)
      {z : ℂ | PrincipalZShift.zLine ≤ z.re ∧ z.re ≤ comparisonZeta₁} :=
    (hcontour.holomorphic ξ hξ).mono hcontour.strip
  have hF : ∀ z : ℂ, PrincipalZShift.zLine ≤ z.re → z.re ≤ comparisonZeta₁ →
      z ≠ ((((1 : ℝ) / 6 : ℝ)) : ℂ) →
      PrincipalWShift.residueKernel Z M W ζ L H ξ z =
        PrincipalZShift.clearedKernel Z M W L R H ξ z / (z - ((((1 : ℝ) / 6 : ℝ)) : ℂ)) := by
    intro z h1 h2 hz
    have hz' : z ≠ (1 / 6 : ℂ) := by rw [← one_div_six_cast]; exact hz
    have hzU : z ∈ hcontour.U := hcontour.strip ⟨h1, h2⟩
    have h := PrincipalZShift.clearedKernel_off_pole Z M W ζ L R H ξ z hz'
      (hcontour.regularization z hzU hz')
    rw [← one_div_six_cast] at h
    exact eq_div_of_mul_eq (sub_ne_zero.mpr hz) (by rw [h]; ring)
  have ha : Integrable (fun t : ℝ =>
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((PrincipalZShift.zLine : ℂ) + (t : ℂ) * I)) :=
    residueKernel_slice_integrable Z M W ζ L R Hη H hcontour ξ hξ (by simp)
  have hb : Integrable (fun t : ℝ =>
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((comparisonZeta₁ : ℂ) + (t : ℂ) * I)) :=
    residueKernel_slice_integrable Z M W ζ L R Hη H hcontour ξ hξ (by simp)
  have hbound : ∀ x ∈ Set.Icc PrincipalZShift.zLine comparisonZeta₁, ∀ y : ℝ, 1 ≤ |y| →
      ‖PrincipalWShift.residueKernel Z M W ζ L H ξ ((x : ℂ) + y * I)‖ ≤
        (hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ)) * (1 + |y|) ^ (-2 : ℝ) := by
    intro x hx y hy
    have hstrip : ((x : ℂ) + y * I) ∈ comparisonClosedStrip PrincipalZShift.zLine comparisonZeta₁ := by
      show PrincipalZShift.zLine ≤ (((x : ℂ) + y * I)).re ∧ (((x : ℂ) + y * I)).re ≤ comparisonZeta₁
      rw [show (((x : ℂ) + y * I)).re = x by simp]
      exact hx
    have him : (((x : ℂ) + y * I)).im = y := by simp
    have hd := hcontour.decay ξ ((x : ℂ) + y * I) hξ hstrip (by rw [him]; exact hy)
    rw [him] at hd
    calc ‖PrincipalWShift.residueKernel Z M W ζ L H ξ ((x : ℂ) + y * I)‖
        ≤ hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |y|) ^ (-2 : ℝ) := hd
      _ = (hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ)) * (1 + |y|) ^ (-2 : ℝ) := by ring
  have hbot : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in PrincipalZShift.zLine..comparisonZeta₁,
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((x : ℂ) + (-T) * I)) Filter.atTop (nhds 0) := by
    simpa using ComparisonShiftProof.horizontal_decay_limit
      (PrincipalWShift.residueKernel Z M W ζ L H ξ) PrincipalZShift.zLine comparisonZeta₁
      (hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ)) (-1) hle (by norm_num) hbound
  have htop : Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in PrincipalZShift.zLine..comparisonZeta₁,
      PrincipalWShift.residueKernel Z M W ζ L H ξ ((x : ℂ) + T * I)) Filter.atTop (nhds 0) := by
    simpa using ComparisonShiftProof.horizontal_decay_limit
      (PrincipalWShift.residueKernel Z M W ζ L H ξ) PrincipalZShift.zLine comparisonZeta₁
      (hcontour.C * (1 + |ξ.im|) ^ (-2 : ℝ)) 1 hle (by norm_num) hbound
  have h := ComparisonShiftProof.simple_pole_of_boundary_control
    (fun z => PrincipalZShift.clearedKernel Z M W L R H ξ z)
    (PrincipalWShift.residueKernel Z M W ζ L H ξ)
    hap hpb hA hF ha hb hbot htop
  rw [h, one_div_six_cast,
    clearedKernel_at_pole Z hZ M W L R Hη H ξ (hcorrection ξ hξ)]

private theorem doubleVerticalIntegral_z_shift
    (Z : ℝ) (hZ : 1 ≤ Z) (M W ζ L R Hη : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (hcorrection : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ → H ξ 1 (1 / 6) = Hη ξ)
    (hcontour : PrincipalZShift.ZContourConditions Z M W ζ L R Hη H) :
    PrincipalWShift.doubleVerticalIntegral comparisonSigma₁ comparisonZeta₁
        (PrincipalWShift.residueKernel Z M W ζ L H) =
      (R 1 / 6 * M (1 / 6) * W 1) *
        comparisonVerticalIntegral comparisonSigma₁ (PrincipalZShift.transformKernel Z L Hη) +
      PrincipalWShift.doubleVerticalIntegral comparisonSigma₁ PrincipalZShift.zLine
        (PrincipalWShift.residueKernel Z M W ζ L H) := by
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hJζ : Integrable (fun q : ℝ × ℝ => PrincipalWShift.residueKernel Z M W ζ L H
      ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (q.2 : ℂ) * I)) :=
    hcontour.endpoints comparisonZeta₁ (by simp)
  have hJz : Integrable (fun q : ℝ × ℝ => PrincipalWShift.residueKernel Z M W ζ L H
      ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (q.2 : ℂ) * I)) :=
    hcontour.endpoints PrincipalZShift.zLine (by simp)
  have hinner (t1 : ℝ) :
      (∫ t2 : ℝ, (PrincipalWShift.residueKernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (t2 : ℂ) * I) -
        PrincipalWShift.residueKernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (t2 : ℂ) * I))) =
      (2 * (Real.pi : ℂ)) * ((R 1 / 6 * M (1 / 6) * W 1) *
        PrincipalZShift.transformKernel Z L Hη ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I)) := by
    have hξre : (((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I)).re = comparisonSigma₁ := by simp
    rw [MeasureTheory.integral_sub
      (residueKernel_slice_integrable Z M W ζ L R Hη H hcontour _ hξre (by simp))
      (residueKernel_slice_integrable Z M W ζ L R Hη H hcontour _ hξre (by simp))]
    have e1 : (∫ t2 : ℝ, PrincipalWShift.residueKernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (t2 : ℂ) * I)) =
        (2 * (Real.pi : ℂ)) * comparisonVerticalIntegral comparisonZeta₁
          (PrincipalWShift.residueKernel Z M W ζ L H
            ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I)) := by
      unfold comparisonVerticalIntegral
      rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    have e2 : (∫ t2 : ℝ, PrincipalWShift.residueKernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (t2 : ℂ) * I)) =
        (2 * (Real.pi : ℂ)) * comparisonVerticalIntegral PrincipalZShift.zLine
          (PrincipalWShift.residueKernel Z M W ζ L H
            ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I)) := by
      unfold comparisonVerticalIntegral
      rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    rw [e1, e2, zShift_one Z hZ M W ζ L R Hη H hcorrection hcontour _ hξre]
    ring
  have hkey : (∫ q : ℝ × ℝ, PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (q.2 : ℂ) * I)) -
      (∫ q : ℝ × ℝ, PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (q.2 : ℂ) * I)) =
      (2 * (Real.pi : ℂ)) ^ 2 * ((R 1 / 6 * M (1 / 6) * W 1) *
        comparisonVerticalIntegral comparisonSigma₁ (PrincipalZShift.transformKernel Z L Hη)) := by
    rw [← MeasureTheory.integral_sub hJζ hJz]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    rw [MeasureTheory.integral_prod
      (fun q : ℝ × ℝ => PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (q.2 : ℂ) * I) -
        PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (q.2 : ℂ) * I))
      (hJζ.sub hJz)]
    have hfun : (fun t1 : ℝ => ∫ t2 : ℝ, (PrincipalWShift.residueKernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (t2 : ℂ) * I) -
        PrincipalWShift.residueKernel Z M W ζ L H
          ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (t2 : ℂ) * I))) =
      (fun t1 : ℝ => (2 * (Real.pi : ℂ)) * ((R 1 / 6 * M (1 / 6) * W 1) *
        PrincipalZShift.transformKernel Z L Hη ((comparisonSigma₁ : ℂ) + (t1 : ℂ) * I))) := by
      funext t1
      exact hinner t1
    rw [hfun, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have e3 : (∫ t : ℝ, PrincipalZShift.transformKernel Z L Hη
          ((comparisonSigma₁ : ℂ) + (t : ℂ) * I)) =
        (2 * (Real.pi : ℂ)) * comparisonVerticalIntegral comparisonSigma₁
          (PrincipalZShift.transformKernel Z L Hη) := by
      unfold comparisonVerticalIntegral
      rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    rw [e3]
    ring
  have hJrel : (∫ q : ℝ × ℝ, PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((comparisonZeta₁ : ℂ) + (q.2 : ℂ) * I)) =
      (∫ q : ℝ × ℝ, PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (q.1 : ℂ) * I) ((PrincipalZShift.zLine : ℂ) + (q.2 : ℂ) * I)) +
      (2 * (Real.pi : ℂ)) ^ 2 * ((R 1 / 6 * M (1 / 6) * W 1) *
        comparisonVerticalIntegral comparisonSigma₁ (PrincipalZShift.transformKernel Z L Hη)) := by
    rw [← hkey]
    ring
  unfold PrincipalWShift.doubleVerticalIntegral
  rw [hJrel, mul_add]
  rw [show (2 * (Real.pi : ℂ))⁻¹ ^ 2 * ((2 * (Real.pi : ℂ)) ^ 2 *
        ((R 1 / 6 * M (1 / 6) * W 1) *
          comparisonVerticalIntegral comparisonSigma₁ (PrincipalZShift.transformKernel Z L Hη))) =
      (R 1 / 6 * M (1 / 6) * W 1) *
        comparisonVerticalIntegral comparisonSigma₁ (PrincipalZShift.transformKernel Z L Hη) by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h2pi, one_pow, one_mul]]
  ring

private theorem numerator_pole
    (Z : ℝ) (hZ : 1 ≤ Z)
    (M W ζ L R Hη : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (hcorrection : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ → H ξ 1 (1 / 6) = Hη ξ)
    (hcontour : PrincipalZShift.ZContourConditions Z M W ζ L R Hη H) :
    R 1 * PrincipalWShift.doubleVerticalIntegral comparisonSigma₁ comparisonZeta₁
        (PrincipalWShift.residueKernel Z M W ζ L H) =
      PrincipalZShift.c₀ (R 1) M W * comparisonVerticalIntegral comparisonSigma₁
        (PrincipalZShift.transformKernel Z L Hη) +
      PrincipalZShift.Rz Z (R 1) M W ζ L H := by
  rw [doubleVerticalIntegral_z_shift Z hZ M W ζ L R Hη H hcorrection hcontour]
  unfold PrincipalZShift.c₀ PrincipalZShift.Rz
  ring

theorem decomposition_of_local_correction
    (Z : ℝ) (hZ : 1 ≤ Z)
    (M W ζ L R Hη : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (hcorrection : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ → H ξ 1 (1 / 6) = Hη ξ)
    (hinitial : PrincipalZShift.InitialContourConditions Z M W ζ L H)
    (hw : PrincipalZShift.WContourConditions Z M W ζ L R H)
    (hz : PrincipalZShift.ZContourConditions Z M W ζ L R Hη H)
    (hxi : PrincipalZShift.XiContourConditions Z L Hη) :
    PrincipalWShift.J Z M W ζ L H 4 4 2 =
      PrincipalZShift.c₀ (R 1) M W * PrincipalZShift.f Z L Hη +
        PrincipalZShift.Rw Z M W ζ L H +
        PrincipalZShift.Rz Z (R 1) M W ζ L H := by
  have hi := PrincipalWShift.initial_corridor Z hZ M W ζ L H
    hinitial.U hinitial.C hinitial.C_nonneg hinitial.open_U hinitial.corridor
    hinitial.holomorphic_xi hinitial.holomorphic_w hinitial.holomorphic_z hinitial.decay
  have hw' := PrincipalWShift.numerator_pole Z hZ M W ζ L R H
    hw.U hw.C hw.C_nonneg hw.open_U hw.strip hw.regularization
    hw.holomorphic hw.decay hw.endpoints hw.residue
  have hz' := numerator_pole Z hZ M W ζ L R Hη H hcorrection hz
  have hx' := (PrincipalZShift.xi_shift Z L Hη hxi).2.2
  rw [hi, hw', hz', hx']
  unfold PrincipalZShift.Rw
  ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
