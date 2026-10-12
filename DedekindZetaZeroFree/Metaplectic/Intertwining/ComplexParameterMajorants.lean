module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Complex.MixedParameterDerivativeFormula
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OpenCellDistributionsAndDivergence

@[expose] public section

section

namespace DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set Filter
open scoped ContDiff Matrix.Norms.Elementwise Real Topology

noncomputable def rowRatio (g : ComplexGL2) : ℝ :=
  ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g

noncomputable def bottomRowLine (g : ComplexGL2) : ComplexProjectiveLine :=
  if (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 then projectiveInfinity 0
  else projectiveOpen
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)

end DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant

theorem halfPlane_neighborhood (s₀ : ℂ) (hs₀ : -(1 / 6 : ℝ) < s₀.re) :
    ∃ ε δ b R : ℝ, 0 < ε ∧ 0 < δ ∧ 0 ≤ R ∧
      1 + δ < 4 / 3 + 2 * b ∧
      Metric.ball s₀ ε ⊆ {s : ℂ | -(1 / 6 : ℝ) < s.re} ∧
      ∀ s ∈ Metric.ball s₀ ε, b ≤ s.re ∧ ‖s‖ ≤ R := by
  set ε : ℝ := (s₀.re + 1 / 6) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set b : ℝ := s₀.re - ε with hb
  have hb_gt : -(1 / 6 : ℝ) < b := by rw [hb, hε]; linarith
  have hδpos : 0 < 1 / 3 + 2 * b := by linarith
  refine ⟨ε, (1 / 3 + 2 * b) / 2, b, ‖s₀‖ + ε,
    hεpos, by linarith, by positivity, by linarith, ?_, ?_⟩
  · intro s hs
    rw [Metric.mem_ball] at hs
    have hdist : ‖s - s₀‖ < ε := by rwa [dist_eq_norm] at hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      have := RCLike.abs_re_le_norm (s - s₀)
      simpa using this
    have hnorm : 0 ≤ ‖s - s₀‖ := norm_nonneg _
    have hlower : s₀.re - ‖s - s₀‖ ≤ s.re := by
      have := (abs_le.mp h1).1
      linarith
    have hbs : b < s.re := by rw [hb]; linarith
    exact lt_trans hb_gt hbs
  · intro s hs
    rw [Metric.mem_ball] at hs
    have hdist : ‖s - s₀‖ < ε := by rwa [dist_eq_norm] at hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      have := RCLike.abs_re_le_norm (s - s₀)
      simpa using this
    have hb_le : b ≤ s.re := by
      have hnorm : 0 ≤ ‖s - s₀‖ := norm_nonneg _
      have : s₀.re - ‖s - s₀‖ ≤ s.re := by
        have := (abs_le.mp h1).1
        linarith
      rw [hb]; linarith
    refine ⟨hb_le, ?_⟩
    have : ‖s‖ ≤ ‖s - s₀‖ + ‖s₀‖ := by
      calc ‖s‖ = ‖(s - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖s - s₀‖ + ‖s₀‖ := norm_add_le _ _
    linarith

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant

end

section

namespace DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set Filter
open scoped ContDiff Matrix.Norms.Elementwise Real Topology

structure CompactPicture where
  toFun : ComplexProjectiveLine → ℂ
  open_smooth : ContDiff ℝ ∞ (toFun ∘ projectiveOpen)
  infinity_smooth : ContDiff ℝ ∞ (toFun ∘ projectiveInfinity)

instance : CoeFun CompactPicture (fun _ => ComplexProjectiveLine → ℂ) :=
  ⟨CompactPicture.toFun⟩

noncomputable def sourceSeminorm (j : ℕ) (φ : CompactPicture) : ℝ :=
  sSup ({0} ∪ {r : ℝ | ∃ q : ℕ, q ≤ j ∧ ∃ z : ℂ,
    z ∈ Metric.closedBall (0 : ℂ) 1 ∧
      (r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ∨
       r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖)})

lemma sourceSeminorm_bddAbove (j : ℕ) (φ : CompactPicture) :
    BddAbove ({0} ∪ {r : ℝ | ∃ q : ℕ, q ≤ j ∧ ∃ z : ℂ,
      z ∈ Metric.closedBall (0 : ℂ) 1 ∧
        (r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ∨
         r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖)}) := by
  have hb : ∀ q : ℕ, BddAbove
      ((fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖) '' Metric.closedBall 0 1 ∪
       (fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖) '' Metric.closedBall 0 1) := by
    intro q
    apply BddAbove.union
    · exact (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
        (φ.open_smooth.continuous_iteratedFDeriv (by simp)).norm.continuousOn
    · exact (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
        (φ.infinity_smooth.continuous_iteratedFDeriv (by simp)).norm.continuousOn
  have hfin : BddAbove (⋃ q ∈ Finset.range (j + 1),
      ((fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖) '' Metric.closedBall 0 1 ∪
       (fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖) '' Metric.closedBall 0 1)) := by
    exact (Finset.finite_toSet _).bddAbove_biUnion.mpr (fun q _ => hb q)
  apply BddAbove.union bddAbove_singleton
  apply hfin.mono
  rintro r ⟨q, hq, z, hz, hr⟩
  apply mem_iUnion₂.mpr
  refine ⟨q, Finset.mem_range.mpr (by omega), ?_⟩
  rcases hr with rfl | rfl
  · exact Or.inl ⟨z, hz, rfl⟩
  · exact Or.inr ⟨z, hz, rfl⟩

lemma sourceSeminorm_nonneg (j : ℕ) (φ : CompactPicture) : 0 ≤ sourceSeminorm j φ := by
  unfold sourceSeminorm
  exact le_csSup (sourceSeminorm_bddAbove j φ) (Or.inl (mem_singleton 0))

lemma norm_iteratedFDeriv_open_le_sourceSeminorm (j q : ℕ) (hq : q ≤ j)
    (φ : CompactPicture) (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
    ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ≤ sourceSeminorm j φ := by
  unfold sourceSeminorm
  exact le_csSup (sourceSeminorm_bddAbove j φ) (Or.inr ⟨q, hq, z, hz, Or.inl rfl⟩)

lemma norm_iteratedFDeriv_infinity_le_sourceSeminorm (j q : ℕ) (hq : q ≤ j)
    (φ : CompactPicture) (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
    ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖ ≤ sourceSeminorm j φ := by
  unfold sourceSeminorm
  exact le_csSup (sourceSeminorm_bddAbove j φ) (Or.inr ⟨q, hq, z, hz, Or.inr rfl⟩)

noncomputable def forwardSection (s : ℂ) (φ : CompactPicture) (g : ComplexGL2) : ℂ :=
  Complex.exp (((4 / 3 : ℂ) + 2 * s) * (Real.log (rowRatio g) : ℂ)) *
    φ (bottomRowLine g)

 lemma ratio_wn (x : ℂ) :
    rowRatio (weyl * upperUnipotent x) = (1 + ‖x‖ ^ 2)⁻¹ := by
  unfold rowRatio bottomRowNormSq weyl upperUnipotent
  simp [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]

structure CompactGroupChart (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  closedSet : Set (Fin n → ℝ)
  closedSet_compact : IsCompact closedSet
  closedSet_subset : closedSet ⊆ domain
  lift : (Fin n → ℝ) → ComplexSU2
  lift_smooth : ContDiffOn ℝ ∞
    (fun u => (lift u : Matrix (Fin 2) (Fin 2) ℂ)) domain

structure ChartDifferentialOperator (n j : ℕ) (U : Set (Fin n → ℝ)) where
  coefficient : (q : Fin (j + 1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ
  coefficient_smooth : ∀ (q : Fin (j + 1)) (a : Fin q.val → Fin n),
    ContDiffOn ℝ ∞ (coefficient q a) U

noncomputable def ChartDifferentialOperator.apply {n j : ℕ} {U : Set (Fin n → ℝ)}
    (D : ChartDifferentialOperator n j U) (f : (Fin n → ℝ) → ℂ)
    (u : Fin n → ℝ) : ℂ :=
  ∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n,
    D.coefficient q a u * iteratedFDeriv ℝ q.val f u
      (fun i => Pi.single (a i) (1 : ℝ))

noncomputable def planarEnvelope (p : ℝ) (x : ℂ) : ℝ :=
  Real.rpow (1 + ‖x‖ ^ 2) (-p)

noncomputable def planarHaar (h : ℝ) : Measure ℂ :=
  ENNReal.ofReal h • euclideanArea

private lemma radial_rpow_integral (p : ℝ) (hp : 1 < p) :
    ∫ r in Set.Ioi (0 : ℝ), r * (1 + r ^ 2) ^ (-p) = 1 / (2 * (p - 1)) := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hne : (2 * (1 - p)) ≠ 0 := by linarith
  set g : ℝ → ℝ := fun r => (1 + r ^ 2) ^ (1 - p) / (2 * (1 - p)) with hgdef
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (x * (1 + x ^ 2) ^ (-p)) x := by
    intro x _
    have hxpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hd1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have hf : HasDerivAt (fun y : ℝ => y ^ (1 - p))
        ((1 - p) * (1 + x ^ 2) ^ ((1 - p) - 1)) (1 + x ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')
    have hd2 : HasDerivAt (fun r : ℝ => (1 + r ^ 2) ^ (1 - p))
        ((1 - p) * (1 + x ^ 2) ^ ((1 - p) - 1) * (2 * x)) x :=
      HasDerivAt.comp (h := fun r : ℝ => 1 + r ^ 2) (hh₂ := hf) (hh := hd1)
    have hd3 : HasDerivAt (fun r : ℝ => (1 + r ^ 2) ^ (1 - p) / (2 * (1 - p)))
        (((1 - p) * (1 + x ^ 2) ^ ((1 - p) - 1) * (2 * x)) / (2 * (1 - p))) x :=
      hd2.div_const (2 * (1 - p))
    have heq : ((1 - p) * (1 + x ^ 2) ^ ((1 - p) - 1) * (2 * x)) / (2 * (1 - p))
        = x * (1 + x ^ 2) ^ (-p) := by
      rw [show (1 - p - 1 : ℝ) = -p by ring]
      rw [div_eq_iff hne]
      ring
    have hgfun : (fun r : ℝ => (1 + r ^ 2) ^ (1 - p) / (2 * (1 - p))) = g := by
      funext r; rw [hgdef]
    rwa [hgfun, heq] at hd3
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), (0 : ℝ) ≤ x * (1 + x ^ 2) ^ (-p) := by
    intro x hx
    have hx1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
    exact mul_nonneg hx.le (Real.rpow_nonneg hx1.le _)
  have htend : Tendsto g atTop (𝓝 0) := by
    have hbase : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1
        (by simpa using tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num))
    have h1 : Tendsto (fun r : ℝ => (1 + r ^ 2) ^ (-(p - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hp1).comp hbase
    have h2 : Tendsto (fun r : ℝ => (1 + r ^ 2) ^ (-(p - 1)) / (2 * (1 - p)))
        atTop (𝓝 0) := by
      simpa using h1.div_const (2 * (1 - p))
    have hg' : g = fun r : ℝ => (1 + r ^ 2) ^ (-(p - 1)) / (2 * (1 - p)) := by
      funext r
      rw [hgdef, show (1 - p : ℝ) = -(p - 1) by ring]
    rwa [hg']
  have hmain := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  rw [hmain, show g 0 = 1 / (2 * (1 - p)) by simp [hgdef]]
  rw [show (1 - p : ℝ) = -(p - 1) by ring]
  field_simp
  ring

 lemma planarEnvelope_volume_integral (p : ℝ) (hp : 1 < p) :
    ∫ x : ℂ, planarEnvelope p x = π / (p - 1) := by
  have hrad := radial_rpow_integral p hp
  have h2pi : ∫ _ in Set.Ioo (-π) π, (1 : ℝ) = 2 * π := by
    rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [Real.pi_nonneg]),
      sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
  calc
    ∫ x : ℂ, planarEnvelope p x
        = ∫ x : ℂ, (1 + ‖x‖ ^ 2) ^ (-p) := rfl
    _ = ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
          q.1 • ((1 + ‖Complex.polarCoord.symm q‖ ^ 2) ^ (-p)) := by
          rw [← Complex.integral_comp_polarCoord_symm (f := fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-p))]
          rfl
    _ = ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
          q.1 * ((1 + q.1 ^ 2) ^ (-p)) := by
          refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
          intro q hq
          have hq1 : (0 : ℝ) < q.1 := Set.mem_Ioi.mp hq.1
          simp only [Complex.norm_polarCoord_symm, smul_eq_mul]
          rw [abs_of_pos hq1]
    _ = (∫ r in Set.Ioi (0 : ℝ), r * (1 + r ^ 2) ^ (-p)) *
          ∫ _ in Set.Ioo (-π) π, (1 : ℝ) := by
          rw [Measure.volume_eq_prod ℝ ℝ,
            ← setIntegral_prod_mul (fun r : ℝ => r * (1 + r ^ 2) ^ (-p))
              (fun _ => (1 : ℝ)) (Set.Ioi (0 : ℝ)) (Set.Ioo (-π) π)]
          refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
          intro q _
          simp only [Pi.one_apply, mul_one]
    _ = π / (p - 1) := by
          rw [hrad, h2pi]
          field_simp

private lemma planarEnvelope_volume_integrable (p : ℝ) (hp : 1 < p) :
    Integrable (planarEnvelope p) (volume : Measure ℂ) := by
  by_contra h
  have hval := planarEnvelope_volume_integral p hp
  rw [integral_undef h] at hval
  have hpos : (0 : ℝ) < π / (p - 1) := by positivity
  linarith

theorem planarEnvelope_integrable (h p : ℝ) (hh : 0 < h) (hp : 1 < p) :
    Integrable (planarEnvelope p) (planarHaar h) := by
  rw [planarHaar, euclideanArea]
  exact (integrable_smul_measure (c := ENNReal.ofReal h)
    (ENNReal.ofReal_ne_zero_iff.mpr hh) ENNReal.ofReal_ne_top).mpr
    (planarEnvelope_volume_integrable p hp)

private lemma rowRatio_pos (g : ComplexGL2) : 0 < rowRatio g := by
  have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 :=
    (Matrix.GeneralLinearGroup.det g).ne_zero
  have hr : 0 < bottomRowNormSq g := by
    unfold bottomRowNormSq
    by_contra hn
    have he : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hn) (by positivity)
    have h0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖]
    have h1 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖]
    apply hdet
    simp [Matrix.det_fin_two, h0, h1]
  exact div_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero) hr

 lemma forwardSection_real_formula (t : ℝ) (φ : CompactPicture) (g : ComplexGL2) :
    forwardSection (t : ℂ) φ g = sphericalFunction (positiveParameter + t) g * φ (bottomRowLine g) := by
  unfold forwardSection sphericalFunction
  change Complex.exp (((4 / 3 : ℂ) + 2 * (t : ℂ)) * (Real.log (rowRatio g) : ℂ)) * _ =
    (((rowRatio g) ^ (1 + 2 * (positiveParameter + t)) : ℝ) : ℂ) * _
  rw [Real.rpow_def_of_pos (rowRatio_pos g) (1 + 2 * (positiveParameter + t))]
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  norm_num [positiveParameter]
  ring

private lemma bottomRowLine_upper (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    bottomRowLine (upperTriangular a d b * g) = bottomRowLine g := by
  have hup : (upperTriangular a d b : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  unfold bottomRowLine
  rw [Matrix.GeneralLinearGroup.coe_mul, hup]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, d.ne_zero]
  split_ifs
  · rfl
  · congr 1
    exact mul_div_mul_left _ _ d.ne_zero

private lemma bottomRowLine_wn (x : ℂ) :
    bottomRowLine (weyl * upperUnipotent x) = projectiveOpen x := by
  unfold bottomRowLine weyl upperUnipotent
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private lemma bottomRowLine_lower (u : ℂ) :
    bottomRowLine (lowerUnipotent u) = projectiveInfinity u := by
  by_cases hu : u = 0
  · subst u
    simp [bottomRowLine, lowerUnipotent]
  · have hlo : (lowerUnipotent u : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; u, 1] := rfl
    unfold bottomRowLine
    rw [hlo]
    simp [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, hu]
    exact (projective_chart_transition u hu).symm

theorem forwardSection_real_mem (t : ℝ) (φ : CompactPicture) :
    forwardSection (t : ℂ) φ ∈ principalSeriesSubmodule (positiveParameter + t) := by
  have hs := (sphericalSection (positiveParameter + t)).property
  change HasCovariance (positiveParameter + t) (sphericalFunction (positiveParameter + t)) ∧
    ContDiff ℝ ∞ (openCoordinate (sphericalFunction (positiveParameter + t))) ∧
    ContDiff ℝ ∞ (infinityCoordinate (sphericalFunction (positiveParameter + t))) at hs
  change HasCovariance (positiveParameter + t) (forwardSection (t : ℂ) φ) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro a d b g
    rw [forwardSection_real_formula, forwardSection_real_formula,
      hs.1 a d b g, bottomRowLine_upper]
    ring
  · have he : openCoordinate (forwardSection (t : ℂ) φ) =
        fun x => openCoordinate (sphericalFunction (positiveParameter + t)) x *
          (φ ∘ projectiveOpen) x := by
      funext x
      simp [openCoordinate, forwardSection_real_formula, bottomRowLine_wn]
    rw [he]
    exact hs.2.1.mul φ.open_smooth
  · have he : infinityCoordinate (forwardSection (t : ℂ) φ) =
        fun u => infinityCoordinate (sphericalFunction (positiveParameter + t)) u *
          (φ ∘ projectiveInfinity) u := by
      funext u
      simp [infinityCoordinate, forwardSection_real_formula, bottomRowLine_lower]
    rw [he]
    exact hs.2.2.mul φ.infinity_smooth

structure CompactMatrixChart (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  closedSet : Set (Fin n → ℝ)
  closedSet_compact : IsCompact closedSet
  closedSet_subset : closedSet ⊆ domain
  lift : (Fin n → ℝ) → ComplexGL2
  lift_smooth : ContDiffOn ℝ ∞
    (fun u => (lift u : Matrix (Fin 2) (Fin 2) ℂ)) domain

noncomputable def mixedReconstructedDerivative {n j : ℕ}
    (chart : CompactMatrixChart n)
    (D : ChartDifferentialOperator n j chart.domain) (m : ℕ)
    (s : ℂ) (φ : CompactPicture) (x : ℂ) (u : Fin n → ℝ) : ℂ :=
  iteratedDeriv m (fun t : ℂ =>
    D.apply (fun v =>
      forwardSection t φ (weyl * upperUnipotent x * chart.lift v)) u) s

theorem compact_g_local_halfPlane_majorant (s₀ : ℂ)
    (hs₀ : -(1 / 6 : ℝ) < s₀.re) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      Metric.ball s₀ ε ⊆ {s : ℂ | -(1 / 6 : ℝ) < s.re} ∧
      ∀ (n j : ℕ) (chart : CompactMatrixChart n)
        (D : ChartDifferentialOperator n j chart.domain) (m : ℕ),
        ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (s : ℂ) (φ : CompactPicture) (x : ℂ)
          (u : Fin n → ℝ), s ∈ Metric.ball s₀ ε → u ∈ chart.closedSet →
            ‖mixedReconstructedDerivative chart D m s φ x u‖ ≤
              C * sourceSeminorm N φ * planarEnvelope (1 + δ) x := by
  obtain ⟨ε, δ, b, R, hε, hδ, hR, hp, hball, hb⟩ :=
    RepresentationTheory.KPComplexIntertwinerParameterMajorant.halfPlane_neighborhood s₀ hs₀
  refine ⟨ε, δ, hε, hδ, hball, ?_⟩
  intro n j chart D m
  obtain ⟨C, N, hC, hc⟩ :=
    RepresentationTheory.KPComplexIntertwinerParameterMajorant.compact_matrix_weighted_bound n j
      chart.domain chart.closedSet chart.domain_open chart.closedSet_compact
      chart.closedSet_subset chart.lift chart.lift_smooth D.coefficient D.coefficient_smooth
      m R b (1 + δ) hR hp
  refine ⟨C, N, hC, ?_⟩
  intro s φ x u hs hu
  exact hc s φ φ.open_smooth φ.infinity_smooth x u (hb s hs).2 (hb s hs).1 hu

end DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant

end
