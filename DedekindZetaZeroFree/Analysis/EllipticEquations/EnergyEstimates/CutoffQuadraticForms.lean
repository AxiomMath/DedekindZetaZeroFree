module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

open MeasureTheory KPContLocalNorm Raw

private theorem re_ofReal_sq (a : ℝ) : RCLike.re ((a : ℂ) ^ 2) = a ^ 2 := by
  change ((a : ℂ) ^ 2).re = a ^ 2
  rw [sq, Complex.mul_re]
  simp
  ring

theorem lp_norm_sq_eq_integral {n : ℕ} {B : LocalBall n} (f : BallL2 B) :
    ‖f‖ ^ 2 = ∫ x in B.carrier, ‖f x‖ ^ 2 := by
  have h1 : RCLike.re (inner ℂ f f) = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact re_ofReal_sq ‖f‖
  rw [← h1, MeasureTheory.L2.inner_def, ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_self_eq_norm_sq_to_K]
  exact re_ofReal_sq ‖f x‖
private theorem raw_complex_quadratic_real {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℂ) :
    (∑ i, ∑ j, (a i j : ℂ) * g j * star (g i)).re =
      (∑ i, ∑ j, a i j * (g i).re * (g j).re) +
      (∑ i, ∑ j, a i j * (g i).im * (g j).im) := by
  change Complex.reAddGroupHom (∑ i, ∑ j, _) = _
  simp only [map_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ((a i j : ℂ) * g j * star (g i)).re = _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem Raw.Coefficients.complex_ellipticity {n : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (D : Coefficients B cρ Cρ κ Λ)
    (x : Space n) (hx : x ∈ B.carrier) (g : Fin n → ℂ) :
    κ * (∑ i, ‖g i‖ ^ 2) ≤
      (∑ i, ∑ j, (D.matrix x i j : ℂ) * g j * star (g i)).re := by
  let reG : Space n := WithLp.toLp 2 (fun i => (g i).re)
  let imG : Space n := WithLp.toLp 2 (fun i => (g i).im)
  have hre := D.ellipticity x hx reG
  have him := D.ellipticity x hx imG
  rw [EuclideanSpace.real_norm_sq_eq] at hre him
  change κ * (∑ i, (g i).re ^ 2) ≤ _ at hre
  change κ * (∑ i, (g i).im ^ 2) ≤ _ at him
  rw [raw_complex_quadratic_real]
  have hn : (∑ i, ‖g i‖ ^ 2) = (∑ i, (g i).re ^ 2) + (∑ i, (g i).im ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  rw [hn, mul_add]
  exact add_le_add hre him

theorem Raw.Coefficients.matrix_entry_bound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hκ : 0 ≤ κ)
    (x : Space n) (hx : x ∈ B.carrier) (i j : Fin n) : |D.matrix x i j| ≤ Λ := by
  classical
  have hdi : κ ≤ D.matrix x i i := by
    have hh := D.ellipticity x hx (EuclideanSpace.single i (1 : ℝ))
    simpa [EuclideanSpace.norm_single, EuclideanSpace.single_apply, mul_ite, ite_mul] using hh
  have hdiu : D.matrix x i i ≤ Λ := by
    have hh := D.upper_bound x hx (EuclideanSpace.single i (1 : ℝ))
    simpa [EuclideanSpace.norm_single, EuclideanSpace.single_apply, mul_ite, ite_mul] using hh
  have hdju : D.matrix x j j ≤ Λ := by
    have hh := D.upper_bound x hx (EuclideanSpace.single j (1 : ℝ))
    simpa [EuclideanSpace.norm_single, EuclideanSpace.single_apply, mul_ite, ite_mul] using hh
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hκ.trans hdi)]
    exact hdiu
  · have hplus := D.ellipticity x hx (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ))
    have hminus := D.ellipticity x hx (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ))
    have hp : 0 ≤ ∑ a, ∑ b, D.matrix x a b *
        (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ)) a *
        (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ)) b :=
      (mul_nonneg hκ (sq_nonneg _)).trans hplus
    have hm : 0 ≤ ∑ a, ∑ b, D.matrix x a b *
        (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)) a *
        (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)) b :=
      (mul_nonneg hκ (sq_nonneg _)).trans hminus
    simp only [PiLp.add_apply, PiLp.sub_apply, EuclideanSpace.single_apply,
      mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at hp hm
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_add_distrib, Finset.sum_sub_distrib] at hp hm
    rw [D.symmetric x hx j i] at hp hm
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem Raw.Coefficients.mixed_cutoff_form_bound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hκ : 0 ≤ κ)
    (x : Space n) (hx : x ∈ B.carrier) {K : ℝ} (hK : 0 ≤ K)
    (t : ℝ) (g d : Fin n → ℂ) (v : ℂ) (hd : ∀ i, ‖d i‖ ≤ K) :
    ‖∑ i, ∑ j, (D.matrix x i j : ℂ) * g j * star ((2 * (t : ℂ) * d i) * v)‖ ≤
      2 * |t| * K * Λ * (n : ℝ) * (∑ j, ‖g j‖) * ‖v‖ := by
  classical
  let i₀ : Fin n := ⟨0, B.dimension_pos⟩
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (D.matrix_entry_bound hκ x hx i₀ i₀)
  calc
    ‖∑ i, ∑ j, (D.matrix x i j : ℂ) * g j * star ((2 * (t : ℂ) * d i) * v)‖ ≤
        ∑ i, ∑ j, ‖(D.matrix x i j : ℂ) * g j * star ((2 * (t : ℂ) * d i) * v)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, Λ * ‖g j‖ * (2 * |t| * K * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      norm_num only [Complex.norm_ofNat]
      gcongr
      · exact D.matrix_entry_bound hκ x hx i j
      · exact hd i
    _ = 2 * |t| * K * Λ * (n : ℝ) * (∑ j, ‖g j‖) * ‖v‖ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem uniform_cutoff_with_derivative_bound (n : ℕ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (inner outer : LocalBall n),
      inner.center = outer.center → inner.radius = r → outer.radius = R →
      ∃ η : TestFunction outer.toOpens ℝ ⊤,
        (∀ x ∈ inner.carrier, η x = 1) ∧
        (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
        (∀ (i : Fin n) x,
          ‖coordinateDerivativeList [i] (fun y => (η y : ℂ)) x‖ ≤ K) := by
  let b : ContDiffBump (0 : Space n) := ⟨r, (r + R) / 2, hr, by linarith⟩
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  obtain ⟨K, hK⟩ := b.hasCompactSupport.fderiv ℝ |>.exists_bound_of_continuous
    (hb.continuous_fderiv (by simp))
  refine ⟨|K| + 1, by positivity, ?_⟩
  intro inner outer hcenter hir hor
  let g : Space n → ℝ := fun x => b (x - outer.center)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hb.comp (contDiff_id.sub contDiff_const)
  have hts : tsupport g ⊆ outer.carrier := by
    change tsupport (b ∘ (Homeomorph.subRight outer.center)) ⊆ outer.carrier
    rw [tsupport_comp_eq_preimage, b.tsupport_eq]
    intro x hx
    have hh : dist (x - outer.center) 0 ≤ (r + R) / 2 := hx
    have hnorm : dist x outer.center ≤ (r + R) / 2 := by
      simpa [dist_eq_norm] using hh
    change dist x outer.center < outer.radius
    rw [hor]
    linarith
  have hcompact : HasCompactSupport g := by
    exact b.hasCompactSupport.comp_homeomorph (Homeomorph.subRight outer.center)
  let η : TestFunction outer.toOpens ℝ ⊤ := ⟨g, hg, hcompact, hts⟩
  refine ⟨η, ?_, ?_, ?_⟩
  · intro x hx
    change b (x - outer.center) = 1
    apply b.one_of_mem_closedBall
    change dist (x - outer.center) 0 ≤ r
    have hh : dist x outer.center < r := by simpa [LocalBall.carrier, hcenter, hir] using hx
    simpa [dist_eq_norm] using hh.le
  · intro x
    exact ⟨b.nonneg, b.le_one⟩
  · intro i x
    have hdg : fderiv ℝ g x = fderiv ℝ b (x - outer.center) := by
      change fderiv ℝ (b ∘ (fun y => id y - outer.center)) x = _
      rw [fderiv_comp x (hb.differentiable (by simp)).differentiableAt
        ((differentiable_id.sub_const outer.center).differentiableAt)]
      rw [fderiv_sub_const, fderiv_id, ContinuousLinearMap.comp_id]
      rfl
    have hcast : fderiv ℝ (fun y => (η y : ℂ)) x =
        Complex.ofRealCLM.comp (fderiv ℝ g x) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ g) x = _
      rw [fderiv_comp x Complex.ofRealCLM.differentiableAt
        (hg.differentiable (by simp)).differentiableAt, ContinuousLinearMap.fderiv]
    change ‖fderiv ℝ (fun y => (η y : ℂ)) x (EuclideanSpace.single i 1)‖ ≤ _
    rw [hcast, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      Complex.norm_real, hdg]
    have hbound := (fderiv ℝ b (x - outer.center)).le_opNorm (EuclideanSpace.single i 1)
    simp only [EuclideanSpace.norm_single, norm_one, mul_one] at hbound
    exact hbound.trans ((hK _).trans (by linarith [le_abs_self K]))

private theorem young_sum {n : ℕ} (a T : ℝ) (ha : 0 < a) (g : Fin n → ℂ)
    (t : ℝ) (v : ℂ) :
    T * |t| * (∑ j, ‖g j‖) * ‖v‖ ≤
      a / 2 * (t ^ 2 * ∑ j, ‖g j‖ ^ 2) +
        (n : ℝ) * T ^ 2 / (2 * a) * ‖v‖ ^ 2 := by
  have hp (j : Fin n) :
      T * |t| * ‖g j‖ * ‖v‖ ≤
        a / 2 * (t ^ 2 * ‖g j‖ ^ 2) + T ^ 2 / (2 * a) * ‖v‖ ^ 2 := by
    have hh := sq_nonneg (a * |t| * ‖g j‖ - T * ‖v‖)
    have ht : |t| ^ 2 = t ^ 2 := sq_abs t
    have hi : 0 < 2 * a := by positivity
    apply (mul_le_mul_iff_left₀ hi).mp
    have he : (a / 2 * (t ^ 2 * ‖g j‖ ^ 2) + T ^ 2 / (2 * a) * ‖v‖ ^ 2) * (2 * a) =
        a ^ 2 * (t ^ 2 * ‖g j‖ ^ 2) + T ^ 2 * ‖v‖ ^ 2 := by field_simp
    rw [he, ← ht]
    nlinarith [hh]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
    mul_assoc, mul_div_assoc, mul_left_comm, mul_comm] using hh

theorem pointwise_cutoff_coercivity {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ) (hκ : 0 < κ)
    (x : Space n) (hx : x ∈ B.carrier) {K : ℝ} (hK : 0 ≤ K)
    (t : ℝ) (g d : Fin n → ℂ) (v : ℂ) (hd : ∀ i, ‖d i‖ ≤ K) :
    (cρ * κ) / 2 * (t ^ 2 * ∑ i, ‖g i‖ ^ 2) ≤
      ((D.density x : ℂ) * ∑ i, ∑ j, (D.matrix x i j : ℂ) * g j *
        star ((t : ℂ) ^ 2 * g i + (2 * (t : ℂ) * d i) * v)).re +
      (n : ℝ) * (Cρ * (2 * K * Λ * (n : ℝ))) ^ 2 / (2 * (cρ * κ)) * ‖v‖ ^ 2 := by
  classical
  let Q := ∑ i, ∑ j, (D.matrix x i j : ℂ) * g j * star (g i)
  let J := ∑ i, ∑ j, (D.matrix x i j : ℂ) * g j * star ((2 * (t : ℂ) * d i) * v)
  have hρ := D.density_bounds x hx
  have hρ0 : 0 ≤ D.density x := hcρ.le.trans hρ.1
  have hΛ : 0 ≤ Λ := by
    let i : Fin n := ⟨0, B.dimension_pos⟩
    exact (abs_nonneg _).trans (D.matrix_entry_bound hκ.le x hx i i)
  have hsplit : (∑ i, ∑ j, (D.matrix x i j : ℂ) * g j *
        star ((t : ℂ) ^ 2 * g i + (2 * (t : ℂ) * d i) * v)) = (t : ℂ) ^ 2 * Q + J := by
    simp only [map_add, map_mul, map_pow, Complex.star_def, Complex.conj_ofReal,
      mul_add, Finset.sum_add_distrib, Q, J]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmain : cρ * κ * (t ^ 2 * ∑ i, ‖g i‖ ^ 2) ≤ D.density x * t ^ 2 * Q.re := by
    have he := D.complex_ellipticity x hx g
    have he0 : 0 ≤ Q.re := (by positivity : 0 ≤ κ * ∑ i, ‖g i‖ ^ 2).trans he
    calc
      _ = cρ * (t ^ 2 * (κ * ∑ i, ‖g i‖ ^ 2)) := by ring
      _ ≤ D.density x * (t ^ 2 * (κ * ∑ i, ‖g i‖ ^ 2)) := by gcongr; exact hρ.1
      _ ≤ D.density x * (t ^ 2 * Q.re) := by gcongr
      _ = _ := by ring
  have hmix : D.density x * ‖J‖ ≤
      (Cρ * (2 * K * Λ * (n : ℝ))) * |t| * (∑ j, ‖g j‖) * ‖v‖ := by
    have hmix' := D.mixed_cutoff_form_bound hκ.le x hx hK t g d v hd
    have hnonneg : 0 ≤ 2 * |t| * K * Λ * (n : ℝ) * (∑ j, ‖g j‖) * ‖v‖ := by positivity
    have hbound := mul_le_mul_of_nonneg_left hmix' hρ0
    have hbound' := mul_le_mul_of_nonneg_right hρ.2 hnonneg
    calc
      _ ≤ D.density x * (2 * |t| * K * Λ * (n : ℝ) * (∑ j, ‖g j‖) * ‖v‖) := hbound
      _ ≤ Cρ * (2 * |t| * K * Λ * (n : ℝ) * (∑ j, ‖g j‖) * ‖v‖) := hbound'
      _ = _ := by ring
  have hy := young_sum (cρ * κ) (Cρ * (2 * K * Λ * (n : ℝ))) (mul_pos hcρ hκ) g t v
  have hlow : -‖J‖ ≤ J.re := by
    exact (neg_le_neg (Complex.abs_re_le_norm J)).trans (neg_abs_le _)
  have hmixlow := mul_le_mul_of_nonneg_left hlow hρ0
  rw [hsplit, mul_add]
  rw [← Complex.ofReal_pow]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, zero_mul, mul_zero, sub_zero, zero_add]
  nlinarith

theorem pointwise_cutoff_lower_order {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ)
    (x : Space n) (hx : x ∈ B.carrier) {M : ℝ} (hM : 0 ≤ M)
    (z v h : ℂ) (hz : ‖z‖ ≤ M) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (z * ((D.density x : ℂ) * v * star ((t : ℂ) ^ 2 * v)) +
      (D.density x : ℂ) * h * star ((t : ℂ) ^ 2 * v)).re ≤
      Cρ * (M + 1) * ‖v‖ ^ 2 + Cρ * ‖h‖ ^ 2 := by
  have hρ := D.density_bounds x hx
  have hρ0 : 0 ≤ D.density x := hcρ.le.trans hρ.1
  have hCρ : 0 ≤ Cρ := hρ0.trans hρ.2
  have ht : ‖(t : ℂ) ^ 2 * v‖ ≤ ‖v‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg v]
  have hbound :
      (z * ((D.density x : ℂ) * v * star ((t : ℂ) ^ 2 * v)) +
        (D.density x : ℂ) * h * star ((t : ℂ) ^ 2 * v)).re ≤
        M * (Cρ * ‖v‖ * ‖v‖) + Cρ * ‖h‖ * ‖v‖ := by
    calc
      _ ≤ ‖z * ((D.density x : ℂ) * v * star ((t : ℂ) ^ 2 * v)) +
        (D.density x : ℂ) * h * star ((t : ℂ) ^ 2 * v)‖ := Complex.re_le_norm _
      _ ≤ ‖z * ((D.density x : ℂ) * v * star ((t : ℂ) ^ 2 * v))‖ +
        ‖(D.density x : ℂ) * h * star ((t : ℂ) ^ 2 * v)‖ := norm_add_le _ _
      _ ≤ M * (Cρ * ‖v‖ * ‖v‖) + Cρ * ‖h‖ * ‖v‖ := by
        simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
        gcongr
        · exact hρ.2
        · simpa only [norm_mul] using ht
        · exact hρ.2
        · simpa only [norm_mul] using ht
  have hs : ‖h‖ * ‖v‖ ≤ ‖v‖ ^ 2 + ‖h‖ ^ 2 := by nlinarith [sq_nonneg (‖h‖ - ‖v‖)]
  have hs' := mul_le_mul_of_nonneg_left hs hCρ
  nlinarith

 theorem raw_index_cases {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n 1 ∨ ∃ i : Fin n, α = firstIndex i := by
  classical
  by_cases hz : ∀ i, (α.val i).val = 0
  · left
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact hz i
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right
    refine ⟨i, ?_⟩
    have hs := Finset.sum_le_one_iff.mp α.property
    have hone := (hs i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2
    apply Subtype.ext
    funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j
      simpa [firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        by_contra hj
        exact hji (hs j i (Finset.mem_univ _) (Finset.mem_univ _) hj hi).1
      simpa [firstIndex, hji] using hj

 theorem raw_first_ne_zero {n : ℕ} (i : Fin n) :
    firstIndex i ≠ zeroIndex n 1 := by
  intro h
  have hd := congrArg (fun α : MultiIndex n 1 => (α.val i).val) h
  simpa [firstIndex, zeroIndex] using hd
 theorem raw_first_injective {n : ℕ} :
    Function.Injective (@firstIndex n) := by
  intro i j h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) h
  by_contra hij
  simpa [firstIndex, hij] using he
 def raw_index_equiv (n : ℕ) : Option (Fin n) ≃ MultiIndex n 1 :=
  Equiv.ofBijective (fun i => i.elim (zeroIndex n 1) firstIndex) (by
    constructor
    · intro i j hij
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some j => exact False.elim (raw_first_ne_zero j hij.symm)
      | some i =>
        cases j with
        | none => exact False.elim (raw_first_ne_zero i hij)
        | some j => exact congrArg some (raw_first_injective hij)
    · intro α
      rcases raw_index_cases α with hz | ⟨i, hi⟩
      · exact ⟨none, hz.symm⟩
      · exact ⟨some i, hi.symm⟩)

theorem raw_first_order_sum {n : ℕ} (F : MultiIndex n 1 → ℝ) :
    (∑ α, F α) = F (zeroIndex n 1) + ∑ i : Fin n, F (firstIndex i) := by
  classical
  rw [← (raw_index_equiv n).sum_comp F]
  change (∑ i : Option (Fin n), F (i.elim (zeroIndex n 1) firstIndex)) = _
  simp [Fintype.sum_option]

private theorem energy_density_memLp {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ) :
    MemLp (fun x => (D.density x : ℂ)) ⊤ (volume.restrict B.carrier) := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp_continuousOn D.density_smooth.continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) Cρ
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (hcρ.le.trans (D.density_bounds x hx).1)]
  exact (D.density_bounds x hx).2

private theorem energy_matrix_memLp {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hκ : 0 < κ) (i j : Fin n) :
    MemLp (fun x => (D.matrix x i j : ℂ)) ⊤ (volume.restrict B.carrier) := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp_continuousOn (D.matrix_smooth i j).continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) Λ
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  simpa using D.matrix_entry_bound hκ.le x hx i j

private theorem energy_integrable {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ) (hκ : 0 < κ)
    (u w : IntegerSobolev B 1) :
    Integrable (fun x => (D.density x : ℂ) * ∑ i, ∑ j,
      (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x))
      (volume.restrict B.carrier) := by
  simp only [Finset.mul_sum, ← mul_assoc]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  have hm : MemLp (fun x => (D.density x : ℂ) *
      ((D.matrix x i j : ℂ) * gradient u j x)) 2 (volume.restrict B.carrier) :=
    (energy_density_memLp D hcρ).mul
      (show MemLp (fun x => (D.matrix x i j : ℂ) * gradient u j x) 2
        (volume.restrict B.carrier) from
        (energy_matrix_memLp D hκ i j).mul (Lp.memLp (gradient u j)))
  convert hm.integrable_mul (Lp.memLp (gradient w i)).star using 1
  ext x
  simp [mul_assoc]

private theorem mass_integrable {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ) (f g : BallL2 B) :
    Integrable (fun x => (D.density x : ℂ) * f x * star (g x))
      (volume.restrict B.carrier) := by
  have hm : MemLp (fun x => (D.density x : ℂ) * f x) 2
      (volume.restrict B.carrier) := (energy_density_memLp D hcρ).mul (Lp.memLp f)
  exact hm.integrable_mul (Lp.memLp g).star

set_option maxHeartbeats 800000 in

theorem cutoff_quadratic_form_bound (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (inner outer : LocalBall n),
      inner.center = outer.center → inner.radius = r → outer.radius = R →
      ∃ η : TestFunction outer.toOpens ℝ ⊤,
        (∀ x ∈ inner.carrier, η x = 1) ∧
        ∀ (D : Coefficients outer cρ Cρ κ Λ) (z : ℂ), ‖z‖ ≤ M →
        ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer)
          (w : IntegerSobolev outer 1),
        (∀ᵐ x ∂volume.restrict outer.carrier,
          value w x = (η x : ℂ) ^ 2 * value u x) →
        (∀ i : Fin n, ∀ᵐ x ∂volume.restrict outer.carrier,
          gradient w i x = (η x : ℂ) ^ 2 * gradient u i x +
            (2 * (η x : ℂ) *
              coordinateDerivativeList [i] (fun y => (η y : ℂ)) x) * value u x) →
        ((∫ x in outer.carrier, (D.density x : ℂ) *
          ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)) -
            z * (∫ x in outer.carrier,
              (D.density x : ℂ) * value u x * star (value w x)) =
              ∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x)) →
        (∑ α : MultiIndex n 1,
          ∫ x in inner.carrier, ‖u.derivatives α x‖ ^ 2) ≤
          (C * (‖value u‖ + ‖h‖)) ^ 2 := by
  classical
  obtain ⟨K, hK, hcut⟩ := uniform_cutoff_with_derivative_bound n r R hr hrR
  let a := (cρ * κ) / 2
  let b := (n : ℝ) * (Cρ * (2 * K * Λ * (n : ℝ))) ^ 2 / (2 * (cρ * κ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let L := 1 + (b + |Cρ| * (M + 2)) / a
  have hL : 1 ≤ L := by
    have hh : 0 ≤ (b + |Cρ| * (M + 2)) / a := by positivity
    dsimp [L]; linarith
  refine ⟨L + 1, by linarith, ?_⟩
  intro inner outer hcenter hir hor
  obtain ⟨η, hηinner, hηrange, hηder⟩ := hcut inner outer hcenter hir hor
  refine ⟨η, hηinner, ?_⟩
  intro D z hz u h w hw hgw heq
  let μ := volume.restrict outer.carrier
  let E := fun x => (D.density x : ℂ) * ∑ i, ∑ j,
    (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)
  let V := fun x => (D.density x : ℂ) * value u x * star (value w x)
  let H := fun x => (D.density x : ℂ) * h x * star (value w x)
  let G := fun x => (η x) ^ 2 * ∑ i, ‖gradient u i x‖ ^ 2
  have hEi : Integrable E μ := energy_integrable D hcρ hκ u w
  have hVi : Integrable V μ := mass_integrable D hcρ (value u) (value w)
  have hHi : Integrable H μ := mass_integrable D hcρ h (value w)
  have hUi : Integrable (fun x => ‖value u x‖ ^ 2) μ :=
    (Lp.memLp (value u)).integrable_norm_pow (by norm_num)
  have hhi : Integrable (fun x => ‖h x‖ ^ 2) μ :=
    (Lp.memLp h).integrable_norm_pow (by norm_num)
  have hgi (i : Fin n) : Integrable (fun x => ‖gradient u i x‖ ^ 2) μ :=
    (Lp.memLp (gradient u i)).integrable_norm_pow (by norm_num)
  have hgs : Integrable (fun x => ∑ i, ‖gradient u i x‖ ^ 2) μ :=
    integrable_finset_sum _ (fun i _ => hgi i)
  have hGi : Integrable G μ := by
    apply hgs.bdd_mul (c := 1) (η.continuous.pow 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change η x ^ 2 ≤ 1
    have ht := hηrange x
    nlinarith
  have hcoer : ∀ᵐ x ∂μ, a * G x ≤ (E x).re + b * ‖value u x‖ ^ 2 := by
    have hgall : ∀ᵐ x ∂μ, ∀ i : Fin n,
        gradient w i x = (η x : ℂ) ^ 2 * gradient u i x +
          (2 * (η x : ℂ) * coordinateDerivativeList [i] (fun y => (η y : ℂ)) x) * value u x :=
      (ae_all_iff).mpr hgw
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hgall] with x hx hgx
    dsimp [E]
    simp only [hgx]
    exact pointwise_cutoff_coercivity D hcρ hκ x hx hK.le (η x)
      (fun i => gradient u i x) _ (value u x) (fun i => hηder i x)
  have hlower : ∀ᵐ x ∂μ, (z * V x + H x).re ≤
      Cρ * (M + 1) * ‖value u x‖ ^ 2 + Cρ * ‖h x‖ ^ 2 := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hw] with x hx hwx
    dsimp [V, H]
    rw [hwx]
    exact pointwise_cutoff_lower_order D hcρ x hx hM z (value u x) (h x) hz (η x)
      (hηrange x).1 (hηrange x).2
  have hEre : Integrable (fun x => (E x).re) μ := Complex.reCLM.integrable_comp hEi
  have hZH : Integrable (fun x => (z * V x + H x).re) μ :=
    Complex.reCLM.integrable_comp ((hVi.const_mul z).add hHi)
  have hcoerint := integral_mono_ae (hGi.const_mul a) (hEre.add (hUi.const_mul b)) hcoer
  have hlowerint := integral_mono_ae hZH
    ((hUi.const_mul (Cρ * (M + 1))).add (hhi.const_mul Cρ)) hlower
  have hident : (∫ x, E x ∂μ) = z * (∫ x, V x ∂μ) + (∫ x, H x ∂μ) := by
    exact sub_eq_iff_eq_add.mp heq |>.trans (add_comm _ _)
  have hrealident : (∫ x, (E x).re ∂μ) = ∫ x, (z * V x + H x).re ∂μ := by
    change (∫ x, RCLike.re (E x) ∂μ) = ∫ x, RCLike.re (z * V x + H x) ∂μ
    have hsum : Integrable (fun x => z * V x + H x) μ := (hVi.const_mul z).add hHi
    rw [integral_re hEi, integral_re hsum,
      integral_add (hVi.const_mul z) hHi, integral_const_mul, hident]
  simp only [Pi.add_apply] at hcoerint hlowerint
  rw [integral_const_mul, integral_add hEre (hUi.const_mul b), integral_const_mul,
    hrealident] at hcoerint
  rw [integral_add (hUi.const_mul (Cρ * (M + 1))) (hhi.const_mul Cρ),
    integral_const_mul, integral_const_mul] at hlowerint
  have henergy : a * (∫ x, G x ∂μ) ≤
      (b + Cρ * (M + 1)) * ‖value u‖ ^ 2 + Cρ * ‖h‖ ^ 2 := by
    change a * (∫ x, G x ∂μ) ≤ _ at hcoerint
    change (∫ x, (z * V x + H x).re ∂μ) ≤
      Cρ * (M + 1) * (∫ x in outer.carrier, ‖value u x‖ ^ 2) +
        Cρ * (∫ x in outer.carrier, ‖h x‖ ^ 2) at hlowerint
    change a * (∫ x, G x ∂μ) ≤ (∫ x, (z * V x + H x).re ∂μ) +
      b * (∫ x in outer.carrier, ‖value u x‖ ^ 2) at hcoerint
    rw [← lp_norm_sq_eq_integral (value u)] at hcoerint
    rw [← lp_norm_sq_eq_integral (value u), ← lp_norm_sq_eq_integral h] at hlowerint
    nlinarith
  have hsub : inner.carrier ⊆ outer.carrier := by
    intro x hx
    change dist x outer.center < outer.radius
    have hdist : dist x outer.center < r := by
      simpa [LocalBall.carrier, hcenter, hir] using hx
    rw [hor]
    exact hdist.trans hrR
  have hvalue : (∫ x in inner.carrier, ‖value u x‖ ^ 2) ≤ ‖value u‖ ^ 2 := by
    rw [lp_norm_sq_eq_integral]
    exact setIntegral_mono_set hUi (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x => hsub (a := x)))
  have hgrad : (∑ i, ∫ x in inner.carrier, ‖gradient u i x‖ ^ 2) ≤ ∫ x, G x ∂μ := by
    have hGinner : (∫ x in inner.carrier, G x) =
        ∑ i, ∫ x in inner.carrier, ‖gradient u i x‖ ^ 2 := by
      calc
        _ = ∫ x in inner.carrier, ∑ i, ‖gradient u i x‖ ^ 2 := by
          apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
          intro x hx
          dsimp [G]
          rw [hηinner x hx]
          simp
        _ = _ := integral_finset_sum _ (fun i _ => (hgi i).mono_measure
          (Measure.restrict_mono hsub le_rfl))
    rw [← hGinner]
    exact setIntegral_mono_set hGi (Filter.Eventually.of_forall (fun x => by dsimp [G]; positivity))
      (Filter.Eventually.of_forall (fun x => hsub (a := x)))
  have htotal : (∑ α : MultiIndex n 1,
      ∫ x in inner.carrier, ‖u.derivatives α x‖ ^ 2) ≤ ‖value u‖ ^ 2 + ∫ x, G x ∂μ := by
    rw [raw_first_order_sum]
    exact add_le_add hvalue hgrad
  have hcoefficient : b + Cρ * (M + 1) ≤ b + |Cρ| * (M + 2) := by
    have ht := mul_le_mul_of_nonneg_right (le_abs_self Cρ) (by linarith : 0 ≤ M + 1)
    nlinarith [abs_nonneg Cρ]
  have hcoeffh : Cρ ≤ b + |Cρ| * (M + 2) := by
    nlinarith [le_abs_self Cρ, abs_nonneg Cρ, mul_nonneg (abs_nonneg Cρ) hM]
  have hbound : (∫ x, G x ∂μ) ≤ (L - 1) * (‖value u‖ ^ 2 + ‖h‖ ^ 2) := by
    apply (mul_le_mul_iff_right₀ ha).mp
    have hLa : (L - 1) * a = b + |Cρ| * (M + 2) := by
      dsimp [L]
      field_simp
      <;> ring
    rw [← mul_assoc, mul_comm a (L - 1), hLa]
    calc
      a * (∫ x, G x ∂μ) ≤ (b + Cρ * (M + 1)) * ‖value u‖ ^ 2 + Cρ * ‖h‖ ^ 2 := henergy
      _ ≤ (b + |Cρ| * (M + 2)) * (‖value u‖ ^ 2 + ‖h‖ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg ‖value u‖),
          mul_le_mul_of_nonneg_right hcoeffh (sq_nonneg ‖h‖)]
  calc
    _ ≤ ‖value u‖ ^ 2 + (L - 1) * (‖value u‖ ^ 2 + ‖h‖ ^ 2) :=
      htotal.trans (add_le_add_right hbound _)
    _ ≤ L * (‖value u‖ ^ 2 + ‖h‖ ^ 2) := by nlinarith [sq_nonneg ‖h‖]
    _ ≤ ((L + 1) * (‖value u‖ + ‖h‖)) ^ 2 := by
      have hsq : ‖value u‖ ^ 2 + ‖h‖ ^ 2 ≤ (‖value u‖ + ‖h‖) ^ 2 := by
        nlinarith [norm_nonneg (value u), norm_nonneg h]
      have hLL : L ≤ (L + 1) ^ 2 := by nlinarith [sq_nonneg L]
      have hh := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ L)
      have hh' := mul_le_mul_of_nonneg_right hLL (sq_nonneg (‖value u‖ + ‖h‖))
      nlinarith

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
