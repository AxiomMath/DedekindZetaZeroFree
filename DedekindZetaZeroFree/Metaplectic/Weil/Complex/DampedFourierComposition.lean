module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.TraceFourierNormalization

@[expose] public section

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory Filter
open scoped Topology

private lemma psi_add (β u v : ℂ) : psi β (u + v) = psi β u * psi β v := by
  unfold psi
  rw [← Complex.exp_add]
  congr 1
  rw [show β * (u + v) = β * u + β * v by ring, Complex.add_re]
  push_cast
  ring

private lemma norm_exp_damped (ε : ℝ) (x : ℂ) :
    ‖Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ))‖ = Real.exp (-ε * ‖x‖ ^ 2) := by
  rw [Complex.norm_exp, Complex.ofReal_re]

theorem norm_damped_fubini_integrand (β a : ℂ) (ε : ℝ)
    (f : SchwartzMap ℂ ℂ) (y x z : ℂ) :
    ‖Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
      psi β (a * x ^ 2 - x * (y + z))‖ =
      Real.exp (-ε * ‖x‖ ^ 2) * ‖f z‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.ofReal_re, norm_psi, mul_one]

theorem integrable_damped_fubini_integrand (β a : ℂ) (hβ : β ≠ 0)
    (ha : a ≠ 0) (ε : ℝ) (hε : 0 < ε) (f : SchwartzMap ℂ ℂ) (y : ℂ) :
    Integrable (fun p : ℂ × ℂ =>
      Complex.exp (((-ε * ‖p.1‖ ^ 2 : ℝ) : ℂ)) * f p.2 *
        psi β (a * p.1 ^ 2 - p.1 * (y + p.2)))
      ((mu β).prod (mu β)) := by
  haveI : SFinite (mu β) := by rw [mu]; infer_instance
  have hgaussvol : Integrable (fun v : ℂ => Real.exp (-ε * ‖v‖^2)) (volume : Measure ℂ) := by
    have hvol : Integrable (fun v : ℂ => Complex.exp (-(ε:ℂ) * ‖v‖^2)) (volume : Measure ℂ) := by
      have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (ε:ℂ))
        (c := 0) (w := 0) (by simpa using hε)
      simpa using this
    refine (hvol.norm).congr ?_
    filter_upwards with v
    rw [Complex.norm_exp]
    have h : -(ε:ℂ) * (‖v‖:ℂ)^2 = ((-ε*‖v‖^2 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.ofReal_re]
  have hgauss : Integrable (fun x : ℂ => Real.exp (-ε * ‖x‖^2)) (mu β) := by
    have := hgaussvol.smul_measure (ENNReal.ofReal_ne_top (r := ‖β‖))
    simpa only [mu] using this
  have hfnorm : Integrable (fun z : ℂ => ‖f z‖) (mu β) := (integrable_schwartz_mu β f).norm
  have hprod := hgauss.mul_prod hfnorm
  have hcont : Continuous (fun p : ℂ × ℂ =>
      Complex.exp (((-ε * ‖p.1‖ ^ 2 : ℝ) : ℂ)) * f p.2 *
        psi β (a * p.1 ^ 2 - p.1 * (y + p.2))) := by
    have hpsi : Continuous fun z : ℂ => psi β z := by unfold psi; fun_prop
    fun_prop
  refine Integrable.mono' hprod hcont.aestronglyMeasurable ?_
  · filter_upwards with p
    rw [norm_damped_fubini_integrand]

theorem F_damped_M_F_eq_integral_K (β a : ℂ) (hβ : β ≠ 0)
    (ha : a ≠ 0) (ε : ℝ) (hε : 0 < ε) (f : SchwartzMap ℂ ℂ) (y : ℂ) :
    F β (fun x : ℂ =>
      Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
        psi β (a * x ^ 2) * F β (⇑f) x) y =
      ∫ z : ℂ, f z * K β ε a (y + z) ∂mu β := by
  haveI : SFinite (mu β) := by rw [mu]; infer_instance
  have hDint := integrable_damped_fubini_integrand β a hβ ha ε hε f y
  have hfac : ∀ x z : ℂ,
      Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z * psi β (a * x ^ 2 - x * (y + z)) =
        Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
          psi β (-x * y) * (f z * psi β (-x * z)) := by
    intro x z
    rw [show a * x ^ 2 - x * (y + z) = a * x ^ 2 + (-x * y + -x * z) by ring]
    rw [psi_add, psi_add]
    ring
  have hinner : ∀ x : ℂ,
      (∫ z : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
          psi β (a * x ^ 2 - x * (y + z)) ∂mu β) =
        (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
          F β (⇑f) x) * psi β (-x * y) := by
    intro x
    calc ∫ z : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
            psi β (a * x ^ 2 - x * (y + z)) ∂mu β
        = ∫ z : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
            psi β (-x * y) * (f z * psi β (-x * z)) ∂mu β :=
          integral_congr_ae (Eventually.of_forall (fun z => hfac x z))
      _ = (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) * psi β (-x * y)) *
            ∫ z : ℂ, f z * psi β (-x * z) ∂mu β := by
          rw [integral_const_mul]
      _ = (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
            F β (⇑f) x) * psi β (-x * y) := by
          have hF : (∫ z : ℂ, f z * psi β (-x * z) ∂mu β) = F β (⇑f) x := by
            rw [F]
            exact integral_congr_ae (Eventually.of_forall (fun z => by
              show f z * psi β (-x * z) = ⇑f z * psi β (-z * x)
              rw [show (-x) * z = (-z) * x by ring]))
          rw [hF]; ring
  have hinner2 : ∀ z : ℂ,
      (∫ x : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
          psi β (a * x ^ 2 - x * (y + z)) ∂mu β) =
        f z * K β ε a (y + z) := by
    intro z
    calc ∫ x : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
            psi β (a * x ^ 2 - x * (y + z)) ∂mu β
        = ∫ x : ℂ, f z * (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
            psi β (a * x ^ 2 - x * (y + z))) ∂mu β :=
          integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = f z * ∫ x : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
            psi β (a * x ^ 2 - x * (y + z)) ∂mu β := by
          rw [integral_const_mul]
      _ = f z * K β ε a (y + z) := by rw [K]
  rw [F]
  calc ∫ x : ℂ, (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
          F β (⇑f) x) * psi β (-x * y) ∂mu β
      = ∫ x : ℂ, ∫ z : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
          psi β (a * x ^ 2 - x * (y + z)) ∂mu β ∂mu β :=
        integral_congr_ae (Eventually.of_forall (fun x => (hinner x).symm))
    _ = ∫ z : ℂ, ∫ x : ℂ, Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
          psi β (a * x ^ 2 - x * (y + z)) ∂mu β ∂mu β :=
        integral_integral_swap (f := fun x z : ℂ => Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * f z *
          psi β (a * x ^ 2 - x * (y + z))) hDint
    _ = ∫ z : ℂ, f z * K β ε a (y + z) ∂mu β :=
        integral_congr_ae (Eventually.of_forall (fun z => hinner2 z))

theorem tendsto_F_damped_M_F (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (f : SchwartzMap ℂ ℂ) (y : ℂ) :
    Tendsto (fun ε : ℝ =>
      F β (fun x : ℂ =>
        Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
          psi β (a * x ^ 2) * F β (⇑f) x) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (F β (M β a (F β (⇑f))) y)) := by
  haveI : SFinite (mu β) := by rw [mu]; infer_instance
  have hpsi : Continuous fun z : ℂ => psi β z := by unfold psi; fun_prop
  have hFint : Integrable (fun x : ℂ => F β (⇑f) x) (mu β) := integrable_F_schwartz_mu β f
  have hFmeas : AEStronglyMeasurable (fun x : ℂ => F β (⇑f) x) (mu β) := hFint.aestronglyMeasurable
  have hbint : Integrable (fun x : ℂ => ‖F β (⇑f) x‖) (mu β) := hFint.norm
  change Tendsto (fun ε : ℝ => ∫ x : ℂ,
      (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) * F β (⇑f) x) *
        psi β (-x * y) ∂mu β)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ x : ℂ, (psi β (a * x ^ 2) * F β (⇑f) x) * psi β (-x * y) ∂mu β))
  refine tendsto_integral_filter_of_dominated_convergence (fun x : ℂ => ‖F β (⇑f) x‖) ?_ ?_ hbint ?_
  · filter_upwards with ε
    have hcont : Continuous (fun x : ℂ =>
        Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) * psi β (-x * y)) := by
      fun_prop
    have hEq : (fun x : ℂ =>
        (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) * F β (⇑f) x) *
          psi β (-x * y)) =
        fun x : ℂ => (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) *
          psi β (-x * y)) * F β (⇑f) x := by
      funext x; ring
    rw [hEq]
    exact hcont.aestronglyMeasurable.mul hFmeas
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with x
    have hle : Real.exp (-ε * ‖x‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hε.le (sq_nonneg ‖x‖))
    simp only [norm_mul, norm_exp_damped, norm_psi, mul_one, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hle
  · filter_upwards with x
    have hc0 : Tendsto (fun ε : ℝ => -(ε:ℂ) * (‖x‖:ℂ)^2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hcont : Continuous (fun ε : ℝ => -(ε:ℂ) * (‖x‖:ℂ)^2) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun ε : ℝ => Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have hfun : (fun ε : ℝ => Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)))
          = (fun ε : ℝ => Complex.exp (-(ε:ℂ) * (‖x‖:ℂ)^2)) := by
        funext ε; congr 1; push_cast; ring
      rw [hfun]
      have hcomp := (Complex.continuous_exp.tendsto 0).comp hc0
      rw [Complex.exp_zero] at hcomp
      exact hcomp
    have hEq : (fun ε : ℝ =>
        (Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) * psi β (a * x ^ 2) * F β (⇑f) x) *
          psi β (-x * y))
        = fun ε : ℝ => Complex.exp (((-ε * ‖x‖ ^ 2 : ℝ) : ℂ)) *
          ((psi β (a * x ^ 2) * F β (⇑f) x) * psi β (-x * y)) := by
      funext ε; ring
    rw [hEq]
    simpa using hc.mul_const ((psi β (a * x ^ 2) * F β (⇑f) x) * psi β (-x * y))

end
end DedekindZetaZeroFree.ComplexWeil
