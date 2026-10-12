module

public import DedekindZetaZeroFree.Analysis.ModifiedBesselKOneThird

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/Eisenstein/CuspAverage.lean.
Source: BesselMellinTransform.lean.
-/

namespace DedekindZetaZeroFree

open MeasureTheory

noncomputable section

def thirdBesselRadialProfile (c t : ℝ) : ℝ :=
  t * KThird (c * Real.sqrt t)

open Filter
open scoped Topology

def thirdSchlafliIntegral (x : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^((1/3:ℂ)-1) *
    Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))

def thirdSchlafliBesselK (x : ℝ) : ℂ :=
  (1/2:ℂ) * (x/2:ℂ)^(-(1/3:ℂ)) * thirdSchlafliIntegral x

private lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2))
      (Set.Ioi 0) volume := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t:ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t:ℂ))) (s := s/2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) (s := s) (a := 2)
      (by norm_num)).mpr hlinear
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,
    Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using hgaussian

private lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2)) =
      (1/2:ℂ)*((1/(r:ℂ))^(s/2)*Complex.Gamma (s/2)) := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) s 2
  simp only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t:ℂ)^(-(2:ℂ)/3)*Complex.exp (-(t:ℂ))*
    ((x:ℂ)^((s-1/3)-1)*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2))

private lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    IntegrableOn (cubicMellinMixture s t) (Set.Ioi 0) volume := by
  apply (complex_gaussian_power_integrable (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)).const_mul

private lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
  simp only [cubicMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)]
  have hb : (1/(((1/(4*t):ℝ):ℂ)))=(4:ℂ)*(t:ℂ) := by
    push_cast
    field_simp
  have hm : ((4:ℂ)*(t:ℂ))^((s-1/3)/2)=
      (4:ℂ)^((s-1/3)/2)*(t:ℂ)^((s-1/3)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0≤(4:ℝ)) ht.le ((s-1/3)/2)
  rw [hb,hm]
  have hp : (t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2)=
      (t:ℂ)^((s+1/3)/2-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        (((t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2))*Complex.exp (-(t:ℂ))) := by ring
    _ = _ := by rw [hp]

private lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0<t) (hx : 0<x) :
    ‖cubicMellinMixture s t x‖ =
      (t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t):ℝ):ℂ)*(x:ℂ)^2=(-(1/(4*t))*x^2:ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re]
  norm_num

private lemma real_gaussian_power_integral (sigma r : ℝ) (hs : 0<sigma) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,x^(sigma-1)*Real.exp (-r*x^2)) =
      r^(-sigma/2)*(1/2)*Real.Gamma (sigma/2) := by
  simpa only [Real.rpow_two,sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=sigma-1) (b:=r)
      (by norm_num) (by linarith) hr)

private lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,‖cubicMellinMixture s t x‖) =
      ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
        (t^((s.re+1/3)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫x : ℝ in Set.Ioi 0,(t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicMellinMixture_norm s t x ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-1/3) (1/(4*t))
        (by linarith) (by positivity)]
      have hpow : (1/(4*t):ℝ)^(-(s.re-1/3)/2)=(4:ℝ)^((s.re-1/3)/2)*t^((s.re-1/3)/2) := by
        rw [show -(s.re-1/3)/2=-((s.re-1/3)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0≤(4:ℝ)) ht.le]
      rw [hpow]
      have hp : t^(-(2:ℝ)/3)*t^((s.re-1/3)/2)=t^((s.re+1/3)/2-1) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
            ((t^(-(2:ℝ)/3)*t^((s.re-1/3)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

private lemma cubicMellinMixture_integrable (s : ℂ) (hs : 1/3<s.re) :
    Integrable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    unfold cubicMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicMellinMixture_slice_integrable s hs t ht
  · have hg := (Real.GammaIntegral_convergent
        (show 0<(s.re+1/3)/2 by linarith)).const_mul
        ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicMellinMixture_integral_norm s hs t ht]
    ring

private lemma cubicMellinMixture_integral_t (s : ℂ) (x : ℝ) :
    (∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      (x:ℂ)^((s-1/3)-1)*thirdSchlafliIntegral x := by
  rw [thirdSchlafliIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : Complex.exp (-(t:ℂ))*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2)=
      Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [show (1/3:ℂ)-1=-(2:ℂ)/3 by ring]
  unfold cubicMellinMixture
  linear_combination (t:ℂ)^(-(2:ℂ)/3)*(x:ℂ)^((s-1/3)-1)*he

open Filter MeasureTheory
open scoped BigOperators Classical Topology

private lemma schlafliBesselK_cubic_mellin_mixture (s : ℂ) (x : ℝ) (hx : 0<x) :
    (x:ℂ)^(s-1)*thirdSchlafliBesselK x =
      ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*(∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
  rw [thirdSchlafliBesselK,cubicMellinMixture_integral_t]
  have hdiv : (x/2:ℂ)^(-(1/3:ℂ))=(x:ℂ)^(-(1/3:ℂ))/(2:ℂ)^(-(1/3:ℂ)) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : 0≤(2:ℝ)) (-(1/3:ℂ))
  rw [hdiv,Complex.cpow_neg (2:ℂ) (1/3),div_inv_eq_mul]
  have hp : (x:ℂ)^(s-1)*(x:ℂ)^(-(1/3:ℂ))=(x:ℂ)^((s-1/3)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1/2:ℂ)*(2:ℂ)^(1/3:ℂ)*thirdSchlafliIntegral x*hp

private lemma schlafliBesselK_cubic_mellin_integrable (s : ℂ) (hs : 1/3<s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*thirdSchlafliBesselK x)
      (Set.Ioi 0) volume := by
  apply ((cubicMellinMixture_integrable s hs).integral_prod_right.const_mul
    ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_cubic_mellin_mixture s x hx).symm

private lemma cubicMellinMixture_double_integral (s : ℂ) (hs : 1/3<s.re) :
    (∫t : ℝ in Set.Ioi 0,∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        Complex.Gamma ((s+1/3)/2) := by
  have hB : 0<((s+1/3)/2).re := by norm_num; linarith
  calc
    _ = ∫t : ℝ in Set.Ioi 0,
        ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicMellinMixture_integral_x s hs t ht
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

private theorem schlafliBesselK_cubic_mellin (s : ℂ) (hs : 1/3<s.re) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*thirdSchlafliBesselK x) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    convert cubicMellinMixture_integrable s hs using 1
    funext p
    rcases p with ⟨t,x⟩
    rfl
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4:ℂ)^((s-1/3)/2)=(2:ℂ)^(2*((s-1/3)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-1/3)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)=(2:ℂ)^s := by
    rw [h4,←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hscale : (1/4:ℂ)*(2:ℂ)^s=(2:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
    ring
  calc
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (∫x : ℝ in Set.Ioi 0,∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_cubic_mellin_mixture s x hx
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          Complex.Gamma ((s+1/3)/2)) := by
      rw [hswap,cubicMellinMixture_double_integral s hs]
    _ = ((1/4:ℂ)*((2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)))*
        Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by ring
    _ = _ := by rw [hprod,hscale]

private lemma thirdSchlafliBesselK_eq_KThird (x : ℝ) (hx : 0 < x) :
    thirdSchlafliBesselK x = (KThird x : ℂ) := by
  have hK : KThird x = KPCplxBessel.modifiedBesselK (1/3) x := by
    rw [KThird_eq_integral x hx]
    unfold KPCplxBessel.modifiedBesselK thirdBesselSchlafliIntegrand
    congr 1
    funext t
    congr 2
    ring
  rw [hK, ← KPCplxBessel.besselKThird_eq_modifiedBesselK x hx]
  unfold thirdSchlafliBesselK thirdSchlafliIntegral KPCplxBessel.besselKThird
  push_cast
  have hp := Complex.ofReal_cpow (by positivity : 0 ≤ x / 2) (-(1/3:ℝ))
  push_cast at hp
  rw [← hp]
  congr 2
  calc
    _ = (∫ t : ℝ in Set.Ioi 0,
        (KPCplxBessel.schlafliKernel (-(2/3:ℝ)) x t : ℂ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          unfold KPCplxBessel.schlafliKernel
          push_cast
          have hp2 := Complex.ofReal_cpow ht.le (-(2/3:ℝ))
          norm_num at hp2 ⊢
          rw [← hp2]
    _ = _ := integral_ofReal

private lemma scaled_mellin_convergent (q : ℂ) (c : ℝ)
    (hq : 1/3 < q.re) (hc : 0 < c) :
    MellinConvergent (fun x => thirdSchlafliBesselK (c*x)) q := by
  apply (MellinConvergent.comp_mul_left hc).mpr
  simpa only [MellinConvergent, smul_eq_mul] using
    schlafliBesselK_cubic_mellin_integrable q hq

private lemma scaled_mellin (q : ℂ) (c : ℝ)
    (hq : 1/3 < q.re) (hc : 0 < c) :
    mellin (fun x => thirdSchlafliBesselK (c*x)) q =
      (c:ℂ)^(-q) * ((2:ℂ)^(q-2)*Complex.Gamma ((q-1/3)/2)*
        Complex.Gamma ((q+1/3)/2)) := by
  rw [mellin_comp_mul_left _ _ hc]
  congr 1
  exact schlafliBesselK_cubic_mellin q hq

private lemma radial_integrand_eq (c t : ℝ) (s : ℂ) (hc : 0 < c) (ht : 0 < t) :
    (thirdBesselRadialProfile c t : ℂ) * (t : ℂ)^s / (t : ℂ) =
      (t : ℂ)^s * thirdSchlafliBesselK (c * t^(1/2:ℝ)) := by
  rw [show t^(1/2:ℝ) = Real.sqrt t from (Real.sqrt_eq_rpow t).symm,
    thirdSchlafliBesselK_eq_KThird _ (by positivity)]
  unfold thirdBesselRadialProfile
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

private lemma radial_convergent (c : ℝ) (hc : 0 < c) (s : ℂ)
    (hs : -(5/6:ℝ) < s.re) :
    MellinConvergent (fun t => thirdSchlafliBesselK (c * t^(1/2:ℝ))) (s+1) := by
  apply (MellinConvergent.comp_rpow (f := fun x => thirdSchlafliBesselK (c*x))
    (s := s+1) (by norm_num : (1/2:ℝ) ≠ 0)).mpr
  convert scaled_mellin_convergent (2*s+2) c (by norm_num; linarith) hc using 1
  congr 1
  push_cast
  ring

lemma radial_integrable (c : ℝ) (hc : 0 < c) (s : ℂ)
    (hs : -(5/6:ℝ) < s.re) :
    IntegrableOn (fun t : ℝ =>
      (thirdBesselRadialProfile c t : ℂ) * (t:ℂ)^s / (t:ℂ)) (Set.Ioi 0) := by
  have h := radial_convergent c hc s hs
  simp only [MellinConvergent, smul_eq_mul, add_sub_cancel_right] at h
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (radial_integrand_eq c t s hc ht).symm

theorem thirdBesselRadialProfile_mellin
    (c : ℝ) (hc : 0 < c) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
      (thirdBesselRadialProfile c t : ℂ) * (t : ℂ) ^ s / (t : ℂ)) =
        (↑(2 / c ^ 2 : ℝ) : ℂ) * (↑(4 / c ^ 2 : ℝ) : ℂ) ^ s *
          Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) := by
  have hq : 1/3 < (2*s+2).re := by norm_num; linarith
  have hM := mellin_comp_rpow (fun x => thirdSchlafliBesselK (c*x)) (s+1) (1/2)
  have harg : (s+1:ℂ) / ((1/2:ℝ):ℂ) = 2*s+2 := by push_cast; ring
  rw [harg, scaled_mellin (2*s+2) c hq hc] at hM
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/2), inv_div, one_div,
    Complex.real_smul, Complex.ofReal_ofNat] at hM
  rw [show (2*s+2:ℂ)-2 = 2*s by ring,
    show ((2*s+2:ℂ)-1/3)/2 = s+5/6 by ring,
    show ((2*s+2:ℂ)+1/3)/2 = s+7/6 by ring] at hM
  have hI : (∫ t : ℝ in Set.Ioi 0,
      (thirdBesselRadialProfile c t : ℂ)*(t:ℂ)^s/(t:ℂ)) =
      mellin (fun t => thirdSchlafliBesselK (c*t^(1/2:ℝ))) (s+1) := by
    simp only [mellin, smul_eq_mul, add_sub_cancel_right]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact radial_integrand_eq c t s hc ht
  rw [hI, hM]
  have hscale : (2:ℂ) * (c:ℂ)^(-(2*s+2)) * (2:ℂ)^(2*s) =
      (↑(2/c^2:ℝ):ℂ) * (↑(4/c^2:ℝ):ℂ)^s := by
    have hc0 : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hp : ((c:ℂ)^2)^s = (c:ℂ)^(2*s) := by
      simpa only [Real.rpow_two, Complex.ofReal_pow, Complex.ofReal_ofNat] using
        (Complex.cpow_mul_ofReal_nonneg hc.le 2 s).symm
    have h2 : (2:ℂ)^(2*s) = (4:ℂ)^s := by
      have h := Complex.natCast_cpow_natCast_mul 2 2 s
      norm_num at h
      exact h
    have hdiv := Complex.div_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 4)
      (sq_nonneg c) s
    push_cast at hdiv
    push_cast
    rw [hdiv, hp, ← h2, show -(2*s+2:ℂ) = -(2*s)-2 by ring,
      Complex.cpow_sub _ _ hc0, Complex.cpow_neg, Complex.cpow_ofNat]
    ring
  linear_combination hscale * Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6)

end

end DedekindZetaZeroFree
