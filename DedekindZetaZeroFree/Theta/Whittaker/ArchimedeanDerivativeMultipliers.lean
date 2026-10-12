module

public import DedekindZetaZeroFree.Theta.Whittaker.UpperTranslation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped NumberField Classical Topology
open NumberField MeasureTheory
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem localIdele_arch (y : R.A.G) (w : InfinitePlace F) :
    adeleEval F (Sum.inl w) (MomentSources.localIdele R y : KPAdeles F) = (y.1 w : w.Completion) := by
  change (Units.map (adeleEval F (Sum.inl w)).toMonoidHom (MomentSources.localIdele R y)).val = _
  unfold MomentSources.localIdele
  simp only [map_mul, map_prod]
  have he (v : KPHilbert.Place F) (z : (KPHilbert.Completion F v)ˣ) :
      Units.map (adeleEval F (Sum.inl w)).toMonoidHom (KPRationalAdelicSplitting.localIdele F v z) =
      Pi.mulSingle (M := fun v : KPHilbert.Place F => (KPHilbert.Completion F v)ˣ) v z (Sum.inl w) :=
    eval_localIdele F v (Sum.inl w) z
  simp_rw [he]
  have hinf : (∏ v : InfinitePlace F,
      Pi.mulSingle (M := fun v : KPHilbert.Place F => (KPHilbert.Completion F v)ˣ)
        (Sum.inl v) (y.1 v) (Sum.inl w)) = y.1 w := by
    rw [Finset.prod_eq_single w]
    · simp
    · intro v _ hv; simp [Pi.mulSingle_apply, Sum.inl_injective.ne hv]
    · simp
  have hfin : (∏ p : R.A.Sf,
      Pi.mulSingle (M := fun v : KPHilbert.Place F => (KPHilbert.Completion F v)ˣ)
        (Sum.inr p.val) (y.2 p) (Sum.inl w)) = 1 := by
    apply Finset.prod_eq_one; intro p _; simp
  rw [hinf, hfin, mul_one]

theorem idele_mul_localAdele (y : R.A.G) (w : InfinitePlace F) (z : w.Completion) :
    (MomentSources.localIdele R y : KPAdeles F) * KPRationalAdelicSplitting.localAdele F (Sum.inl w) z =
      KPRationalAdelicSplitting.localAdele F (Sum.inl w) ((y.1 w : w.Completion) * z) := by
  apply Prod.ext
  · funext v
    change (MomentSources.localIdele R y : KPAdeles F).1 v * Pi.single w z v =
      Pi.single w ((y.1 w : w.Completion) * z) v
    by_cases hv : v = w
    · subst v
      simp only [Pi.single_eq_same]
      have h := localIdele_arch R y w
      change (MomentSources.localIdele R y : KPAdeles F).1 w = _ at h
      rw [h]
    · simp [Pi.single_eq_of_ne hv]
  · change (MomentSources.localIdele R y : KPAdeles F).2 * 0 = 0
    simp

def complexCoordinate {R : PrincipalMellin.ActualRecipe S η} (y : R.A.G) (w : InfinitePlace F) : ℂ :=
  InfinitePlace.Completion.extensionEmbedding w (y.1 w : w.Completion)

theorem trace_upperCurve (y : R.A.G) (w : InfinitePlace F) (b : Bool) (t : ℝ) :
    (adelicTraceCharacter F ((MomentSources.localIdele R y : KPAdeles F) *
      KPRationalAdelicSplitting.localAdele F (Sum.inl w)
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
          upperLieDirection R w b)) : ℂ) =
      Complex.exp (Complex.I * (4 * Real.pi : ℂ) *
        (t : ℂ) * ((complexCoordinate y w * direction b).re : ℂ)) := by
  rw [idele_mul_localAdele]
  rw [KPRationalAdelicSplitting.localAdele, adelicTraceCharacter_arch_single,
    archTraceCharacter_of_isComplex w (R.A.complex_place w), Circle.coe_exp]
  simp only [map_mul, RingEquiv.apply_symm_apply]
  have he : InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)
      (upperLieDirection R w b) = direction b := by cases b <;> simp [upperLieDirection, direction]
  rw [he]
  change Complex.exp ((2 * Real.pi * (2 * (complexCoordinate y w * ((t : ℂ) * direction b)).re) : ℝ) * Complex.I) = _
  congr 1
  have hr : (complexCoordinate y w * ((t : ℂ) * direction b)).re =
      t * (complexCoordinate y w * direction b).re := by
    rw [show complexCoordinate y w * ((t : ℂ) * direction b) =
      (t : ℂ) * (complexCoordinate y w * direction b) by ring]
    simp [Complex.mul_re]
  rw [hr]
  push_cast
  ring

theorem fourier_upperLieDerivative (dq : Measure (KPAdditiveQuotient F))
    (hHaar : dq.IsAddHaarMeasure) (hprob : dq Set.univ = 1) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (w : InfinitePlace F) (b : Bool) (y : R.A.G) :
    MomentSources.fourier R dq (upperLieDerivative R w b f) (diagonal R y) =
      Complex.I * (4 * Real.pi : ℂ) * ((complexCoordinate y w * direction b).re : ℂ) *
        MomentSources.fourier R dq f (diagonal R y) := by
  have hcurve (t : ℝ) : MomentSources.fourier R dq f (diagonal R y * upperCurve R w b t) =
      Complex.exp (Complex.I * (4 * Real.pi : ℂ) * (t : ℂ) *
        ((complexCoordinate y w * direction b).re : ℂ)) * MomentSources.fourier R dq f (diagonal R y) := by
    rw [diagonal, upperCurve, diagonal_upper]
    change MomentSources.fourier R dq f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 _ * _) = _
    rw [fourier_upper_translation R dq hHaar hprob f hf.1 hr, trace_upperCurve R y w b t]
  have hd := (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul
    (Complex.I * (4 * Real.pi : ℂ))).mul_const
      ((complexCoordinate y w * direction b).re : ℂ)).cexp.mul_const
        (MomentSources.fourier R dq f (diagonal R y))
  have hd' := fourier_upperCurve_hasDeriv R dq hprob f hf hr w b (diagonal R y)
  have hfuns : (fun t => MomentSources.fourier R dq f (diagonal R y * upperCurve R w b t)) =
      fun t : ℝ => Complex.exp (Complex.I * (4 * Real.pi : ℂ) * (t : ℂ) *
        ((complexCoordinate y w * direction b).re : ℂ)) * MomentSources.fourier R dq f (diagonal R y) := funext hcurve
  rw [hfuns] at hd'
  have hh := hd'.unique hd
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
    one_mul, Complex.ofReal_one, mul_one] using hh

theorem angular_multiplier (y : R.A.G) (w : InfinitePlace F) (e : ℤ) (he : e = 1 ∨ e = -1) :
    (‖(y.1 w : w.Completion)‖ : ℂ) * DHCubic.angular (complexCoordinate y w) ^ e =
      if e = 1 then complexCoordinate y w else star (complexCoordinate y w) := by
  have hn : ‖complexCoordinate y w‖ = ‖(y.1 w : w.Completion)‖ := by
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq
      (y.1 w : w.Completion) 0
    simpa only [map_zero, dist_zero_right, complexCoordinate] using h
  have hz : complexCoordinate y w ≠ 0 := by
    intro hz
    have he := (InfinitePlace.Completion.isometry_extensionEmbedding w).injective
    have hzero : InfinitePlace.Completion.extensionEmbedding w (0 : w.Completion) = 0 := map_zero _
    exact (y.1 w).ne_zero (he (hz.trans hzero.symm))
  have hnorm : (‖complexCoordinate y w‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [← hn]
  rcases he with rfl | rfl
  · simp only [DHCubic.angular, zpow_one, ite_true]
    field_simp
  · simp only [DHCubic.angular, zpow_neg_one, show (-1 : ℤ) ≠ 1 by norm_num, ite_false]
    have hm := Complex.mul_conj' (complexCoordinate y w)
    field_simp
    exact hm.symm

theorem fourier_firstRootLocalDerivative (dq : Measure (KPAdditiveQuotient F))
    (hHaar : dq.IsAddHaarMeasure) (hprob : dq Set.univ = 1) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (w : InfinitePlace F) (e : ℤ) (he : e = 1 ∨ e = -1) (y : R.A.G) :
    MomentSources.fourier R dq (firstRootLocalDerivative R w e f) (diagonal R y) =
      ((‖(y.1 w : w.Completion)‖ : ℂ) * DHCubic.angular (complexCoordinate y w) ^ e) *
        MomentSources.fourier R dq f (diagonal R y) := by
  have hR := upperLieDerivative_smooth R w false f hf
  have hI := upperLieDerivative_smooth R w true f hf
  have hiR := fourier_integrable R dq hprob _ hR.1
    (fun γ => upperLieDerivative_left_invariant R w false f _ (hr γ)) (diagonal R y)
  have hiI := fourier_integrable R dq hprob _ hI.1
    (fun γ => upperLieDerivative_left_invariant R w true f _ (hr γ)) (diagonal R y)
  have hlin : MomentSources.fourier R dq (firstRootLocalDerivative R w e f) (diagonal R y) =
    (Complex.I * (4 * Real.pi : ℂ))⁻¹ *
      (MomentSources.fourier R dq (upperLieDerivative R w false f) (diagonal R y) +
        (if e = 1 then -Complex.I else Complex.I) *
          MomentSources.fourier R dq (upperLieDerivative R w true f) (diagonal R y)) := by
    unfold MomentSources.fourier firstRootLocalDerivative
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_const_mul]
    congr 1
    calc
      _ = _ := integral_add hiR (hiI.const_mul _)
      _ = _ := by rw [integral_const_mul]; rfl
  rw [hlin, fourier_upperLieDerivative R dq hHaar hprob f hf hr,
    fourier_upperLieDerivative R dq hHaar hprob f hf hr, angular_multiplier R y w e he]
  simp only [direction, Bool.false_eq_true, if_false, if_true, mul_one, Complex.mul_I_re,
    Complex.ofReal_neg]
  have hpi : (4 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hparts := Complex.re_add_im (complexCoordinate y w)
  rcases he with rfl | rfl
  · simp only [ite_true]
    field_simp
    linear_combination (MomentSources.fourier R dq f (diagonal R y)) * hparts
  · simp only [show (-1 : ℤ) ≠ 1 by norm_num, ite_false]
    have hp := congrArg star hparts
    simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I] at hp
    simp only [Complex.star_def]
    field_simp
    linear_combination (MomentSources.fourier R dq f (diagonal R y)) * hp

end DedekindZetaZeroFree.RootDerivatives

end
