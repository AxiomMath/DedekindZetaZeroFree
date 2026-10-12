module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedJacquetImage

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxRootDerivativeVectors KPCplxIntertwinerEigenvalues TraceHaarTransport
open KPCplxHarmonicPropagation.RaisingCalculation
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

 def Bcurve (c d z : ℂ) (t : ℝ) : ℝ := ‖c‖^2 + ‖d + (t:ℂ)*c*z‖^2
 def Bvel (c d z : ℂ) : ℝ := 2 * inner ℝ d (c*z)
private lemma Bcurve_deriv (c d z : ℂ) : HasDerivAt (Bcurve c d z) (Bvel c d z) 0 := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const (c*z)).const_add d
  have hd := h.norm_sq
  convert hd.const_add (‖c‖^2) using 1
  · funext t; simp [Bcurve, mul_assoc]
  · simp [Bvel]

private lemma Bvel_complex (c d z : ℂ) :
    (Bvel c d z : ℂ) = c*z*star d + d*star (c*z) := by
  simp only [Bvel, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  change ((2 * (c*z*star d).re : ℝ):ℂ) = _
  rw [← Complex.add_conj]
  simp only [map_mul, Complex.star_def, Complex.conj_conj]
  ring

 def Wcurve (c d z : ℂ) (t : ℝ) : ℂ :=
  2*c*star (d+(t:ℂ)*c*z) / (Bcurve c d z t : ℂ)
 def Wvel (c d z : ℂ) : ℂ :=
  (2*c*star (c*z)*(‖c‖^2+‖d‖^2:ℝ) - 2*c*star d*(Bvel c d z:ℂ)) /
    ((‖c‖^2+‖d‖^2:ℝ):ℂ)^2
private lemma Wcurve_deriv (c d z : ℂ) (hb : ‖c‖^2+‖d‖^2 ≠ 0) :
    HasDerivAt (Wcurve c d z) (Wvel c d z) 0 := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const (c*z)).const_add d
  have hB := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (Bcurve_deriv c d z)
  convert (h.star.const_mul (2*c)).div hB (by simpa [Bcurve] using Complex.ofReal_ne_zero.mpr hb) using 1
  · funext t; simp [Wcurve, mul_assoc]
  · simp [Wvel, Bcurve, Function.comp_def]

 def Hcurve (s : ℝ) (n : ℕ) (D : ℝ) (c d z : ℂ) (t : ℝ) : ℂ :=
  (Real.rpow (D / Bcurve c d z t) (1+2*s) : ℂ) * Wcurve c d z t ^ n
 def Hvel (s : ℝ) (n : ℕ) (D : ℝ) (c d z : ℂ) : ℂ :=
  (Real.rpow (D/(‖c‖^2+‖d‖^2)) (1+2*s) : ℂ) *
    (-((1+2*s:ℝ):ℂ) * (Bvel c d z:ℂ) / ((‖c‖^2+‖d‖^2:ℝ):ℂ) *
      (2*c*star d/((‖c‖^2+‖d‖^2:ℝ):ℂ))^n +
      (n:ℂ)*(2*c*star d/((‖c‖^2+‖d‖^2:ℝ):ℂ))^(n-1)*Wvel c d z)
private lemma Hcurve_deriv (s : ℝ) (n : ℕ) (D : ℝ) (c d z : ℂ)
    (hD : 0 < D) (hb : 0 < ‖c‖^2+‖d‖^2) :
    HasDerivAt (Hcurve s n D c d z) (Hvel s n D c d z) 0 := by
  have hr := (hasDerivAt_const (0:ℝ) D).div (Bcurve_deriv c d z) (by simpa [Bcurve] using hb.ne')
  have hp := hr.rpow_const (p := 1+2*s) (Or.inl (by simpa [Bcurve] using (div_pos hD hb).ne'))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hp
  convert hc.mul ((Wcurve_deriv c d z hb.ne').pow n) using 1
  · rfl
  · dsimp [Function.comp_def, Hvel, Bcurve, Wcurve, Complex.ofRealCLM_apply]
    simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_sub]
    have he : (D/(‖c‖^2+‖d‖^2)) ^ (1+2*s-1:ℝ) =
        (D/(‖c‖^2+‖d‖^2)) ^ (1+2*s:ℝ) / (D/(‖c‖^2+‖d‖^2)) := by
      rw [Real.rpow_sub (div_pos hD hb), Real.rpow_one]
    rw [he]
    push_cast
    field_simp [hD.ne', hb.ne']
    <;> ring

private lemma highest_orbit_curve (s : ℝ) (n : ℕ) (g : ComplexGL2) (z : ℂ) (t : ℝ) :
    harmonicSection s n (g * upperUnipotent ((t:ℂ)*z)) =
      Hcurve s n ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ (g 1 0) (g 1 1) z t := by
  change (Real.rpow (‖((g * upperUnipotent ((t:ℂ)*z) : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
    rowB (g * upperUnipotent ((t:ℂ)*z))) (1+2*s) : ℂ) *
    rowW (g * upperUnipotent ((t:ℂ)*z)) ^ n = _
  simp only [Hcurve, rowW, rowB, Bcurve, Wcurve, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, upperUnipotent, Matrix.det_mul]
  have he : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * ((t:ℂ)*z) + g 1 1 =
      g 1 1 + (t:ℂ)*(g 1 0*z) := by ring
  simp [Matrix.det_fin_two, he, mul_assoc, add_comm, mul_comm, mul_left_comm]

private lemma highest_orbit_deriv (s : ℝ) (n : ℕ) (g : ComplexGL2) (z : ℂ) :
    deriv (fun t : ℝ => harmonicSection s n (g * upperUnipotent ((t:ℂ)*z))) 0 =
      Hvel s n ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ (g 1 0) (g 1 1) z := by
  simp_rw [highest_orbit_curve]
  exact (Hcurve_deriv s n _ _ _ z
    (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) (rowB_pos g)).deriv

private lemma Hvel_plus (s : ℝ) (n : ℕ) (D : ℝ) (c d : ℂ)
    (hb : ‖c‖^2+‖d‖^2 ≠ 0) :
    (Hvel s n D c d 1 - Complex.I * Hvel s n D c d Complex.I)/2 =
      -((n:ℂ)+((1+2*s:ℝ):ℂ))/2 *
        (Real.rpow (D/(‖c‖^2+‖d‖^2)) (1+2*s):ℂ) *
          (2*c*star d/((‖c‖^2+‖d‖^2:ℝ):ℂ))^(n+1) := by
  simp only [Hvel, Wvel, Bvel_complex, star_mul, star_one, Complex.star_def, Complex.conj_I, mul_one]
  have hbc : ((‖c‖^2+‖d‖^2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  cases n with
  | zero =>
    simp only [Nat.cast_zero, pow_zero, zero_mul, add_zero, zero_add, pow_one]
    field_simp [hbc]
    ring_nf
    simp only [Complex.I_sq]
    ring
  | succ n =>
    simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]
    field_simp [hbc]
    ring_nf
    simp only [Complex.I_sq, pow_succ]
    ring

def highestImage (β : ℂˣ) (n : ℕ) : Theta β :=
  ⟨harmonicSection negativeParameter n,
    harmonicKType_le_imageSubmodule β n (harmonicSection_harmonic negativeParameter n)⟩

theorem highestImage_upper (β : ℂˣ) (n : ℕ) :
    dPiComplexUpperRoot β Z_plus (highestImage β n) =
      (-((n:ℂ)+(2/3:ℂ))/2) • highestImage β (n+1) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (Z_plus.1 * deriv (fun t : ℝ => harmonicSection negativeParameter n
    (g * upperUnipotent ((t:ℂ)*1))) 0 +
    Z_plus.2 * deriv (fun t : ℝ => harmonicSection negativeParameter n
    (g * upperUnipotent ((t:ℂ)*Complex.I))) 0) = _
  rw [highest_orbit_deriv, highest_orbit_deriv]
  have hh := Hvel_plus negativeParameter n ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖
    (g 1 0) (g 1 1) (rowB_pos g).ne'
  norm_num [negativeParameter] at hh
  simp only [Z_plus, E_R, E_I, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at ⊢
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_zero, Prod.snd_zero, smul_eq_mul, mul_zero, mul_one, sub_zero, zero_sub,
    mul_one]
  change (1/2:ℂ) * Hvel negativeParameter n _ _ _ 1 +
    (1/2:ℂ) * (-Complex.I) * Hvel negativeParameter n _ _ _ Complex.I = _
  change _ = (-((n:ℂ)+(2/3:ℂ))/2) *
    ((Real.rpow (‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ / rowB g)
      (1+2*negativeParameter):ℂ) * rowW g ^ (n+1))
  dsimp only [rowW, rowB]
  norm_num only [negativeParameter] at ⊢
  simp only [Real.rpow_eq_pow, Complex.star_def, Complex.ofReal_add, Complex.ofReal_pow] at ⊢
  convert hh using 1 <;> ring

private lemma whittaker_one (β : ℂˣ) (h : Theta β) :
    whittakerValue β h 1 = KPCplxJacquetFunctional.thetaJacquetFunctional β h := by
  have hd : diagonal (1:ℂˣ) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.one_apply]
  unfold whittakerValue
  rw [hd, map_one]
  have he : imageAction β 1 h = h := by
    apply Subtype.ext
    exact pi_one negativeParameter h.val
  rw [he]

theorem highestImage_jacquet_ne_zero (n : ℕ) :
    KPCplxJacquetFunctional.thetaJacquetFunctional standardComplexParameter
      (highestImage standardComplexParameter n) ≠ 0 := by
  induction n with
  | zero =>
    have hs := spherical_image standardComplexParameter
    have hp := KPCplxPlanarKernel.jacquet_spherical_diagonal_positive
      (4*Real.pi) (by positivity) standardComplexParameter
      (by rfl) (1:ℂˣ)
    rw [← KPCplxJacquetFunctional.thetaJacquetFunctional_intertwiner] at hp
    have hw := whittaker_one standardComplexParameter
      (intertwinerToImage standardComplexParameter (sphericalSection positiveParameter))
    have hd : diagonal (1:ℂˣ) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.one_apply]
    rw [hd, map_one, pi_one] at hp
    have he : intertwinerToImage standardComplexParameter (sphericalSection positiveParameter) =
        (3*characterScale standardComplexParameter/2:ℂ) • highestImage standardComplexParameter 0 := by
      apply Subtype.ext
      rw [hs.1]
      apply Subtype.ext
      funext g
      change _ = (3*characterScale standardComplexParameter/2:ℂ) *
        (sphericalSection negativeParameter g * rowW g ^ 0)
      simp
    rw [he, map_smul, smul_eq_mul] at hp
    intro hz
    rw [hz, mul_zero] at hp
    simpa using hp.2
  | succ n ih =>
    have h := (whittaker_complexUpperRootDerivatives (4*Real.pi) (by positivity)
      standardComplexParameter (by rfl) (highestImage standardComplexParameter n) 1).1
    rw [highestImage_upper, whittaker_one, whittaker_one, map_smul, smul_eq_mul] at h
    intro hz
    rw [hz, mul_zero] at h
    have hn : (Complex.I * (4*Real.pi:ℂ)/2) ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (show (4*Real.pi:ℝ) ≠ 0 by positivity))
      · norm_num
    apply ih
    apply (mul_eq_zero.mp h.symm).resolve_left
    simpa only [Units.val_one, mul_one, Complex.ofReal_mul, Complex.ofReal_ofNat] using hn

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
