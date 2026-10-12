module

public import DedekindZetaZeroFree.Adeles.Characters.TracePhaseUniqueness
public import DedekindZetaZeroFree.LFunctions.Tate.Local.HaarMellinComparison

@[expose] public section

section
namespace DedekindZetaZeroFree
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace RadialCancellingProfile
 def bump : ContDiffBump (9 / 4 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
 def phi (z : ℂ) : ℂ := (bump (Complex.normSq z) : ℂ)
private theorem phi_smooth : ContDiff ℝ (⊤ : ℕ∞) phi := by
  apply Complex.ofRealCLM.contDiff.comp
  apply bump.contDiff.comp
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
private theorem phi_annulus : tsupport phi ⊆ {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
  apply closure_minimal
  · intro z hz
    have hb : bump (Complex.normSq z) ≠ 0 := by simpa [Function.mem_support, phi] using hz
    have hb' := (bump.support_eq ▸ hb : Complex.normSq z ∈ Metric.ball (9 / 4 : ℝ) 1)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hb'
    rw [Complex.normSq_eq_norm_sq] at hb'
    dsimp [bump] at hb'
    have hn := norm_nonneg z
    constructor <;> nlinarith
  · exact isClosed_le continuous_const continuous_norm |>.inter
      (isClosed_le continuous_norm continuous_const)
private theorem phi_annular : IsComplexAnnular phi := by
  refine ⟨phi_smooth, ?_, 1, 2, by norm_num, by norm_num, phi_annulus⟩
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 2) isClosed_closure
  intro z hz
  simpa using (phi_annulus hz).2
private theorem phi_radial (z w : ℂ) (h : ‖z‖ = ‖w‖) : phi z = phi w := by
  simp [phi, Complex.normSq_eq_norm_sq, h]
private theorem phi_mellin_ne : complexNormMellin phi (5 / 6) ≠ 0 := by
  let w : ℂ → ℝ := fun z => (max (‖z‖ ^ 2) 1) ^ (-1 / 6 : ℝ)
  have hw : Continuous w := by
    apply Continuous.rpow_const ((continuous_norm.pow 2).max continuous_const)
    intro z
    left
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _))
  let g : ℂ → ℝ := fun z => (phi z).re * w z
  have hc : Continuous g := (Complex.reCLM.continuous.comp phi_smooth.continuous).mul hw
  have hk : HasCompactSupport g := phi_annular.2.1.comp_left (g := Complex.reCLM) (by simp) |>.mul_right
  have hp : 0 < ∫ z : ℂ, g z := by
    apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hk
    · intro z; exact mul_nonneg bump.nonneg (Real.rpow_nonneg (le_max_right _ _ |>.trans' (by norm_num)) _)
    · show g ((3 / 2 : ℝ) : ℂ) ≠ 0
      have hb : bump (Complex.normSq ((3 / 2 : ℝ) : ℂ)) = 1 := by
        apply bump.one_of_mem_closedBall
        norm_num [bump, Complex.normSq_apply, Metric.mem_closedBall, Real.dist_eq]
      dsimp [g, phi, w]
      rw [hb]
      simp only [Complex.ofReal_re, one_mul]
      exact (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)) _).ne'
  have he : complexNormMellinIntegrand phi (5 / 6) = fun z => (g z : ℂ) := by
    funext z
    by_cases hz : phi z = 0
    · simp [complexNormMellinIntegrand, hz, g]
    · have ha := (phi_annulus (subset_tsupport phi hz)).1
      have hz0 : z ≠ 0 := by intro h; have := ha; norm_num [h] at this
      have hsq : 1 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      simp [complexNormMellinIntegrand, hz0, g, w, max_eq_left hsq, phi]
      norm_num
  rw [complexNormMellin, he]
  change (Real.pi : ℂ)⁻¹ * (∫ x : ℂ, (g x : ℂ)) ≠ 0
  rw [integral_complex_ofReal]
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast Real.pi_ne_zero))
    (by exact_mod_cast hp.ne')
 def dil (z : ℂ) : ℂ := phi ((1 / 2 : ℝ) • z)
private theorem dil_annular : IsComplexAnnular dil := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) dil := phi_smooth.comp (contDiff_id.const_smul (1 / 2 : ℝ))
  have ha : tsupport dil ⊆ {z : ℂ | 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 4} := by
    apply closure_minimal
    · intro z hz
      have h := phi_annulus (subset_tsupport phi (by simpa [Function.mem_support, dil] using hz))
      norm_num [norm_smul, Real.norm_eq_abs] at h
      constructor <;> linarith [h.1, h.2]
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  refine ⟨hs, ?_, 2, 4, by norm_num, by norm_num, ha⟩
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 4) isClosed_closure
  intro z hz
  simpa using (ha hz).2
 def f (z : ℂ) : ℂ := phi z - (1 / 4 : ℂ) * dil z
private theorem f_annular : IsComplexAnnular f := by
  refine ⟨phi_smooth.sub (contDiff_const.mul dil_annular.1),
    phi_annular.2.1.sub (dil_annular.2.1.mul_left), 1, 4, by norm_num, by norm_num, ?_⟩
  apply closure_minimal
  · intro z hz
    have hn : phi z ≠ 0 ∨ dil z ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      simp [Function.mem_support, f, h.1, h.2] at hz
    rcases hn with h | h
    · have h := phi_annulus (subset_tsupport phi h)
      exact ⟨h.1, h.2.trans (by norm_num)⟩
    · have h' := phi_annulus (subset_tsupport phi h)
      norm_num [norm_smul, Real.norm_eq_abs] at h'
      constructor <;> linarith [h'.1, h'.2]
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
private theorem f_integral_zero : (∫ z : ℂ, f z) = 0 := by
  have hi : Integrable phi volume := phi_smooth.continuous.integrable_of_hasCompactSupport phi_annular.2.1
  have hj : Integrable dil volume := dil_annular.1.continuous.integrable_of_hasCompactSupport dil_annular.2.1
  change (∫ z : ℂ, phi z - (1 / 4 : ℂ) * dil z) = 0
  rw [integral_sub hi (hj.const_mul _), integral_const_mul]
  have he : (∫ z : ℂ, dil z) = (4 : ℂ) * ∫ z : ℂ, phi z := by
    have h := Measure.integral_comp_smul volume phi (1 / 2 : ℝ)
    norm_num [dil, Complex.finrank_real_complex, Complex.real_smul] at h ⊢
    exact h
  rw [he]
  ring
private theorem dil_mellin : complexNormMellin dil (5 / 6) =
    ((2 : ℝ) ^ (5 / 3 : ℝ) : ℝ) * complexNormMellin phi (5 / 6) := by
  have he : complexNormMellinIntegrand dil (5 / 6) = fun z =>
      (((2 : ℝ) ^ (-1 / 3 : ℝ) : ℝ) : ℂ) * complexNormMellinIntegrand phi (5 / 6) ((1 / 2 : ℝ) • z) := by
    funext z
    by_cases hz : z = 0
    · simp [complexNormMellinIntegrand, hz]
    have hz' : (1 / 2 : ℝ) • z ≠ 0 := smul_ne_zero (by norm_num) hz
    simp only [complexNormMellinIntegrand, if_neg hz, if_neg hz', dil]
    norm_num only [norm_smul, Real.norm_eq_abs, abs_div, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [mul_pow, Real.mul_rpow (by positivity) (sq_nonneg _)]
    have hp : ((1 / 2 : ℝ) ^ 2) ^ ((5 / 6 : ℝ) - 1) = 2 ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
      congr 1
      norm_num
    convert_to phi ((1 / 2 : ℝ) • z) * ↑((‖z‖ ^ 2) ^ (-(1 / 6 : ℝ))) =
      ↑((2 : ℝ) ^ (-1 / 3 : ℝ)) * (phi ((1 / 2 : ℝ) • z) *
        ↑(((1 / 2 : ℝ) ^ 2) ^ (-(1 / 6 : ℝ)) * ((‖z‖ ^ 2) ^ (-(1 / 6 : ℝ))))) using 1 <;> norm_num
    have hp' : (1 / 4 : ℝ) ^ (-(1 / 6 : ℝ)) = 2 ^ (1 / 3 : ℝ) := by
      convert hp using 1 <;> norm_num
    rw [hp']
    have hh : (2 : ℝ) ^ (-1 / 3 : ℝ) * 2 ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num
    have hh' : (((2 : ℝ) ^ (-1 / 3 : ℝ) : ℝ) : ℂ) * (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hh
    simp only [Complex.real_smul] at *
    norm_num at hh'
    linear_combination -(phi ((1 / 2 : ℂ) * z) * ↑((‖z‖ ^ 2) ^ (-(1 / 6 : ℝ)))) * hh'
  rw [complexNormMellin, he, integral_const_mul]
  have hd := Measure.integral_comp_smul volume (complexNormMellinIntegrand phi (5 / 6)) (1 / 2 : ℝ)
  simp only [Complex.finrank_real_complex] at hd
  norm_num only [one_div, inv_pow, inv_inv, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul] at hd
  change (Real.pi : ℂ)⁻¹ * ((((2 : ℝ) ^ (-1 / 3 : ℝ) : ℝ) : ℂ) * ∫ a : ℂ, complexNormMellinIntegrand phi (5 / 6) ((1 / 2 : ℝ) • a)) = _
  simp only [Complex.real_smul]
  rw [hd]
  have hp : (2 : ℝ) ^ (-1 / 3 : ℝ) * 4 = 2 ^ (5 / 3 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by positivity)]
    congr 1
    norm_num
  have hp' : (((2 : ℝ) ^ (-1 / 3 : ℝ) : ℝ) : ℂ) * 4 = (((2 : ℝ) ^ (5 / 3 : ℝ) : ℝ) : ℂ) := by exact_mod_cast hp
  unfold complexNormMellin
  push_cast
  linear_combination (Real.pi : ℂ)⁻¹ * (∫ x : ℂ, complexNormMellinIntegrand phi (5 / 6) x) * hp'
private theorem f_mellin_ne : complexNormMellin f (5 / 6) ≠ 0 := by
  have hi := complexAnnular_normMellin_integrable phi phi_annular (1 / 6) (by norm_num) (by norm_num)
  have hj := complexAnnular_normMellin_integrable dil dil_annular (1 / 6) (by norm_num) (by norm_num)
  norm_num at hi hj
  have he : complexNormMellin f (5 / 6) = complexNormMellin phi (5 / 6) -
      (1 / 4 : ℂ) * complexNormMellin dil (5 / 6) := by
    have he' : complexNormMellinIntegrand f (5 / 6) = fun z =>
        complexNormMellinIntegrand phi (5 / 6) z - (1 / 4 : ℂ) * complexNormMellinIntegrand dil (5 / 6) z := by
      funext z
      by_cases hz : z = 0
      · simp [complexNormMellinIntegrand, hz]
      · simp only [complexNormMellinIntegrand, if_neg hz, f]
        ring
    rw [complexNormMellin, he', integral_sub hi (hj.const_mul _), integral_const_mul]
    unfold complexNormMellin
    ring
  rw [he, dil_mellin]
  have hlt : (2 : ℝ) ^ (5 / 3 : ℝ) < 4 := by
    calc
      _ < (2 : ℝ) ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hn : (1 : ℂ) - (1 / 4 : ℂ) * (((2 : ℝ) ^ (5 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have h : (1 : ℝ) - (1 / 4 : ℝ) * (2 : ℝ) ^ (5 / 3 : ℝ) ≠ 0 := by linarith
    have hc : ((1 - (1 / 4 : ℝ) * (2 : ℝ) ^ (5 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast at hc
    norm_num at hc ⊢
    exact hc
  rw [show complexNormMellin phi (5 / 6) -
    (1 / 4 : ℂ) * (↑((2 : ℝ) ^ (5 / 3 : ℝ)) * complexNormMellin phi (5 / 6)) =
    (1 - (1 / 4 : ℂ) * ↑((2 : ℝ) ^ (5 / 3 : ℝ))) * complexNormMellin phi (5 / 6) by ring]
  exact mul_ne_zero hn phi_mellin_ne
private theorem profile_exists : ∃ f : ℂ → ℂ, IsComplexAnnular f ∧
    (∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w) ∧
    (∫ z : ℂ, f z) = 0 ∧ complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0 := by
  refine ⟨f, f_annular, ?_, f_integral_zero, ?_⟩
  · intro z w h
    dsimp [f, dil]
    rw [phi_radial z w h]
    congr 2
    apply phi_radial
    simp [norm_mul, h]
  · rw [complexTraceFourier_normMellin f f_annular (1 / 6) (by norm_num) (by norm_num)]
    convert mul_ne_zero (complexGamma_ratio_ne_zero (1 / 6) (by norm_num) (by norm_num)) f_mellin_ne using 1 <;> norm_num
end RadialCancellingProfile

 def radialBumpProfile : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem exists_radial_complex_cancelling_profile :
    ∃ f : ℂ → ℂ, IsComplexAnnular f ∧
      (∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w) ∧
      (∫ z : ℂ, f z ∂(volume : Measure ℂ)) = 0 ∧
      complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0 := by
  exact RadialCancellingProfile.profile_exists

end
end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree.ProbeAnnularTensorWeights
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

structure AnnularCoordinates where
  fReal : (v : {v : InfinitePlace F // v.IsReal}) → ℝ → ℂ
  fComplex : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ
  fFinite : (v : ↥S) → v.val.adicCompletion F → ℂ
  real_regular : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fReal v) ∧
    HasCompactSupport (fReal v) ∧ (0 : ℝ) ∉ tsupport (fReal v)
  complex_regular : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fComplex v) ∧
    HasCompactSupport (fComplex v) ∧ (0 : ℂ) ∉ tsupport (fComplex v) ∧
    ∀ z w, ‖z‖ = ‖w‖ → fComplex v z = fComplex v w
  finite_regular : ∀ v, IsLocallyConstant (fFinite v) ∧
    HasCompactSupport (fFinite v) ∧
    (0 : v.val.adicCompletion F) ∉ tsupport (fFinite v)

def tensor (c : AnnularCoordinates F S) (x : SLocalProduct F S) : ℂ :=
  (∏ v, c.fReal v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
    (∏ v, c.fComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
    ∏ v : ↥S, c.fFinite v (x.2 v)

def modulus (y : (SLocalProduct F S)ˣ) : ℝ :=
  (∏ v : InfinitePlace F, ‖(y.val.1 v)‖ ^ (2 : ℕ)) *
    ∏ v : ↥S, ‖y.val.2 v‖

def fourierMellin (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F S) (borel _))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (W : SLocalProduct F S → ℂ) (z : ℂ) : ℂ :=
  ∫ y, (∫ x, W x * ProbeAdditive.phase F S e (-x * y.val) ∂μ) *
    (modulus F S y : ℂ) ^ z ∂ν

theorem complex_profile_ne_zero (f : ℂ → ℂ)
    (hm : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0) : f ≠ 0 := by
  intro h
  subst f
  apply hm
  simp [complexNormMellin, complexNormMellinIntegrand, complexTraceFourier]

theorem arithmetic_complex_place (A : SArithmeticData F) :
    Nonempty {v : InfinitePlace F // v.IsComplex} := by
  exact ⟨⟨Classical.arbitrary (InfinitePlace F), A.infinite_isComplex _⟩⟩

def shellCoordinates (A : SArithmeticData F) (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w) : AnnularCoordinates F A.Sf where
  fReal := fun _ _ => 0
  fComplex := fun _ => f
  fFinite := fun v => TateFiniteShell.annularTest F v.val
  real_regular := fun v => False.elim
    ((InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.1)) v.2)
  complex_regular := fun _ => ⟨hf.1, hf.2.1,
    TateTensorProfile.complexAnnular_zero_not_tsupport f hf, hrad⟩
  finite_regular := fun v => by
    have hs := TateFiniteShell.annularTest_mem_localSchwartz F v.val
    refine ⟨hs.1, hs.2, ?_⟩
    let U := TateFiniteShell.unitShell F v.val
    have hU : IsClosed U :=
      (isCompact_finiteCompletionBall F v.val 0).isClosed.inter
        (isOpen_finiteCompletionBall F v.val 1).isClosed_compl
    have ht : tsupport (TateFiniteShell.annularTest F v.val) ⊆ U := by
      apply closure_minimal _ hU
      intro x hx
      by_contra h
      exact hx (by simp [TateFiniteShell.annularTest, U, h])
    intro h
    have := (TateFiniteShell.mem_unitShell_iff F v.val 0).mp (ht h)
    simpa using this

theorem shellCoordinates_tensor_eq (A : SArithmeticData F) (f : ℂ → ℂ)
    (hf : IsComplexAnnular f) (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    [NumberField.IsTotallyComplex F] :
    tensor F A.Sf (shellCoordinates F A f hf hrad) =
      TateTensorProfile.coordinateTensor F A.Sf (fun _ => f) := by
  haveI : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.1)) v.2⟩
  funext x
  simp [tensor, shellCoordinates, TateTensorProfile.coordinateTensor,
    TateTensorProfile.archTensor, PoissonArch.infiniteAdeleToSpace_coordinates]

theorem shellCoordinates_canonical_pairings (A : SArithmeticData F)
    (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    (hcancel : (∫ z : ℂ, f z) = 0)
    (hmoment : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0)
    [NumberField.IsTotallyComplex F] :
    (∫ x, tensor F A.Sf (shellCoordinates F A f hf hrad) x
      ∂TateTensorProfile.additiveMeasure F A.Sf) = 0 ∧
    tensor F A.Sf (shellCoordinates F A f hf hrad) ≠ 0 ∧
    TateTensorProfile.normMellin F A.Sf
      (tensor F A.Sf (shellCoordinates F A f hf hrad)) (1 / 6) ≠ 0 := by
  rw [shellCoordinates_tensor_eq]
  refine ⟨?_, TateTensorProfile.coordinateTensor_ne_zero F A.Sf (fun _ => f)
    (fun _ => complex_profile_ne_zero f hmoment), ?_⟩
  · have hz := TateTensorProfile.coordinateTensor_fourier_zero F A.Sf (fun _ => f)
      (Classical.choice (arithmetic_complex_place F A)) hcancel
    simpa [TateTensorProfile.fourier] using hz
  · exact TateTensorProfile.coordinateTensor_normMellin_ne_zero_of_factors F A.Sf
      (fun _ => f) (1 / 6) (by norm_num) (fun _ => hmoment)
      (fun v => TateFiniteShellFourierIntegrals.finiteShell_weighted_fourier_integral_ne_zero F v.val
        (1 / 6) (by norm_num) (by norm_num))

 instance instMeasurableSpaceAnnularTensorInfiniteAdeleRing : MeasurableSpace (InfiniteAdeleRing F) := borel _
 instance instBorelSpaceAnnularTensorInfiniteAdeleRing : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
 instance instMeasurableSpaceAnnularTensorAdicCompletion (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
 instance instBorelSpaceAnnularTensorAdicCompletion (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem tensorAdditiveHaar [NumberField.IsTotallyComplex F] :
    (TateTensorProfile.additiveMeasure F S).IsAddHaarMeasure := by
  letI := PoissonArch.traceMeasure_isAddHaarMeasure F
  letI : ∀ v : S, (localNormalizedHaar F v.val).IsAddHaarMeasure :=
    fun v => localNormalizedHaar_isAddHaarMeasure F v.val
  letI := (PoissonArch.infiniteAdeleToSpace F).symm.isAddHaarMeasure_map
    (PoissonArch.traceMeasure F)
  unfold TateTensorProfile.additiveMeasure
  infer_instance

theorem shellCoordinates_additive_cancel (A : SArithmeticData F)
    (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    (hcancel : (∫ z : ℂ, f z) = 0)
    (hmoment : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0)
    [NumberField.IsTotallyComplex F]
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ) :
    (∫ x, tensor F A.Sf (shellCoordinates F A f hf hrad) x ∂μ) = 0 := by
  letI := tensorAdditiveHaar F A.Sf
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F) :=
    fun v => PoissonS.completion_secondCountable F v.val
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.secondCountableTopology
  have heq := BorelSpace.measurable_eq (α := SLocalProduct F A.Sf)
  revert μ hμ
  rw [← heq]
  intro μ hμ
  letI := hμ
  rw [Measure.isAddLeftInvariant_eq_smul μ (TateTensorProfile.additiveMeasure F A.Sf)]
  rw [integral_smul_nnreal_measure,
    (shellCoordinates_canonical_pairings F A f hf hrad hcancel hmoment).1, smul_zero]

theorem modulus_eq_canonical (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F] (y : (SLocalProduct F S)ˣ) :
    modulus F S y = TateTensorProfile.modulus F S y.val := by
  unfold modulus TateTensorProfile.modulus
  congr 1
  rw [InfiniteAdeleRing.norm_def]
  apply Finset.prod_congr rfl
  intro v hv
  rw [(NumberField.IsTotallyComplex.isComplex v).mult_eq_two]

theorem exists_tensor_from_haar_comparison (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    (hcancel : (∫ z : ℂ, f z ∂(volume : Measure ℂ)) = 0)
    (hmoment : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0)
    (hphase : ∀ x, ProbeAdditive.phase F A.Sf e x =
      (sLocalTraceCharacter F A.Sf x : ℂ))
    (hcomparison : ∃ a : ℝ, 0 < a ∧ ∀ (W : SLocalProduct F A.Sf → ℂ) (s : ℝ),
      (∫ y, (∫ x, W x * (sLocalTraceCharacter F A.Sf (-x * y.val) : ℂ) ∂μ) *
        (TateTensorProfile.modulus F A.Sf y.val : ℂ) ^ (s : ℂ) ∂ν) =
        (a : ℂ) * TateTensorProfile.normMellin F A.Sf W s) :
    ∃ (c : AnnularCoordinates F A.Sf)
      (vc : {v : InfinitePlace F // v.IsComplex}),
      c.fComplex vc = f ∧
      (∫ x, tensor F A.Sf c x ∂μ) = 0 ∧
      tensor F A.Sf c ≠ 0 ∧
      fourierMellin F A.Sf e μ ν (tensor F A.Sf c) (1 / 6) ≠ 0 := by
  letI : NumberField.IsTotallyComplex F := ⟨A.infinite_isComplex⟩
  let c := shellCoordinates F A f hf hrad
  let vc := Classical.choice (arithmetic_complex_place F A)
  refine ⟨c, vc, rfl,
    shellCoordinates_additive_cancel F A f hf hrad hcancel hmoment μ hμ,
    (shellCoordinates_canonical_pairings F A f hf hrad hcancel hmoment).2.1, ?_⟩
  obtain ⟨a, ha, hcomp⟩ := hcomparison
  have heq : fourierMellin F A.Sf e μ ν (tensor F A.Sf c) (1 / 6) =
      (a : ℂ) * TateTensorProfile.normMellin F A.Sf (tensor F A.Sf c) (1 / 6) := by
    unfold fourierMellin
    simp_rw [hphase, modulus_eq_canonical]
    convert hcomp (tensor F A.Sf c) (1 / 6) using 1 <;> norm_num
  rw [heq]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')
    (shellCoordinates_canonical_pairings F A f hf hrad hcancel hmoment).2.2

theorem exists_tensor_from_complex_profile (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    (hcancel : (∫ z : ℂ, f z ∂(volume : Measure ℂ)) = 0)
    (hmoment : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0) :
    ∃ (c : AnnularCoordinates F A.Sf)
      (vc : {v : InfinitePlace F // v.IsComplex}),
      c.fComplex vc = f ∧
      (∫ x, tensor F A.Sf c x ∂μ) = 0 ∧
      tensor F A.Sf c ≠ 0 ∧
      fourierMellin F A.Sf e μ ν (tensor F A.Sf c) (1 / 6) ≠ 0 := by
  letI : NumberField.IsTotallyComplex F := ⟨A.infinite_isComplex⟩
  exact exists_tensor_from_haar_comparison F A e he htrace μ ν hμ hν f hf hrad
    hcancel hmoment
    (TateSLocalComparison.compatible_phase_eq_trace F A e he htrace)
    (TateSLocalComparison.haar_fourierMellin_comparison F A.Sf μ ν hμ hν)

end
end DedekindZetaZeroFree.ProbeAnnularTensorWeights

end

section

namespace DedekindZetaZeroFree.ProbeAnnularTensorWeights
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain NumberField.InfinitePlace

 def supportMixedHomeo (F : Type) [Field F] [NumberField F] :
    InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
    (fun v => v.Completion)).trans
    ((Homeomorph.prodCongr
      (Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))))

theorem tensor_compactSupport_and_unit_support
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c : AnnularCoordinates F S) :
    HasCompactSupport (tensor F S c) ∧
      tsupport (tensor F S c) ⊆ {x | IsUnit x} := by
  classical
  let Kr := Set.pi Set.univ (fun v => tsupport (c.fReal v))
  let Kc := Set.pi Set.univ (fun v => tsupport (c.fComplex v))
  let Kf := Set.pi Set.univ (fun v => tsupport (c.fFinite v))
  let e := (supportMixedHomeo F).prodCongr
    (Homeomorph.refl ((v : ↥S) → v.val.adicCompletion F))
  let K := e ⁻¹' ((Kr ×ˢ Kc) ×ˢ Kf)
  have hr : IsCompact Kr := isCompact_univ_pi (fun v => (c.real_regular v).2.1)
  have hc : IsCompact Kc := isCompact_univ_pi (fun v => (c.complex_regular v).2.1)
  have hf : IsCompact Kf := isCompact_univ_pi (fun v => (c.finite_regular v).2.1)
  have hK : IsCompact K := e.isCompact_preimage.mpr ((hr.prod hc).prod hf)
  have hs : Function.support (tensor F S c) ⊆ K := by
    intro x hx
    have hn : tensor F S c x ≠ 0 := hx
    unfold tensor at hn
    have hrn := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
    have hcn := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    have hfn := (mul_ne_zero_iff.mp hn).2
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 ∈ Kr ∧
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 ∈ Kc) ∧ x.2 ∈ Kf
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v hv
      exact subset_tsupport _ ((Finset.prod_ne_zero_iff.mp hrn) v (Finset.mem_univ v))
    · intro v hv
      exact subset_tsupport _ ((Finset.prod_ne_zero_iff.mp hcn) v (Finset.mem_univ v))
    · intro v hv
      exact subset_tsupport _ ((Finset.prod_ne_zero_iff.mp hfn) v (Finset.mem_univ v))
  have ht : tsupport (tensor F S c) ⊆ K :=
    closure_minimal hs hK.isClosed
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport _) ht, ?_⟩
  intro x hx
  have hxK := ht hx
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 ∈ Kr ∧
    (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 ∈ Kc) ∧ x.2 ∈ Kf at hxK
  apply Prod.isUnit_iff.mpr
  constructor
  · have hu : IsUnit (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) := by
      apply Prod.isUnit_iff.mpr
      constructor
      · apply Pi.isUnit_iff.mpr
        intro v
        apply isUnit_iff_ne_zero.mpr
        intro hz
        exact (c.real_regular v).2.2 (hz ▸ hxK.1.1 v (Set.mem_univ v))
      · apply Pi.isUnit_iff.mpr
        intro v
        apply isUnit_iff_ne_zero.mpr
        intro hz
        exact (c.complex_regular v).2.2.1 (hz ▸ hxK.1.2 v (Set.mem_univ v))
    have hu' := hu.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toMonoidHom
    change IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)) at hu'
    rw [RingEquiv.symm_apply_apply] at hu'
    exact hu'
  · apply Pi.isUnit_iff.mpr
    intro v
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact (c.finite_regular v).2.2 (hz ▸ hxK.2 v (Set.mem_univ v))

end
end DedekindZetaZeroFree.ProbeAnnularTensorWeights

end

section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

structure ProbeRealAnnularWeight where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compactSupport : HasCompactSupport toFun
  support_positive : tsupport toFun ⊆ Set.Ioi 0
  nonnegative : ∀ v, 0 ≤ toFun v
  nonzero : toFun ≠ 0

instance : CoeFun ProbeRealAnnularWeight (fun _ => ℝ → ℝ) :=
  ⟨ProbeRealAnnularWeight.toFun⟩

def probeRealWeightMellin (W : ProbeRealAnnularWeight) (w : ℂ) : ℂ :=
  ∫ v in Set.Ioi (0 : ℝ), (W v : ℂ) * (v : ℂ) ^ w / (v : ℂ)

theorem probeRealWeightMellin_one (W : ProbeRealAnnularWeight) :
    probeRealWeightMellin W 1 = (∫ v, W v : ℝ) := by
  have hfun : ∀ v : ℝ,
      (W v : ℂ) * (v : ℂ) ^ (1 : ℂ) / (v : ℂ) = (W v : ℂ) := by
    intro v
    by_cases hv : 0 < v
    · simp [Complex.cpow_one, ne_of_gt hv,
        Complex.ofReal_ne_zero.mpr (ne_of_gt hv)]
    · have hz : W v = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro he
        exact hv (W.support_positive he)
      simp [hz]
  simp only [probeRealWeightMellin, hfun]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_ofReal
  · intro v hv
    have hz : W v = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro he
      exact hv (W.support_positive he)
    simp [hz]

theorem probeRealWeightMellin_one_ne_zero (W : ProbeRealAnnularWeight) :
    probeRealWeightMellin W 1 ≠ 0 := by
  rw [probeRealWeightMellin_one]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, W x ≠ 0 := by
    by_contra h
    apply W.nonzero
    ext x
    simpa using not_exists.mp h x
  have hp : 0 < ∫ v : ℝ, W v :=
    W.smooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      W.compactSupport W.nonnegative hx
  exact_mod_cast (ne_of_gt hp)

def probeBump : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem probeBump_tsupport_subset : tsupport (probeBump : ℝ → ℝ) ⊆ Set.Ioi 0 := by
  intro x hx
  rw [ContDiffBump.tsupport_eq] at hx
  have hr : probeBump.rOut = 1 / 2 := rfl
  rw [hr, Metric.mem_closedBall, Real.dist_eq] at hx
  have h := (abs_le.mp hx).1
  simp only [Set.mem_Ioi]
  linarith

theorem probeBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (probeBump : ℝ → ℝ) :=
  probeBump.contDiff

theorem probeBump_nonneg (x : ℝ) : 0 ≤ probeBump x := probeBump.nonneg

theorem probeBump_nonzero : (probeBump : ℝ → ℝ) ≠ 0 := by
  intro h
  have h1 : probeBump (1 : ℝ) = 1 :=
    ContDiffBump.one_of_mem_closedBall (f := probeBump) (x := (1 : ℝ)) (by
      rw [Metric.mem_closedBall, dist_self]
      exact probeBump.rIn_pos.le)
  have h2 : probeBump (1 : ℝ) = 0 := congrFun h 1
  rw [h1] at h2
  exact one_ne_zero h2

def probeRealBumpWeight : ProbeRealAnnularWeight where
  toFun := probeBump
  smooth := probeBump_contDiff
  compactSupport := probeBump.hasCompactSupport
  support_positive := probeBump_tsupport_subset
  nonnegative := probeBump_nonneg
  nonzero := probeBump_nonzero

namespace ProbeWeight
variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local instance : MeasurableSpace (SLocalProduct F S) := borel _

local instance : BorelSpace (SLocalProduct F S) := ⟨rfl⟩

def IsAnnularTensor (W : SLocalProduct F S → ℂ) : Prop :=
  ∃ (fReal : (v : {v : InfinitePlace F // v.IsReal}) → ℝ → ℂ)
    (fComplex : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (fFinite : (v : ↥S) → v.val.adicCompletion F → ℂ),
    (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fReal v) ∧ HasCompactSupport (fReal v) ∧
      (0 : ℝ) ∉ tsupport (fReal v)) ∧
    (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fComplex v) ∧ HasCompactSupport (fComplex v) ∧
      (0 : ℂ) ∉ tsupport (fComplex v) ∧
      ∀ z w, ‖z‖ = ‖w‖ → fComplex v z = fComplex v w) ∧
    (∀ v, IsLocallyConstant (fFinite v) ∧ HasCompactSupport (fFinite v) ∧
      (0 : v.val.adicCompletion F) ∉ tsupport (fFinite v)) ∧
    ∀ x, W x =
      (∏ v, fReal v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
      (∏ v, fComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
      ∏ v : ↥S, fFinite v (x.2 v)

def fourier (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : Measure (SLocalProduct F S)) (W : SLocalProduct F S → ℂ)
    (y : SLocalProduct F S) : ℂ :=
  ∫ x, W x * ProbeAdditive.phase F S e (-x * y) ∂μ

def modulus (y : (SLocalProduct F S)ˣ) : ℝ :=
  (∏ v : InfinitePlace F, ‖(y.val.1 v)‖ ^ (2 : ℕ)) *
    ∏ v : ↥S, ‖y.val.2 v‖

def fourierMellin (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : Measure (SLocalProduct F S)) (ν : Measure (SLocalProduct F S)ˣ)
    (W : SLocalProduct F S → ℂ) (z : ℂ) : ℂ :=
  ∫ y, fourier F S e μ W y.val * (modulus F S y : ℂ) ^ z ∂ν

end ProbeWeight

theorem ProbeWeight.fourier_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F S) (borel _))
    (W : SLocalProduct F S → ℂ) :
    ProbeWeight.fourier F S e μ W 0 = ∫ x, W x ∂μ := by
  have hx : ∀ x : InfinitePlace F, (0 : InfiniteAdeleRing F) x = 0 := fun x => rfl
  have h0 : ProbeAdditive.phase F S e (0 : SLocalProduct F S) = 1 := by
    unfold ProbeAdditive.phase ProbeAdditive.archPhase
    simp only [Prod.fst_zero, Prod.snd_zero]
    simp [AddChar.map_zero_eq_one, NumberField.InfiniteAdeleRing, hx]
  rw [ProbeWeight.fourier]
  simp only [mul_zero, neg_zero, h0, mul_one]

theorem probe_fixed_weight_construction (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν) :
    ∃ (W1 : ProbeRealAnnularWeight) (W0 : SLocalProduct F A.Sf → ℂ),
      ProbeWeight.IsAnnularTensor F A.Sf W0 ∧ HasCompactSupport W0 ∧
      tsupport W0 ⊆ {x | IsUnit x} ∧ W0 ≠ 0 ∧
      ProbeWeight.fourier F A.Sf e μ W0 0 = 0 ∧
      ProbeWeight.fourierMellin F A.Sf e μ ν W0 (1 / 6) ≠ 0 ∧
      probeRealWeightMellin W1 1 ≠ 0 := by
  obtain ⟨f, hf, hrad, hcancel, hmoment⟩ := exists_radial_complex_cancelling_profile
  obtain ⟨c, vc, hvc, hmass, hnonzero, hmellin⟩ :=
    ProbeAnnularTensorWeights.exists_tensor_from_complex_profile F A e he htrace μ ν hμ hν
      f hf hrad hcancel hmoment
  obtain ⟨hcompact, hunit⟩ :=
    ProbeAnnularTensorWeights.tensor_compactSupport_and_unit_support F A.Sf c
  refine ⟨probeRealBumpWeight, ProbeAnnularTensorWeights.tensor F A.Sf c, ?_, hcompact,
    hunit, hnonzero, ?_, ?_, probeRealWeightMellin_one_ne_zero probeRealBumpWeight⟩
  · exact ⟨c.fReal, c.fComplex, c.fFinite, c.real_regular, c.complex_regular,
      c.finite_regular, fun x => rfl⟩
  · rw [ProbeWeight.fourier_zero]
    exact hmass
  · exact hmellin

end
end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree.ProbeAnnularTensorWeights
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem tensor_ne_zero_of_coordinates (c : AnnularCoordinates F S)
    (hr : ∀ v, c.fReal v ≠ 0) (hc : ∀ v, c.fComplex v ≠ 0)
    (hf : ∀ v, c.fFinite v ≠ 0) : tensor F S c ≠ 0 := by
  have hreal : ∀ v, ∃ x, c.fReal v x ≠ 0 := by
    intro v
    by_contra h
    exact hr v (funext (by simpa using not_exists.mp h))
  have hcomplex : ∀ v, ∃ x, c.fComplex v x ≠ 0 := by
    intro v
    by_contra h
    exact hc v (funext (by simpa using not_exists.mp h))
  have hfinite : ∀ v, ∃ x, c.fFinite v x ≠ 0 := by
    intro v
    by_contra h
    exact hf v (funext (by simpa using not_exists.mp h))
  choose xr hxr using hreal
  choose xc hxc using hcomplex
  choose xf hxf using hfinite
  let x : SLocalProduct F S :=
    ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (xr, xc), xf⟩
  have hx : tensor F S c x ≠ 0 := by
    simp only [tensor, x, RingEquiv.apply_symm_apply]
    exact mul_ne_zero
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun v _ => hxr v))
        (Finset.prod_ne_zero_iff.mpr (fun v _ => hxc v)))
      (Finset.prod_ne_zero_iff.mpr (fun v _ => hxf v))
  intro h
  exact hx (congrFun h x)

theorem exists_coordinates_from_complex_profile (A : SArithmeticData F)
    (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    (hmoment : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0)
    (φ : (v : ↥A.Sf) → v.val.adicCompletion F → ℂ)
    (hφ : ∀ v, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v) ∧
      (0 : v.val.adicCompletion F) ∉ tsupport (φ v))
    (hφnz : ∀ v, φ v ≠ 0) :
    ∃ (c : AnnularCoordinates F A.Sf)
      (vc : {v : InfinitePlace F // v.IsComplex}),
      c.fComplex vc = f ∧ tensor F A.Sf c ≠ 0 := by
  classical
  have h0 : (0 : ℂ) ∉ tsupport f := by
    obtain ⟨a, b, ha, _, hs⟩ := hf.2.2
    intro h
    have hh := (hs h).1
    simp only [norm_zero] at hh
    linarith
  haveI : Nonempty {v : InfinitePlace F // v.IsComplex} := arithmetic_complex_place F A
  haveI : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.1)) v.2⟩
  let c : AnnularCoordinates F A.Sf := {
    fReal := fun _ _ => 0
    fComplex := fun _ => f
    fFinite := φ
    real_regular := fun v => isEmptyElim v
    complex_regular := fun _ => ⟨hf.1, hf.2.1, h0, hrad⟩
    finite_regular := hφ }
  have hc : c.fComplex (Classical.arbitrary {v : InfinitePlace F // v.IsComplex}) = f := rfl
  refine ⟨c, Classical.arbitrary _, hc, ?_⟩
  apply tensor_ne_zero_of_coordinates F A.Sf c
  · intro v; exact isEmptyElim v
  · intro v; exact complex_profile_ne_zero f hmoment
  · intro v; exact hφnz v

def finiteAnnularProfile (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : ℂ :=
  if x - 1 ∈ finiteCompletionBall F v 1 then 1 else 0

theorem finiteAnnularProfile_regular (v : HeightOneSpectrum (𝓞 F)) :
    IsLocallyConstant (finiteAnnularProfile F v) ∧
    HasCompactSupport (finiteAnnularProfile F v) ∧
    (0 : v.adicCompletion F) ∉ tsupport (finiteAnnularProfile F v) := by
  let U : Set (v.adicCompletion F) := {x | x - 1 ∈ finiteCompletionBall F v 1}
  have hc : IsCompact U := isCompact_finiteCompletionBall_coset F v 1 1
  have ho : IsOpen U := isOpen_finiteCompletionBall_coset F v 1 1
  have hl : IsLocallyConstant (finiteAnnularProfile F v) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp [finiteAnnularProfile, show y - 1 ∈ finiteCompletionBall F v 1 from hy,
        show x - 1 ∈ finiteCompletionBall F v 1 from hx]
    · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [finiteAnnularProfile, show y - 1 ∉ finiteCompletionBall F v 1 from hy,
        show x - 1 ∉ finiteCompletionBall F v 1 from hx]
  have hs : tsupport (finiteAnnularProfile F v) ⊆ U := by
    apply closure_minimal _ hc.isClosed
    intro x hx
    by_contra h
    exact hx (by simp [finiteAnnularProfile, show x - 1 ∉ finiteCompletionBall F v 1 from h])
  refine ⟨hl, hc.of_isClosed_subset (isClosed_tsupport _) hs, ?_⟩
  intro hz
  have h := hs hz
  change Valued.v ((0 : v.adicCompletion F) - 1) ≤ WithZero.exp (-(1 : ℤ)) at h
  norm_num at h

theorem finiteAnnularProfile_ne_zero (v : HeightOneSpectrum (𝓞 F)) :
    finiteAnnularProfile F v ≠ 0 := by
  intro h
  have hh := congrFun h 1
  simpa [finiteAnnularProfile] using hh

theorem exists_annular_tensor_from_complex_profile (A : SArithmeticData F)
    (f : ℂ → ℂ) (hf : IsComplexAnnular f)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → f z = f w)
    (hmoment : complexNormMellin (complexTraceFourier f) (1 / 6 : ℝ) ≠ 0) :
    ∃ (c : AnnularCoordinates F A.Sf)
      (vc : {v : InfinitePlace F // v.IsComplex}),
      c.fComplex vc = f ∧ tensor F A.Sf c ≠ 0 := by
  exact exists_coordinates_from_complex_profile F A f hf hrad hmoment
    (fun v => finiteAnnularProfile F v.val)
    (fun v => finiteAnnularProfile_regular F v.val)
    (fun v => finiteAnnularProfile_ne_zero F v.val)

theorem fourierMellin_smul_measures
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F S) (borel _))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (W : SLocalProduct F S → ℂ) (z : ℂ) (a b : ENNReal) :
    fourierMellin F S e (a • μ) (b • ν) W z =
      (b.toReal * a.toReal) • fourierMellin F S e μ ν W z := by
  simp only [fourierMellin, integral_smul_measure]
  simp_rw [smul_mul_assoc]
  rw [integral_smul]
  rw [smul_smul]

theorem fourierMellin_smul_measures_ne_zero_iff
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F S) (borel _))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (W : SLocalProduct F S → ℂ) (z : ℂ) (a b : ENNReal)
    (ha : a ≠ 0) (hat : a ≠ ⊤) (hb : b ≠ 0) (hbt : b ≠ ⊤) :
    fourierMellin F S e (a • μ) (b • ν) W z ≠ 0 ↔
      fourierMellin F S e μ ν W z ≠ 0 := by
  rw [fourierMellin_smul_measures]
  exact smul_ne_zero_iff_right (mul_ne_zero
    (ENNReal.toReal_ne_zero.mpr ⟨hb, hbt⟩) (ENNReal.toReal_ne_zero.mpr ⟨ha, hat⟩))

end
end DedekindZetaZeroFree.ProbeAnnularTensorWeights

end
