module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogDensityWeakDerivatives

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeSheetVerticalDecay
noncomputable section
open MeasureTheory

theorem uniform_oscillatory_integral_rapid_decay
    {P : Type*} (s : Set P) (p : P → ℝ → ℂ)
    (hsmooth : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (p i))
    (hintegrable : ∀ i ∈ s, ∀ n : ℕ, Integrable (iteratedDeriv n (p i)))
    (hbound : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ i ∈ s,
      (∫ t : ℝ, ‖iteratedDeriv n (p i) t‖) ≤ D)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ τ : ℝ,
      ‖∫ t : ℝ, p i t * Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ))‖ ≤
        C * (1 + |τ|) ^ (-B) := by
  obtain ⟨n, hn⟩ := exists_nat_ge B
  obtain ⟨D₀, hD₀, h₀⟩ := hbound 0
  obtain ⟨Dₙ, hDₙ, hₙ⟩ := hbound n
  refine ⟨2 ^ n * (D₀ + Dₙ), by positivity, ?_⟩
  intro i hi τ
  let w : ℝ := -τ / (2 * Real.pi)
  let F : ℂ := FourierTransform.fourier (p i) w
  have heq : F = ∫ t : ℝ, p i t *
      Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ)) := by
    rw [show F = FourierTransform.fourier (p i) w from rfl,
      Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext t
    rw [smul_eq_mul, mul_comm]
    congr 1
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    dsimp [w]
    push_cast
    field_simp
    <;> ring
  have hzero : ‖F‖ ≤ D₀ := by
    calc
      ‖F‖ ≤ ∫ t : ℝ, ‖p i t‖ := by
        rw [heq]
        apply (norm_integral_le_integral_norm _).trans
        apply le_of_eq
        congr 1
        funext t
        simp [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
      _ ≤ D₀ := by simpa using h₀ i hi
  have hderiv := congrFun (Real.fourier_iteratedDeriv (hsmooth i hi)
    (fun k _ => hintegrable i hi k) (n := n) (by simp)) w
  have hweight : |τ| ^ n * ‖F‖ ≤ Dₙ := by
    have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * (w : ℂ))‖ = |τ| := by
      have hid : 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) =
          -Complex.I * (τ : ℂ) := by
        have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        dsimp [w]
        push_cast
        field_simp
        <;> ring
      rw [hid]
      simp [norm_mul]
    calc
      |τ| ^ n * ‖F‖ = ‖FourierTransform.fourier (iteratedDeriv n (p i)) w‖ := by
        rw [hderiv, norm_smul, norm_pow, hnorm]
      _ ≤ ∫ t : ℝ, ‖iteratedDeriv n (p i) t‖ := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        apply (norm_integral_le_integral_norm _).trans
        apply le_of_eq
        congr 1
        funext t
        simp [norm_smul, Complex.norm_exp, Complex.mul_re]
      _ ≤ Dₙ := hₙ i hi
  have hpoly : (1 + |τ|) ^ n * ‖F‖ ≤ 2 ^ n * (D₀ + Dₙ) := by
    by_cases ht : |τ| ≤ 1
    · calc
        (1 + |τ|) ^ n * ‖F‖ ≤ 2 ^ n * ‖F‖ := by
          gcongr
          linarith
        _ ≤ 2 ^ n * (D₀ + Dₙ) := by gcongr; linarith
    · have ht' : 1 ≤ |τ| := le_of_lt (lt_of_not_ge ht)
      calc
        (1 + |τ|) ^ n * ‖F‖ ≤ (2 * |τ|) ^ n * ‖F‖ := by
          gcongr
          linarith
        _ = 2 ^ n * (|τ| ^ n * ‖F‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ n * (D₀ + Dₙ) := by gcongr; linarith
  have hpos : 0 < 1 + |τ| := by positivity
  have hnat : ‖F‖ ≤ (2 ^ n * (D₀ + Dₙ)) * (1 + |τ|) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos hpos n)).2 (by simpa [mul_comm] using hpoly)
  rw [← heq]
  apply hnat.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by linarith)

end
end DedekindZetaZeroFree.ProbeSheetVerticalDecay

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

private theorem probeModulus_pos
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : (SLocalProduct F S)ˣ) :
    0 < ProbeWeight.modulus F S y := by
  obtain ⟨ha, hb⟩ := Prod.isUnit_iff.mp y.isUnit
  unfold ProbeWeight.modulus
  apply mul_pos
  · apply Finset.prod_pos
    intro v _
    exact pow_pos (norm_pos_iff.mpr (isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp ha v))) _
  · apply Finset.prod_pos
    intro v _
    exact norm_pos_iff.mpr (isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp hb v))

private theorem modulus_cpow_split
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : (SLocalProduct F S)ˣ)
    (σ τ : ℝ) :
    (ProbeWeight.modulus F S y : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I) =
      (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ) *
        Complex.exp (Complex.I * (τ : ℂ) * (Real.log (ProbeWeight.modulus F S y) : ℂ)) := by
  have hpos := probeModulus_pos S y
  have hne : (ProbeWeight.modulus F S y : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hτ : (ProbeWeight.modulus F S y : ℂ) ^ ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (τ : ℂ) * (Real.log (ProbeWeight.modulus F S y) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hne, (Complex.ofReal_log hpos.le).symm]
    congr 1
    ring
  rw [Complex.cpow_add (σ : ℂ) ((τ : ℂ) * Complex.I) hne, hτ]

theorem log_disintegration_fourier_identity
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (h : SLocalProduct F S → ℂ) (a b : ℝ)
    (p : ℝ → ℝ → ℂ) (hp : IsLogMellinDensity S ν h a b p) :
    ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      (∫ y : (SLocalProduct F S)ˣ, h y.val *
        (ProbeWeight.modulus F S y : ℂ) ^
          ((σ : ℂ) + (τ : ℂ) * Complex.I) ∂ν) =
      ∫ t : ℝ, p σ t * Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ)) := by
  intro σ hσ τ
  have hcont : Continuous (fun t : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ))) := by
    fun_prop
  have hbdd : ∃ C : ℝ, ∀ t : ℝ, ‖Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ))‖ ≤ C := by
    refine ⟨1, fun t => ?_⟩
    rw [Complex.norm_exp]
    have hre : (Complex.I * (τ : ℂ) * (t : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hkey := hp.2.2 σ hσ
    (fun t : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ))) hcont hbdd
  rw [← hkey]
  apply integral_congr_ae
  filter_upwards with y
  rw [modulus_cpow_split S y σ τ]
  ring

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open MeasureTheory

theorem derivative_envelopes_uniform_L1
    (p : ℝ → ℝ → ℂ) (K : Set ℝ)
    (hp : ∀ σ ∈ K, ContDiff ℝ (⊤ : ℕ∞) (p σ))
    (hM : ∀ n : ℕ, ∃ M : ℝ → ℝ,
      Integrable M ∧ (∀ t, 0 ≤ M t) ∧
      ∀ σ ∈ K, ∀ t, ‖iteratedDeriv n (p σ) t‖ ≤ M t) :
    (∀ σ ∈ K, ∀ n : ℕ, Integrable (iteratedDeriv n (p σ))) ∧
    (∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ σ ∈ K,
      (∫ t : ℝ, ‖iteratedDeriv n (p σ) t‖) ≤ D) := by
  have hI : ∀ σ ∈ K, ∀ n : ℕ, Integrable (iteratedDeriv n (p σ)) := by
    intro σ hσ n
    obtain ⟨M, hMint, hMpos, hbound⟩ := hM n
    apply hMint.mono ((hp σ hσ).continuous_iteratedDeriv n (by simp)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hMpos t)] using hbound σ hσ t
  refine ⟨hI, ?_⟩
  intro n
  obtain ⟨M, hMint, hMpos, hbound⟩ := hM n
  refine ⟨∫ t : ℝ, M t, integral_nonneg hMpos, ?_⟩
  intro σ hσ
  exact integral_mono (hI σ hσ n).norm hMint (hbound σ hσ)

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open MeasureTheory

private theorem verticalStrip_complexExpWeight_iteratedDeriv (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (Real.exp (c * t) : ℂ)) =
      fun t => (c : ℂ) ^ n * (Real.exp (c * t) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd := (((hasDerivAt_id t).const_mul c).exp.ofReal_comp).const_mul
      ((c : ℂ) ^ n)
    convert hd.deriv using 1 <;>
      simp only [pow_succ, Complex.ofReal_mul, id_eq, mul_one] <;> ring

private theorem verticalStrip_nonpositiveExpWeight_derivative_bound
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c D : ℝ) (hD : |c| ≤ D) (n : ℕ) (t : ℝ) (ht : c * t ≤ 0) :
    ‖iteratedDeriv n (fun t => (Real.exp (c * t) : ℂ) * f t) t‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * D ^ i *
        ‖iteratedDeriv (n - i) f t‖ := by
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (Real.exp (c * t) : ℂ)) := by
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (c * t)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp he
  rw [iteratedDeriv_fun_mul (hw.of_le (by simp)).contDiffAt
    (hf.of_le (by simp)).contDiffAt]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [verticalStrip_complexExpWeight_iteratedDeriv]
  simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (c * t) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr ht
  have hpow : |c| ^ i ≤ D ^ i := pow_le_pow_left₀ (abs_nonneg c) hD i
  calc
    (n.choose i : ℝ) * (|c| ^ i * Real.exp (c * t)) *
        ‖iteratedDeriv (n - i) f t‖ ≤
      (n.choose i : ℝ) * (D ^ i * 1) * ‖iteratedDeriv (n - i) f t‖ := by
        have hD0 : 0 ≤ D := (abs_nonneg c).trans hD
        gcongr
    _ = _ := by ring

theorem exponential_family_derivative_envelope
    (a b : ℝ) (hab : a ≤ b) (p : ℝ → ℝ → ℂ) (n : ℕ)
    (hp : ∀ σ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (p σ))
    (hshift : ∀ σ ∈ Set.Icc a b, ∀ τ ∈ Set.Icc a b,
      p σ = fun t => (Real.exp ((σ - τ) * t) : ℂ) * p τ t)
    (ha : ∀ k ≤ n, Integrable (iteratedDeriv k (p a)))
    (hb : ∀ k ≤ n, Integrable (iteratedDeriv k (p b))) :
    ∃ M : ℝ → ℝ, Integrable M ∧ (∀ t, 0 ≤ M t) ∧
      ∀ σ ∈ Set.Icc a b, ∀ t, ‖iteratedDeriv n (p σ) t‖ ≤ M t := by
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  let C : ℕ → ℝ := fun i => (n.choose i : ℝ) * (b - a) ^ i
  let M : ℝ → ℝ := fun t => ∑ i ∈ Finset.range (n + 1), C i *
    (‖iteratedDeriv (n - i) (p a) t‖ + ‖iteratedDeriv (n - i) (p b) t‖)
  have hC (i : ℕ) : 0 ≤ C i :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hab) i)
  refine ⟨M, ?_, ?_, ?_⟩
  · exact integrable_finset_sum _ fun i hi =>
      ((ha (n - i) (Nat.sub_le _ _)).norm.add
        (hb (n - i) (Nat.sub_le _ _)).norm).const_mul (C i)
  · intro t
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hC i) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro σ hσ t
    by_cases ht : t ≤ 0
    · rw [hshift σ hσ a ha_mem]
      have hD : |σ - a| ≤ b - a := by
        rw [abs_of_nonneg (sub_nonneg.mpr hσ.1)]; linarith [hσ.2]
      apply (verticalStrip_nonpositiveExpWeight_derivative_bound (p a) (hp a ha_mem) (σ - a) (b - a)
        hD n t (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hσ.1) ht)).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (hC i)
    · rw [hshift σ hσ b hb_mem]
      have hD : |σ - b| ≤ b - a := by
        rw [abs_of_nonpos (sub_nonpos.mpr hσ.2)]; linarith [hσ.1]
      apply (verticalStrip_nonpositiveExpWeight_derivative_bound (p b) (hp b hb_mem) (σ - b) (b - a)
        hD n t (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hσ.2)
          (le_of_not_ge ht))).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (hC i)

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512
private lemma modulus_positive {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : (SLocalProduct F S)ˣ) :
    0 < ProbeWeight.modulus F S y := by
  apply mul_pos
  · apply Finset.prod_pos
    intro v _
    exact pow_pos (Units.norm_pos (Units.map
      ((Pi.evalMonoidHom (fun v : InfinitePlace F => v.Completion) v).comp
        (MonoidHom.fst _ _)) y)) _
  · apply Finset.prod_pos
    intro v _
    have hz : y.val.2 v ≠ 0 := by
      intro hz
      have he := congrArg (fun x : SLocalProduct F S => x.2 v) y.val_inv
      change y.val.2 v * y.inv.2 v = 1 at he
      rw [hz, zero_mul] at he
      exact zero_ne_one he
    exact norm_pos_iff.mpr hz

private lemma weight_shift (r σ τ : ℝ) (hr : 0 < r) :
    (r : ℂ) ^ (σ : ℂ) * (Real.exp ((τ - σ) * Real.log r) : ℂ) =
      (r : ℂ) ^ (τ : ℂ) := by
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_mul, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem logMellinDensity_parameter_shift
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (h : SLocalProduct F S → ℂ) (a b : ℝ)
    (p : ℝ → ℝ → ℂ) (hp : IsLogMellinDensity S ν h a b p)
    (σ τ : ℝ) (hσ : σ ∈ Set.Icc a b) (hτ : τ ∈ Set.Icc a b) :
    p τ = fun t => (Real.exp ((τ - σ) * t) : ℂ) * p σ t := by
  have hw : Continuous (fun t : ℝ => (Real.exp ((τ - σ) * t) : ℂ)) := by fun_prop
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) _
    (hp.1 τ hτ).continuous (hw.mul (hp.1 σ hσ).continuous)
  apply ae_eq_of_integral_contDiff_smul_eq (hp.2.1 τ hτ).locallyIntegrable
    (hw.mul (hp.1 σ hσ).continuous).locallyIntegrable
  intro g hg hgc
  have hc : Continuous (fun t => (g t : ℂ)) := Complex.continuous_ofReal.comp hg.continuous
  have hgcC : HasCompactSupport (fun t => (g t : ℂ)) := by
    exact hgc.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have hcb : ∃ C : ℝ, ∀ t, ‖(g t : ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real] using hgc.exists_bound_of_continuous hg.continuous
  have htestc : Continuous (fun t => (Real.exp ((τ - σ) * t) : ℂ) * (g t : ℂ)) :=
    hw.mul hc
  have htestb : ∃ C : ℝ, ∀ t, ‖(Real.exp ((τ - σ) * t) : ℂ) * (g t : ℂ)‖ ≤ C :=
    (hgcC.mul_left).exists_bound_of_continuous htestc
  have ht := hp.2.2 τ hτ (fun t => (g t : ℂ)) hc hcb
  have hs := hp.2.2 σ hσ
    (fun t => (Real.exp ((τ - σ) * t) : ℂ) * (g t : ℂ)) htestc htestb
  have he : (∫ y : (SLocalProduct F S)ˣ,
      (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (τ : ℂ)) *
        (g (Real.log (ProbeWeight.modulus F S y)) : ℂ) ∂ν) =
    ∫ y : (SLocalProduct F S)ˣ,
      (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
        ((Real.exp ((τ - σ) * Real.log (ProbeWeight.modulus F S y)) : ℂ) *
          (g (Real.log (ProbeWeight.modulus F S y)) : ℂ)) ∂ν := by
    apply integral_congr_ae
    filter_upwards with y
    rw [← weight_shift _ σ τ (modulus_positive S y)]
    ring
  rw [ht, hs] at he
  simpa only [Complex.real_smul, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using he

theorem schwartzTensor_log_density_derivative_envelopes
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (p : ℝ → ℝ → ℂ) (hp : IsLogMellinDensity S ν h a b p) :
    ∀ n : ℕ, ∃ M : ℝ → ℝ,
      Integrable M ∧ (∀ t, 0 ≤ M t) ∧
      ∀ σ ∈ Set.Icc a b, ∀ t, ‖iteratedDeriv n (p σ) t‖ ≤ M t := by
  intro n
  apply exponential_family_derivative_envelope a b hab p n hp.1
  · intro σ hσ τ hτ
    exact logMellinDensity_parameter_shift S ν h a b p hp τ σ hτ hσ
  · intro k _
    exact schwartzTensor_log_density_iteratedDeriv_integrable S ν hν h hh
      a b p hp a ⟨le_rfl, hab⟩ ha k
  · intro k _
    exact schwartzTensor_log_density_iteratedDeriv_integrable S ν hν h hh
      a b p hp b ⟨hab, le_rfl⟩ (lt_of_lt_of_le ha hab) k

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetVerticalDecay
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

theorem schwartzTensor_log_mellin_density
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ) (hh : IsSchwartzTensor F S h)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ p : ℝ → ℝ → ℂ,
      (∀ σ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (p σ)) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n : ℕ, Integrable (iteratedDeriv n (p σ))) ∧
      (∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ σ ∈ Set.Icc a b,
        (∫ t : ℝ, ‖iteratedDeriv n (p σ) t‖) ≤ D) ∧
      (∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
        (∫ y : (SLocalProduct F S)ˣ, h y.val *
          (ProbeWeight.modulus F S y : ℂ) ^
            ((σ : ℂ) + (τ : ℂ) * Complex.I) ∂ν) =
        ∫ t : ℝ, p σ t * Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ))) := by
  obtain ⟨p, hp⟩ :=
    ProbeSheetLogDensity.schwartzTensor_smooth_log_disintegration
      S ν hν h hh a b ha hab
  have hM := ProbeSheetLogDensity.schwartzTensor_log_density_derivative_envelopes
    S ν hν h hh a b ha hab p hp
  obtain ⟨hint, hbound⟩ :=
    ProbeSheetLogDensity.derivative_envelopes_uniform_L1 p (Set.Icc a b) hp.1 hM
  exact ⟨p, hp.1, hint, hbound,
    ProbeSheetLogDensity.log_disintegration_fourier_identity S ν h a b p hp⟩

end
end DedekindZetaZeroFree.ProbeSheetVerticalDecay

end

section
namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

theorem fourier_mellin_rapid_on_strip
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖ProbeWeight.fourierMellin F A.Sf e μ ν W0
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B) := by
  have hfourier := ProbeSheetVerticalDecay.fourier_isSchwartzTensor
    A.Sf e he hne μ hμ W0 hW0 hcompact
  obtain ⟨p, hsmooth, hintegrable, hbound, hidentity⟩ :=
    ProbeSheetVerticalDecay.schwartzTensor_log_mellin_density A.Sf ν hν
      (ProbeWeight.fourier F A.Sf e μ W0) hfourier a b ha hab
  obtain ⟨C, hC, hdecay⟩ :=
    ProbeSheetVerticalDecay.uniform_oscillatory_integral_rapid_decay
      (Set.Icc a b) p hsmooth hintegrable hbound B hB
  refine ⟨C, hC, ?_⟩
  intro σ hσ τ
  rw [ProbeWeight.fourierMellin, hidentity σ hσ τ]
  exact hdecay σ hσ τ

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds

end
