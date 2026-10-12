module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.ReflectedTransformHolomorphy
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.MellinConverseAxisInversion
public import DedekindZetaZeroFree.Nonvanishing.Mellin.HolomorphicZeroTransfer
public import DedekindZetaZeroFree.Moments.Probes.MellinGrowth
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ShiftedKernelFlatness
public import DedekindZetaZeroFree.Nonvanishing.Mellin.TripleMellinInitialEstimates
public import DedekindZetaZeroFree.LFunctions.Hecke.FiniteEulerFactorNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
open MeasureTheory Filter Asymptotics

theorem fixed_probe_assembly
    (I f : ℝ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hI : ∀ ε : ℝ, 0 < ε → I =O[atTop] (fun x : ℝ => x ^ (933 / 2000 + ε : ℝ)))
    (hcomparison : (fun x : ℝ => I x - c * f x) =O[atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500)))
    (L N G : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | (5999 / 6000 : ℝ) < s.re ∧ s ≠ 1})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | (5999 / 6000 : ℝ) < s.re ∧ s ≠ 1})
    (hN_ne : ∀ s ∈ {s : ℂ | (5999 / 6000 : ℝ) < s.re ∧ s ≠ 1}, N s ≠ 0)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 < s.re})
    (hdecay : ∀ a b : ℝ, 1 < a → a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ Set.Icc a b, ∀ t : ℝ, ‖G ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2))
    (hinv : ∀ x : ℝ, 0 < x → ((x ^ (8 / 15 : ℝ) : ℝ) : ℂ) * f x =
      mellinInv (-2) (fun z : ℂ => G (-z)) x)
    (hquotient : ∀ s : ℂ, 1 < s.re → G s = N s / L s)
    (hL_right : ∀ s : ℂ, 1 < s.re → L s ≠ 0) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 → L s ≠ 0 := by
  let g : ℝ → ℂ := fun x => ((x ^ (8 / 15 : ℝ) : ℝ) : ℂ) * f x
  have htop : ∀ ε : ℝ, 0 < ε → g =O[atTop]
      (fun x : ℝ => x ^ (5999 / 6000 + ε : ℝ)) :=
    (mellin_probe_growth I f c hc hI hcomparison).2
  obtain ⟨hg_cont, hg_local, hg_zero, -⟩ := mellin_right_shift_flat G g hG hdecay hinv
  have hT := mellin_arbitrary_epsilon_holomorphic g (5999 / 6000) hg_local htop hg_zero
  have hg_mellin : MellinConvergent g (-(2 : ℂ)) :=
    mellin_arbitrary_epsilon_convergent g (5999 / 6000) hg_local htop hg_zero 2 (by norm_num)
  have hG_cont : Continuous (fun t : ℝ => G ((2 : ℂ) + t * Complex.I)) := by
    apply hG.continuousOn.comp_continuous
    · fun_prop
    · intro t; simp
  obtain ⟨C, -, hb⟩ := hdecay 2 2 (by norm_num) le_rfl
  have hG_int : Integrable (fun t : ℝ => G ((2 : ℂ) + t * Complex.I)) := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hG_cont.aestronglyMeasurable ?_
    filter_upwards [] with t
    simpa [div_eq_mul_inv] using hb 2 ⟨le_rfl, le_rfl⟩ t
  have haxis := mellin_converse_axis_inversion 2 g G (by norm_num) hg_cont hg_mellin
    hG_int hG_cont hinv
  have hprod : ∀ t : ℝ, L ((2 : ℂ) + t * Complex.I) *
      mellin g (-((2 : ℂ) + t * Complex.I)) = N ((2 : ℂ) + t * Complex.I) := by
    intro t
    have ht : 1 < ((2 : ℂ) + t * Complex.I).re := by simp
    have haxis_t : mellin g (-((2 : ℂ) + t * Complex.I)) =
        G ((2 : ℂ) + t * Complex.I) := by simpa using haxis t
    rw [haxis_t, hquotient _ ht]
    exact mul_div_cancel₀ _ (hL_right _ ht)
  have hzero := mellin_holomorphic_zero_transfer (5999 / 6000) (by norm_num)
    L (fun s => mellin g (-s)) N hL (hT.mono (fun s hs => hs.1)) hN hprod hN_ne
  intro s hs hs1
  exact hzero s ⟨hs, hs1⟩

theorem inverse_formula
    (F : Type) [Field F] [NumberField F] (S : SArithmeticData F)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η) (Hη : ℂ → ℂ)
    (x : ℝ) (hx : 0 < x) :
    ((x ^ (8 / 15 : ℝ) : ℝ) : ℂ) * comparisonPrincipalSpectralTransform F S η hη P Hη x =
      mellinInv (-2) (fun z : ℂ => Complex.exp ((-z - 5 / 6) ^ 2) * Hη (-z) /
        comparisonPrincipalIncompleteL F S η hη P (-z)) x := by
  have hpow (s : ℂ) : ((x ^ (8 / 15 : ℝ) : ℝ) : ℂ) *
      comparisonRealPower x (comparisonC s) = (x : ℂ) ^ s := by
    rw [Complex.ofReal_cpow hx.le]
    unfold comparisonRealPower comparisonC
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.ofReal_log hx.le, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hreflect (t : ℝ) : -((-2 : ℂ) + (t : ℂ) * Complex.I) =
      (2 : ℂ) + (-t : ℝ) * Complex.I := by push_cast; ring
  unfold comparisonPrincipalSpectralTransform comparisonVerticalIntegral mellinInv
  simp only [Complex.real_smul, smul_eq_mul]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_ofNat]
  simp_rw [hreflect]
  rw [integral_neg_eq_self (fun t : ℝ =>
    (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) *
      (Complex.exp (((2 : ℂ) + t * Complex.I - 5 / 6) ^ 2) *
        Hη ((2 : ℂ) + t * Complex.I) /
        comparisonPrincipalIncompleteL F S η hη P ((2 : ℂ) + t * Complex.I))) volume]
  rw [mul_left_comm, ← integral_const_mul]
  have hcoeff : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (2 * (Real.pi : ℂ))⁻¹ := by push_cast; simp only [one_div]
  rw [hcoeff]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← hpow]
  ring

theorem recipe_zero_free_of_moment
    {F : Type} [Field F] [NumberField F] {S : SArithmeticData F}
    {η : RayClassCharacter F S.modulus} (R : PrincipalMellin.ActualRecipe S η)
    (hmoment : PoissonProbe.BalancedReflectedMomentConclusion R.A R.probe.coefficients) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 → R.L s ≠ 0 := by
  have hgrowth : ∀ ε : ℝ, 0 < ε → R.I =O[atTop]
      (fun x : ℝ => x ^ (933 / 2000 + ε : ℝ)) := by
    intro ε hε
    obtain ⟨C, _, hbound⟩ := PoissonProbe.principal_reflected_exponent_bound_of_moment
      R.A R.σ R.target R.traceBad R.probe hmoment ε hε
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Z hZ
    change ‖NormalizedProbe.probe R.A R.probe.coefficients R.probe.domain
      R.probe.W0 R.probe.W1 (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] using hbound Z hZ
  obtain ⟨hc, hcomparison⟩ := PrincipalMellin.actual_principal_comparison S η R
  obtain ⟨hN, hNne, hG, hdecay, hright⟩ := PrincipalMellin.actual_principal_spectral_properties S η R
  have hL : AnalyticOnNhd ℂ R.L {s : ℂ | (5999 / 6000 : ℝ) < s.re ∧ s ≠ 1} := by
    apply DifferentiableOn.analyticOnNhd _ (mellin_punctured_halfplane_isOpen (5999 / 6000) (by norm_num))
    unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
    apply (R.continuation.L_holo.mono (fun s hs => ⟨by linarith [hs.1], hs.2⟩)).mul
    apply DifferentiableOn.fun_finset_prod
    intro v hv
    unfold comparisonRealPower
    fun_prop
  exact fixed_probe_assembly R.I R.f R.c hc hgrowth hcomparison R.L R.N R.G hL
    hN hNne hG hdecay (fun x hx => inverse_formula F R.A R.target R.probe.principal R.continuation R.H x hx)
    (fun _ _ => rfl) hright

end DedekindZetaZeroFree.MomentSources
