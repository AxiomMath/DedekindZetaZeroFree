module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ChamberIntegrals.FiniteVectorFubini

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology BigOperators ENNReal
open MeasureTheory Filter ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor

open _root_.DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant renaming planarEnvelope_volume_integral → planarEnvelope_volume_integral
open _root_.DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant renaming ratio_wn → ratio_wn

private theorem actual_arch_trace_spherical_real_integral (t : ℝ)
    (ht : -(1 / 6 : ℝ) < t) :
    (∫ x : ℂ, KPComplexIntertwinerParameterMajorant.forwardSection (t : ℂ)
      KPComplexStandardIntertwinerGerm.compactSpherical
        (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1)
      ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea)) =
        2 * (Real.pi : ℂ) / ((1 / 3 : ℂ) + 2 * (t : ℂ)) := by
  have he (x : ℂ) : KPComplexIntertwinerParameterMajorant.forwardSection (t : ℂ)
      KPComplexStandardIntertwinerGerm.compactSpherical
        (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1) =
      (KPComplexIntertwinerParameterMajorant.planarEnvelope ((4 / 3 : ℝ) + 2*t) x : ℂ) := by
    simp only [mul_one, KPComplexIntertwinerParameterMajorant.forwardSection,
      KPComplexStandardIntertwinerGerm.compactSpherical, mul_one, ratio_wn,
      KPComplexIntertwinerParameterMajorant.planarEnvelope, Real.log_inv,
      Complex.ofReal_neg]
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by positivity), Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_smul_measure]
  change (2 : ℝ) • (∫ x : ℂ,
    (KPComplexIntertwinerParameterMajorant.planarEnvelope ((4 / 3 : ℝ) + 2*t) x : ℂ)) = _
  rw [integral_complex_ofReal, planarEnvelope_volume_integral _ (by linarith)]
  push_cast
  simp only [Complex.real_smul]
  rw [show (4 / 3 : ℂ) + 2 * (t : ℂ) - 1 = (1 / 3 : ℂ) + 2 * (t : ℂ) by ring]
  push_cast
  ring

private theorem actual_arch_trace_integral_eq_character (s : ℂ) :
    (∫ x : ℂ, KPComplexIntertwinerParameterMajorant.forwardSection s
      KPComplexStandardIntertwinerGerm.compactSpherical
        (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1)
      ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea)) =
      (4 * Real.pi : ℂ) * KPComplexStandardIntertwinerGerm.haarIntegral 1 s
        KPComplexStandardIntertwinerGerm.compactSpherical 1 := by
  unfold KPComplexStandardIntertwinerGerm.haarIntegral KPCplxCharacterHaar.characterHaar
  rw [integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (div_pos (KPCplxCharacterHaar.characterScale_pos 1) (by positivity)).le]
  have hscale : KPCplxCharacterHaar.characterScale (1 : ℂˣ) = 1 := by
    simp [KPCplxCharacterHaar.characterScale]
  rw [hscale]
  norm_num only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul]
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp
  ring

 theorem actual_arch_trace_spherical_parameter_integral (s : ℂ)
    (hs : s ∈ KPComplexStandardIntertwinerGerm.halfPlane) :
    (∫ x : ℂ, KPComplexIntertwinerParameterMajorant.forwardSection s
      KPComplexStandardIntertwinerGerm.compactSpherical
        (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1)
      ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea)) =
        2 * (Real.pi : ℂ) / ((1 / 3 : ℂ) + 2 * s) := by
  let f : ℂ → ℂ := fun z => (4 * Real.pi : ℂ) *
    KPComplexStandardIntertwinerGerm.haarIntegral 1 z KPComplexStandardIntertwinerGerm.compactSpherical 1
  let g : ℂ → ℂ := fun z => 2 * (Real.pi : ℂ) / ((1 / 3 : ℂ) + 2 * z)
  have hf : AnalyticOnNhd ℂ f KPComplexStandardIntertwinerGerm.halfPlane :=
    ((differentiableOn_const _).mul
      (KPComplexStandardIntertwinerGerm.haarIntegral_holomorphic 1
        KPComplexStandardIntertwinerGerm.compactSpherical 1)).analyticOnNhd
      KPComplexStandardIntertwinerGerm.halfPlane_open_connected.1
  have hg : AnalyticOnNhd ℂ g KPComplexStandardIntertwinerGerm.halfPlane := by
    intro z hz
    have hn : (1 / 3 : ℂ) + 2 * z ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [Complex.add_re, Complex.mul_re, Complex.zero_re] at hr
      change -(1 / 6 : ℝ) < z.re at hz
      norm_num at hr
      linarith
    exact analyticAt_const.div (by fun_prop) hn
  let u : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1)
  have hu : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall ?_⟩
    intro n
    exact one_div_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  have he : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    apply hu.frequently
    apply (Filter.Eventually.of_forall ?_).frequently
    intro n
    have ht : -(1 / 6 : ℝ) < 1 / ((n : ℝ) + 1) :=
      lt_trans (by norm_num) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    have hr := actual_arch_trace_spherical_real_integral (1 / ((n : ℝ) + 1)) ht
    rw [actual_arch_trace_integral_eq_character] at hr
    simpa [f,g,u] using hr
  rw [actual_arch_trace_integral_eq_character]
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    KPComplexStandardIntertwinerGerm.halfPlane_open_connected.2.isPreconnected
    (by norm_num [KPComplexStandardIntertwinerGerm.halfPlane]) he hs

open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPRankOneShellRepair KPRankOneShellContinuation

def rationalChamberIntegrand
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C₀.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val)
      (C₀.canonical q.val).iwasawa .plus)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (s : ℂ)
    (x : ∀ q : E, LocalField F q.val) : ℂ :=
  rationalStageEval F ζ hζ P₀ C₀ E hE t
    (fun q => ((compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val)
      (C₀.canonical q.val).iwasawa .plus s (φ q)).val
      ((C₀.canonical q.val).borel.liftedW⁻¹ * (C₀.canonical q.val).borel.upperRoot
        (Multiplicative.ofAdd (x q)) * 1)))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor

end
