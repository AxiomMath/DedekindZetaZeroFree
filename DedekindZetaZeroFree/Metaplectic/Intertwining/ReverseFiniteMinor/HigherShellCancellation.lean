module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.LowShellContinuation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.HigherShellTranslationCancellation

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorHigherShell
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPTameJacquetTestDuality
open KPTameTransposeKernelUnfoldingRaw KPTameValuationCoordinates
open KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation
open _root_.DedekindZetaZeroFree.ActualReverseMinorLowShell renaming numerator_family → numerator_family
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actual_test_family_chamber → actual_test_family_chamber
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actual_test_family_zero → actual_test_family_zero
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testDeformation → testDeformation
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testCompact → testCompact
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

private theorem actual_reverse_coordinate_eq_of_chamber_eq
    (f : sectionSpace S.borel P .minus 0)
    (g₁ g₂ : ActualCover F ζ hζ q)
    (heq : ∀ s : ℂ, convergenceHalfPlane .minus s →
      (∫ u : LocalField F q,
        ((testDeformation F ζ hζ q S P f s).val
          (kernelW (LocalField F q) S.borel .minus *
            S.borel.upperRoot (Multiplicative.ofAdd u) * g₁)).val 1 ∂μ) =
      (∫ u : LocalField F q,
        ((testDeformation F ζ hζ q S P f s).val
          (kernelW (LocalField F q) S.borel .minus *
            S.borel.upperRoot (Multiplicative.ofAdd u) * g₂)).val 1 ∂μ)) :
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ f).val g₁).val 1 =
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ f).val g₂).val 1 := by
  obtain ⟨H, _, hH, hspec⟩ := numerator_family F ζ hζ q S P μ hμ f
  have hch : ∀ s, convergenceHalfPlane .minus s → H g₁ s = H g₂ s := by
    intro s hs
    rw [hspec s (denominator_ne_zero_of_convergence (LocalField F q) .minus s hs),
      hspec s (denominator_ne_zero_of_convergence (LocalField F q) .minus s hs),
      actual_test_family_chamber F ζ hζ q S P μ hμ f s hs,
      actual_test_family_chamber F ζ hζ q S P μ hμ f s hs, heq s hs]
  have he : H g₁ 0 = H g₂ 0 := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (fun s _ => (hH g₁).analyticAt s) (fun s _ => (hH g₂).analyticAt s)
      isPreconnected_univ (Set.mem_univ (-1 : ℂ)) _ (Set.mem_univ (0 : ℂ))
    have hn : ∀ᶠ s : ℂ in 𝓝 (-1 : ℂ), s.re < -(1 / 6 : ℝ) :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
    filter_upwards [hn] with s hs
    exact hch s hs
  rw [hspec 0 (denominator_ne_zero_at_zero (LocalField F q) .minus),
    hspec 0 (denominator_ne_zero_at_zero (LocalField F q) .minus),
    actual_test_family_zero F ζ hζ q S P μ hμ,
    actual_test_family_zero F ζ hζ q S P μ hμ] at he
  exact mul_left_cancel₀ (denominator_ne_zero_at_zero (LocalField F q) .minus) he

variable (coordinates : ∀ ε : Sign,
  sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
  (hcoordinates : ∀ ε f g, (coordinates ε f).val g = (f.val g).val 1)

include hcoordinates in

theorem eventual_actual_higher_shell_cancellation
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hconductor : HasConductorIntegers F q ψ)
    (i : Fin 3) (f' : DiagonalValuations) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π f') m f →
      ∀ r : ℕ, 2 ≤ r →
        (∫ x in expandingBall F q π r \ expandingBall F q π (r-1),
          ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
            ((coordinates .minus).symm f)).val
            (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 *
                (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ) = 0 := by
  obtain ⟨t, htball, ht⟩ :=
    KPTameTransposeKernelUnfoldingRaw.HigherShellCancellation.exists_conductor_one_translation
      F q π hπ ψ hconductor
  obtain ⟨M, hM⟩ := deep_diagonal_test_cubic_unit_conjugation
    F ζ hζ q S P hP coordinates hcoordinates htame π f'
  refine ⟨M, ?_⟩
  intro m hm f hf r hr
  apply KPTameTransposeKernelUnfoldingRaw.HigherShellCancellation.integral_zero_of_translation
    F q π hπ μ ψ t htball ht _ r hr
  intro x hx
  apply actual_reverse_coordinate_eq_of_chamber_eq F ζ hζ q S P μ hμ
  intro s hs
  obtain ⟨c, hc, hxt⟩ := high_shell_translation_is_cubic_unit_multiple
    F q htame π hπ r hr x hx t htball
  have hroot (u : LocalField F q) :
      (S.borel.upperRoot (Multiplicative.ofAdd u) : ActualCover F ζ hζ q) =
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u := (S.openCell P).upper_eq u
  simp only [hroot, hxt]
  simpa only [eta, testDeformation, testCompact, deformedTest] using
    reverse_integral_cubic_unit_change_variable F ζ hζ q S μ (π ^ i.val) c hc
      (fun g => ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1)
      (hM m hm f hf c hc s) x

end DedekindZetaZeroFree.ActualReverseMinorHigherShell

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorStableAssembly
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPTameJacquetTestDuality
open KPTameTransposeKernelUnfoldingRaw KPTameValuationCoordinates
open _root_.DedekindZetaZeroFree.ActualReverseMinorHigherShell renaming eventual_actual_higher_shell_cancellation → eventual_actual_higher_shell_cancellation
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

private theorem valuation_norm_le (x y : LocalField F q) :
    valuation (LocalField F q) x ≤ valuation (LocalField F q) y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v y ↔ _
  exact (Valued.toNormedField.norm_le_iff).symm

private theorem ball_norm (π : (LocalField F q)ˣ) (r : ℕ) (x : LocalField F q) :
    x ∈ expandingBall F q π r ↔ ‖x‖ ≤ ‖(π : LocalField F q)‖⁻¹ ^ r := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (π ^ r).ne_zero
  have hn : ‖a‖ = ‖(π : LocalField F q)‖⁻¹ ^ r := by
    simp [a, norm_inv, norm_pow, inv_pow]
  have hm : ∀ y : LocalField F q, y ∈ (valuation (LocalField F q)).integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← map_one (valuation (LocalField F q)), valuation_norm_le]
    simp
  change (∃ u : (valuation (LocalField F q)).integer, x = a * (u : LocalField F q)) ↔ _
  rw [← hn]
  constructor
  · rintro ⟨u, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hm _).mp u.property)
  · intro hx
    refine ⟨⟨x / a, (hm _).mpr ?_⟩, (mul_div_cancel₀ x ha).symm⟩
    rw [norm_div, div_le_one (norm_pos_iff.mpr ha)]
    exact hx

private theorem stableIntegral_of_higher_shell_cancellation
    (μ : Measure (LocalField F q)) (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (g : LocalField F q → ℂ)
    (hint : ∀ r : ℕ, IntegrableOn g (expandingBall F q π r) μ)
    (hcancel : ∀ r : ℕ, 2 ≤ r →
      (∫ x in expandingBall F q π r \ expandingBall F q π (r - 1), g x ∂μ) = 0) :
    HasStableIntegral F q μ π g
      ((∫ x in lowShell F q, g x ∂μ) +
       (∫ x in conductorOneShell F q π, g x ∂μ)) := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hn : 1 ≤ ‖(π : LocalField F q)‖⁻¹ := by
    have hh := not_le.mpr hv
    rw [← map_one (valuation (LocalField F q)), valuation_norm_le] at hh
    have hp : 0 < ‖(π : LocalField F q)‖ := norm_pos_iff.mpr π.ne_zero
    exact le_of_lt (one_lt_inv₀ hp |>.mpr (by simpa using not_le.mp hh))
  have hmeas : ∀ r, MeasurableSet (expandingBall F q π r) := by
    intro r
    have hset : expandingBall F q π r =
        (fun x : LocalField F q => ‖x‖) ⁻¹' Set.Iic (‖(π : LocalField F q)‖⁻¹ ^ r) := by
      ext x
      exact ball_norm F q π r x
    rw [hset]
    exact measurableSet_Iic.preimage (by fun_prop)
  have hmono : Monotone (expandingBall F q π) := by
    intro r s hrs x hx
    rw [ball_norm] at hx ⊢
    exact hx.trans (pow_le_pow_right₀ hn hrs)
  have hzero : expandingBall F q π 0 = lowShell F q := by
    ext x
    simp only [expandingBall, lowShell, pow_zero, Units.val_one, inv_one, one_mul,
      Set.mem_setOf_eq, Valuation.mem_integer_iff]
    constructor
    · rintro ⟨o, rfl⟩
      exact (Valuation.mem_integer_iff _ _).mp o.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hbase : (∫ x in expandingBall F q π 1, g x ∂μ) =
      (∫ x in lowShell F q, g x ∂μ) +
      (∫ x in conductorOneShell F q π, g x ∂μ) := by
    have he := setIntegral_sdiff (hmeas 0) (hint 1) (hmono (by omega : 0 ≤ 1))
    rw [hzero] at he
    unfold conductorOneShell
    linear_combination -he
  have heq : ∀ r : ℕ, 1 ≤ r →
      (∫ x in expandingBall F q π r, g x ∂μ) =
      (∫ x in expandingBall F q π 1, g x ∂μ) := by
    intro r
    induction r with
    | zero => omega
    | succ r ih =>
      intro hr
      by_cases h : r = 0
      · subst r
        rfl
      · have he := setIntegral_sdiff (hmeas r) (hint (r + 1))
          (hmono (Nat.le_succ r))
        have hc := hcancel (r + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hc
        rw [hc] at he
        exact (sub_eq_zero.mp he.symm).trans (ih (by omega))
  exact ⟨1, fun r hr => ⟨hint r, (heq r hr).trans hbase⟩⟩

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (coordinates : ∀ ε : Sign,
    sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
  (hcoordinates : ∀ ε f g, (coordinates ε f).val g = (f.val g).val 1)

include hcoordinates in
theorem eventual_actual_stable_value_eq_two_shells
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    (hconductor : HasConductorIntegers F q ψ)
    (i : Fin 3) (f' : DiagonalValuations) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π f') m f →
      let Rf := coordinates .plus
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ ((coordinates .minus).symm f))
      HasStableValue F ζ hζ q S P hP .plus π ψ μ (eta F ζ hζ q π i) Rf
        ((∫ x in lowShell F q,
          jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π i) Rf x ∂μ) +
        (∫ x in conductorOneShell F q π,
          jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π i) Rf x ∂μ)) := by
  obtain ⟨M, hM⟩ := eventual_actual_higher_shell_cancellation F ζ hζ q S P hP μ hμ
    coordinates hcoordinates htame π hπ ψ hconductor i f'
  refine ⟨M, ?_⟩
  intro m hm f hf
  dsimp only
  let Rf := coordinates .plus
    (actualCanonicalReverseMap F ζ hζ q S P μ hμ ((coordinates .minus).symm f))
  have hint (r : ℕ) := KPTameJacquetBruhatTests.jacquet_integrable_on_expanding_ball
    F ζ hζ q S P hP .plus π ψ hψ μ (eta F ζ hζ q π i) Rf r
  have hcancel (r : ℕ) (hr : 2 ≤ r) :
      (∫ x in expandingBall F q π r \ expandingBall F q π (r - 1),
        jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π i) Rf x ∂μ) = 0 := by
    simpa only [Rf, jacquetIntegrand, hcoordinates] using hM m hm f hf r hr
  exact stableIntegral_of_higher_shell_cancellation F q μ π hπ _ hint hcancel

end DedekindZetaZeroFree.ActualReverseMinorStableAssembly

end

end
