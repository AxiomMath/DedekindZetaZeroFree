module

public import DedekindZetaZeroFree.Theta.Unfolding.TameTransposeKernel
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.LowShellContinuation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorConductorOffSupport
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Set Filter
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding KPTameValuationCoordinates
open KPRankOneShellContinuation KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.ActualReverseMinorLowShell renaming numerator_family → numerator_family
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actualTestFamily → actualTestFamily
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testDeformation → testDeformation
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testCompact → testCompact
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actual_test_family_zero → actual_test_family_zero
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actual_test_family_chamber → actual_test_family_chamber
open _root_.DedekindZetaZeroFree.KPTameConductorOneBruhat.StandardIntegral renaming offlabel_standard_zero → offlabel_standard_zero

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

private theorem actual_conductor_coordinate_zero_of_affineLabel_ne_zero
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (a : DiagonalValuations)
    (hne : ((a.1 - a.2 + (i.val : ℤ) + 2 : ℤ) : ZMod 3) ≠ 0)
    (m : ℕ) (hm : 0 < m) (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π a) m f)
    (x : LocalField F q) (hx : x ∈ conductorOneShell F q π) :
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
      ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 = 0 := by
  let f₀ := (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f
  let g := eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) x
  have hz (s : ℂ) (hs : convergenceHalfPlane .minus s) :
      ((actualTestFamily F ζ hζ q S P μ hμ f₀ s).val g).val 1 = 0 := by
    rw [actual_test_family_chamber F ζ hζ q S P μ hμ f₀ s hs g 1]
    have he := offlabel_standard_zero F ζ hζ q S P hP
      (scalarCoordinateEquiv F ζ hζ q S P hP) (by intros; rfl)
      μ π hπ i a hne m hm f hf s x hx
    have hroot (u : LocalField F q) :
        (S.borel.upperRoot (Multiplicative.ofAdd u) : ActualCover F ζ hζ q) =
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) u := by
      simpa only [KPRankOneOpenCellKernel.nLift] using (S.openCell P).upper_eq u
    simpa only [standardIntegralCoordinate, sourceSign, id_eq, testDeformation, testCompact, f₀, g, hroot]
      using he
  obtain ⟨H, _, hH, heH⟩ := numerator_family F ζ hζ q S P μ hμ f₀
  have hev : H g =ᶠ[𝓝 (-1 : ℂ)] (fun _ => (0 : ℂ)) := by
    have hn : ∀ᶠ s : ℂ in 𝓝 (-1 : ℂ), s.re < -(1/6 : ℝ) :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
    filter_upwards [hn] with s hs
    rw [heH s (denominator_ne_zero_of_convergence (LocalField F q) .minus s hs) g,
      hz s hs, mul_zero]
  have he := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun s _ => (hH g).analyticAt s) (fun s _ => analyticAt_const)
    isPreconnected_univ (Set.mem_univ (-1 : ℂ)) hev (Set.mem_univ (0 : ℂ))
  have hd := denominator_ne_zero_at_zero (LocalField F q) .minus
  rw [heH 0 hd g] at he
  simp_rw [actual_test_family_zero F ζ hζ q S P μ hμ f₀] at he
  exact (mul_eq_zero.mp he).resolve_left hd

theorem eventual_actual_conductor_shell_off_support
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i j : Fin 3)
      (f : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((j.val : ℤ), 0)) m f →
      (j.val : ZMod 3) ≠ 1 - (i.val : ZMod 3) →
      (∫ x in conductorOneShell F q π,
        ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
          (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 *
          (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ) = 0 := by
  refine ⟨1, ?_⟩
  intro m hm i j f hf hne
  have hl : (((j.val : ℤ) - 0 + (i.val : ℤ) + 2 : ℤ) : ZMod 3) ≠ 0 := by
    intro h
    apply hne
    push_cast at h
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2] at h
    linear_combination h
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [actual_conductor_coordinate_zero_of_affineLabel_ne_zero F ζ hζ q S P hP μ hμ
    π hπ i ((j.val : ℤ), 0) hl m (by omega) f hf x hx, zero_mul]

end DedekindZetaZeroFree.ActualReverseMinorConductorOffSupport

end
