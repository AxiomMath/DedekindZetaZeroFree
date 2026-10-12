module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps

open scoped NumberField Valued ValuativeRel Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private theorem convolution_eval {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (p : ℤ →₀ (V →ₗ[ℂ] W)) (ψ : ℤ →₀ V)
    (r : ℂ) (hr : r ≠ 0) :
    (∑ n ∈ p.support, ∑ m ∈ ψ.support, Finsupp.single (n + m) ((p n) (ψ m))).sum
      (fun k w => r ^ k • w) =
    (p.sum (fun n M => r ^ n • M)) (ψ.sum (fun m v => r ^ m • v)) := by
  classical
  rw [← Finsupp.sum_finsetSum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  simp only [← Finsupp.sum_finsetSum_index (fun _ => smul_zero _)
    (fun _ _ _ => smul_add _ _ _)]
  simp only [Finsupp.sum_single_index, smul_zero]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, Finset.smul_sum, zpow_add₀ hr, mul_smul]
  rw [Finset.sum_comm]
  congr 1
  ext m
  congr 1
  ext n
  rw [smul_comm]

private theorem root_parameter (r : ℂˣ) :
    KPRankOneRootParameter.r (LocalField F q) (additiveParameter F q r) = (r : ℂ) := by
  have hq1 : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
  have hlog : (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) ≠ 0 := by
    have hl : Real.log (residueCardinality (LocalField F q) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hq1)).ne'
    exact_mod_cast hl
  unfold KPRankOneRootParameter.r additiveParameter
  rw [show -(-Complex.log (r : ℂ) / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) *
      (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) = Complex.log (r : ℂ) by
    field_simp]
  exact Complex.exp_log r.ne_zero

set_option backward.isDefEq.respectTransparency false in

theorem forward_uniform_laurent_numerator
    (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (L : CompactOpenLevel (Cover F ζ hζ q))
    (hL : (L.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup)
    (ψ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .plus L)
    (hinput : ∀ r : ℂˣ,
      actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r =
        centerCompactTrivialization F ζ hζ q T A I .plus (additiveParameter F q r)
          (ψ.sum (fun n f => (r : ℂ) ^ n • f)).val) :
    ∃ χ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .minus L,
      ∀ r : ℂˣ, IsRegular F q r →
        forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r =
          centerCompactTrivialization F ζ hζ q T A I .minus (-additiveParameter F q r)
            ((1 - t F q (r : ℂ))⁻¹ • χ.sum (fun n f => (r : ℂ) ^ n • f)).val := by
  classical
  obtain ⟨p, hp, _⟩ := J.numerators L hL .plus
  let χ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .minus L :=
    ∑ n ∈ p.support, ∑ m ∈ ψ.support, Finsupp.single (n + m) ((p n) (ψ m))
  refine ⟨χ, ?_⟩
  intro r hr
  have heval : evaluationUnit (LocalField F q) .plus (additiveParameter F q r) = r := by
    apply Units.ext
    simp only [evaluationUnit, if_true, KPRankOneRootParameter.rUnit,
      Units.val_mk0, root_parameter]
  have hden : denominator (LocalField F q) .plus (additiveParameter F q r) =
      1 - t F q (r : ℂ) := by
    simp only [denominator, if_true, KPRankOneRootParameter.t, root_parameter, t]
  have ha : denominator (LocalField F q) .plus (additiveParameter F q r) ≠ 0 := by
    rw [hden]
    exact hr
  have hs := J.shell_eq L .plus p hp (additiveParameter F q r) ha
    (ψ.sum (fun n f => (r : ℂ) ^ n • f))
  change J.op .plus (additiveParameter F q r)
    (centerCompactTrivialization F ζ hζ q T A I .plus (additiveParameter F q r)
      (ψ.sum (fun n f => (r : ℂ) ^ n • f)).val) = _ at hs
  unfold forwardSection
  rw [hinput r, hs]
  congr 1
  change ((denominator (LocalField F q) .plus (additiveParameter F q r))⁻¹ •
    (centerEvaluate F ζ hζ q T A I L .plus p
      (evaluationUnit (LocalField F q) .plus (additiveParameter F q r))
      (ψ.sum (fun n f => (r : ℂ) ^ n • f)))).val = _
  rw [heval, hden]
  have hc := convolution_eval
    (V := centerCompactLevel F ζ hζ q T A I .plus L)
    (W := centerCompactLevel F ζ hζ q T A I .minus L) p ψ (r : ℂ) r.ne_zero
  change χ.sum (fun n f => (r : ℂ) ^ n • f) =
    centerEvaluate F ζ hζ q T A I L .plus p r
      (ψ.sum (fun n f => (r : ℂ) ^ n • f)) at hc
  rw [hc]

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps
