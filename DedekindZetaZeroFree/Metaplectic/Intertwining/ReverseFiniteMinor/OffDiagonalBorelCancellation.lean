module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseOperatorEvaluation
public import DedekindZetaZeroFree.Theta.Unfolding.TameTransposeKernel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorOffDiagonal
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
open KPTameTransposeLowShellSupport
open _root_.DedekindZetaZeroFree.KPTameTransposeLowShellSupport renaming eventual_actual_compact_normalizers → eventual_actual_compact_normalizers
open _root_.DedekindZetaZeroFree.KPTameTransposeLowShellSupport renaming unitDilation_preservesLowShellHaar → unitDilation_preservesLowShellHaar
open _root_.DedekindZetaZeroFree.KPTameTransposeLowShellSupport renaming unitDilation → unitDilation
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def offDiagonalReverseLinear
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    scalarSections F ζ hζ q S P hP .minus →ₗ[ℂ]
      scalarSections F ζ hζ q S P hP .plus :=
  (scalarCoordinateEquiv F ζ hζ q S P hP .plus).toLinearMap.comp
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm.toLinearMap)

private theorem offDiagonalReverseLinear_intertwines
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (t : ActualCover F ζ hζ q) (f : scalarSections F ζ hζ q S P hP .minus) :
    offDiagonalReverseLinear F ζ hζ q S P hP μ hμ
      (scalarAction F ζ hζ q S P hP .minus t f) =
    scalarAction F ζ hζ q S P hP .plus t
      (offDiagonalReverseLinear F ζ hζ q S P hP μ hμ f) := by
  let v := (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f
  have he : (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm
      (scalarAction F ζ hζ q S P hP .minus t f) = IMinus S.borel P t v := by
    apply (scalarCoordinateEquiv F ζ hζ q S P hP .minus).injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = scalarAction F ζ hζ q S P hP .minus t
      (scalarCoordinateEquiv F ζ hζ q S P hP .minus v)
    rw [LinearEquiv.apply_symm_apply]
  change (scalarCoordinateEquiv F ζ hζ q S P hP .plus)
    (actualCanonicalReverseMap F ζ hζ q S P μ hμ _) = _
  erw [he]
  exact congrArg (scalarCoordinateEquiv F ζ hζ q S P hP .plus)
    (actualCanonicalReverseLinear_intertwines F ζ hζ q S P μ hμ t v)

private theorem actual_lowShell_covariance
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (a e t : ActualCover F ζ hζ q) (m : ℕ)
    (hnormalW : ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (hnormalT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      t⁻¹ * k * t ∈ splitCongruenceSet F ζ hζ q m)
    (bminus bplus : BL F ζ hζ q S P)
    (hbminus : a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) * t =
      bminus * (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))
    (σ : LocalField F q → LocalField F q)
    (hσ : MeasurePreserving σ (μ.restrict (lowShell F q)) (μ.restrict (lowShell F q)))
    (hσemb : MeasurableEmbedding σ)
    (hbplus : ∀ x ∈ lowShell F q,
      (e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (σ x)) * t =
      bplus * (e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f) :
    let J : ℂ := ∫ x in lowShell F q,
      (offDiagonalReverseLinear F ζ hζ q S P hP μ hμ f).val
        (e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∂μ
    chi F ζ hζ q S P hP .minus bminus * J =
      chi F ζ hζ q S P hP .plus bplus * J := by
  let R := offDiagonalReverseLinear F ζ hζ q S P hP μ hμ
  let g : LocalField F q → ActualCover F ζ hζ q := fun x =>
    e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) x
  have hfEigen : scalarAction F ζ hζ q S P hP .minus t f =
      chi F ζ hζ q S P hP .minus bminus • f := by
    apply Subtype.ext
    funext x
    exact minusTest_unit_eigen_of_chart_normalization F ζ hζ q S P hP a t m
      hnormalW hnormalT bminus hbminus f hf x
  have hREigen : scalarAction F ζ hζ q S P hP .plus t (R f) =
      chi F ζ hζ q S P hP .minus bminus • R f := by
    rw [← offDiagonalReverseLinear_intertwines F ζ hζ q S P hP μ hμ]
    rw [hfEigen, map_smul]
  have hpoint : ∀ x ∈ lowShell F q,
      chi F ζ hζ q S P hP .minus bminus * (R f).val (g (σ x)) =
      chi F ζ hζ q S P hP .plus bplus * (R f).val (g x) := by
    intro x hx
    have he := congrArg (fun v : scalarSections F ζ hζ q S P hP .plus =>
      v.val (g (σ x))) hREigen
    change (R f).val (g (σ x) * t) =
      chi F ζ hζ q S P hP .minus bminus * (R f).val (g (σ x)) at he
    rw [hbplus x hx, (R f).property.1] at he
    exact he.symm
  have hsubst : (∫ x in lowShell F q, (R f).val (g (σ x)) ∂μ) =
      ∫ x in lowShell F q, (R f).val (g x) ∂μ :=
    hσ.integral_comp hσemb (fun x => (R f).val (g x))
  dsimp only
  change chi F ζ hζ q S P hP .minus bminus * (∫ x in lowShell F q, (R f).val (g x) ∂μ) =
    chi F ζ hζ q S P hP .plus bplus * (∫ x in lowShell F q, (R f).val (g x) ∂μ)
  calc
    _ = chi F ζ hζ q S P hP .minus bminus * (∫ x in lowShell F q, (R f).val (g (σ x)) ∂μ) := by rw [hsubst]
    _ = ∫ x in lowShell F q, chi F ζ hζ q S P hP .minus bminus * (R f).val (g (σ x)) ∂μ := (integral_const_mul _ _).symm
    _ = ∫ x in lowShell F q, chi F ζ hζ q S P hP .plus bplus * (R f).val (g x) ∂μ :=
      setIntegral_congr_fun (valuation (LocalField F q)).isOpen_integer.measurableSet hpoint
    _ = _ := integral_const_mul _ _

set_option backward.isDefEq.respectTransparency false in

private theorem actual_lowShell_zero_of_full_chi_ne
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (a e t : ActualCover F ζ hζ q) (m : ℕ)
    (hnormalW : ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (hnormalT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      t⁻¹ * k * t ∈ splitCongruenceSet F ζ hζ q m)
    (bminus bplus : BL F ζ hζ q S P)
    (hbminus : a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) * t =
      bminus * (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))
    (σ : LocalField F q → LocalField F q)
    (hσ : MeasurePreserving σ (μ.restrict (lowShell F q)) (μ.restrict (lowShell F q)))
    (hσemb : MeasurableEmbedding σ)
    (hbplus : ∀ x ∈ lowShell F q,
      (e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (σ x)) * t =
      bplus * (e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f)
    (hchi : chi F ζ hζ q S P hP .minus bminus ≠
      chi F ζ hζ q S P hP .plus bplus) :
    let J : ℂ := ∫ x in lowShell F q,
      (offDiagonalReverseLinear F ζ hζ q S P hP μ hμ f).val
        (e * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∂μ
    J = 0 := by
  have hcov := actual_lowShell_covariance F ζ hζ q S P hP μ hμ a e t m hnormalW hnormalT bminus bplus hbminus
    σ hσ hσemb hbplus f hf
  dsimp only at hcov ⊢
  by_contra hJ
  exact hchi (mul_right_cancel₀ hJ hcov)

theorem actual_lowShell_integral_zero_of_differenceLabel_ne_zero
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (hnorm : KPTameTransposeLiteral.RawNormalizedExtension F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (f' : DiagonalValuations)
    (hne : ((f'.1 - f'.2 - (i.val : ℤ) : ℤ) : ZMod 3) ≠ 0) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π f') m f →
      (∫ x in lowShell F q,
        ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
            (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
              KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 ∂μ) = 0 := by
  set_option maxHeartbeats 1000000 in
  obtain ⟨u, hu⟩ := exists_tame_cubic_unit_detecting_exponent F ζ hζ q htame π hπ
    (f'.1 - f'.2 - (i.val : ℤ)) hne
  let a := KPTameLowShellConcreteCharts.diagonalTorus F ζ hζ q π f'
  let e := ActualFiniteTorus.torusLift F ζ hζ q (π ^ i.val)
  let bm := KPTameLowShellConcreteCharts.conjugateUnitBorel F ζ hζ q S P hP a u
  let bp := KPTameLowShellConcreteCharts.conjugateUnitBorel F ζ hζ q S P hP e u
  have hratio := KPTameLowShellConcreteCharts.concrete_chi_ratio F ζ hζ q S P hP
    hnorm π f' i u
  have hchi : chi F ζ hζ q S P hP .minus bm ≠ chi F ζ hζ q S P hP .plus bp := by
    intro heq
    have hp : chi F ζ hζ q S P hP .plus bp ≠ 0 := by
      exact mul_ne_zero (Units.ne_zero _) (Complex.exp_ne_zero _)
    change chi F ζ hζ q S P hP .minus bm / chi F ζ hζ q S P hP .plus bp = _ at hratio
    rw [heq, div_self hp] at hratio
    exact hu hratio.symm
  obtain ⟨M, hM⟩ := eventual_actual_compact_normalizers F ζ hζ q htame
  refine ⟨M, fun m hm f hf => ?_⟩
  have hn := hM m hm
  have hnT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
    (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)⁻¹)⁻¹ * k *
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)⁻¹ ∈
        splitCongruenceSet F ζ hζ q m := by
    simpa only [map_inv] using hn.2 u⁻¹
  have hs : MeasurePreserving (fun x : LocalField F q =>
      x / (KPTameCompact.unitInclusion F q u : LocalField F q))
    (μ.restrict (lowShell F q)) (μ.restrict (lowShell F q)) := by
    convert unitDilation_preservesLowShellHaar F q μ hμ u⁻¹ using 1
    funext x
    change x / (KPTameCompact.unitInclusion F q u : LocalField F q) =
      (KPTameCompact.unitInclusion F q u⁻¹ : LocalField F q) * x
    simp [div_eq_mul_inv, mul_comm]
    all_goals rfl
  have hse : MeasurableEmbedding (fun x : LocalField F q =>
      x / (KPTameCompact.unitInclusion F q u : LocalField F q)) := by
    convert (unitDilation F q u⁻¹).toHomeomorph.measurableEmbedding using 1
    funext x
    change x / (KPTameCompact.unitInclusion F q u : LocalField F q) =
      (KPTameCompact.unitInclusion F q u⁻¹ : LocalField F q) * x
    simp [div_eq_mul_inv, mul_comm]
  simpa [e, ActualFiniteTorus.torusLift, ActualFiniteTorus.normalWord,
    ActualFiniteTorus.central, eta, offDiagonalReverseLinear,
    LinearMap.comp_apply, scalarCoordinateEquiv] using
    actual_lowShell_zero_of_full_chi_ne F ζ hζ q S P hP μ hμ a e
    (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)⁻¹)
    m hn.1 hnT bm bp
    (KPTameLowShellConcreteCharts.inner_chart F ζ hζ q S P hP a u)
    _ hs hse
    (fun x hx => KPTameLowShellConcreteCharts.concrete_outer_chart F ζ hζ q S P hP e u x)
    f hf hchi

end DedekindZetaZeroFree.ActualReverseMinorOffDiagonal

end
