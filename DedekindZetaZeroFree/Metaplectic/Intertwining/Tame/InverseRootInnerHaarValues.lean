module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.InverseRootTestIndicators
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RootLevelMassPositivity

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.TameInverseRootValueAudit

open scoped NumberField Classical
open NumberField IsDedekindDomain ValuativeRel MeasureTheory
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameTransposeUnitNumeratorSteps

theorem eventual_inverse_root_inner_haar_value
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : KPTameTransposeLiteral.RawNormalizedExtension F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : Fin 3,
      ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m f →
      ∀ u : (KPTameCompact.O F q)ˣ,
      let g : LocalField F q → ℂ := fun v =>
        f.val (KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
          (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q)
              (-(KPTameCompact.unitInclusion F q u : LocalField F q) / π)))
      let A : Set (LocalField F q) := (fun t : LocalField F q =>
        ((π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) : LocalField F q) /
          ((KPTameCompact.unitInclusion F q u : LocalField F q) +
            (π : LocalField F q) * t)) '' rootLevelSet F ζ hζ q m
      Integrable g μ ∧ (∀ v ∉ A, g v = 0) ∧
        (∫ v : LocalField F q, g v ∂μ) =
          (rootMass F ζ hζ q μ m : ℂ) *
            ((residueCardinality (LocalField F q) : ℂ) ^ (-(i.val : ℤ) - 2)) *
              (ordinaryIota F ζ hζ
                (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^
                  ((i.val : ℤ) + 1)) : ℂ) := by
  obtain ⟨M, hM⟩ := eventual_inverse_root_normalized_test_indicator
    F ζ hζ q S P hP htame hnormalized π hπ
  refine ⟨max M 1, ?_⟩
  intro m hm i f hf u
  have hmM : M ≤ m := (le_max_left _ _).trans hm
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hm)
  dsimp only
  let A : Set (LocalField F q) := (fun t : LocalField F q =>
    ((π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) : LocalField F q) /
      ((KPTameCompact.unitInclusion F q u : LocalField F q) +
        (π : LocalField F q) * t)) '' rootLevelSet F ζ hζ q m
  let e : ℂ := ordinaryIota F ζ hζ
    (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^
      ((i.val : ℤ) + 1))
  have hg : (fun v : LocalField F q =>
      f.val (KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
        (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q)
            (-(KPTameCompact.unitInclusion F q u : LocalField F q) / π)))) =
      A.indicator (fun _ => e) := funext (hM m hmM i f hf u)
  rw [hg]
  have hrootmeas : MeasurableSet (rootLevelSet F ζ hζ q m) :=
    (rootLevelSet_isOpen F ζ hζ q S P m hmpos).measurableSet
  have hA : A = (fun t : LocalField F q =>
      ((π ^ ((i.val : ℤ) + 1) / KPTameCompact.unitInclusion F q u :
        (LocalField F q)ˣ) : LocalField F q) -
      ((π ^ ((i.val : ℤ) + 2) / (KPTameCompact.unitInclusion F q u)^2 :
        (LocalField F q)ˣ) : LocalField F q) * t) '' rootLevelSet F ζ hζ q m := by
    dsimp [A]
    rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hmpos,
      fullDiagonal_inverse_root_ideal_image F q π hπ u i]
  let a : LocalField F q := ((π ^ ((i.val : ℤ) + 1) /
    KPTameCompact.unitInclusion F q u : (LocalField F q)ˣ) : LocalField F q)
  let c : (LocalField F q)ˣ := π ^ ((i.val : ℤ) + 2) /
    (KPTameCompact.unitInclusion F q u)^2
  let E := (MeasurableEquiv.mulLeft₀ (-(c : LocalField F q))
    (neg_ne_zero.mpr c.ne_zero)).trans (MeasurableEquiv.addLeft a)
  have hmeas : MeasurableSet A := by
    rw [hA]
    change MeasurableSet ((fun t => a - (c : LocalField F q) * t) '' _)
    have he : (fun t => a - (c : LocalField F q) * t) = E := by
      funext t
      simp [E, sub_eq_add_neg]
    rw [he]
    exact E.measurableSet_image.mpr hrootmeas
  have hI : IsCompact ((valuation (LocalField F q)).integer : Set (LocalField F q)) := by
    have hr := isCompact_range (continuous_subtype_val :
      Continuous (fun x : ↥(valuation (LocalField F q)).integer => (x : LocalField F q)))
    convert hr using 1
    ext x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  have hrootfin : μ (rootLevelSet F ζ hζ q m) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (b := μ ((valuation (LocalField F q)).integer : Set (LocalField F q)))
    · apply measure_mono
      rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hmpos]
      rintro _ ⟨t, _, rfl⟩
      exact t.property
    · exact hI.measure_lt_top
  have hAfin : μ A ≠ ⊤ := by
    change μ ((fun t : LocalField F q => _) '' rootLevelSet F ζ hζ q m) ≠ ⊤
    rw [fullDiagonal_inverse_root_haar_mass F q ζ hζ S P μ π hπ u i m hmpos]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hrootfin
  refine ⟨(integrable_indicator_iff hmeas).mpr (integrableOn_const hAfin), ?_, ?_⟩
  · intro v hv
    rw [hM m hmM i f hf u v, Set.indicator_of_notMem hv]
  · rw [integral_indicator_const e hmeas]
    have hmass := fullDiagonal_inverse_root_real_mass F q ζ hζ S P μ π hπ u i m hmpos
    change (μ A).toReal = _ at hmass
    rw [show μ.real A = (μ A).toReal from rfl, hmass]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_natCast]
    ring

end DedekindZetaZeroFree.TameInverseRootValueAudit

end
