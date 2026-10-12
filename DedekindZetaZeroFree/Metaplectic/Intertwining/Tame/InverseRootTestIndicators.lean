module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.InverseRootCubeRatios
public import DedekindZetaZeroFree.Metaplectic.Torus.InverseRootCentralSheetValues

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.TameInverseRootValueAudit

open scoped NumberField Classical
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open _root_.DedekindZetaZeroFree.TameInverseRootValueAudit renaming actual_full_inverse_root_factorization → actual_full_inverse_root_factorization
open _root_.DedekindZetaZeroFree.TameInverseRootValueAudit renaming normalized_centre_torus_value → normalized_centre_torus_value
open _root_.DedekindZetaZeroFree.TameInverseRootValueAudit renaming hilbert_shift_by_cube → hilbert_shift_by_cube

theorem eventual_inverse_root_normalized_test_indicator
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : KPTameTransposeLiteral.RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : Fin 3,
      ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m f →
      ∀ u : (KPTameCompact.O F q)ˣ, ∀ v : LocalField F q,
      f.val (KPRankOneShellContinuation.kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
        (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q)
            (-(KPTameCompact.unitInclusion F q u : LocalField F q) / π))) =
      (((fun t : LocalField F q =>
          ((π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) : LocalField F q) /
            ((KPTameCompact.unitInclusion F q u : LocalField F q) +
              (π : LocalField F q) * t)) ''
        rootLevelSet F ζ hζ q m).indicator
        (fun _ => (ordinaryIota F ζ hζ
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^
            ((i.val : ℤ) + 1)) : ℂ))) v := by
  obtain ⟨D, hD, hdeep⟩ := KPLocalChartTopology.deep_chart_topology F ζ hζ q
  obtain ⟨R, hR⟩ := eventual_inverse_root_chart_ratio_cube F ζ hζ q S P hP π hπ
  refine ⟨max D R, ?_⟩
  intro m hm i f hf u v
  have hmd : D ≤ m := (le_max_left _ _).trans hm
  have hmr : R ≤ m := (le_max_right _ _).trans hm
  have hdepth : KPLocalChartTopology.MatrixChartDepth F q m := (hdeep m hmd).1
  let chart : LocalField F q → LocalField F q := fun t =>
    ((π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) : LocalField F q) /
      ((KPTameCompact.unitInclusion F q u : LocalField F q) + (π : LocalField F q) * t)
  change _ = ((chart '' rootLevelSet F ζ hζ q m).indicator (fun _ => _)) v
  by_cases hv : v ∈ chart '' rootLevelSet F ζ hζ q m
  · rw [Set.indicator_of_mem hv]
    obtain ⟨t, ht, rfl⟩ := hv
    have htint := ht
    rw [KPTameTransposeUnitNumeratorSteps.rootLevelSet_eq_congruence_ideal
      F q ζ hζ S P m (lt_of_lt_of_le Nat.zero_lt_one hdepth.1)] at htint
    obtain ⟨t₀, ht₀, htval⟩ := htint
    change (t₀ : LocalField F q) = t at htval
    obtain ⟨w, hw⟩ := KPTameTransposeUnitNumeratorSteps.fullDiagonal_shifted_unit F q π hπ u t₀
    have hw' : (KPTameCompact.unitInclusion F q w : LocalField F q) =
        (KPTameCompact.unitInclusion F q u : LocalField F q) + (π : LocalField F q) * t := by
      simpa only [htval] using hw
    have hchart : chart t = ((π ^ ((i.val : ℤ) + 1) /
        KPTameCompact.unitInclusion F q w : (LocalField F q)ˣ) : LocalField F q) := by
      simp only [chart, Units.val_div_eq_div_val, hw']
    rw [hchart, actual_full_inverse_root_factorization F ζ hζ q S π
      (KPTameCompact.unitInclusion F q u) (KPTameCompact.unitInclusion F q w) i t hw']
    obtain ⟨h, hh, hχ⟩ := normalized_centre_torus_value F ζ hζ q S P hP hnormalized π w i
    let x : LocalField F q := -(KPTameCompact.unitInclusion F q w : LocalField F q) /
      ((π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) : LocalField F q)
    let n := S.borel.upperRoot (Multiplicative.ofAdd x)
    have hn : (n : ActualCover F ζ hζ q) = KPPGLLocalCover.N F ζ hζ (Sum.inr q) x :=
      (S.openCell P).upper_eq _
    let b : BL F ζ hζ q S P :=
      ⟨(n * S.borel.torus h : S.borel.B), ⟨n * S.borel.torus h, by
        change S.borel.retract (n * S.borel.torus h) ∈ HL F ζ hζ q S P
        rw [map_mul, S.borel.retract_upperRoot, S.borel.retract_torus, one_mul]
        exact h.property, rfl⟩⟩
    have hb : retractL F ζ hζ q S P b = h := by
      apply Subtype.ext
      change S.borel.retract (inBorel F ζ hζ q S P b) = h
      have hi : inBorel F ζ hζ q S P b = n * S.borel.torus h := Subtype.ext rfl
      rw [hi, map_mul, S.borel.retract_upperRoot, S.borel.retract_torus, one_mul]
    have hcentral : Commute
        (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q w) ^
            ((i.val : ℤ) + 1))) (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) := by
      have hz := KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q)
        ⟨KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q w) ^
          ((i.val : ℤ) + 1), rfl⟩
      exact ((Subgroup.mem_center_iff.mp hz) _).symm
    have hbval : (b : ActualCover F ζ hζ q) =
        KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)
          (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q w) ^
            ((i.val : ℤ) + 1)) * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) ((KPTameCompact.unitInclusion F q w)^2) := by
      change (n : ActualCover F ζ hζ q) * (S.borel.torus h : ActualCover F ζ hζ q) = _
      rw [hn, S.torus_full, hh, ← mul_assoc, hcentral.eq]
    have hfixed : f.val ((diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1) *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q)) * KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) = 1 := by
      have he := congrArg (fun g : scalarSections F ζ hζ q S P hP .minus =>
        g.val (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1) *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q))) (hf.1 _ ht)
      change f.val (_ * KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) = _ at he
      exact he.trans hf.2.2
    change f.val (_ * _ * _ * ((diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1) *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q)) * KPPGLLocalCover.N F ζ hζ (Sum.inr q) t)) = _
    rw [← hbval, f.property.1, hfixed, mul_one, chi, hb, hχ]
    obtain ⟨y, hy⟩ := hR m hmr u w t ht hw'
    rw [hilbert_shift_by_cube F ζ hζ q π (KPTameCompact.unitInclusion F q u)
      y (KPTameCompact.unitInclusion F q w) hy]
  · rw [Set.indicator_of_notMem hv]
    apply Classical.byContradiction
    intro hnonzero
    have hs := hf.2.1 (show _ ∈ Function.support f.val from hnonzero)
    obtain ⟨t, w, ht, hw, hv'⟩ :=
      KPTameTransposeUnitNumeratorSteps.fullDiagonal_actual_support_inverse_root_chart
        F ζ hζ q S P π hπ i m hdepth u v hs
    apply hv
    refine ⟨t, ht, ?_⟩
    rw [hv', Units.val_div_eq_div_val, hw]

end DedekindZetaZeroFree.TameInverseRootValueAudit

end
