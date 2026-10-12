module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.InverseRootInnerHaarValues

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.TameInverseRootValueAudit
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPRankOneRootParameter
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameTransposeUnitNumeratorSteps
open _root_.DedekindZetaZeroFree.TameInverseRootValueAudit renaming eventual_inverse_root_inner_haar_value → eventual_inverse_root_inner_haar_value

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

 def reverseIntegrand (φ : compactPicture S.borel P S.iwasawa .minus)
    (g : ActualCover F ζ hζ q) (s : ℂ) (v : LocalField F q) : ℂ :=
  ((compactTrivialization S.borel P S.iwasawa .minus (-s) φ).val
    (kernelW (LocalField F q) S.borel .minus *
      (S.borel.upperRoot (Multiplicative.ofAdd v) : ActualCover F ζ hζ q) * g)).val 1

private theorem compact_reverse_endpoint
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (φ : compactLevel S.borel P S.iwasawa .minus J)
    (g : ActualCover F ζ hζ q)
    (C : Set (LocalField F q)) (hC : IsCompact C) (hmC : MeasurableSet C)
    (hsupp : ∀ s v, v ∉ C → reverseIntegrand F ζ hζ q S P φ.val g s v = 0) :
    (∀ s, Integrable (reverseIntegrand F ζ hζ q S P φ.val g s) μ) ∧
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
      (compactTrivialization S.borel P S.iwasawa .minus 0 φ.val)).val g).val 1 =
        ∫ v, reverseIntegrand F ζ hζ q S P φ.val g 0 v ∂μ := by
  have hsupport (s : ℂ) : Function.support (reverseIntegrand F ζ hζ q S P φ.val g s) ⊆ C := by
    intro v hv
    by_contra h
    exact hv (hsupp s v h)
  have hint (s : ℂ) : Integrable (reverseIntegrand F ζ hζ q S P φ.val g s) μ := by
    apply (integrableOn_iff_integrable_of_support_subset (hsupport s)).mp
    exact standardIntegral_integrableOn_compact (LocalField F q) S.borel P S.iwasawa μ
      .minus s φ.val g 1 C hC hmC
  have hcut (s : ℂ) : (∫ v, reverseIntegrand F ζ hζ q S P φ.val g s v ∂μ) =
      ∫ v in C, reverseIntegrand F ζ hζ q S P φ.val g s v ∂μ := by
    rw [← integral_indicator hmC]
    apply integral_congr_ae
    filter_upwards [] with v
    by_cases hv : v ∈ C
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hsupp s v hv]
  obtain ⟨l, hl⟩ := actual_initial_cutoff_laurent F ζ hζ q S P μ .minus φ.val g 1 C hC hmC
  let L : ℂ → ℂ := fun s => l.sum (fun n c => (evaluationUnit (LocalField F q) .minus s : ℂ)^n * c)
  have hL (s : ℂ) : (∫ v, reverseIntegrand F ζ hζ q S P φ.val g s v ∂μ) = L s :=
    (hcut s).trans (hl s)
  let p := actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus
  let N : ℂ → ℂ := fun s => ∑ n ∈ p.support,
    (evaluationUnit (LocalField F q) .minus s : ℂ)^n *
      ((compactTrivialization S.borel P S.iwasawa .plus s
        (((p n) φ).val : compactPicture S.borel P S.iwasawa .plus)).val g).val 1
  let V : ℂ → ℂ := fun s =>
    ((compactTrivialization S.borel P S.iwasawa .plus s
      (actualCanonicalContinued F q ζ hζ S P μ hμ .minus s φ.val)).val g).val 1
  have hV (s : ℂ) : V s = (denominator (LocalField F q) .minus s)⁻¹ * N s := by
    dsimp [V]
    rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .minus s J hJ φ]
    have hv : ((continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus p s φ).val :
        compactPicture S.borel P S.iwasawa .plus) =
        (denominator (LocalField F q) .minus s)⁻¹ •
          ∑ n ∈ p.support, (evaluationUnit (LocalField F q) .minus s : ℂ)^n •
            (((p n) φ).val : compactPicture S.borel P S.iwasawa .plus) := by
      simp only [continuedLevel, evaluate, Finsupp.sum, LinearMap.smul_apply,
        LinearMap.sum_apply, Submodule.coe_smul, Submodule.coe_sum]
    rw [hv]
    change (((compactTrivialization S.borel P S.iwasawa .plus s).toLinearMap _).val g).val 1 = _
    simp only [map_smul, map_sum, Submodule.coe_smul, Submodule.coe_sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hchamber (s : ℂ) (hs : convergenceHalfPlane .minus s) : V s = L s := by
    have he := actualContinued_section_eq_integral F ζ hζ q S P μ hμ
      (actualFamilyUniformizer F q) (actualFamilyUniformizer_spec F q) .minus s hs
      (compactTrivialization S.borel P S.iwasawa .minus (-s) φ.val) g 1
    have he' : V s = ∫ v, reverseIntegrand F ζ hζ q S P φ.val g s v ∂μ := by
      change ((compactTrivialization S.borel P S.iwasawa .plus (- -s)
        (actualContinued F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
          (actualFamilyUniformizer_spec F q) .minus s
          ((compactTrivialization S.borel P S.iwasawa .minus (-s)).symm
            (compactTrivialization S.borel P S.iwasawa .minus (-s) φ.val)))).val g).val 1 = _ at he
      rw [LinearEquiv.symm_apply_apply, neg_neg] at he
      exact he
    exact he'.trans (hL s)
  have hunit : Differentiable ℂ (fun s => (evaluationUnit (LocalField F q) .minus s : ℂ)) := by
    change Differentiable ℂ (fun s => (r (LocalField F q) s)⁻¹)
    apply Differentiable.inv
    · unfold r
      fun_prop
    · intro s
      exact Complex.exp_ne_zero _
  have hN : Differentiable ℂ N := by
    apply Differentiable.fun_sum
    intro n hn
    apply Differentiable.mul
    · exact hunit.zpow (Or.inl (fun s => Units.ne_zero _))
    · have hh := compact_level_holomorphic S.borel P S.iwasawa .plus J hJ ((p n) φ) 1 g 1
      simpa only [map_one, Module.End.one_apply] using hh
  have hLd : Differentiable ℂ L := by
    apply Differentiable.fun_sum
    intro n hn
    exact (hunit.zpow (Or.inl (fun s => Units.ne_zero _))).mul_const _
  have hden : Differentiable ℂ (denominator (LocalField F q) .minus) := by
    change Differentiable ℂ (fun s => 1 - (residueCardinality (LocalField F q) : ℂ) *
      (r (LocalField F q) s)⁻¹ ^ 6)
    fun_prop
  have hEq : N = fun s => denominator (LocalField F q) .minus s * L s := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hN)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr (hden.mul hLd)) (z₀ := (-1 : ℂ))
    have ho : IsOpen {s : ℂ | convergenceHalfPlane .minus s} :=
      isOpen_lt Complex.continuous_re continuous_const
    have hm : (-1 : ℂ) ∈ {s : ℂ | convergenceHalfPlane .minus s} := by
      norm_num [convergenceHalfPlane]
    filter_upwards [ho.mem_nhds hm] with s hs
    have hd := denominator_ne_zero_of_convergence (LocalField F q) .minus s hs
    have hh := hchamber s hs
    rw [hV] at hh
    calc
      N s = denominator (LocalField F q) .minus s *
          ((denominator (LocalField F q) .minus s)⁻¹ * N s) := by
        rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
      _ = _ := congrArg (denominator (LocalField F q) .minus s * ·) hh
  refine ⟨hint, ?_⟩
  rw [actualCanonicalReverseMap_level F ζ hζ q S P μ hμ J hJ φ]
  have he0 := hV (0 : ℂ)
  dsimp [V] at he0
  rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .minus 0 J hJ φ] at he0
  rw [he0]
  rw [congrFun hEq 0, ← mul_assoc,
    inv_mul_cancel₀ (denominator_ne_zero_at_zero (LocalField F q) .minus), one_mul, ← hL]

theorem eventual_actual_inverse_root_endpoint
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
      ∀ u : (KPTameCompact.O F q)ˣ,
      let g := eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q)
          (-(KPTameCompact.unitInclusion F q u : LocalField F q) / π)
      let f₀ := (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f
      let φ₀ := (compactTrivialization S.borel P S.iwasawa .minus 0).symm f₀
      (∃ C : Set (LocalField F q), IsCompact C ∧ MeasurableSet C ∧
        ∀ s : ℂ, Integrable (reverseIntegrand F ζ hζ q S P φ₀ g s) μ ∧
          (∀ v ∉ C, reverseIntegrand F ζ hζ q S P φ₀ g s v = 0)) ∧
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ f₀).val g).val 1 =
        (rootMass F ζ hζ q μ m : ℂ) *
          ((residueCardinality (LocalField F q) : ℂ) ^ (-(i.val : ℤ) - 2)) *
            (ordinaryIota F ζ hζ
              (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^
                ((i.val : ℤ) + 1)) : ℂ) := by
  obtain ⟨M, hM⟩ := eventual_inverse_root_inner_haar_value F ζ hζ q S P hP
    htame hnormalized μ π hπ
  refine ⟨max M 1, ?_⟩
  intro m hm i f hf u
  have hmM : M ≤ m := (le_max_left _ _).trans hm
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hm)
  let g := eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q)
      (-(KPTameCompact.unitInclusion F q u : LocalField F q) / π)
  let f₀ := (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f
  let φ₀ := (compactTrivialization S.borel P S.iwasawa .minus 0).symm f₀
  let A : Set (LocalField F q) := (fun t : LocalField F q =>
    ((π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) : LocalField F q) /
      ((KPTameCompact.unitInclusion F q u : LocalField F q) + π * t)) ''
        rootLevelSet F ζ hζ q m
  let a : LocalField F q := ((π ^ ((i.val : ℤ) + 1) /
    KPTameCompact.unitInclusion F q u : (LocalField F q)ˣ) : LocalField F q)
  let c : (LocalField F q)ˣ := π ^ ((i.val : ℤ) + 2) /
    (KPTameCompact.unitInclusion F q u)^2
  let C : Set (LocalField F q) := (fun t : LocalField F q => a - (c : LocalField F q)*t) ''
    ((valuation (LocalField F q)).integer : Set (LocalField F q))
  have hI : IsCompact ((valuation (LocalField F q)).integer : Set (LocalField F q)) := by
    have hr := isCompact_range (continuous_subtype_val :
      Continuous (fun x : ↥(valuation (LocalField F q)).integer => (x : LocalField F q)))
    convert hr using 1
    ext x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  have hC : IsCompact C := hI.image (continuous_const.sub (continuous_const.mul continuous_id))
  have hmC : MeasurableSet C := hC.measurableSet
  have hAC : A ⊆ C := by
    dsimp [A]
    rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hmpos,
      fullDiagonal_inverse_root_ideal_image F q π hπ u i]
    apply Set.image_mono
    rintro _ ⟨t, _, rfl⟩
    exact t.property
  have hscalar (x : ActualCover F ζ hζ q) : (f₀.val x).val 1 = f.val x := by
    have he := congrArg (fun z : scalarSections F ζ hζ q S P hP .minus => z.val x)
      ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).apply_symm_apply f)
    exact he
  have hz (v : LocalField F q) : reverseIntegrand F ζ hζ q S P φ₀ g 0 v =
      f.val (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) v * g) := by
    unfold reverseIntegrand
    rw [neg_zero, LinearEquiv.apply_symm_apply]
    rw [(S.openCell P).upper_eq]
    exact hscalar _
  obtain ⟨_, hoff, hvalue⟩ := hM m hmM i f hf u
  have hsupp : ∀ s v, v ∉ C → reverseIntegrand F ζ hζ q S P φ₀ g s v = 0 := by
    intro s v hv
    have hvA : v ∉ A := fun h => hv (hAC h)
    have hz0 : reverseIntegrand F ζ hζ q S P φ₀ g 0 v = 0 := (hz v).trans (hoff v hvA)
    let x := kernelW (LocalField F q) S.borel .minus *
      (S.borel.upperRoot (Multiplicative.ofAdd v) : ActualCover F ζ hζ q) * g
    have he0 := initialCoordinate_monomial F ζ hζ q S P .minus φ₀ x 1 0
    have hes := initialCoordinate_monomial F ζ hζ q S P .minus φ₀ x 1 s
    have hu0 : (evaluationUnit (LocalField F q) .minus 0 : ℂ) = 1 := by
      simp [evaluationUnit, rUnit, r]
    rw [hu0, one_zpow, mul_one] at he0
    change reverseIntegrand F ζ hζ q S P φ₀ g 0 v = _ at he0
    rw [← he0, hz0, zero_mul] at hes
    exact hes
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P .minus φ₀
  let φ : compactLevel S.borel P S.iwasawa .minus J := ⟨φ₀, hφ⟩
  have hend := compact_reverse_endpoint F ζ hζ q S P μ hμ J hJ φ g C hC hmC hsupp
  dsimp only
  refine ⟨⟨C, hC, hmC, fun s => ⟨hend.1 s, hsupp s⟩⟩, ?_⟩
  have hback : compactTrivialization S.borel P S.iwasawa .minus 0 φ.val = f₀ :=
    (compactTrivialization S.borel P S.iwasawa .minus 0).apply_symm_apply f₀
  rw [hback] at hend
  exact hend.2.trans ((integral_congr_ae (Filter.Eventually.of_forall hz)).trans hvalue)

end DedekindZetaZeroFree.TameInverseRootValueAudit

end
